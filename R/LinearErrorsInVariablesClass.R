# LinearErrorsInVariablesClass.R
# Defines the class leiv for linear errors-in-variables objects
# Defines print and plot methods for the class
# Defines a partition integrate function
# Defines a median function
# Defines a probability interval function
# Author: David Leonard
# Date: 26 April 2010

# Date: 17 May 2010
# fix error when leiv is called with cor=0

# Date: 21 May 2010
# fix error when leiv is called with zero covariance data
# fix special handling of singular cases in plot method

# Date: 26 May 2010
# replace beta cdf with equivalent F cdf

# utility function
partitionIntegrate <- function(f,partition,rel.tol=.Machine$double.eps^0.25,abs.tol=rel.tol) {
	# returns an integral calculated as the sum of integrals over a partition of the argument
	# use to force recognition of landmarks in the integrand
	return(sum(
		sapply(index <- 2:length(partition),
			function(index) integrate(f,partition[index-1],partition[index],rel.tol=rel.tol,abs.tol=abs.tol)$value
		)
	))
}

# median function
p50 <- function (p,lower,upper) {
	# returns the median of the density p
	if (lower>0) {
		prob <- function(x) partitionIntegrate(p,c(x,upper,Inf))
	} else {
		prob <- function(x) partitionIntegrate(p,c(-Inf,lower,x))
	}
	return(optimize(function(x) (2*prob(x)-1)^2,lower=lower,upper=upper)$minimum)
}

# probability interval function
probInt <- function (p,partition,level) {
	# returns the shortest (100*level)% probability interval of the density p
	# partition is a vector with components xMin,xMiddle,xMax
	# xMiddle is any point dividing the domain of p into lower and upper tails

	# confirm valid partition
	prob0 <- partitionIntegrate(p,partition)
	intOK <- prob0 > (1+level)/2 # overshoot by half the distance
	while (!intOK) {
		intRange <- range(partition)
		intRange <- intRange-2*(partition[2]-intRange)
		partition <- c(intRange[1],partition[2],intRange[2])
		prob0 <- partitionIntegrate(p,partition)
		intOK <- prob0 > (1+level)/2
	}
	
	part <- function(y) {
		xLower <- optimize(function(x) (p(x)-y)^2,partition[-3])$minimum
		xUpper <- optimize(function(x) (p(x)-y)^2,partition[-1])$minimum
		return(c(xLower,partition[2],xUpper))
	}
	
	prob <- function(y) partitionIntegrate(p,part(y))
	
	yOpt <- optimize(function(y) (prob(y)-level)^2,range(p(partition)))$minimum
	
	return(part(yOpt)[-2])
}


# class definition

setClass("leiv",
	representation(
		slope="numeric",
		intercept="numeric",
		slopeInt="numeric",
		interceptInt="numeric",
		density="function",
		n="numeric",
		cor="numeric",
		sdRatio="numeric",
		xMean="numeric",
		yMean="numeric",
		call="call",
		priorType="character",
		probIntCalc="logical",
		level="numeric",
		x="numeric",
		y="numeric",
		na.action="NULL"
	)
)

# generating function

leiv <-
function(formula, data, subset, n=NULL, cor=NULL, sdRatio=NULL, xMean=0, yMean=0, priorType="cauchy", probIntCalc=FALSE, level=0.95, rel.tol=.Machine$double.eps^0.25, abs.tol=rel.tol, ... ) {
	cl <- match.call()
	if (is.null(n) || is.null(cor) || is.null(sdRatio)) {
		# interpret the call
		mf <- match.call(expand.dots = FALSE)
		m <- match(c("formula", "data", "subset"), names(mf), 0L)
		mf <- mf[c(1L, m)]
		mf$drop.unused.levels <- TRUE
		mf[[1L]] <- as.name("model.frame")
		mf <- eval(mf, parent.frame())
		naAction <- attr(mf,"na.action")
		mt <- attr(mf, "terms")
		y <- model.response(mf, "numeric")
		if (NCOL(y) != 1L) stop("only one dependent variable is supported")
		attr(mt,"intercept") <- 0 # drop intercept from x
		x <- model.matrix(mt, mf)
		if (ncol(x) != 1L) stop("only one independent variable is supported")
		else x <- as.vector(x)
		
		# sufficient statistics
		n <- length(x)
		Sxy <- cov(x,y)
		Sxx <- var(x)
		Syy <- var(y)
		if (Sxx > 0 && Syy > 0)	cor <- Sxy/sqrt(Sxx*Syy)
		else if (Sxx > 0 || Syy > 0) cor <- 1
		else stop ("requires n >= 2 distinct data points")
		sdRatio <- sqrt(Syy/Sxx)
		xMean <- mean(x)
		yMean <- mean(y)
	} else {
		x <- numeric()
		y <- numeric()
		naAction <- NULL
	}
	if (n < 2L) stop("requires n >= 2 data points")

	# all of the following in terms of the dimensionless slope

	if (cor > -1 && cor < 1) {

		# intermediates
		v <- n-1
		vp <- v+1
		vm <- v-1
		s <- sqrt((1-cor^2)/v)

		I <- function(b,r) {
			# central integral of dimensionless, scalar arguments
			tLower <- -r/s
			tUpper <- (b-r)/s
			if (tLower<0 && tUpper>0) tPartition <- c(tLower,0,tUpper)
			else tPartition <- c(tLower,tUpper)
			tIntegral <- partitionIntegrate(
				function(t) {
					F <- vm/vp*(v+t^2)/(tUpper+t-2*tLower)/(tUpper-t)
					return(dt(t,v)*pf(F,vp,vm))
				},tPartition,rel.tol=rel.tol,abs.tol=abs.tol)
			return(tIntegral)
		}

		J <- function(b) {
			# pseudo-likelihood of dimensionless b vector
			sapply(b,
				function(b) {
					bSign <- sign(b)
					bAbs <- bSign*b
					rbSign <- cor*bSign
					return(I(bAbs,rbSign)+I(1/bAbs,rbSign))
				}
			)
		}

		# prior density
		if (priorType=="uniform") {
			prior <- function(b) 1
		} else {
			prior <- function(b) dt(b,df=1) # cauchy
		}

		# unnormalized posterior density
		p0 <- function(b) prior(b)*J(b)

		# normalized posterior density
		if (cor==0) bb <- c(-1,1)
		else {
			bb <- c(cor,1/cor) # (bYX,bXY)
			bb <- bb[order(bb)]
		}
		bPartition <- c(-Inf,bb,Inf)
		k0 <- partitionIntegrate(p0,bPartition)
		p <- function(b) p0(b)/k0

		# posterior median
		if (cor==0) bMedian <- 0
		else bMedian <- p50(p,bb[1],bb[2])
	
		# probability interval
		if (probIntCalc) {
			blim <- bb-10/sqrt(n)*(bMedian-bb)
			partition <- c(blim[1],bMedian,blim[2])
			bInt <- probInt(p,partition,level=level)
		} else {
			level <- numeric(0)
			bInt <- numeric(0)
		}

	} else {
		# all points are colinear
		p <- function(b) ifelse(b==cor,1,0) # posterior density
		bMedian <- cor # posterior median
		if (probIntCalc) {
			bInt <- c(cor,cor)
		} else {
			level <- numeric(0)
			bInt <- numeric(0)
		}
	}
	
	# new leiv object with values in original units
	new("leiv",
		slope=bMedian*sdRatio,
		intercept=yMean-bMedian*sdRatio*xMean,
		slopeInt=bInt*sdRatio,
		interceptInt=if (xMean>0) (yMean-bInt*sdRatio*xMean)[c(2,1)] else yMean-bInt*sdRatio*xMean,
		density=function(b) p(b/sdRatio)/sdRatio,
		n=n,
		cor=cor,
		sdRatio=sdRatio,
		xMean=xMean,
		yMean=yMean,
		call=cl,
		priorType=ifelse(priorType=="uniform","uniform","Cauchy"),
		probIntCalc=probIntCalc,
		level=level,
		x=x,
		y=y,
		na.action=naAction
	)
}

# print method

setMethod("print",
	signature(x="leiv"),
	function (x, digits = max(3, getOption("digits") - 3), ...) 
	{
    	cat("\nCall:\n", deparse(x@call), "\n", sep = "")
    	suffStats <- c(x@n,format(x@xMean,digits=digits),format(x@yMean,digits=digits),format(x@cor,digits=digits),format(x@sdRatio,digits=digits))
    	names(suffStats) <- c("sample size","mean x","mean y","sample cor", "sd ratio")
    	cat("\nSufficient statistics:\n")
    	print(suffStats,quote=FALSE)
    	cat("\n\nPrior type:",x@priorType)
    	cat("\n\nSlope Estimate:",format(x@slope,digits=digits))
    	cat("\n\nIntercept Estimate:",format(x@intercept,digits=digits))
		if (x@probIntCalc)
			cat("\n\nShortest",100*x@level,"% probability intervals:","\nslope (",toString(format(x@slopeInt,digits=digits)),")\nintercept (",toString(format(x@interceptInt,digits=digits)),")")
    	cat("\n\n")
    	invisible(x)
	}
)

# plot method

setMethod("plot",
	signature(x="leiv", y="missing"),
	function (x, plotType="density", xlim=NULL, ylim=NULL, xlab=NULL, ylab=NULL, col=NULL, lwd=NULL, ...) 
	{
		if (plotType=="scatter") {
			if (x@n < 2L) stop("requires n >= 2 data points")
			else if (length(x@x)==0) stop("requires (x,y) data")
			else {
				if (is.null(xlab)) xlab <- "x"
				if (is.null(ylab)) ylab <- "y"
				if (is.null(col)) col <- "black"
				if (is.null(lwd)) lwd <- 1
				plot(x@x, x@y, xlim=xlim, ylim=ylim, xlab=xlab, ylab=ylab, ...)
				if (is.finite(x@slope)) abline(x@intercept, x@slope, col=col, lwd=lwd, ...)
				else abline(v=x@xMean, col=col, lwd=lwd, ...)
			}
		} else {
			if (is.infinite(x@slope)) stop("point mass at infinity")
			else {
				if (is.null(xlab)) xlab <- "slope"
				if (is.null(ylab)) ylab <- "density"
				if (is.null(col)) col <- "black"
				if (x@cor > -1 && x@cor < 1) {
					if (is.null(xlim) || is.null(ylim)) {
						if (x@cor==0) {
							if (is.null(xlim)) xlim <- c(-1,1)-20/sqrt(x@n)*(x@slope-c(-1,1))
							if (is.null(ylim)) ylim <- c(0,1.2*optimize(x@density,xlim,maximum=TRUE)$objective)
						} else {
							bYX <- x@cor*x@sdRatio
							bXY <- x@sdRatio/x@cor
							bb <- c(bYX,bXY)
							bb <- bb[order(bb)]
							if (is.null(xlim)) xlim <- bb-20/sqrt(x@n)*(x@slope-bb)
							if (is.null(ylim)) ylim <- c(0,1.2*optimize(x@density,bb,maximum=TRUE)$objective)
						}
					}
					if (is.null(lwd)) lwd <- 2
					plot(x@density, xlim=xlim, ylim=ylim, xlab=xlab, ylab=ylab, col=col, lwd=lwd, ...)
				} else {
					if (is.null(xlim)) xlim <- x@slope+c(-1,1)
					if (is.null(ylim)) ylim <- c(0,1.2)
					if (is.null(lwd)) lwd <- 1
					plot(x=x@slope, y=1, xlim=xlim, ylim=ylim, xlab=xlab, ylab=ylab, col=col, lwd=lwd, ...)
				}
			}
		}
   		invisible(x)
	}
)
