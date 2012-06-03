\name{leiv}
\alias{leiv}
\alias{leiv-class}
\alias{leiv-package}
\alias{print-methods}
\alias{print,ANY-method}
\alias{print,leiv-method}
\alias{plot-methods}
\alias{plot,ANY,ANY-method}
\alias{plot,leiv,missing-method}
\title{Bivariate Linear Errors-In-Variables Estimation}
\description{
Generates a linear errors-in-variables object.
}
\usage{
leiv(formula, data, subset, prior = NULL,
      n = NULL, cor = NULL, sdRatio = NULL, xMean = 0, yMean = 0,
      probIntCalc = FALSE, level = 0.95, subdivisions = 100,
      rel.tol = .Machine$double.eps^0.25, abs.tol = 0.1*rel.tol, \dots)

\S4method{print}{leiv}(x, digits = max(3, getOption("digits") - 3), \dots)
\S4method{plot}{leiv,missing}(x, plotType = "density", xlim = NULL, ylim = NULL,
     xlab = NULL, ylab = NULL, col = NULL, lwd = NULL, \dots)
}
\arguments{
  \item{formula}{an optional object of class \code{"\link{formula}"} (or one that can be coerced to that class): a symbolic description of the model to be fitted.  The details of model specification are given in the \sQuote{Details} section of the documentation for \code{\link{lm}}.  An intercept is always included and integrated out as a nuisance parameter: \code{y ~ x}, \code{y ~ 0 + x}, and \code{y ~ x - 1} are equivalent.  If not provided, the sufficient statistics \code{n}, \code{cor}, and \code{sdRatio} must be provided.}
  \item{data}{an optional data frame (or object coercible by \code{\link{as.data.frame}} to a data frame) containing the variables in the model.  If not found in \code{data}, the variables are taken from \code{environment(formula)}, typically the environment from which \code{leiv} is called.}
  \item{subset}{an optional vector specifying a subset of observations to be used in the fitting process.}
  \item{prior}{an optional object of class \code{leiv} to use as the prior density of the scale invariant slope; otherwise the rotationally invariant Cauchy density is used.}
  \item{n}{an optional sample size (if \code{formula} is missing).}
  \item{cor, sdRatio}{optional sample correlation \code{cor(x,y)} and ratio \code{sd(y)/sd(x)} (if \code{formula} is missing).}
  \item{xMean, yMean}{optional sample means \code{mean(x)} and \code{mean(y)} (if \code{formula} is missing).}
  \item{probIntCalc}{logical; if \code{TRUE} returns the shortest (100*\code{level})\% probability intervals; if \code{FALSE} (the default) no probability intervals are returned.}
  \item{level}{the probability level requested (if \code{probIntCalc = TRUE}).}
  \item{subdivisions}{the maximum number of subintervals (see \code{\link{integrate}}).}
  \item{rel.tol}{the relative accuracy requested (see \code{\link{integrate}}).}
  \item{abs.tol}{the absolute accuracy requested (see \code{\link{integrate}}).}
  \item{x}{a \code{leiv} object.}
  \item{digits}{controls formating of \link{numeric} objects.}
  \item{plotType}{specifies the type of plot; if \code{plotType = "density"} (the default) then the posterior density of the slope is plotted; if \code{plotType = "scatter"} then a scatter plot with the fitted line.}
  \item{xlim, ylim}{\var{x} limits \code{c(x1,x2)} and \var{y} limits \code{c(y1,y2)} of the plot.}
  \item{xlab, ylab}{labels for the \var{x} and \var{y} axes of the plot.}
  \item{col, lwd}{color and width of plotted lines.}
  \item{\dots}{additional argument(s) for generic methods.}
}
\details{
Use \code{leiv} to estimate the slope and intercept of a bivariate linear relationship when both variables are observed with error.  The method is exact when the true values and the errors are normally distributed.  The posterior density depends on the data only through the correlation coefficient and ratio of standard deviations; it is invariant to interchange and scaling of the coordinates.
}
\value{
\code{leiv} returns an object of class \code{"leiv"} with the following components:

  \item{slope}{the (posterior median) slope estimate.}
  \item{intercept}{the (maximum likelihood) intercept estimate.}
  \item{slopeInt}{the shortest (100*\code{level})\% probability interval of the slope.}
  \item{interceptInt}{the shortest (100*\code{level})\% probability interval of the intercept.}
  \item{density}{the posterior probability density function.}
  \item{n}{the number of (\var{x},\var{y}) pairs.}
  \item{cor}{the sample correlation \code{cor(x,y)}.}
  \item{sdRatio}{the ratio \code{sd(y)/sd(x)}.}
  \item{xMean}{the sample mean \code{mean(x)}.}
  \item{yMean}{the sample mean \code{mean(y)}.}
  \item{call}{the matched call.}
  \item{probIntCalc}{the logical probability interval request.}
  \item{level}{the probability level of the probability interval.}
  \item{x}{the \var{x} data.}
  \item{y}{the \var{y} data.}
}
\note{
Numerical integration is used to normalize the posterior density.  When the data is nearly linear, normalization using the default tolerance parameters may fail.  Specifying \code{abs.tol = 1e-6} (or smaller) may help, but expect a longer run time.  In general, \code{rel.tol} cannot be less than \code{max(50*.Machine$double.eps, 0.5e-28)} if \code{abs.tol <= 0}.  In addition, when using a sharply peaked \code{leiv} object as a prior density, normalization may fail.  In this case, an alternative is to first fit using the default Cauchy prior, then multiply by the appropriate ratio of prior densities and tackle the normalization outside of the \code{leiv} environment.
}
\references{
Leonard, David. (2011). \dQuote{Estimating a Bivariate Linear Relationship.} \emph{Bayesian Analysis}, 6:727-754. DOI:10.1214/11-BA627.

Zellner, Arnold. (1971). \emph{An Introduction to Bayesian Inference in Econometrics}, Chapter 5. John Wiley & Sons.
}
\author{David Leonard}
\seealso{\code{\link{lm}} for formula syntax; \code{\link{integrate}} for control parameters.}
\examples{
## generate artificial data 
set.seed(1123)
n <- 20
X <- rnorm(n, mean=5, sd=4) # true x
x <- X + rnorm(n, mean=0, sd=5) # observed x
Y <- 2 + X # true y
y <- Y + rnorm(n, mean=0, sd=3) # observed y

## fit with default options
fit <- leiv(y ~ x)
print(fit)
plot(fit) # density plot
dev.new()
plot(fit,plotType="scatter")

## calculate a density to use as an informative prior density of
## the scale invariant slope in a subsequent fit
fit0 <- leiv(n=10, cor=0.5, sdRatio=1.0)
print(fit0)

## refit the data using the informative prior density
fit1 <- leiv(y ~ x, prior=fit0, abs.tol=1e-6)
print(fit1)
}
\keyword{models}
\keyword{regression}
