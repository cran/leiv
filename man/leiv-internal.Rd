\name{leiv-internal}
\alias{p50}
\alias{probInt}
\title{Probability Density Utilities}
\description{
\code{p50} calculates the median of the \code{\link{leiv}} posterior probability density.  \code{probInt} calculates the shortest probability interval of the \code{\link{leiv}} posterior probability density for a given probability level.
}
\usage{
p50(p, interval, subdivisions = 100,
      rel.tol = .Machine$double.eps^0.25,
      abs.tol = rel.tol)

probInt(p, interval, level, subdivisions = 100,
      rel.tol = .Machine$double.eps^0.25,
      abs.tol = rel.tol)
}
\arguments{
  \item{p}{a normalized probability density function.}
  \item{interval}{a vector containing the endpoints of the interval to be searched.}
  \item{level}{the probability level requested.}
  \item{subdivisions}{the maximum number of subintervals (see \code{\link{integrate}}).}
  \item{rel.tol}{the relative accuracy requested (see \code{\link{integrate}}).}
  \item{abs.tol}{the absolute accuracy requested (see \code{\link{integrate}}, \code{\link{optimize}} and \code{\link{uniroot}}).}
}
\details{
Internal functions for integrating the posterior density returned by the function \code{\link{leiv}}.  These functions are not meant to be called by the user.
}
\value{
\code{p50} returns a numeric scalar. \code{probInt} returns a 2-dimensional numeric vector of interval endpoints.
}
\note{
\code{p} must accept a vector of inputs and produce a vector of function evaluations at those points.
\code{rel.tol} cannot be less than \code{max(50*.Machine$double.eps, 0.5e-28)} if \code{abs.tol <= 0}.
}
\seealso{\code{\link{leiv}} for general information; \code{\link{integrate}} for control parameters.}
