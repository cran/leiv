\name{leiv-internals}
\alias{partitionIntegrate}
\alias{p50}
\alias{probInt}
\title{Integration Utilities}
\description{
\code{partitionIntegrate} integrates a function by summing integrals over a partition of the integration interval. \code{p50} calculates the median of a normalized probability density.  \code{probInt} calculates the shortest probability interval of a normalized probability density for a given probability level.
}
\usage{
partitionIntegrate(f, partition,
      rel.tol = .Machine$double.eps^0.25,
      abs.tol = rel.tol)

p50(p, lower, upper)

probInt(p, partition, level)
}
\arguments{
  \item{f}{an \R function taking a numeric first argument and returning a numeric vector of the same length.  Returning a non-finite element will generate an error.}
  \item{partition}{for \code{partitionIntegrate}, a vector of breakpoints (including the endpoints, possibly \code{Inf}) of the integration domain of \code{f}; for \code{probInt}, a vector of three ordered values that divide the domain of \code{p} into two tails.}
  \item{rel.tol}{the relative accuracy requested (see \code{\link{integrate}}).}
  \item{abs.tol}{the absolute accuracy requested (see \code{\link{integrate}}).}
  \item{p}{a normalized probability density function.}
  \item{lower,upper}{the endpoints of a search interval for the median.}
  \item{level}{the probability level requested.}
}
\details{
Internal functions for calculating and integrating the posterior density returned by the function \code{\link{leiv}}.  These functions are not meant to be called by the user.
}
\value{
\code{partitionIntegrate} and \code{p50} return a numeric scalar. \code{probInt} returns a 2-dimensional numeric vector of interval endpoints.
}
\note{
\code{f} and \code{p} must accept a vector of inputs and produce a vector of function evaluations at those points.
}
\seealso{\code{\link{leiv}} for general information; \code{\link{integrate}} for tolerance parameters.}
