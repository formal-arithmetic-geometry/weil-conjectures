+++
id = "lem-wf-deep-principal-unit-log"
kind = "lemma"
title = "The logarithm on sufficiently deep principal units"
order = 2615
+++
Let $E/\mathbf Q_\ell$ be finite, with valuation ring
$\mathcal O_E$, maximal ideal $\mathfrak m_E$, and normalized valuation
$v_E(\mathfrak m_E)=1$. If $e=v_E(\ell)$, then for every integer

$$
r>\frac{e}{\ell-1}
$$

the power series

$$
\log(1+x)=\sum_{n\geq1}(-1)^{n+1}\frac{x^n}{n},
\exp(x)=\sum_{n\geq0}\frac{x^n}{n!}
$$

converge on $\mathfrak m_E^r$, are inverse there, and give mutually
inverse continuous group homomorphisms

$$
\log:1+\mathfrak m_E^r\xrightarrow{\sim}\mathfrak m_E^r,
\qquad
\exp:\mathfrak m_E^r\xrightarrow{\sim}1+\mathfrak m_E^r.
$$

Moreover, there is an integer $N\geq1$ such that
$u^N\in1+\mathfrak m_E^r$ for every $u\in\mathcal O_E^\times$.

## Proof

For $x\in\mathfrak m_E^r$,

$$
v_E(x^n/n)\geq nr-e\,v_\ell(n)\longrightarrow+\infty.
$$

Also $v_\ell(n!)\leq n/(\ell-1)$, so

$$
v_E(x^n/n!)\geq n\left(r-\frac e{\ell-1}\right)
\longrightarrow+\infty.
$$

Thus both series converge. The formal identities
$\log(\exp x)=x$, $\exp(\log(1+x))=1+x$, and
$\log((1+x)(1+y))=\log(1+x)+\log(1+y)$ may be evaluated in this
domain, because every series involved converges there. They prove that
$\log$ and $\exp$ are inverse continuous homomorphisms; in particular
$\log$ is injective. The quotient
$\mathcal O_E^\times/(1+\mathfrak m_E^r)$ is finite. Taking $N$ to be
its exponent gives the last assertion. The strict inequality on $r$
also covers $\ell=2$, so no shallow principal-unit torsion remains in the
logarithm domain.
