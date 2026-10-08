+++
id = "lem-sc-principal-ideal-dvr"
kind = "lemma"
title = "Local domains with principal maximal ideal"
order = 687
+++
A noetherian local domain $(R,\mathfrak m)$ with principal
maximal ideal $\mathfrak m=(t)$, $t\neq0$, is a discrete
valuation ring.

## Proof

First, $\bigcap_{n\geq0}\mathfrak m^n=0$. This is the Krull
intersection theorem, which we derive from the Artin–Rees lemma
(*reference: Stacks Project, Commutative Algebra, Lemma
10.51.2, [Tag 00IN](https://stacks.math.columbia.edu/tag/00IN) (Artin–Rees) and Lemma 10.51.4,
[Tag 00IP](https://stacks.math.columbia.edu/tag/00IP) (Krull's intersection theorem)*): if
$0\neq x\in E:=\bigcap_n\mathfrak m^n$, Artin–Rees applied to
the submodule $(x)\subseteq R$ gives a $c$ with

$$
x\in\mathfrak m^n\subseteq\mathfrak m^n\cap(x)
=\mathfrak m^{n-c}(\mathfrak m^c\cap(x))\subseteq\mathfrak m^{n-c}x
\qquad(n\geq c),
$$

so $x=xy_n$ with $y_n\in\mathfrak m^{n-c}$, hence
$x(1-y_n)=0$, and $1-y_n$ is a unit (it is not in
$\mathfrak m$), forcing $x=0$. Hence for every nonzero
$x\in R$ there is a unique $n\geq0$ with
$x\in\mathfrak m^n\setminus\mathfrak m^{n+1}$. Since
$\mathfrak m^n=(t^n)$, such an $x$ has the form $x=t^nu$ with
$u\notin\mathfrak m$, i.e. $u$ a unit. It follows that every
nonzero ideal equals a power of $(t)$: given an ideal
$\mathfrak a\neq0$, choose a nonzero $x\in\mathfrak a$ and
write $x=t^nu$ with $u$ a unit, so that $t^n\in\mathfrak a$;
if $m=\min\{n:t^n\in\mathfrak a\}$, then every
$y\in\mathfrak a$ is $t^rv$ with $r\geq m$, so
$y\in(t^m)$, and $\mathfrak a=(t^m)$. Thus $R$ is a local
PID, i.e. a discrete valuation ring: the function $v(x)=n$ for
$x=t^nu$ a unit (and $v(0)=+\infty$) is a discrete valuation
with $R=\{x:v(x)\geq0\}$ and
$\mathfrak m=\{x:v(x)>0\}$.
