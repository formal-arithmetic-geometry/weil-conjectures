+++
id = "sk-prop-av-mult-n-pullback"
kind = "section"
title = "Pullback of symmetric modules under multiplication by $n$"
lean = ["AlgebraicGeometry.nonempty_iso_overPullback_npow_id"]
order = 481
uses = ["sk-def-av", "sk-def-av-mult-n", "sk-prop-av-cube", "sk-prop-av-symmetric-ample"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety over $k$, let $\cN$ be an invertible
$\cO_A$-module with $[-1]^*\cN\cong\cN$, and let $n\ge1$. Then, with
$[n]$ as in [sk-def-av-mult-n],

$$
[n]^*\cN\cong\cN^{\otimes n^2}.
$$

## Proof

Pull the cube relation of [sk-prop-av-cube] back along
$x\mapsto(x,x,-x)$: here $m_{123}(x,x,-x)=x$, $m_1=m_2=\mathrm{id}$,
$m_3=[-1]$, $m_{12}=[2]$ and $m_{13}=m_{23}=0$, so
$\cL^{\otimes3}\otimes[-1]^*\cL\cong[2]^*\cL$; for symmetric $\cN$
this reads $[2]^*\cN\cong\cN^{\otimes4}$. Next pull back along
$x\mapsto(x,x,[n-1]x)$: here $m_{123}=[n+1]$, $m_1=m_2=\mathrm{id}$,
$m_3=[n-1]$, $m_{12}=[2]$ and $m_{13}=m_{23}=[n]$, giving

$$
[n+1]^*\cN\otimes\cN^{\otimes2}\otimes[n-1]^*\cN
\cong[2]^*\cN\otimes[n]^*\cN^{\otimes2}.
$$

Induction on $n$ (basis $n=1$ trivial, $n=2$ just proved) yields
$[n+1]^*\cN\cong\cN^{\otimes(4+2n^2-2-(n-1)^2)}=\cN^{\otimes(n+1)^2}$.

Uses: [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-cube], [sk-prop-av-symmetric-ample]
