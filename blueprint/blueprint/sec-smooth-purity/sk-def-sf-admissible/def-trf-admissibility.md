+++
id = "def-trf-admissibility"
kind = "definition"
title = "Exceptional-adjoint admissibility datum"
order = 1512
uses = ["def-trf-coefficient-conventions", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, and let $f:X\to Y$ be a
separated finite-type
morphism of finite-type $k$-schemes. Say that $f$ is
*exceptionally admissible at $A$* when the compact-support direct image
$Rf_!:D^b_{ctf}(X,A)\to D^b_{ctf}(Y,A)$ has a specified right adjoint
$Rf^!:D^b_{ctf}(Y,A)\to D^b_{ctf}(X,A)$, with unit
$\operatorname{id}\to Rf^!Rf_!$ and counit
$Rf_!Rf^!\to\operatorname{id}$ (i.e. the adjunction $Rf_!\dashv Rf^!$),
and the composition and base-change exchange isomorphisms used below; and
*exceptionally admissible* when this holds at every finite coefficient stage
$A=A_{E,n}$ with constants independent of $n$. The functor in question is
the constructible exceptional inverse image of
[def-weil-exceptional-inverse-image], and the condition is a *theorem*, not a
restriction: every separated finite-type morphism of finite-type $k$-schemes
is exceptionally admissible, the adjunction on $D^b_{ctf}$ being
thm-sf-ambient-adjoint-class, the preservation
$Rf^!D^b_{ctf}(Y,A)\subseteq D^b_{ctf}(X,A)$ with stage-independent constants
being thm-sf-preservation-class, and the composition and base-change
isomorphisms being the mates of those of $Rf_!$. The trace-formula chapter
names the condition only to make explicit which functor each statement uses.
Nothing of the strong ambient notion of
[def-weil-exceptional-adjoint-admissibility] — the ambient datum
$\operatorname{FullCD}$ on every pro-etale sheaf together with an ambient
right adjoint — is assumed: that datum fails in general (for an elliptic
curve over $\overline{\mathbf F}_p$ with $A=\mathbf F_r$;
rem:sf-ambient-counterexample in the six-functors chapter), and no
preservation clause is assumed either.

*Recorded in advance* from chapter *The trace formula* of the source.
