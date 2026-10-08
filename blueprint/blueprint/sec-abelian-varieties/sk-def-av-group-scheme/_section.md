+++
id = "sk-def-av-group-scheme"
kind = "section"
title = "Group schemes, order, and étaleness"
lean = ["CategoryTheory.GrpObj.ker", "AlgebraicGeometry.Scheme.Hom.finrankΓ"]
order = 421
+++
*Definition (sketch).*

Let $k$ be a field. A *group scheme* over $k$ is a group object
in the category of $k$-schemes: a $k$-scheme $G$ with $k$-morphisms
$m:G\times_kG\to G$ (multiplication), $e:\Spec k\to G$ (unit) and
$i:G\to G$ (inverse) satisfying the group axioms. A *closed
subgroup scheme* is a closed subscheme stable under $m$, $e$, $i$;
the *kernel* $\ker(f)$ of a homomorphism $f:G\to H$ is the fibre
product $G\times_H\Spec k$ along $e_H$, a closed subgroup scheme. A
group scheme is *commutative* if $m=m\circ s$, $s$ the swap of
the two factors. For $G$ finite over $k$ its *order* is
$\lvert G\rvert:=\dim_k\Gamma(G,\cO_G)$; $G$ is *étale* over
$k$ if its structure morphism is étale, equivalently if $\cO_G$ is
a finite étale $k$-algebra.
