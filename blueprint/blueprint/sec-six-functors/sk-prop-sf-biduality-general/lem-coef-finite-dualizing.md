+++
id = "lem-coef-finite-dualizing"
kind = "lemma"
title = "Finite coefficient change for the dualizing object"
order = 2140
uses = ["cor-amb-affine-space-adjunction", "lem-amb-etale-adjoint-locality", "lem-coef-finite-closed-shriek", "lem-fix-compact-support-coefficient-change", "lem-weil-finite-duality-site-comparison", "lem-weil-verdier-preservation-strata"]
+++
Let $a_X:X\to\operatorname{Spec}k$ and
$\omega_{X,A}=Ra_{X,A}^{\times}A$. There is a canonical
isomorphism

$$
u_{X,A,B}:\omega_{X,A}\otimes_A^LB
\xrightarrow{\sim}\omega_{X,B}.
$$

It is the adjoint, for $Ra_{X,B!}\dashv Ra_{X,B}^{\times}$, of

$$
Ra_{X,B!}(\omega_{X,A}\otimes_A^LB)
\cong(Ra_{X,A!}\omega_{X,A})\otimes_A^LB
\longrightarrow A\otimes_A^LB=B.
$$

These maps satisfy the quotient cocycle and carry the reduction
of the dualizing counit to the dualizing counit.

## Proof

The object $\omega_{X,A}$ is finite-Tor constructible by
[lem-weil-verdier-preservation-strata], applied to $A_X$.
Thus compact-support coefficient comparison
[lem-fix-compact-support-coefficient-change] constructs the
displayed adjoint map without any coefficient compatibility
assumption on an exceptional right adjoint.

By [lem-amb-etale-adjoint-locality], the assertion is local
on $X$. Choose an affine open and a closed embedding
$i:X\hookrightarrow\mathbf A^r_k$. Composition of ambient
right adjoints and [cor-amb-affine-space-adjunction] give

$$
\omega_{X,A}=Ri_A^!A(r)[2r],\qquad
\omega_{X,B}=Ri_B^!B(r)[2r].
$$

The Tate rank-one object at $A$ reduces to the one at $B$,
and shifts commute with coefficient tensor. Applying
[lem-coef-finite-closed-shriek] therefore proves the displayed
map is an isomorphism. The local map is the global map defined
above: transposing it under the composite adjunction yields the
closed-immersion counit followed by the affine-space counit,
which is the structure-morphism counit. In particular these
maps agree on overlaps. The same adjoint calculation proves
the quotient cocycle and compatibility with the counit.
The dualizing-object comparison of
[lem-weil-finite-duality-site-comparison] transports this
canonical map to the finite pro-etale realization.
