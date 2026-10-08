+++
id = "sk-p-dl-a1-middle"
kind = "section"
title = "Irreducible middle extensions under Fourier"
order = 2750
uses = ["sk-d-dl-a1-setup", "sk-i-dl-a1-local", "sk-p-dl-a1-perverse", "sk-thm-inversion"]
lean = ["AlgebraicGeometry.WeilSheaf.IsNonexceptional", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierPartner", "AlgebraicGeometry.exists_middleExtension_fourierTransform", "AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity"]
+++
*Proposition (sketch).*

Call a nonzero irreducible lisse Weil sheaf $M$ on $U_0$
*nonexceptional* if none of its geometric irreducible constituents
is $\mathcal L_{\psi(ax)}|_U$, for any $a\in k$, including $a=0$.
For such $M$, there are a dense open $j':U'_0\hookrightarrow A'_0$ and
a nonzero irreducible lisse Weil sheaf $M'$ with

$$
\DLAFT_\psi((j_*M)[1])\simeq(j'_*M')[1].
$$

If $M$ is unramified at infinity and not geometrically constant, it is
nonexceptional.

## Proof

The simple objects in the curve perverse heart are punctual objects
and $(j_*M)[1]$ for irreducible lisse $M$. This follows by restricting
to a lisse open and using the absence of boundary subobjects and
quotients in intermediate extension. Fourier preserves simplicity.
The inverse transform of a punctual object is geometrically a sum of
shifted linear Artin–Schreier sheaves. Conversely, such linear
characters transform to punctual objects, so nonexceptionality forces
one-dimensional support and the displayed middle-extension form.

For the last assertion, nonzero linear characters are excluded by
their ramification at infinity. A geometric constant constituent in an
irreducible Weil representation forces geometric constancy: restriction
to the normal geometric subgroup is semisimple, since translates of a
minimal nonzero invariant subspace span the irreducible representation.
Its nonzero space of geometric invariants is then Weil-stable and must
be the whole representation. This also explains why arithmetic
irreducibility suffices; geometric irreducibility is not assumed.

Uses: [sk-d-dl-a1-setup], [sk-i-dl-a1-local], [sk-p-dl-a1-perverse], [sk-thm-inversion]
