module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # An ample line induces an isogeny over any field

Source: Milne, Abelian Varieties, I Proposition 8.1 and Remark 8.2, p.35;
Proposition 8.14 and the normalized-difference construction, pp.39–40; §11, p.53.
(blueprint: lem-sfb-ample-line-polarization-isogeny)

The dual datum and normalized difference are the recorded constructions. The kernel
in `IsIsogeny` is scheme-theoretic, so inseparable isogenies are included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The homomorphism classifying the normalized difference of an ample invertible
module is an isogeny. The field is arbitrary and the dual datum is supplied.
`ClassifiesAbelianDifference` uses existence of an isomorphism of the normalized
families. Such an isomorphism can be made rigidified by correcting it by the
pullback, along the second projection, of its identity-axis scalar discrepancy.

Source: Milne AV I Proposition 8.1, Remark 8.2, Proposition 8.14, pp.35, 39–40;
§11 opening, p.53 (blueprint: lem-sfb-ample-line-polarization-isogeny).

Proof plan (the accepted DAG split):
1. Choose an algebraic closure $\Omega/k$ by [def-weil-algebraic-closure], and put $X=A_\Omega$,
$D=(A^\vee)_\Omega$, and $M=L_\Omega$. By [lem-sc-abelian-variety-characterization], both $A$
and $A^\vee$ are geometrically integral; hence $X,D$ are connected and integral by
[def-pc-geometrically-irreducible]. Properness and smoothness survive this base change by
[lem-pc-proper-base-change]. Their group operations base change by the fibre-product universal
property, so $X,D$ are abelian varieties. Apply [lem-trf-scheme-relative-ample-base-change] over
$\operatorname{Spec}k$ to see that $M$ is absolutely ample. The hypotheses are satisfied because
the only nonempty affine open of either field spectrum is the whole spectrum.

2. The pulled-back Poincare module $P_\Omega$ on $X\times_\Omega D$ represents the same
normalized functor over $\Omega$: for any $\Omega$-scheme $T$, regard $T$ as a $k$-scheme and
identify $X\times_\Omega T=A\times_kT$. Its identity rigidification and its geometric-fibre
algebraic triviality are exactly the conditions in [def-sfb-abelian-dual-poincare-datum]. The
unique classifying $k$-map $T\to A^\vee$, paired with the structural map
$T\to\operatorname{Spec}\Omega$, is a unique $\Omega$-map $T\to D$. The tensor group law also
pulls back: the group structure of $D(T)$ is that of $A^\vee(T)$, so the tensor product of the
families classified by $u,v:T\to D$ is classified by $u+v$. Let $E$ and $\mathcal P_X$ be the
dual and Poincare sheaf of $X$ in [lem-sfb-abelian-polarization-calculus]. Applying the two
universal properties to the universal families gives $\Omega$-morphisms $\psi:D\to E$ with
$(1\times\psi)^*\mathcal P_X\simeq P_\Omega$ and $\chi:E\to D$ with
$(1\times\chi)^*P_\Omega\simeq\mathcal P_X$, both respecting rigidifications. They are inverse
because their composites classify the original universal families. The identity $0_D$ classifies
$P_\Omega|_{X\times0}$, which is trivial by the datum, and $0_E$ classifies the trivial family
by the normalization of $\mathcal P_X$ on $X\times0$; uniqueness gives $\psi(0_D)=0_E$. No
compatibility of $\psi$ with the group laws is used below:
[lem-sfb-abelian-polarization-calculus] does not identify the addition of $E$ with tensor
product, so all additive arguments are made in $D$. Write $f:X\to D$ for $(\phi_L)_\Omega$. The
pullback-composition and tensor comparisons [lem-pc-module-pullback-identity-composition,
lem-weil-pbc-module-pullback-tensor] give $N_L|_{X\times X}=N_M$ including the constant
identity-line factor. Thus $f$ classifies $N_M$ in $D$, with its rigidification.

3. Apply [lem-weil-pbc-ample-very-ample-immersion-affine-base] to $X/\Omega$ and $M$. It gives
$d\ge1$ and an immersion $i:X\to\mathbf P^r_\Omega$ with $H:=M^{\otimes d}\simeq i^*\mathcal
O(1)$. We also verify the complete-linear-system convention of [def-sc-ample]. By
[lem-fin-proper-coherent-finite-dimensional], $V=H^0(X,H)$ is finite dimensional; invertibility
makes $H$ coherent since $X$ is finite type over the field. The last clause of
[lem-trf-relative-ample-very-ample], applied to the relatively very ample $H$ and the
quasi-compact structure map of the proper $X$, says that the evaluation quotient is surjective
and that its associated complete-system map $j:X\to\mathbf P(V)$ is an immersion. This
projective space is separated by [lem-trf-projective-bundle-quotient-geometry]. Since $X$ is
proper, [lem-weil-pbc-proper-to-separated] makes $j$ proper. An immersion is a monomorphism, so
[lem-pc-proper-monomorphism-closed] makes $j$ a closed immersion. Hence $H$ is very ample, and
therefore ample in [def-sc-ample].

4. The global generation of $H$ in step 3 and the identity point of the nonempty $X$ give a
nonzero section $s\in H^0(X,H)$: if every section were zero, evaluation at that point could not
generate its one-dimensional fibre. As $X$ is integral,
[lem-pc-nonzero-section-integral-cartier] makes $F=Z(s)$ an effective Cartier divisor. By
[lem-pc-zero-scheme-divisor-iso], $H\simeq\mathcal O_X(F)$. Apply the effective-divisor
criterion in [lem-sfb-abelian-polarization-calculus] to $X,F$: step 3 verified its ampleness
hypothesis in precisely its complete-system convention. Thus the homomorphism
$\phi_H=\phi_{\mathcal O_X(F)}:X\to E$ is surjective and has finite scheme-theoretic kernel. Let
$g:X\to D$ be the map classifying $N_H$ in $D$ (step 2). Then $\psi\circ g$ classifies $(1\times
g)^*P_\Omega\simeq N_H$ in $E$, so $\psi\circ g=\phi_H$ by uniqueness. As $\psi$ is an
isomorphism with $\psi(0_D)=0_E$, $g$ is surjective and $\ker
g=X\times_{D,g,0_D}\operatorname{Spec}\Omega
=X\times_{E,\phi_H,0_E}\operatorname{Spec}\Omega=\ker\phi_H$
is finite. This also covers the empty divisor on a zero-dimensional abelian variety.

5. Expand the four factors of the normalized difference from
[def-sfb-abelian-dual-poincare-datum]. Pullback distributes over tensor product by
[lem-weil-pbc-module-pullback-tensor], and the dual of a tensor power of a line is its inverse
tensor power (checked on a local generator and evaluation). Consequently $N_H=N_{M^{\otimes
d}}\simeq N_M^{\otimes d}$ with the identity-axis trivialization; the constant factor is
$(0^*M)^{\otimes d}$ on both sides. The datum's tensor group law in $D$ (step 2) says that the
family on the right is classified by the $d$-fold sum $f+\dots+f=[d]_D\circ f$ in $D(X)$. Its
uniqueness therefore gives $g=[d]_D\circ f$. Since $f=(\phi_L)_\Omega$ is a group homomorphism,
repeated addition also gives $[d]_D\circ f=f\circ[d]_X$. These are identities of morphisms,
obtained from rigidified families, not only identities on geometric points.

6. Surjectivity of $g=f\circ[d]_X$ implies surjectivity of $f$: a point in the image of $g$ is
the image under $f$ of the corresponding point under $[d]_X$. Let $K=\ker f$ and $K_d=\ker g$.
By [lem-sc-kernel-subgroup], both are closed subgroup schemes of $X$. The equality $g=[d]_D\circ
f$ gives a factorization $K\to K_d$ of their closed immersions into $X$. This is a closed
immersion: locally in $X$, the ideals satisfy $I_{K_d}\subseteq I_K$, so the induced map is the
quotient by $I_K/I_{K_d}$. Since $K_d$ is finite over $\Omega$, it is affine with
finite-dimensional coordinate algebra by [def-weil-finite-integral-morphism]; its closed
subscheme $K$ has a quotient coordinate algebra, still finite dimensional, and is therefore
finite. Nilpotents are retained in this quotient argument; reducedness of either kernel is not
used.

7. The singleton $\operatorname{Spec}\Omega\to\operatorname{Spec}k$ is an fpqc covering in
[def-weil-pbc-fpqc-covering]: it is flat by [lem-pc-field-extension-flat], and the one affine
source covers the one-point target. Its pullback $D\to A^\vee$ is an fpqc covering, hence
surjective, by [lem-galois-fpqc-covering-base-change]. By step 2, $f$ is exactly
$(\phi_L)_\Omega$, so step 6 proves this base-changed homomorphism surjective. For any point
$y\in A^\vee$ choose a point of $D$ over it and then a preimage under $(\phi_L)_\Omega$; its
projection to $A$ maps to $y$. Thus $\phi_L$ is surjective. Moreover the kernel fibre product
commutes with this scalar extension:
$(A\times_{A^\vee,\phi_L,0}\operatorname{Spec}k)_\Omega
=X\times_{D,(\phi_L)_\Omega,0}\operatorname{Spec}\Omega$,
by the universal property of the two fibre products [lem-sc-kernel-subgroup]. Step 6 makes the
latter finite. Apply [lem-weil-pbc-fpqc-descend-finite] to the former kernel's structure map and
the same fpqc covering to conclude that $\ker\phi_L$ is finite over $k$.

8. The given $\phi_L$ is a group-scheme homomorphism, and step 7 supplies surjectivity and
finiteness of its scheme-theoretic kernel. These are exactly the two requirements of
[def-sc-isogeny]. The algebraic-closure reduction used neither perfectness of $k$ nor a
prime-to-characteristic tensor exponent; the quotient-algebra and fpqc arguments allow
nonreduced kernels.
-/
theorem IsAbelianVariety.isIsogeny_of_isAmple_classifiesAbelianDifference
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (D : AbelianDualPoincareDatum A) (L : A.left.Modules) [L.IsInvertible]
    (hL : Scheme.Modules.IsAmple A.left L) (φ : A ⟶ D.dual) [IsMonHom φ]
    (hφ : ClassifiesAbelianDifference D L φ) : IsIsogeny φ := by
  sorry

end AlgebraicGeometry
