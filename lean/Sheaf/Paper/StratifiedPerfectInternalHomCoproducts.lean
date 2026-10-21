/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Internal Hom and bounded-below sums for stratified perfect sources

Source: Bhatt--Scholze, Lemma 6.3.14(2)--(4), its final devissage, and Lemma 6.8.12.
(blueprint: lem-weil-pbc-stratified-perfect-internal-hom-coproducts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Internal derived Hom from a bounded-above stratified perfect source preserves
uniformly bounded-below coproducts, before applying derived global sections.
The local perfect models use the actual completed coefficient ring on every stratum.
Source: Bhatt--Scholze, Lemma 6.3.14(2)--(4), the closed-stratum argument at the end
of its proof, and the same argument in Lemma 6.8.12.
(blueprint: lem-weil-pbc-stratified-perfect-internal-hom-coproducts).

Proof:
1. For a ring sheaf R on a qcqs scheme S and B bounded above by b, define C_S(B)
by global Hom continuity on every qcqs pro-etale slice. The lower bound N-b for
internal Hom, and the affine weakly contractible hypercover computation of derived
sections, identify C_S(B) with invertibility of the internal coproduct comparison.
Indeed the comparison cone is zero if its cohomology sections vanish on all affine
weakly contractible objects, since such objects cover every affine. Exact slice
restriction preserves coproducts and internal Hom, so this property is local for
qcqs pro-etale covering families. All coefficients here are inverse images of R.
2. The class C is closed under shifts, finite sums, retracts and triangles: Hom
is triangulated in the source, and direct sums of triangles are triangles. The
comparison maps form a morphism of triangles, so the long exact cohomology sequence
proves two-out-of-three. The unit belongs to C by bounded-below continuity of derived
sections. A bounded finite-projective A-complex, tensored with R, belongs to C by
its finite stupid-truncation triangles and finite-projective retracts of finite free
modules. Flatness of the completed constant algebra identifies this with the
recorded integralConstantDerived realization.
3. For a quasi-compact open immersion j, exact extension by zero is left adjoint
to restriction. It therefore carries C_U to C_S: the derived adjunction identifies
Hom out of j_!B with Hom out of B into the restricted target. Restriction preserves
the common lower bound and sums. This argument applies on every qcqs slice;
restriction of extension by zero is extension by zero on the corresponding open.
4. Let i:Z→S be closed with quasi-compact open complement and let L on Z be
locally a finite-projective tensor model. Work affine locally on S. Refine the
trivializing cover of Z by a finite family of affine ind-etale objects and lift
them to affine pro-etale objects of S by the closed-site lifting functor. Together
with the open complement they cover S. Closed pushforward restricts to the closed
pushforward on each lifted object, with the inverse-image ring coefficients.
There L is the restriction of a perfect tensor model P on the ambient object.
The localization triangle j_!P|_U→P→i_*L and steps 2 and 3 put i_*L in C.
Locality then gives the claim on S. This uses closed-pushforward base change,
not commutation of internal Hom with arbitrary closed inverse image.
5. Refine the finite locally closed stratification of K to a finite closed
filtration by membership patterns in the finitely many opens defining its strata.
Give closed sets their reduced induced structures. Each reduced pattern piece
factors through its original stratum, since its image lies there; pulling back a
finite-projective splitting preserves its tensor description. Thus every layer
is still locally perfect. All complementary opens are quasi-compact since T is
Noetherian. Write U_k for their decreasing sequence of open complements.
6. The localization triangles for j_{k,!}K|_{U_k} have third vertices given by
extension by zero of closed pushforwards from these layers. Steps 3 and 4 place
these vertices in C. Starting at the empty open and using triangle closure proves
C_T(K). Compositions of open extension functors are identified as left adjoints to
the same composite restriction, so these are the actual localization triangles.
7. By step 1 the internal comparison is an isomorphism. Equivalently the image
under internal Hom of any colimit cofan is colimiting, which is PreservesColimit.
The argument works for arbitrary integer N and includes empty coproducts. -/
theorem integralStratifiedPerfect_internalHom_preservesColimit
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b : ℤ) [K.IsLE b] (hK : IsIntegralStratifiedPerfect T d K)
    (I : Type (u + 1)) (M : I → DerivedCategory
      (pbcModules T (pbcAdicCompletion T d)))
    (N : ℤ) (hM : ∀ i, (M i).IsGE N) :
    PreservesColimit (Discrete.functor M)
      ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
        (ProEt.topology T) (pbcAdicCompletion T d))).obj (op K)) := by sorry

end AlgebraicGeometry.Scheme
