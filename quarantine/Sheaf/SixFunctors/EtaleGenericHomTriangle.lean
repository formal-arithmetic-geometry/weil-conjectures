/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfHomTriangulated
import Sheaf.SixFunctors.EtaleHomComplexPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Étale pullback comparison for internal Hom triangles

Source: `literature/stacks-project/sites-cohomology.tex`, Tags 08J7 and 08JC
(lemma-RHom-triangulated), and the evaluation-induced pullback compatibility in the proof
of the finite-stratification comparison (blueprint: lem-sf-etale-generic-hom-triangle).

The contravariant Hom shift is constructed by adjunction transport from the canonical
first-factor tensor shift and `commShiftDerivedHomObj`. Derived pullback retains its global
canonical shift instance. The comparison itself is the evaluation transpose.
-/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

section CanonicalShift

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : Scheme.{u}}
/-- Naturality of the canonical first-factor tensor shift.
Source: Stacks Tag 08JC; the signed tensor shift in the comparison proof
(blueprint: lem-sf-etale-generic-hom-triangle).
Proof: use the naturality in the fixed right factor of the canonical two-variable derived
 tensor shift, supplied by `DerivedCategory.commShift₂CurriedTensor`. Its component at K is
 precisely the displayed equality. -/
theorem etaleInternalHomTensorShift_naturality
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    {N N' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (f : N ⟶ N') :
    ((derivedTensor B X).obj (K⟦n⟧)).map f ≫
        (((derivedTensor B X).flip.obj N').commShiftIso n).hom.app K =
      (((derivedTensor B X).flip.obj N).commShiftIso n).hom.app K ≫
        (shiftFunctor _ n).map (((derivedTensor B X).obj K).map f) := by
  sorry
/-- The canonical first-factor tensor shift, naturally in the other factor.
Source: Stacks Tag 08JC; signed cochain tensor shifts
(blueprint: lem-sf-etale-generic-hom-triangle).
The components are the existing canonical `commShiftDerivedTensorFlipObj` maps. Only their
naturality is postponed, as the separately named theorem above. -/
noncomputable def etaleInternalHomTensorShiftIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ) :
    (derivedTensor B X).obj (K⟦n⟧) ≅
      (derivedTensor B X).obj K ⋙ shiftFunctor _ n :=
  NatIso.ofComponents
    (fun N ↦ (((derivedTensor B X).flip.obj N).commShiftIso n).app K)
    (fun f ↦ etaleInternalHomTensorShift_naturality B K n f)
/-- Canonical source shift of derived internal Hom, by adjunction transport.
Source: Stacks Tags 08J7 and 08JC, with the cochain signs of def-pur-hom-complex
(blueprint: lem-sf-etale-generic-hom-triangle).
Transport the composite tensor-Hom/shift adjunction along the canonical first-factor tensor
shift. Uniqueness of right adjoints gives RHom(K[n],-) = [−n] followed by RHom(K,-).
Finally use `commShiftDerivedHomObj` to move this shift outside RHom. Thus this specifies
actual data, not an arbitrary shift isomorphism or a choice from a mere existence theorem. -/
noncomputable def etaleInternalHomSourceShiftIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ) :
    (RHom(X)[B]).obj (op (K⟦n⟧)) ≅
      (RHom(X)[B]).obj (op K) ⋙ shiftFunctor _ (-n) :=
  (derivedTensorHomAdjunction B (K⟦n⟧)).rightAdjointUniq
    (((derivedTensorHomAdjunction B K).comp (shiftEquiv _ n).toAdjunction).ofNatIsoLeft
      (etaleInternalHomTensorShiftIso B K n).symm) ≪≫
    (((RHom(X)[B]).obj (op K)).commShiftIso (-n))
/-- Unnormalized signed shift component for contravariant derived internal Hom.
Source: Stacks Tags 08J7 and 08JC; the signed source-shift formula of def-pur-hom-complex
(blueprint: lem-sf-etale-generic-hom-triangle).
The opposite-category shift by n is the original shift by -n. Apply the adjunction transport
above at -n, then identify -(-n) with n. Under the standard Hom-complex model its degree-r,
p-component is the signed reindexing f ↦ (-1)^(n*r) f^(p+n). -/
noncomputable def etaleInternalHomFlipRawShiftComponent
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology B))ᵒᵖ) :
    ((shiftFunctor _ n ⋙ (RHom(X)[B]).flip.obj M).obj K) ≅
      (((RHom(X)[B]).flip.obj M ⋙ shiftFunctor _ n).obj K) :=
  by
    simpa only [neg_neg, op_unop, Functor.comp_obj, Functor.flip_obj_obj] using
      (((RHom(X)[B]).flip.obj M).mapIso
        ((shiftFunctorOpIso _ n (-n) (add_neg_cancel n)).app K) ≪≫
          (etaleInternalHomSourceShiftIso B K.unop (-n)).app M)

/-- Coherent extension of the canonical degree-one contravariant Hom shift.
Source: Stacks Tags 08J7 and 08JC, with the cochain signs of def-pur-hom-complex
(blueprint: lem-sf-etale-generic-hom-triangle).
The raw source-shift maps compose with the Koszul discrepancy (-1)^(n*m). Multiplication
by (-1)^(n*(n-1)/2) removes that discrepancy, since q(n+m) = q(n)+q(m)+n*m.
This fixes degrees zero and one and gives the coherent integral shift convention. The same
scalar occurs on both rows of the comparison, so its signed shift square is unchanged. -/
noncomputable def etaleInternalHomFlipShiftComponent
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology B))ᵒᵖ) :
    ((shiftFunctor _ n ⋙ (RHom(X)[B]).flip.obj M).obj K) ≅
      (((RHom(X)[B]).flip.obj M ⋙ shiftFunctor _ n).obj K) :=
  (n * (n - 1) / 2).negOnePow • etaleInternalHomFlipRawShiftComponent B M n K

/-- Naturality of the canonical signed contravariant Hom shift.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle).
Proof: transport the tensor-shift naturality square through the tensor-Hom adjunction on
both sides. The unit/counit identities make right-adjoint uniqueness natural in K; naturality
of `commShiftDerivedHomObj` and of `shiftFunctorOpIso` completes the displayed square.
Equivalently, on the Hom complex it is signed reindexing commuting with precomposition;
the normalizing scalar depends only on n and commutes with every map. -/
theorem etaleInternalHomFlipShiftComponent_naturality
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    {K K' : (DerivedCategory (Sheaf X.smallEtaleTopology B))ᵒᵖ} (f : K ⟶ K') :
    (shiftFunctor _ n ⋙ (RHom(X)[B]).flip.obj M).map f ≫
        (etaleInternalHomFlipShiftComponent B M n K').hom =
      (etaleInternalHomFlipShiftComponent B M n K).hom ≫
        ((RHom(X)[B]).flip.obj M ⋙ shiftFunctor _ n).map f := by
  sorry

/-- Canonical signed commutation with shifts, assembled from its explicit components.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle). -/
noncomputable def etaleInternalHomFlipShiftIso
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n : ℤ) :
    shiftFunctor _ n ⋙ (RHom(X)[B]).flip.obj M ≅
      (RHom(X)[B]).flip.obj M ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K ↦ etaleInternalHomFlipShiftComponent B M n K)
    (fun f ↦ etaleInternalHomFlipShiftComponent_naturality B M n f)

/-- Zero coherence for the canonical contravariant Hom shift.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle).
Proof: use the zero coherence of the tensor shift and of its adjoint `commShiftDerivedHomObj`.
Uniqueness of the adjunct identifies the transported zero component with the zero shift
unitors. In the signed Hom-complex formula the reindexing is the identity and the sign is 1;
the normalizing exponent q(0) is zero. -/
theorem etaleInternalHomFlipShiftIso_zero
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    etaleInternalHomFlipShiftIso B M 0 =
      Functor.CommShift.isoZero ((RHom(X)[B]).flip.obj M) ℤ := by
  sorry

/-- Addition coherence for the canonical contravariant Hom shift.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle).
Proof: apply tensor-shift addition coherence, then transport through the composite adjunction.
For the raw source shifts, the interchange of the two tensor shifts contributes (-1)^(n*m).
The normalizing exponent q(n) = n*(n-1)/2 satisfies q(n+m) = q(n)+q(m)+n*m, for all integers.
Its scalar therefore cancels precisely that discrepancy. The resulting maps obey
`CommShift.isoAdd`, including negative shifts and characteristic two. -/
theorem etaleInternalHomFlipShiftIso_add
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (n m : ℤ) :
    etaleInternalHomFlipShiftIso B M (n + m) =
      Functor.CommShift.isoAdd
        (etaleInternalHomFlipShiftIso B M n) (etaleInternalHomFlipShiftIso B M m) := by
  sorry

/-- The canonical shift structure on contravariant derived Hom, with explicit data.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle). -/
@[instance_reducible]
noncomputable def etaleInternalHomFlipCommShift
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((RHom(X)[B]).flip.obj M).CommShift ℤ where
  commShiftIso := etaleInternalHomFlipShiftIso B M
  commShiftIso_zero := etaleInternalHomFlipShiftIso_zero B M
  commShiftIso_add := etaleInternalHomFlipShiftIso_add B M

end CanonicalShift

/-- The canonical contravariant Hom shift on constant-coefficient étale modules.
Source: Stacks Tags 08J7 and 08JC (blueprint: lem-sf-etale-generic-hom-triangle). -/
noncomputable instance etaleInternalHomFlipCommShift_instance
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X : Scheme.{u}} (M : DerivedCategoryModule A X) :
    ((RHom(X)[ModuleCat.{u + 1} A]).flip.obj M).CommShift ℤ :=
  etaleInternalHomFlipCommShift (ModuleCat.{u + 1} A) M

/-- The evaluation-transpose comparison
`Lg^* RHom_X(K,M) ⟶ RHom_{X'}(Lg^*K,Lg^*M)`.

Source: the evaluation-induced comparison in Stacks Tag 08JC and the canonical derived tensor
comparison `leftDerivedUpperStarTensorIso` (blueprint: lem-sf-etale-generic-hom-triangle).
The map is defined as the transpose, under the derived tensor--Hom adjunction on `X'`, of the
pullback of evaluation after the inverse of the canonical tensor comparison.
(blueprint: lem-sf-etale-generic-hom-triangle)
-/
noncomputable def etaleInternalHomPullbackComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    (K M : DerivedCategoryModule A X) :
    (L((g)^*[ModuleCat.{u + 1} A])).obj
        (((RHom(X)[ModuleCat.{u + 1} A]).obj (op K)).obj M) ⟶
      ((RHom(X')[ModuleCat.{u + 1} A]).obj
        (op ((L((g)^*[ModuleCat.{u + 1} A])).obj K))).obj
        ((L((g)^*[ModuleCat.{u + 1} A])).obj M) :=
  ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      ((L((g)^*[ModuleCat.{u + 1} A])).obj K)).homEquiv _ _
    (((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
        (((RHom(X)[ModuleCat.{u + 1} A]).obj (op K)).obj M)).inv) ≫
      (L((g)^*[ModuleCat.{u + 1} A])).map
        ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M)))


/-- For a distinguished triangle in the first variable, the evaluation-transpose comparisons form
an actual morphism of the reversed internal-Hom triangles after pullback.  If any two comparison
maps are isomorphisms, then the third is an isomorphism.

Source: Stacks Tag 08JC (lemma-RHom-triangulated), with the signed shift convention of the
internal Hom and the evaluation-induced pullback comparison.
Blueprint: (blueprint: lem-sf-etale-generic-hom-triangle).

Proof plan (the six steps of the node):
1. By prop-weil-pbc-inverse-image-modules-exact, constant-coefficient inverse image is exact.
   Its derived functor preserves triangles (lem-sf-exact-functor-derived-triangulated).
   Apply lem-sf-hom-triangulated on X and X' in the first variable, then pull back the row
   on X. This gives the reversed distinguished Hom rows without boundedness assumptions.
2. Represent M by a K-injective I and take a K-injective resolution q : g*I → J on X'
   (prop-pur-kinjective-resolutions-exist). For a representative E of K form b_E by the
   ordinary Hom-complex pullback map followed by postcomposition with q
   (lem-sf-etale-hom-complex-pullback). It represents the desired map; g*I need not be
   K-injective. Exactness computes the pulled-back source Hom complex.
3. Identify Q(b_E) with the evaluation transpose defined below. First choose E K-flat with
   flat terms and a K-flat resolution P → Hom(E,I) (lem-pc-kflat-resolution). Pullbacks of
   P and E remain K-flat, and the canonical tensor comparison is computed on these models
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-site-derived-tensor-descent). The tensor transpose in each bidegree is
   q composed with pulled-back evaluation. Uniqueness in the tensor-Hom bijection
   (lem-sf-ringed-derived-closed-symmetric-monoidal) therefore identifies it with beta.
   For arbitrary E use a K-flat replacement and lem-pur-rhom-well-defined.
4. The chain maps b_E commute with precomposition, by lem-sf-etale-hom-complex-pullback
   and def-pur-hom-complex. Both functors invert quasi-isomorphisms; the naturality square
   therefore descends through localization, including inverses of quasi-isomorphisms
   (def-weil-abstract-derived-category). Hence beta is natural contravariantly in K.
5. Use the same I, J and q for E and E[m]. The signed source-shift square for ordinary
   Hom-complex pullback commutes. Postcomposition with q preserves it: both components are
   (-1)^(m*n) times q^(p+n-m) composed with f^(p-m). This gives b_(E[m]) = b_E[-m]
   under the signed identifications (def-pur-hom-complex and
   lem-weil-pbc-ringed-internal-hom-exact-restriction). The adjunction-transport shift
   constructed above is this canonical degree-one shift; its coherent extension to arbitrary
   integers has the same quadratic normalizing scalar on both rows. Derived pullback uses
   Derived.Shift. Steps 2 and 3 give beta's shift square, without preserving products.
6. Write the arrows of T as u, v, w. Naturality at v and u gives the first two squares
   of the reversed rows, in component order obj₃, obj₂, obj₁. Naturality at w[-1], followed
   by step 5, gives the boundary square with beta_(obj₃)[1]. Both reversed triangles
   have the same last-arrow sign (lem-sf-hom-triangulated), so this is exactly comm₃.
   The specified maps thus form the triangle morphism. Apply lem-sf-triangle-morphism-iso
   for each pair of invertible components to obtain all three two-of-three implications.
-/
theorem etale_internalHom_pullback_triangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    (M : DerivedCategoryModule A X)
    (T : Triangle (DerivedCategoryModule A X))
    (hT : T ∈ distTriang (DerivedCategoryModule A X)) :
    ((∃ φ :
        (L((g)^*[ModuleCat.{u + 1} A])).mapTriangle.obj
          (((RHom(X)[ModuleCat.{u + 1} A]).flip.obj M).mapTriangle.obj
            ((triangleOpEquivalence (DerivedCategoryModule A X)).functor.obj (op T))) ⟶
          (((RHom(X')[ModuleCat.{u + 1} A]).flip.obj
              ((L((g)^*[ModuleCat.{u + 1} A])).obj M)).mapTriangle.obj
            ((triangleOpEquivalence (DerivedCategoryModule A X')).functor.obj
              (op ((L((g)^*[ModuleCat.{u + 1} A])).mapTriangle.obj T)))),
        φ.hom₁ = etaleInternalHomPullbackComparison A g (T.obj₃) M ∧
        φ.hom₂ = etaleInternalHomPullbackComparison A g (T.obj₂) M ∧
        φ.hom₃ = etaleInternalHomPullbackComparison A g (T.obj₁) M)) ∧
      (IsIso (etaleInternalHomPullbackComparison A g (T.obj₃) M) ∧
          IsIso (etaleInternalHomPullbackComparison A g (T.obj₂) M) →
        IsIso (etaleInternalHomPullbackComparison A g (T.obj₁) M)) ∧
      (IsIso (etaleInternalHomPullbackComparison A g (T.obj₃) M) ∧
          IsIso (etaleInternalHomPullbackComparison A g (T.obj₁) M) →
        IsIso (etaleInternalHomPullbackComparison A g (T.obj₂) M)) ∧
      (IsIso (etaleInternalHomPullbackComparison A g (T.obj₂) M) ∧
          IsIso (etaleInternalHomPullbackComparison A g (T.obj₁) M) →
        IsIso (etaleInternalHomPullbackComparison A g (T.obj₃) M)) := by
  sorry

end AlgebraicGeometry.Etale
