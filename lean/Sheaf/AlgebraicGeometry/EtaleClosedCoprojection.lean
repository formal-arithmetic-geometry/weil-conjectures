/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise
import WeilConjectures.CategoryTheory.Adjunction.TensorInvertible
import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-!
# Co-projection on ordinary small etale derived categories

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/_section.md and sk-lem-coprojection.proof.md
(blueprint: sk-lem-coprojection).

The four conjuncts are the co-projection, its base-pullback specialization, its
Tate twist-and-shift specialization, and its iteration along a separated diagonal.
The twist datum is unpacked into its objects, specified inverse pairs and pullback
identifications, exactly as in the node. No geometric normalization of twists is used.
The exceptional inverse image is the right adjoint supplied by lem-exc-closed-ambient.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

universe v

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

attribute [local instance] Sheaf.monoidalCategory

private noncomputable def coprojectionOfProjection [UpperStarPreservesFlat A]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (adj : R(lowerStar A i) ⊣ G)
    (L M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (e : ((derivedTensor A X).obj M).obj L ≅ 𝟙_ _)
    (e' : ((derivedTensor A X).obj L).obj M ≅ 𝟙_ _)
    [IsIso (rightDerivedLowerStarProjectionMap A i)] :
    derivedTensorRight A X L ⋙ G ≅
      G ⋙ derivedTensorRight A Z ((L(upperStar A i)).obj L) := by
  letI := leftDerivedUpperStarMonoidal A i
  exact adj.tensorRightCompIsoOfTensorIso (L(upperStar A i)) e e'
    (asIso (((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap A i)).app M))

end General

private theorem ambientCoprojection
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K L : DerivedCategoryModule Λ X) (hL : DerivedCategory.isInvertible Λ X L) :
    Nonempty ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
        ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj K)).obj
          ((L(upperStar (ModuleCat.{u + 1} Λ) i)).obj L)) := by
  obtain ⟨M, ⟨e'⟩, ⟨e⟩⟩ := hL
  have := finite_projection_iso Λ i
  exact ⟨(coprojectionOfProjection (ModuleCat.{u + 1} Λ) i _
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} Λ) i))) L M e e').app K⟩

/-- Co-projection and its three specializations on ordinary unbounded derived categories.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-coprojection/_section.md
(blueprint: sk-lem-coprojection).

The datum `twist` has inverse objects `twist T (-m)` and specified pullback isomorphisms;
these are the formal Tate data stipulated in the node, not a Kummer normalization.
Bounded constructibility uses def-weil-pbc-constructible-complexes; finite Tor amplitude
is the existence of an interval for def-kun-tor-amplitude. The functor
`(R(lowerStar (ModuleCat Λ) i)).rightAdjoint` is Ri! of lem-exc-closed-ambient.

Proof (sk-lem-coprojection.proof.md):
1. On the chosen small sites, lem-weil-pbc-ring-sheaves-grothendieck,
   lem-pc-sheaf-modules-tensor-closed and lem-pc-sites-modules-functorial-flat-cover
   give the hypotheses of lem-sfb-derived-monoidal. Its K-flat tensor has the unit
   isomorphisms of lem-kun-tensor-unit.
2. Choose an inverse M of L. Associativity and the two inverse isomorphisms make
   tensoring by L and M quasi-inverse functors. By lem-weil-pbc-quasi-inverse-adjoint,
   Hom(P, K tensor L) is naturally Hom(P tensor M, K).
3. By prop-weil-pbc-inverse-image-modules-exact and
   lem-weil-pbc-exact-functor-derived-functor, inverse image is represented termwise.
   The monoidal comparison lem-kun-inverse-image-monoidal pulls both inverse identities
   back, giving the same Hom transfer on Z.
4. Closed i is proper and finite (lem-weil-pbc-closed-immersion-proper and
   lem-weil-pbc-closed-immersion-finite). Apply
   lem-etale-proper-projection-formula-finite-objectwise to arbitrary A and M; its
   canonical map is def-kun-projection-formula-map. Finite direct image is exact by
   lemma-weil-pbc-finite-direct-image-exact and def-weil-sheaf-of-modules-category.
   The exact-functor comparison and lem-weil-pbc-kinjective-total-derived identify
   termwise i* with Ri*, hence lem-exc-closed-ambient gives Ri* left adjoint to Ri!.
5. For every ambient A, compose the preceding natural Hom bijections:
   Hom(A, Ri!(K tensor L)) = Hom(Ri*A, K tensor L) = Hom(Ri*A tensor M, K)
   = Hom(Ri*(A tensor Li*M), K) = Hom(A tensor Li*M, Ri!K)
   = Hom(A, Ri!K tensor Li*L).
6. Lem-galois-yoneda-fully-faithful gives the object isomorphism. The argument applies
   to ambient K, so does not assert constructibility of Ri!K or of intermediate objects.
7. Substitute Lf*B, which is invertible by step 3. The inverse-image composition
   comparison lem-weil-pbc-inverse-image-composition is linear for constant scalars
   by naturality, hence for locally constant scalars by the sheaf axiom. Apply it
   termwise to identify Li*Lf*B with L(i followed by f)*B.
8. Substitute twist X m shifted by 2m. Its inverse is twist X (-m) shifted by -2m.
   Reindex the K-flat total tensor (def-kun-derived-tensor); even shifts have sign 1.
   Termwise inverse image and twistPullback identify its restriction. Reindex again
   to express the result as the shift of K(m) and of (Ri!K)(m).
9. For separated f the diagonal is closed (def-weil-proper-morphism). Pullbacks of
   omega are invertible by step 3. Apply step 6 twice, inserting the tensor unit
   with lem-kun-tensor-unit, to obtain the displayed left-associated threefold tensor. -/
theorem closedImmersion_coprojection
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (twist : (T : Scheme.{u}) → ℤ → DerivedCategoryModule Λ T)
    (_twistInverse : ∀ (T : Scheme.{u}) (m : ℤ),
      Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj (twist T m)).obj
        (twist T (-m)) ≅ constantComplex Λ T) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj (twist T (-m))).obj
        (twist T m) ≅ constantComplex Λ T))
    (_twistPullback : ∀ {U V : Scheme.{u}} (f : U ⟶ V) (m : ℤ),
      Nonempty ((L(upperStar (ModuleCat.{u + 1} Λ) f)).obj (twist V m) ≅ twist U m)) :
    (∀ (Z X : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (K L : DerivedCategoryModule Λ X),
      DerivedCategory.isBoundedConstructible Λ X K →
      (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b K) →
      DerivedCategory.isBoundedConstructible Λ X L →
      (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b L) →
      DerivedCategory.isInvertible Λ X L →
      Nonempty ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj K)).obj
            ((L(upperStar (ModuleCat.{u + 1} Λ) i)).obj L))) ∧
    (∀ (Z X Y : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Y)
      (K : DerivedCategoryModule Λ X) (B : DerivedCategoryModule Λ Y),
      DerivedCategory.isBoundedConstructible Λ X K →
      (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b K) →
      DerivedCategory.isInvertible Λ Y B →
      Nonempty ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
            ((L(upperStar (ModuleCat.{u + 1} Λ) f)).obj B)) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj K)).obj
            ((L(upperStar (ModuleCat.{u + 1} Λ) (i ≫ f))).obj B))) ∧
    (∀ (Z X : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (K : DerivedCategoryModule Λ X) (m : ℤ),
      DerivedCategory.isBoundedConstructible Λ X K →
      (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b K) →
      Nonempty ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj
          ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj (twist X m))⟦2 * m⟧) ≅
        (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.obj K)).obj
            (twist Z m))⟦2 * m⟧)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f]
      (omega : DerivedCategoryModule Λ X), DerivedCategory.isInvertible Λ X omega →
      Nonempty ((R(lowerStar (ModuleCat.{u + 1} Λ) (pullback.diagonal f))).rightAdjoint.obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
            ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f f))).obj omega)).obj
              ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f f))).obj omega)) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
            ((R(lowerStar (ModuleCat.{u + 1} Λ) (pullback.diagonal f))).rightAdjoint.obj
              (constantComplex Λ (pullback f f)))).obj
                ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.diagonal f))).obj
                  ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f f))).obj omega)))).obj
          ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.diagonal f))).obj
            ((L(upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f f))).obj omega)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z X i _ K L _ _ _ _ hL
    exact ambientCoprojection Λ i K L hL
  · intro Z X Y i _ f K B _ _ hB
    obtain ⟨e⟩ := ambientCoprojection Λ i K _ (hB.leftDerivedUpperStar f)
    exact ⟨e ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i f).app B).symm⟩
  · intro Z X i _ K m _ _
    have ht : DerivedCategory.isInvertible Λ X (twist X m) :=
      ⟨twist X (-m), _twistInverse X m⟩
    obtain ⟨e⟩ := ambientCoprojection Λ i K ((twist X m)⟦2 * m⟧) (ht.shift (2 * m))
    obtain ⟨et⟩ := _twistPullback i m
    exact ⟨(R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.mapIso
        ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).commShiftIso
          (2 * m)).app (twist X m)).symm ≪≫ e ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).mapIso
        (((L(upperStar (ModuleCat.{u + 1} Λ) i)).commShiftIso (2 * m)).app _ ≪≫
          (shiftFunctor _ (2 * m)).mapIso et) ≪≫
      (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).commShiftIso
        (2 * m)).app _⟩
  · intro X Y f _ omega homega
    let i : X ⟶ pullback f f := pullback.diagonal f
    let L₁ : DerivedCategoryModule Λ (pullback f f) :=
      (L(upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f f))).obj omega
    let L₂ : DerivedCategoryModule Λ (pullback f f) :=
      (L(upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f f))).obj omega
    obtain ⟨e₁⟩ := ambientCoprojection Λ i (constantComplex Λ (pullback f f)) L₁
      (homega.leftDerivedUpperStar (pullback.fst f f))
    obtain ⟨e₂⟩ := ambientCoprojection Λ i
      (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
        (constantComplex Λ (pullback f f))).obj L₁) L₂
      (homega.leftDerivedUpperStar (pullback.snd f f))
    exact ⟨(R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint.mapIso
        (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).mapIso
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) (pullback f f) L₁).symm).app L₂) ≪≫
      e₂ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e₁).app _⟩

end AlgebraicGeometry.Etale
