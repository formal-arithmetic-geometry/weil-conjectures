/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Unbounded closed-immersion compact support at the identity-open compactification

Source: blueprint sec-six-functors-basics/sk-prop-a1, first localization triangle;
Stacks Tags 08M3, 04CA, 015F, 03S3 and 010N
(blueprint: lem-pur-closed-unbounded-compact-support-normalization).

All categories below are ordinary unbounded derived categories of etale sheaves of modules.
The three existential isomorphisms carry their normalization equations: the localization
comparison is the canonical termwise one, the first compact-support comparison removes
identity extension by zero, and the second inverts the actual total-derived comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.Etale

/-- Exact closed direct image, its unbounded termwise descent, and the canonical chain
from compact support at `(id_Z,i)` to the total right derived and termwise direct images.
The cohomology comparison is an isomorphism of functors, hence natural for every derived
morphism. Both upper and lower cohomological bounds are preserved without imposing either
bound or constructibility on the input.

Source: blueprint sk-prop-a1, first localization triangle; Stacks Tags 08M3, 04CA,
015F, 03S3, 01W5, 01T6 and 010N
(blueprint: lem-pur-closed-unbounded-compact-support-normalization).

Proof plan:
1. Apply lem-trf-oriented-closed-base-localization to the closed immersion and constant
   coefficient modules. Its module direct image is `lowerStar`, which is therefore exact.
2. Apply lem-weil-pbc-exact-functor-derived-factorization: the termwise functor preserves
   quasi-isomorphisms and descends on the entire unbounded category, with comparison phi.
3. By lem-weil-pbc-exact-functor-derived-functor this normalized descent is a right derived
   functor. The functor CoCh -> K is full and the identity on objects, so its Kan universal
   property agrees with that of the chosen homotopy-category total right derived functor
   (lem-weil-pbc-kinjective-total-derived, def-weil-abstract-derived-category). Uniqueness
   makes the actual comparison invertible at every complex and gives delta with the
   displayed equation. Localization uniqueness descends its inverse naturally.
4. For the identity open immersion the presheaf defining extension by zero is the original
   sheaf. The sheafification universal property gives inverse maps, natural in the sheaf.
   Descend termwise by lem-weil-pbc-localization-universal-property to remove its derived
   extension by zero. This is the existing canonical identity isomorphism used below.
5. A closed immersion is proper (lem-weil-pbc-closed-immersion-proper); finite-type schemes
   over the field are Noetherian (lem-weil-pbc-finite-type-over-noetherian). Thus ofIsProper
   is the admissible compactification `(id_Z,i)`. Whisker the identity isomorphism from
   Step 4 by the total right derived direct image and apply its left unitor to obtain e.
6. Apply lem-weil-pbc-exact-functor-complex-cohomology to every degree on complexes.
   Combine with phi and the cohomology-on-representatives comparison, and descend the
   natural isomorphism by lem-weil-pbc-localization-universal-property. Exact additive
   direct image preserves zero objects, so vanishing in degrees below a or above b is
   preserved. No boundedness or constructibility hypothesis was used. -/
theorem closed_unbounded_compactSupport_normalization
    (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of P.field.k))]
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of P.field.k))] :
    (PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} P.Coefficient) i) ∧
      PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ∧
    ∃ (phi : _root_.DerivedCategory.Q ⋙
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ _root_.DerivedCategory.Q)
      (e : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
          (Compactification.ofIsProper i) ≅
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor)
      (delta : (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor ≅
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory),
      phi = (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategoryFactors ∧
      e = Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} P.Coefficient) Z)
          (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor ≪≫
        Functor.leftUnitor
          (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor ∧
      (∀ K : CochainComplex (Sheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)) ℤ,
        IsIso ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft _root_.DerivedCategory.Qh delta.hom =
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategoryFactorsh.inv ∧
      (∀ m : ℤ, Nonempty
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory ⋙
            _root_.DerivedCategory.homologyFunctor _ m ≅
          _root_.DerivedCategory.homologyFunctor _ m ⋙
            lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ∧
      (∀ (V : DerivedCategoryModule P.Coefficient Z) (a b : ℤ),
        (V.IsGE a →
          ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj V).IsGE a) ∧
        (V.IsLE b →
          ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj V).IsLE b)) := by
  let F := lowerStar (ModuleCat.{u + 1} P.Coefficient) i
  refine ⟨⟨inferInstance, inferInstance⟩, F.mapDerivedCategoryFactors,
    Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} P.Coefficient) Z)
        F.rightDerivedFunctor ≪≫ Functor.leftUnitor F.rightDerivedFunctor,
    F.rightDerivedFunctorIsoMapDerivedCategory, rfl, rfl, ?_,
    F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac, ?_, ?_⟩
  · intro K
    infer_instance
  · intro m
    exact ⟨(F.mapDerivedCategoryHomologyFunctorIso m).symm⟩
  · intro V a b
    constructor
    · intro h
      exact F.isGE_mapDerivedCategory_obj V a
    · intro h
      exact F.isLE_mapDerivedCategory_obj V b

end AlgebraicGeometry.Etale
