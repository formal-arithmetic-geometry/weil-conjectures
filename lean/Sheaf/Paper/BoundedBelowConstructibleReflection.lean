/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.Paper.ProEtaleConstantModuleConstructibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

set_option linter.style.haveILetI false
set_option linter.style.longLine false

/-!
# Reflection of bounded constructibility from the pro-etale comparison

Source: Stacks Project, Tags 099T and 09AK; blueprint
`lem-sf-bounded-below-ctf-reflection`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Intrinsic finite-level constructibility of the comparison pullback reflects bounded
constructibility for a bounded-below etale complex.
Source: Stacks Project, Tags 099T and 09AK; blueprint
`lem-sf-bounded-below-ctf-reflection`.

Proof: exact fully faithful comparison identifies the cohomology sheaves of a complex with
those of its pullback and reflects their vanishing. The intrinsic finite-level constructible
origin theorem supplies a constructible etale antecedent for the pullback cohomology. Fullness
and faithfulness lift the resulting sheaf isomorphisms, and the finite cohomological interval
is reflected degree by degree. The bounded constructible predicate follows from these two
properties and the assumed bounded-below t-structure condition. -/
theorem finiteCoefficient_boundedBelow_constructible_reflection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of D.k))]
    (C : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hPlus : _root_.DerivedCategory.TStructure.t.plus C)
    (_hConstructible : Scheme.intrinsicFiniteTorsionConstructible l E n hn T
      ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj C)) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T C  := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  letI : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  let K := (@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T B
    inferInstance (Padic.finite_coefficientExtensionRing l E n hn)).obj C
  have hfinite : Set.Finite {i : ℤ | ¬ IsZero
      ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.Scheme.proEtaleRingModules T
          (AlgebraicGeometry.Scheme.proEtaleConstantRing T B)) i).obj K)} := by
    exact _hConstructible.1
  have hbounds : ∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.Scheme.proEtaleRingModules T
          (AlgebraicGeometry.Scheme.proEtaleConstantRing T B)) i).obj K) := by
    obtain ⟨c, hc⟩ := hfinite.bddBelow
    obtain ⟨d, hd⟩ := hfinite.bddAbove
    refine ⟨min c d, max c d, min_le_max, ?_⟩
    intro i hi
    by_contra hnz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (hc hnz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hd hnz)) (lt_of_le_of_lt (le_max_right _ _) hi)
  have hintr :
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T B
        ((DerivedCategory.homologyFunctor
          (AlgebraicGeometry.Scheme.proEtaleRingModules T
            (AlgebraicGeometry.Scheme.proEtaleConstantRing T B)) i).obj K)) ∧
        ∃ c d : ℤ, c ≤ d ∧ ∀ i : ℤ, (i < c ∨ d < i) →
          IsZero ((DerivedCategory.homologyFunctor
            (AlgebraicGeometry.Scheme.proEtaleRingModules T
              (AlgebraicGeometry.Scheme.proEtaleConstantRing T B)) i).obj K) :=
    ⟨_hConstructible.2, hbounds⟩
  obtain ⟨L, ⟨e⟩⟩ :=
    (Scheme.finiteRing_constructibleDerived_origin T B).2.2.1 K |>.mpr hintr
  have hL := L.property
  have hLplus : _root_.DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hz⟩ := hL.2
    exact ⟨c, (DerivedCategory.isGE_iff L.obj c).2 (fun i hi ↦ hz i (Or.inl hi))⟩
  let R := ProEtale.finiteCoefficientIntrinsicRealization T B
  letI : R.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T B).1
  let F := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T |>.mapDerivedCategory
  have eR : R.mapDerivedCategory.obj (F.obj L.obj) ≅ R.mapDerivedCategory.obj (F.obj C) := by
    exact (Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T) R).app L.obj |>.symm ≪≫
      e ≪≫
      (Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T) R).app C
  let eFixed : F.obj L.obj ≅ F.obj C := R.mapDerivedCategory.preimageIso eR
  obtain ⟨f, hf⟩ :=
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map L.obj C _hPlus).2
      eFixed.hom
  obtain ⟨g, hg⟩ :=
    (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C L.obj hLplus).2
      eFixed.inv
  have hfg : f ≫ g = 𝟙 L.obj := by
    apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map L.obj L.obj hLplus).1
    change F.map f = eFixed.hom at hf
    change F.map g = eFixed.inv at hg
    change F.map (f ≫ g) = F.map (𝟙 L.obj)
    rw [F.map_comp, hf, hg, Iso.hom_inv_id, F.map_id]
  have hgf : g ≫ f = 𝟙 C := by
    apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C C _hPlus).1
    change F.map f = eFixed.hom at hf
    change F.map g = eFixed.inv at hg
    change F.map (g ≫ f) = F.map (𝟙 C)
    rw [F.map_comp, hg, hf, Iso.inv_hom_id, F.map_id]
  let e' : L.obj ≅ C := { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }
  refine ⟨?_, ?_⟩
  · intro i
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    letI : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ i).obj L.obj) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL.1 i)
    apply Scheme.IsConstructibleSheaf.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e')
  · obtain ⟨a, b, hab, hz⟩ := hL.2
    refine ⟨a, b, hab, fun i hi ↦ ?_⟩
    exact (hz i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e'.symm)

end AlgebraicGeometry
