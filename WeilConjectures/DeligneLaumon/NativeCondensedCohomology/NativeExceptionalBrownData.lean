/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
import WeilConjectures.AlgebraicGeometry.SchemeFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible

/-! # Ordinary Brown data for exceptional cohomology

The compact-support functor on the localizing constructible closure has an
ordinary Brown right adjoint. The coefficient unit belongs to its target closure.
Frobenius transport and native cohomology comparison are separate steps.
Source: sk-thm-existence and the exceptional-adjoint paragraph of
`lem-fix-weil-operations.proof.md` (blueprint: lem-sf-native-exceptional-brown-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  [IsSeparated (X ↘ Spec (.of k₀))] [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [QuasiCompact (X ↘ Spec (.of k₀))]
  [IsSeparated (Y ↘ Spec (.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
  [QuasiCompact (Y ↘ Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification (fiberMap k₀ f).hom.left)
  (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj ell)
    (AlgebraicClosure k₀))

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- The specified compact-support functor has a Brown right adjoint and its target
localizing closure contains the coefficient unit.
Source: sk-prop-sf-existence and constant coefficient constructibility.
(blueprint: lem-sf-native-exceptional-brown-data).
Proof: base change the geometry to the algebraic closure, infer the map properties
from its finite-type source and separated target, and apply localizing Brown existence.
The unit has constructible finite-Tor cohomology; it belongs to the generating class
and hence to the localizing closure. Proof irrelevance identifies the preservation
witness in Brown's restriction with the one specified by H. -/
theorem exceptional_brown_data :
    ∃ R : (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
        (Y ↘ Spec (.of k₀)).geometricFiber).FullSubcategory ⥤
      (localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
        (X ↘ Spec (.of k₀)).geometricFiber).FullSubcategory,
      Nonempty (localSupport k₀ ell f c H ⊣ R) ∧
      localizingClosureProEtale (Profinite.padicAlgClRingObj ell)
        (Y ↘ Spec (.of k₀)).geometricFiber (unitObject k₀ ell Y) := by
  classical
  let k := AlgebraicClosure k₀
  have : Fact (ringChar k).Prime :=
    ⟨(ringChar.eq k (ringChar k₀)).symm ▸ FiniteField.ringChar_prime (k := k₀)⟩
  have : Fact (ringChar k ≠ ell) :=
    ⟨(ringChar.eq k (ringChar k₀)).symm ▸ (Fact.out : ringChar k₀ ≠ ell)⟩
  have hΛ : IsLocalizingAdmissibleCoefficient ell
      (Profinite.padicAlgClRingObj ell) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  let A := fiber k₀ X
  let B := fiber k₀ Y
  let g : A ⟶ B := fiberMap k₀ f
  have : QuasiCompact (g.hom.left ≫ B.obj.hom) := by
    rw [g.hom.w]
    exact (inferInstance : QuasiCompact A.obj.hom)
  have : QuasiCompact g.hom.left := QuasiCompact.of_comp g.hom.left B.obj.hom
  have : IsSeparated (g.hom.left ≫ B.obj.hom) := by
    rw [g.hom.w]
    exact (inferInstance : IsSeparated A.obj.hom)
  have : IsSeparated g.hom.left := IsSeparated.of_comp g.hom.left B.obj.hom
  have : LocallyOfFiniteType (g.hom.left ≫ B.obj.hom) := by
    rw [g.hom.w]
    exact (inferInstance : LocallyOfFiniteType A.obj.hom)
  have : LocallyOfFiniteType g.hom.left :=
    locallyOfFiniteType_of_comp g.hom.left B.obj.hom
  let : A.obj.left.Over (Spec (.of k)) := ⟨A.obj.hom⟩
  let : B.obj.left.Over (Spec (.of k)) := ⟨B.obj.hom⟩
  have : LocallyOfFiniteType (A.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.obj.hom)
  have : QuasiCompact (A.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact A.obj.hom)
  have : IsSeparated (A.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated A.obj.hom)
  have : LocallyOfFiniteType (B.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType B.obj.hom)
  have : QuasiCompact (B.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact B.obj.hom)
  have : IsSeparated (B.obj.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated B.obj.hom)
  have : g.hom.left.IsOver (Spec (.of k)) := ⟨g.hom.w⟩
  let c' := detSfBoundaryCompactification c
  obtain ⟨h, hX, hY, hdata⟩ :=
    exists_localizingExceptionalAdjoint (Profinite.padicAlgClRingObj ell) ell k
      (BaseFieldFiniteCD.of_isAlgClosed ell k) g.hom.left c' hΛ
  let := hX
  let := hY
  obtain ⟨_, _, _, _, G, sG, hG⟩ := hdata
  let := sG
  obtain ⟨_, _, adj, _⟩ := hG
  have : CompactSpace B.obj.left := QuasiCompact.compactSpace_of_compactSpace B.obj.hom
  have : QuasiSeparatedSpace B.obj.left := quasiSeparatedSpace_of_quasiSeparated B.obj.hom
  have hu : (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) B.obj.left ⊓
      DerivedCategory.finiteTorAmplitude _) (unitObject k₀ ell Y) :=
    constantCoefficientObject_mem (Profinite.padicAlgClRingObj ell) B.obj.left
  refine ⟨G, ⟨adj⟩, ?_⟩
  intro P hP hgen
  exact hgen _ hu

end WeilConjectures.NativeCondensedCohomology
