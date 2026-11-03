/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerAdjunct
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Uniform bounds in the current image-tower coordinates

Source: integral direct-image proof (1), widening Tor bounds by twice the fibre dimension.
(blueprint: lem-sp-current-image-uniform-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem tor_of_iso (T : Scheme.{u}) (R : Type u) [CommRing R]
    {K L : Scheme.proEtaleDerivedCategory T R} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T R K a b) :
    Scheme.HasProEtaleTorAmplitude T R L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_of_iso (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    {K L : Scheme.proEtaleDerivedCategory T R} (e : K ≅ L)
    (h : spFiniteConstructibleTor T R K) : spFiniteConstructibleTor T R L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, tor_of_iso T R e ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((Scheme.proEtaleModuleRestriction T R).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

/-- Uniform input-level Tor bounds give the asserted output Tor and homology bounds.
Proof: deduce Noetherianity from finite type over a field, so the compactification's
open immersion is quasi-compact. A smooth map of relative dimension d has geometric
fibres of dimension at most d. Transport the input finite constructibility and Tor
bounds through the recorded derived evaluation comparison, apply the existing
compact-support bound to the realized strict tower, and transport back through the
realization counit. All transports are the specified equivalence/evaluation maps.
The interval is ordered even for the zero input; no nonemptiness is assumed.
Source: blueprint integral direct-image proof (1).
(blueprint: lem-sp-current-image-uniform-bounds). -/
theorem imageLevel_bounds_of_level_bounds
    (s : Coefficients l E) (e : Evaluation l E s)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) (M : Integral l E X) (a b : ℤ) (hab : a ≤ b)
    (hM : ∀ n : ℕ,
      spFiniteConstructibleTor X (SpTowerShriek.R l E n) ((level l E s X n).obj M) ∧
      Scheme.HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
        ((level l E s X n).obj M) a b) :
    ∀ n : ℕ, Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
        (imageLevel l E s c M n) a (b + 2 * d) ∧
      ∀ i : ℤ, (i < a ∨ b + 2 * d < i) →
        IsZero ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules Y
            (Scheme.proEtaleConstantRing Y (SpTowerShriek.R l E n)))
          _ _ (HasDerivedCategory.standard _) i).obj (imageLevel l E s c M n)) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsSeparated (f ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  have : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType c.g
  have : QuasiCompact c.i := inferInstance
  have hd (y : Y) : topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞) := by
    exact topologicalKrullDim_le_of_smoothOfRelativeDimension (pullback.snd _ _) d
  let C := (realization l E s X).functor.obj ((red l E s X).obj M)
  have hC (n : ℕ) :
      spFiniteConstructibleTor X (SpTowerShriek.R l E n) ((SpTowerShriek.Ev l E X n).obj C) ∧
      Scheme.HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
        ((SpTowerShriek.Ev l E X n).obj C) a b := by
    have : Finite (SpTowerShriek.R l E n) := s.base.finite n
    let ei := (Evaluation.derived l E s e X n).app ((red l E s X).obj M)
    exact ⟨finite_of_iso X _ ei.symm (hM n).1, tor_of_iso X _ ei.symm (hM n).2⟩
  have h := (compactSupport_uniform_tor_bound (ringChar k) l k
    (Ne.symm (Fact.out : ringChar k ≠ l)) X Y f c d hd a b hab).2 E
      s.base s.operations C hC
  intro n
  let eo : imageLevel l E s c M n ≅
      (SpTowerShriek.Ev l E Y n).obj ((SpTowerShriek.F l E s.base s.operations c).obj C) :=
    (Evaluation.derived l E s e Y n).symm.app (imageTower l E s c M) ≪≫
      (SpTowerShriek.Ev l E Y n).mapIso ((realization l E s Y).counitIso.app _)
  refine ⟨tor_of_iso Y _ eo.symm (h n).1, ?_⟩
  intro i hi
  exact ((h n).2 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eo)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
