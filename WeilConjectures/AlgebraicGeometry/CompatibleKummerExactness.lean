/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompatibleKummerCoefficients.CompatibleKummerCoefficientData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # Exactness and finite normalization of the compatible-root Kummer row

Source: Stacks 03PL; compatible-root proof Steps 1--4
(blueprint: lem-pur-compatible-kummer-exactness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale
variable (ell : ℕ) [Fact ell.Prime]

omit [Fact ell.Prime] in
private theorem unitsCoordinate_step (T : Scheme.{u}) (r : ℕ) :
    compatibleUnitsProjectionAt ell T (r + 1) ≫ Scheme.proEtaleUnitsPower T ell =
      compatibleUnitsProjectionAt ell T r := by
  have h := limit.w (compatibleUnitsTower ell T) (homOfLE (Nat.le_succ r)).op
  erw [show (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ r)).op =
    Scheme.proEtaleUnitsPower T ell from
      Functor.ofOpSequence_map_homOfLE_succ _ r] at h
  exact h

omit [Fact ell.Prime] in
/-- The r-th compatible unit raised to ell^r is the zeroth unit.
Source: Stacks 03PL, proof Step 4
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: iterate the adjacent compatibility equation, using multiplication of powers. -/
theorem compatibleUnitsProjectionAt_power (T : Scheme.{u}) (r : ℕ) :
    compatibleUnitsProjectionAt ell T r ≫ Scheme.proEtaleUnitsPower T (ell ^ r) =
      compatibleUnitsProjection ell T := by
  induction r with
  | zero =>
    change compatibleUnitsProjectionAt ell T 0 ≫ (1 • 𝟙 _) =
      compatibleUnitsProjectionAt ell T 0
    simp only [one_smul, Category.comp_id]
  | succ r ih =>
    have hp : Scheme.proEtaleUnitsPower T (ell ^ (r + 1)) =
        Scheme.proEtaleUnitsPower T ell ≫ Scheme.proEtaleUnitsPower T (ell ^ r) := by
      simp only [Scheme.proEtaleUnitsPower, Preadditive.comp_nsmul,
        Preadditive.nsmul_comp, Category.id_comp, smul_smul]
      erw [pow_succ, Nat.mul_comm]
    calc
      _ = compatibleUnitsProjectionAt ell T (r + 1) ≫
          (Scheme.proEtaleUnitsPower T ell ≫ Scheme.proEtaleUnitsPower T (ell ^ r)) :=
        congrArg (fun v ↦ compatibleUnitsProjectionAt ell T (r + 1) ≫ v) hp
      _ = (compatibleUnitsProjectionAt ell T (r + 1) ≫
          Scheme.proEtaleUnitsPower T ell) ≫ Scheme.proEtaleUnitsPower T (ell ^ r) :=
        (Category.assoc _ _ _).symm
      _ = compatibleUnitsProjectionAt ell T r ≫
          Scheme.proEtaleUnitsPower T (ell ^ r) :=
        congrArg (fun v ↦ v ≫ Scheme.proEtaleUnitsPower T (ell ^ r))
          (unitsCoordinate_step ell T r)
      _ = _ := ih

private theorem rootsTransition_inclusion (T : Scheme.{u}) (n : ℕ) :
    (compatibleRootsTower ell T).map (homOfLE (Nat.le_succ n)).op ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)) =
      Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 2)) ≫
        Scheme.proEtaleUnitsPower T ell := by
  simp only [compatibleRootsTower, SpTowerClasses.roots,
    Scheme.proEtaleRootsOfUnityTower, Functor.ofOpSequence_map_homOfLE_succ]
  ext U x
  exact Scheme.proEtaleRootsOfUnityTransition_prime T ell Fact.out n U x

private def compatibleKernelComponent (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}}
    (g : A ⟶ compatibleUnits ell T) (hg : g ≫ compatibleUnitsProjection ell T = 0)
    (n : ℕ) : A ⟶ Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) :=
  kernel.lift _ (g ≫ compatibleUnitsProjectionAt ell T (n + 1)) (by
    erw [Category.assoc, compatibleUnitsProjectionAt_power, hg])

private theorem compatibleKernelComponent_step (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}}
    (g : A ⟶ compatibleUnits ell T) (hg : g ≫ compatibleUnitsProjection ell T = 0)
    (n : ℕ) :
    compatibleKernelComponent ell T g hg n =
      compatibleKernelComponent ell T g hg (n + 1) ≫
        (compatibleRootsTower ell T).map (homOfLE (Nat.le_succ n)).op := by
  have : Mono (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))) := by
    dsimp [Scheme.proEtaleRootsOfUnityInclusion]
    exact equalizer.ι_mono
  apply (cancel_mono (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)))).mp
  have hl (m : ℕ) : compatibleKernelComponent ell T g hg m ≫
      Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (m + 1)) =
      g ≫ compatibleUnitsProjectionAt ell T (m + 1) := kernel.lift_ι _ _ _
  let j := Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  let j' := Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 2))
  let t := (compatibleRootsTower ell T).map (homOfLE (Nat.le_succ n)).op
  let a := compatibleKernelComponent ell T g hg n
  let b := compatibleKernelComponent ell T g hg (n + 1)
  let p := Scheme.proEtaleUnitsPower T ell
  change a ≫ j = (b ≫ t) ≫ j
  calc
    a ≫ j = g ≫ compatibleUnitsProjectionAt ell T (n + 1) := hl n
    _ = g ≫ (compatibleUnitsProjectionAt ell T (n + 2) ≫ p) :=
      congrArg (fun v ↦ g ≫ v) (unitsCoordinate_step ell T (n + 1)).symm
    _ = (g ≫ compatibleUnitsProjectionAt ell T (n + 2)) ≫ p :=
      (Category.assoc _ _ _).symm
    _ = (b ≫ j') ≫ p := congrArg (fun v ↦ v ≫ p) (hl (n + 1)).symm
    _ = b ≫ (j' ≫ p) := Category.assoc _ _ _
    _ = b ≫ (t ≫ j) :=
      congrArg (fun v ↦ b ≫ v) (rootsTransition_inclusion ell T n).symm
    _ = (b ≫ t) ≫ j := (Category.assoc _ _ _).symm

private def compatibleKernelCone (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}}
    (g : A ⟶ compatibleUnits ell T) (hg : g ≫ compatibleUnitsProjection ell T = 0) :
    Cone (compatibleRootsTower ell T) :=
  Cone.mk A (NatTrans.ofOpSequence (compatibleKernelComponent ell T g hg) (by
    intro n
    change 𝟙 A ≫ compatibleKernelComponent ell T g hg n = _
    erw [Category.id_comp]
    exact compatibleKernelComponent_step ell T g hg n))

private theorem compatibleRootInclusion_mono (T : Scheme.{u}) :
    Mono (compatibleRootInclusion ell T).hom := by
  constructor
  intro A g h e
  apply limit.hom_ext
  rintro ⟨n⟩
  have : Mono (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))) := by
    dsimp [Scheme.proEtaleRootsOfUnityInclusion]
    exact equalizer.ι_mono
  apply (cancel_mono (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)))).mp
  change (g ≫ compatibleRootsCoordinate ell T n) ≫
      Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)) =
    (h ≫ compatibleRootsCoordinate ell T n) ≫
      Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  let i := (compatibleRootInclusion ell T).hom
  let p := compatibleUnitsProjectionAt ell T (n + 1)
  let q := compatibleRootsCoordinate ell T n
  let j := Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  have hp : i ≫ p = q ≫ j := (compatibleRootInclusion ell T).positive n
  calc
    (g ≫ q) ≫ j = g ≫ (q ≫ j) := Category.assoc _ _ _
    _ = g ≫ (i ≫ p) := congrArg (fun v ↦ g ≫ v) hp.symm
    _ = (g ≫ i) ≫ p := (Category.assoc _ _ _).symm
    _ = (h ≫ i) ≫ p := e =≫ p
    _ = h ≫ (i ≫ p) := Category.assoc _ _ _
    _ = h ≫ (q ≫ j) := congrArg (fun v ↦ h ≫ v) hp
    _ = (h ≫ q) ≫ j := (Category.assoc _ _ _).symm

/-- The compatible-root inclusion is the kernel of the zeroth unit projection.
Source: Stacks 03PL, proof Step 2
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: a tuple whose zeroth coordinate is one has its (n+1)-st coordinate in
mu_(ell^(n+1)). The finite kernel lifts form a compatible cone. The limit lift
factors the tuple, and the root inclusions and limit projections make it unique. -/
private def compatibleKummerKernel (T : Scheme.{u}) :
    IsLimit (KernelFork.ofι (compatibleRootInclusion ell T).hom
      (compatibleRootZero ell T)) := by
  letI := compatibleRootInclusion_mono ell T
  apply KernelFork.IsLimit.ofι'
  intro A g hg
  let l : A ⟶ compatibleRoots ell T :=
    limit.lift _ (compatibleKernelCone ell T g hg)
  refine ⟨l, ?_⟩
  apply limit.hom_ext
  rintro ⟨n⟩
  cases n with
  | zero =>
    change (l ≫ (compatibleRootInclusion ell T).hom) ≫
      compatibleUnitsProjection ell T = g ≫ compatibleUnitsProjection ell T
    erw [Category.assoc, compatibleRootZero, comp_zero, hg]
  | succ n =>
    erw [Category.assoc, (compatibleRootInclusion ell T).positive n,
      ← Category.assoc]
    dsimp only [l]
    erw [limit.lift_π]
    exact kernel.lift_ι _ _ _

/-- The compatible-root row is short exact whenever ell is a unit on T.
Source: Stacks 03PL and pro-etale repleteness, proof Steps 1--2
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: finite Kummer exactness makes each unit-tower transition epic. Repleteness
makes the zeroth limit projection epic. The explicit kernel cone gives exactness
and monicity of its inclusion. -/
theorem compatibleKummer_shortExact (T : Scheme.{u}) (hT : IsUnit (ell : Γ(T, ⊤))) :
    (compatibleKummerComplex ell T).ShortExact := by
  have ht (n : ℕ) : Epi ((compatibleUnitsTower ell T).map
      (homOfLE (Nat.le_succ n)).op) := by
    simp only [compatibleUnitsTower, SpTowerClasses.powerUnits,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (cartierProKummer_exact T ell (Fact.out : ell.Prime).pos hT).epi_g
  have hp : Epi (compatibleUnitsProjection ell T) :=
    Scheme.ProEt.epi_π_app_zero_of_epi_ab (limit.isLimit (compatibleUnitsTower ell T)) ht
  exact {
    exact := ShortComplex.exact_of_f_is_kernel _ (compatibleKummerKernel ell T)
    mono_f := compatibleRootInclusion_mono ell T
    epi_g := hp }

/-- The coordinate maps form the canonical morphism to a finite Kummer row.
Source: Stacks 03PL, proof Step 4
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: the left square is the positive-coordinate normalization. The right
square is the iterated power equation. -/
def compatibleKummerToFinite (T : Scheme.{u}) (n : ℕ) :
    compatibleKummerComplex ell T ⟶ finiteKummerComplex ell T (n + 1) where
  τ₁ := compatibleRootsCoordinate ell T n
  τ₂ := compatibleUnitsProjectionAt ell T (n + 1)
  τ₃ := 𝟙 _
  comm₁₂ := ((compatibleRootInclusion ell T).positive n).symm
  comm₂₃ := by
    change compatibleUnitsProjectionAt ell T (n + 1) ≫
        Scheme.proEtaleUnitsPower T (ell ^ (n + 1)) =
      compatibleUnitsProjection ell T ≫ 𝟙 _
    erw [Category.comp_id]
    exact compatibleUnitsProjectionAt_power ell T (n + 1)

/-- Projection preserves the entire positive boundary, including its sign.
Source: Stacks 03PL, proof Step 4
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: apply naturality of the distinguished triangle of the actual morphism
of short exact rows; its rightmost component is the identity. -/
theorem compatibleBoundaryAt_eq_finite (T : Scheme.{u}) (n : ℕ)
    (h : (compatibleKummerComplex ell T).ShortExact)
    (hf : (finiteKummerComplex ell T (n + 1)).ShortExact) :
    compatibleBoundaryAt ell T n h = finiteKummerBoundary ell T (n + 1) hf := by
  have he := (ShortComplex.ShortExact.singleTriangle.map h hf
    (compatibleKummerToFinite ell T n)).comm₃
  change compatibleBoundaryAt ell T n h =
    (DerivedCategory.singleFunctor _ 0).map (𝟙 _) ≫
      finiteKummerBoundary ell T (n + 1) hf at he
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using he

/-- Every finite change of the root target preserves the positive extension class.
Source: Stacks 03PL, proof Step 4
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: apply naturality of the extension class to the coordinate morphism of rows.
Its right component is the identity, so composing on the left has no effect.
Associativity then allows the arbitrary target map to be appended. -/
theorem compatibleKummer_finite_specialization (T : Scheme.{u}) (n : ℕ)
    (h : (compatibleKummerComplex ell T).ShortExact)
    (hf : (finiteKummerComplex ell T (n + 1)).ShortExact)
    (H : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
    (q : Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ⟶ H) :
    cartierKummerClass h (compatibleRootsCoordinate ell T n ≫ q) =
      cartierKummerClass hf q := by
  have he := ShortComplex.ShortExact.extClass_naturality h hf
    (compatibleKummerToFinite ell T n)
  change h.extClass.comp (Ext.mk₀ (compatibleRootsCoordinate ell T n)) (add_zero 1) =
    (Ext.mk₀ (𝟙 _)).comp hf.extClass (zero_add 1) at he
  let C := Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}
  let p := compatibleRootsCoordinate ell T n
  have he' : h.extClass.comp (Ext.mk₀ p) (add_zero 1) = hf.extClass :=
    he.trans (Ext.mk₀_id_comp (C := C) hf.extClass)
  change h.extClass.comp (Ext.mk₀ (p ≫ q)) (add_zero 1) =
    hf.extClass.comp (Ext.mk₀ q) (add_zero 1)
  refine (congrArg (fun v : Ext (compatibleRoots ell T) H 0 ↦
    h.extClass.comp v (add_zero 1)) (Ext.mk₀_comp_mk₀ (C := C) p q).symm).trans ?_
  refine (Ext.comp_assoc_of_second_deg_zero (C := C)
    h.extClass (Ext.mk₀ p) (Ext.mk₀ q) (add_zero 1)).symm.trans ?_
  exact congrArg (fun v : Ext (Scheme.proEtaleUnitsSheaf T)
    (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))) 1 ↦
      v.comp (Ext.mk₀ q) (add_zero 1)) he'

/-- The canonical units and finite-root maps give the geometric pullback datum.
Source: Stacks 03PL, proof Step 7
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: use the actual inverse-image maps; both required normalizations are reflexive. -/
def compatiblePullbackData {T' T : Scheme.{u}} (f : T' ⟶ T) :
    CompatiblePullback ell T' T f where
  unitMap := (SpTowerClasses.unitsPull f).app (op 0)
  unitMap_canonical := rfl
  rootMap n := Scheme.proEtaleRootsOfUnityInverseImageMap f (ell ^ (n + 1))
  rootMap_canonical _ := rfl

/-- Every positive finite Kummer row is exact when ell is a unit.
Source: Stacks 03PL (blueprint: lem-pur-compatible-kummer-exactness).
Proof: a positive prime power is positive and is a unit whenever ell is a unit;
apply the actual pro-etale finite Kummer exactness theorem. -/
theorem compatibleKummerFinite_shortExact (T : Scheme.{u})
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ) :
    (finiteKummerComplex ell T (n + 1)).ShortExact := by
  exact cartierProKummer_exact T (ell ^ (n + 1))
    (pow_pos (Fact.out : ell.Prime).pos _) (by simpa using hT.pow (n + 1))

/-- The standing coefficient prime is invertible on every scheme over its base field.
Source: purity coefficient conventions
(blueprint: lem-pur-compatible-kummer-exactness).
Proof: the prime is a unit in every stalk by its nonzero image in the base field.
The local criterion for an invertible global section then proves the claim. -/
theorem compatibleKummer_primeUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))] :
    IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk T
    (T ↘ Spec (CommRingCat.of P.field.k)) x

end AlgebraicGeometry.ProEtale
