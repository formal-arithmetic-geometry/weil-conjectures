/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.LocalAlgebraApproximationSystem
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.TraceFormula.LocalizationSystemKernelStabilization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-! # Eventual injectivity of residue tensor comparisons

Source: Stacks Project, Algebra, Tag 046Y, middle proof paragraph, with the
Noetherian tensor diagram and its localization transition maps made explicit
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective).
-/


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace LocalAlgebraApproximationSystem

/-- The residue field of the specified limit ring. Source: Stacks Project, Tag 046Y
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev residueField (A : LocalAlgebraApproximationSystem.{u}) :=
  IsLocalRing.ResidueField A.r.pt

/-- `D_i = S_i ⊗[R_i] k`. Source: Stacks Project, Tag 046Y
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev residueTensorRing (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :=
  A.S.obj i ⊗[A.R.obj i] A.residueField

/-- `P_i = M_i ⊗[R_i] k`. Source: Stacks Project, Tag 046Y
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev residueTensorModule (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :=
  A.M.obj i ⊗[A.R.obj i] A.residueField

/-- `P = M ⊗[R] k`. Source: Stacks Project, Tag 046Y
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev limitResidueTensorModule (A : LocalAlgebraApproximationSystem.{u}) :=
  A.μ.pt ⊗[A.r.pt] A.residueField

/-- `S_i / m_i S_i`, using the extended maximal ideal. Source: Stacks Project,
Tag 046Y (blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev stageResidueRing (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :=
  A.S.obj i ⧸ (IsLocalRing.maximalIdeal (A.R.obj i)).map
    (algebraMap (A.R.obj i) (A.S.obj i))

/-- `M_i / m_i M_i`, with its actual ideal-times-module quotient. Source: Stacks
Project, Tag 046Y (blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev stageResidueModule (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :=
  A.M.obj i ⧸ (IsLocalRing.maximalIdeal (A.R.obj i) •
    (⊤ : Submodule (A.R.obj i) (A.M.obj i)))

/-- `M / m M`. Source: Stacks Project, Tag 046Y
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
abbrev limitResidueModule (A : LocalAlgebraApproximationSystem.{u}) :=
  A.μ.pt ⧸ (IsLocalRing.maximalIdeal A.r.pt • (⊤ : Submodule A.r.pt A.μ.pt))

/-- The full conclusion of the residue tensor construction, including existence of
all its canonical actions and maps. Every action and map is normalized on pure tensors
or residue classes; no localization, quotient, colimit or injectivity assertion is
an input to this structure. Source: Stacks Project, Algebra, Tag 046Y, middle paragraph
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective). -/
structure ResidueTensorComparison (A : LocalAlgebraApproximationSystem.{u}) where
  /-- The canonical coefficient actions on the stage and limit tensors. -/
  [stageAction : ∀ i : A.I, Module (A.residueTensorRing i) (A.residueTensorModule i)]
  [limitAction : ∀ i : A.I, Module (A.residueTensorRing i) A.limitResidueTensorModule]
  stageAction_tmul : ∀ (i : A.I) (a : A.S.obj i) (c : A.residueField)
    (x : A.M.obj i) (e : A.residueField),
    (a ⊗ₜ[A.R.obj i] c) • (x ⊗ₜ[A.R.obj i] e) = (a • x) ⊗ₜ[A.R.obj i] (c * e)
  limitAction_tmul : ∀ (i : A.I) (a : A.S.obj i) (c : A.residueField)
    (x : A.μ.pt) (e : A.residueField),
    (a ⊗ₜ[A.R.obj i] c) • (x ⊗ₜ[A.r.pt] e) =
      ((@id A.s.pt (A.s.ι.app i a)) • x) ⊗ₜ[A.r.pt] (c * e)
  /-- The three canonical maps of the tensor diagram. -/
  d : ∀ i j : A.I, i ≤ j → A.residueTensorRing i →+* A.residueTensorRing j
  p : ∀ i j : A.I, i ≤ j → A.residueTensorModule i →+ A.residueTensorModule j
  ψ : ∀ i : A.I, A.residueTensorModule i →ₗ[A.residueTensorRing i]
    A.limitResidueTensorModule
  d_tmul : ∀ (i j : A.I) (h : i ≤ j) (a : A.S.obj i) (c : A.residueField),
    d i j h (a ⊗ₜ[A.R.obj i] c) = A.S.map (homOfLE h) a ⊗ₜ[A.R.obj j] c
  p_tmul : ∀ (i j : A.I) (h : i ≤ j) (x : A.M.obj i) (c : A.residueField),
    p i j h (x ⊗ₜ[A.R.obj i] c) = A.M.map (homOfLE h) x ⊗ₜ[A.R.obj j] c
  ψ_tmul : ∀ (i : A.I) (x : A.M.obj i) (c : A.residueField),
    ψ i (x ⊗ₜ[A.R.obj i] c) = (@id A.μ.pt (A.μ.ι.app i x)) ⊗ₜ[A.r.pt] c
  /-- The Noetherian and finite-module assertions, including the actual linear kernel. -/
  noetherian : ∀ i : A.I, IsNoetherianRing (A.residueTensorRing i)
  finite : ∀ i : A.I, Module.Finite (A.residueTensorRing i) (A.residueTensorModule i)
  finite_kernel : ∀ i : A.I, Module.Finite (A.residueTensorRing i) (LinearMap.ker (ψ i))
  /-- The residue-field scalar extension and quotient actions, with their formulas. -/
  [residueFieldAlgebra : ∀ i : A.I,
    Algebra (IsLocalRing.ResidueField (A.R.obj i)) A.residueField]
  residueFieldAlgebra_map : ∀ i : A.I,
    algebraMap (IsLocalRing.ResidueField (A.R.obj i)) A.residueField =
      @IsLocalRing.ResidueField.map (A.R.obj i) A.r.pt _ (A.localR i) _ A.localLimitR
        (@id (A.R.obj i →+* A.r.pt) (A.r.ι.app i).hom) (A.coconeLocalR i)
  [quotientRingAlgebra : ∀ i : A.I,
    Algebra (IsLocalRing.ResidueField (A.R.obj i)) (A.stageResidueRing i)]
  quotientRingAlgebra_map : ∀ (i : A.I) (b : A.R.obj i),
    algebraMap (IsLocalRing.ResidueField (A.R.obj i)) (A.stageResidueRing i)
      (IsLocalRing.residue (A.R.obj i) b) =
      Ideal.Quotient.mk _ (algebraMap (A.R.obj i) (A.S.obj i) b)
  /-- The canonical residue module scalar action supplied by Mathlib's quotient. -/
  [quotientModule : ∀ i : A.I,
    Module (IsLocalRing.ResidueField (A.R.obj i)) (A.stageResidueModule i)]
  quotientModule_smul : ∀ (i : A.I) (b : A.R.obj i) (x : A.M.obj i),
    IsLocalRing.residue (A.R.obj i) b •
      (Submodule.Quotient.mk x : A.stageResidueModule i) =
      (Submodule.Quotient.mk (b • x) : A.stageResidueModule i)
  /-- The ring and module quotient-tensor identifications, not just abstract isomorphisms. -/
  ringEquiv : ∀ i : A.I, A.residueTensorRing i ≃+*
    (A.stageResidueRing i ⊗[IsLocalRing.ResidueField (A.R.obj i)] A.residueField)
  ringEquiv_tmul : ∀ (i : A.I) (a : A.S.obj i) (c : A.residueField),
    ringEquiv i (a ⊗ₜ[A.R.obj i] c) =
      Ideal.Quotient.mk _ a ⊗ₜ[IsLocalRing.ResidueField (A.R.obj i)] c
  moduleEquiv : ∀ i : A.I, A.residueTensorModule i ≃+
    (A.stageResidueModule i ⊗[IsLocalRing.ResidueField (A.R.obj i)] A.residueField)
  moduleEquiv_tmul : ∀ (i : A.I) (x : A.M.obj i) (c : A.residueField),
    moduleEquiv i (x ⊗ₜ[A.R.obj i] c) =
      (Submodule.Quotient.mk x : A.stageResidueModule i) ⊗ₜ c
  limitEquiv : A.limitResidueTensorModule ≃+ A.limitResidueModule
  limitEquiv_tmul : ∀ (x : A.μ.pt) (b : A.r.pt),
    limitEquiv (x ⊗ₜ[A.r.pt] IsLocalRing.residue A.r.pt b) =
      (Submodule.Quotient.mk (b • x) : A.limitResidueModule)
  /-- The map on the residue quotients corresponding to the tensor comparison. -/
  quotientComparison : ∀ i : A.I,
    (A.stageResidueModule i ⊗[IsLocalRing.ResidueField (A.R.obj i)] A.residueField) →+
      A.limitResidueModule
  quotientComparison_tmul : ∀ (i : A.I) (x : A.M.obj i) (b : A.r.pt),
    quotientComparison i ((Submodule.Quotient.mk x : A.stageResidueModule i) ⊗ₜ
      IsLocalRing.residue A.r.pt b) =
      (Submodule.Quotient.mk (b • (@id A.μ.pt (A.μ.ι.app i x))) : A.limitResidueModule)
  comparison_square : ∀ (i : A.I) (x : A.residueTensorModule i),
    limitEquiv (ψ i x) = quotientComparison i (moduleEquiv i x)
  /-- For any original localization witness, the residue transition localizes at
  its specified image. The module equivalence is the canonical fraction map. -/
  localization : ∀ (i j : A.I) (h : i ≤ j) [_a : Algebra (A.R.obj i) (A.R.obj j)],
    algebraMap (A.R.obj i) (A.R.obj j) = (A.R.map (homOfLE h)).hom →
    ∀ (W : Submonoid (A.S.obj i ⊗[A.R.obj i] A.R.obj j))
      (g : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.S.obj j),
      (∀ (x : A.S.obj i) (b : A.R.obj j),
        g (x ⊗ₜ[A.R.obj i] b) =
          A.S.map (homOfLE h) x * algebraMap (A.R.obj j) (A.S.obj j) b) →
      @IsLocalization _ _ W _ _ g.toAlgebra →
      ∃ θ : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.residueTensorRing i,
        (∀ (x : A.S.obj i) (b : A.R.obj j),
          θ (x ⊗ₜ[A.R.obj i] b) = x ⊗ₜ[A.R.obj i]
            IsLocalRing.residue A.r.pt (A.r.ι.app j b)) ∧
        @IsLocalization _ _ (W.map θ) _ _ (d i j h).toAlgebra ∧
        ∃ e : LocalizedModule (W.map θ) (A.residueTensorModule i) ≃+
          A.residueTensorModule j,
          ∀ (x : A.residueTensorModule i) (w : W.map θ),
            ∃ b : A.residueTensorRing j, d i j h w * b = 1 ∧
              e (LocalizedModule.mk x w) = b • p i j h x
  /-- The comparison maps are a cocone and satisfy the abelian group colimit property. -/
  compatible : ∀ (i j : A.I) (h : i ≤ j),
    (ψ j).toAddMonoidHom.comp (p i j h) = (ψ i).toAddMonoidHom
  colimit : ∀ (Q : AddCommGrpCat.{u}) (f : ∀ i : A.I, A.residueTensorModule i →+ Q),
    (∀ (i j : A.I) (h : i ≤ j), (f j).comp (p i j h) = f i) →
    ∃! g : A.limitResidueTensorModule →+ Q,
      ∀ i : A.I, g.comp (ψ i).toAddMonoidHom = f i
  /-- The uniform eventual injectivity, for every starting index. -/
  eventually_injective : ∀ i₀ : A.I, ∃ i₁ : A.I, i₀ ≤ i₁ ∧
    ∀ j : A.I, i₁ ≤ j → Function.Injective (ψ j)

private noncomputable def baseChangeEquiv
    (R S K M : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] : (S ⊗[R] K) ⊗[S] M ≃+ M ⊗[R] K :=
  ((TensorProduct.comm S (S ⊗[R] K) M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M K)).toAddEquiv

@[instance_reducible]
private noncomputable def baseChangeAction
    (R S K M : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] : Module (S ⊗[R] K) (M ⊗[R] K) :=
  (baseChangeEquiv R S K M).symm.module _

private theorem baseChangeAction_tmul
    (R S K M : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (a : S) (c : K) (x : M) (e : K) :
    let := baseChangeAction R S K M
    (a ⊗ₜ[R] c) • (x ⊗ₜ[R] e) = (a • x) ⊗ₜ[R] (c * e) := by
  change baseChangeEquiv R S K M
    ((a ⊗ₜ[R] c) • (baseChangeEquiv R S K M).symm (x ⊗ₜ[R] e)) = _
  simp [baseChangeEquiv, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]

private theorem baseChange_finite
    (R S K M : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    let := baseChangeAction R S K M
    Module.Finite (S ⊗[R] K) (M ⊗[R] K) := by
  let := baseChangeAction R S K M
  exact Module.Finite.equiv ((baseChangeEquiv R S K M).symm.linearEquiv _).symm

private theorem residueTensor_noetherian (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : IsNoetherianRing (A.residueTensorRing i) := by
  have : IsNoetherianRing (A.residueField ⊗[A.R.obj i] A.S.obj i) :=
    Algebra.EssFiniteType.isNoetherianRing A.residueField _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm (A.R.obj i) A.residueField (A.S.obj i)).toRingEquiv

private def tensorAddMap
    {R S M N K L : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup K] [AddCommGroup L]
    [Module R M] [Module S N] [Module R K] [Module S L]
    (σ : R →+* S) (f : M →+ N) (g : K →+ L)
    (hf : ∀ r x, f (r • x) = σ r • f x)
    (hg : ∀ r x, g (r • x) = σ r • g x) : M ⊗[R] K →+ N ⊗[S] L :=
  TensorProduct.liftAddHom
    { toFun := fun x ↦
        { toFun := fun c ↦ f x ⊗ₜ[S] g c
          map_zero' := by simp
          map_add' := by intros; simp [TensorProduct.tmul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [TensorProduct.add_tmul] }
    (by intros; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hf, hg,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul])

private theorem base_semilinear (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) (a : A.R.obj i) (x : A.M.obj i) :
    A.M.map (homOfLE h) (a • x) = A.R.map (homOfLE h) a •
      A.M.map (homOfLE h) x := by
  rw [← IsScalarTower.algebraMap_smul (A.S.obj i) a x, A.semilinear]
  have he := DFunLike.congr_fun (A.square i j h) a
  change A.S.map (homOfLE h) (algebraMap _ _ a) =
    algebraMap _ _ (A.R.map (homOfLE h) a) at he
  rw [he, IsScalarTower.algebraMap_smul]

private theorem limit_base_semilinear (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) (a : A.R.obj i) (x : A.M.obj i) :
    A.μ.ι.app i (a • x) = (@id A.r.pt (A.r.ι.app i a)) •
      (@id A.μ.pt (A.μ.ι.app i x)) := by
  rw [← IsScalarTower.algebraMap_smul (A.S.obj i) a x, A.coconeSemilinear]
  have he := DFunLike.congr_fun (A.coconeSquare i) a
  change algebraMap A.r.pt A.s.pt (A.r.ι.app i a) =
    A.s.ι.app i (algebraMap (A.R.obj i) (A.S.obj i) a) at he
  change (@id A.s.pt (A.s.ι.app i (algebraMap (A.R.obj i) (A.S.obj i) a))) •
    (@id A.μ.pt (A.μ.ι.app i x)) = _
  rw [← he]
  exact IsScalarTower.algebraMap_smul A.s.pt
    (@id A.r.pt (A.r.ι.app i a)) (@id A.μ.pt (A.μ.ι.app i x))

private theorem residue_transition (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) (a : A.R.obj i) :
    algebraMap (A.R.obj i) A.residueField a =
      algebraMap (A.R.obj j) A.residueField (A.R.map (homOfLE h) a) := by
  rw [A.residueAlgebraMap, A.residueAlgebraMap]
  exact congrArg (IsLocalRing.residue A.r.pt)
    (ConcreteCategory.congr_hom (A.r.w (homOfLE h)) a).symm

@[irreducible]
private noncomputable def tensorTransition (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) : A.residueTensorModule i →+ A.residueTensorModule j :=
  tensorAddMap (R := ↥(A.R.obj i)) (S := ↥(A.R.obj j))
    (A.R.map (homOfLE h)).hom (A.M.map (homOfLE h)).hom
    (AddMonoidHom.id _) (A.base_semilinear i j h) (by
      intro a c
      simp only [AddMonoidHom.id_apply, Algebra.smul_def]
      change algebraMap (A.R.obj i) A.residueField a * c =
        algebraMap (A.R.obj j) A.residueField (A.R.map (homOfLE h) a) * c
      rw [A.residue_transition i j h])

@[irreducible]
private noncomputable def tensorComparison (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : A.residueTensorModule i →+ A.limitResidueTensorModule :=
  tensorAddMap (R := ↥(A.R.obj i)) (S := ↥A.r.pt)
    (@id (A.R.obj i →+* A.r.pt) (A.r.ι.app i).hom) (A.μ.ι.app i).hom (AddMonoidHom.id _)
    (A.limit_base_semilinear i) (by
      intro a c
      simp only [AddMonoidHom.id_apply, Algebra.smul_def]
      change algebraMap (A.R.obj i) A.residueField a * c =
        algebraMap A.r.pt A.residueField (A.r.ι.app i a) * c
      rw [A.residueAlgebraMap]
      rfl)

private theorem tensorComparison_tmul (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) (x : A.M.obj i) (c : A.residueField) :
    tensorComparison A i (x ⊗ₜ[A.R.obj i] c) =
      (@id A.μ.pt (A.μ.ι.app i x)) ⊗ₜ[A.r.pt] c := by
  unfold tensorComparison
  rfl

private noncomputable def tensorRingTransition (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) : A.residueTensorRing i →+* A.residueTensorRing j :=
  Algebra.TensorProduct.mapRingHom (A.R.map (homOfLE h)).hom
    (A.S.map (homOfLE h)).hom (RingHom.id _) (A.square i j h) (by
      ext a
      exact A.residue_transition i j h a)

private theorem tensorTransition_tmul (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) (x : A.M.obj i) (c : A.residueField) :
    tensorTransition A i j h (x ⊗ₜ[A.R.obj i] c) =
      A.M.map (homOfLE h) x ⊗ₜ[A.R.obj j] c := by
  unfold tensorTransition
  rfl

private theorem tensorTransition_semilinear (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) :
    let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
    ∀ (a : A.residueTensorRing i) (x : A.residueTensorModule i),
      tensorTransition A i j h (a • x) =
        tensorRingTransition A i j h a • tensorTransition A i j h x := by
  let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
  dsimp only
  intro a x
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp_all [add_smul]
  | tmul a c =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp_all [smul_add]
    | tmul x e =>
      simp only [baseChangeAction_tmul, tensorRingTransition,
        Algebra.TensorProduct.mapRingHom_tmul, RingHom.id_apply]
      rw [tensorTransition_tmul, tensorTransition_tmul]
      change (A.M.map (homOfLE h) (a • x)) ⊗ₜ[A.R.obj j] (c * e) = _
      rw [A.semilinear]
      change _ = (_ ⊗ₜ[A.R.obj j] c) •
        ((A.M.map (homOfLE h) x) ⊗ₜ[A.R.obj j] e)
      rw [baseChangeAction_tmul]

private noncomputable def tensorLimitRingMap (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : A.residueTensorRing i →+* (A.s.pt ⊗[A.r.pt] A.residueField) :=
  Algebra.TensorProduct.mapRingHom
    (@id (A.R.obj i →+* A.r.pt) (A.r.ι.app i).hom)
    (@id (A.S.obj i →+* A.s.pt) (A.s.ι.app i).hom) (RingHom.id _)
    (A.coconeSquare i).symm (by
      ext a
      change algebraMap (A.R.obj i) A.residueField a =
        IsLocalRing.residue A.r.pt (A.r.ι.app i a)
      rw [A.residueAlgebraMap]
      rfl)

@[instance_reducible]
private noncomputable def tensorLimitAction (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : Module (A.residueTensorRing i) A.limitResidueTensorModule :=
  let := baseChangeAction (↥A.r.pt) (↥A.s.pt) A.residueField (↥A.μ.pt)
  Module.compHom _ (tensorLimitRingMap A i)

private theorem tensorLimitAction_tmul (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) (a : A.S.obj i) (c : A.residueField) (x : A.μ.pt) (e : A.residueField) :
    let := tensorLimitAction A i
    (a ⊗ₜ[A.R.obj i] c) • (x ⊗ₜ[A.r.pt] e) =
      ((@id A.s.pt (A.s.ι.app i a)) • x) ⊗ₜ[A.r.pt] (c * e) := by
  change @SMul.smul (A.s.pt ⊗[A.r.pt] A.residueField) A.limitResidueTensorModule
    (baseChangeAction (↥A.r.pt) (↥A.s.pt) A.residueField (↥A.μ.pt)).toSMul
    (tensorLimitRingMap A i (a ⊗ₜ[A.R.obj i] c)) (x ⊗ₜ[A.r.pt] e) = _
  simp only [tensorLimitRingMap, Algebra.TensorProduct.mapRingHom_tmul, RingHom.id_apply]
  exact baseChangeAction_tmul _ _ _ _ _ _ _ _

@[instance_reducible]
private noncomputable def residueFieldAction (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : Algebra (IsLocalRing.ResidueField (A.R.obj i)) A.residueField :=
  (@IsLocalRing.ResidueField.map (A.R.obj i) A.r.pt _ (A.localR i) _ A.localLimitR
    (A.r.ι.app i).hom (A.coconeLocalR i)).toAlgebra

private theorem residueFieldTower (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :
    let := residueFieldAction A i
    IsScalarTower (A.R.obj i) (IsLocalRing.ResidueField (A.R.obj i)) A.residueField := by
  let := residueFieldAction A i
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact DFunLike.congr_fun (A.residueAlgebraMap i) a

@[instance_reducible]
private noncomputable def residueRingAction (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) : Algebra (IsLocalRing.ResidueField (A.R.obj i)) (A.stageResidueRing i) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

private noncomputable instance residueQuotientModule
    (R M : Type u) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] :
    Module (IsLocalRing.ResidueField R)
      (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :=
  inferInstanceAs <| Module (R ⧸ IsLocalRing.maximalIdeal R) _

private instance residueQuotientTower
    (R M : Type u) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] :
    IsScalarTower R (IsLocalRing.ResidueField R)
      (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :=
  inferInstanceAs <| IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) _

private noncomputable def quotientModuleEquiv
    (R K M : Type u) [CommRing R] [IsLocalRing R] [CommRing K] [Algebra R K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [AddCommGroup M] [Module R M] :
    (M ⊗[R] K) ≃+
      ((M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        ⊗[IsLocalRing.ResidueField R] K) :=
  let q : (IsLocalRing.ResidueField R ⊗[R] M) ≃ₗ[IsLocalRing.ResidueField R]
      (M ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :=
    LinearEquiv.extendScalarsOfSurjective IsLocalRing.residue_surjective
      (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R))
  (TensorProduct.comm R M K).toAddEquiv.trans <|
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (IsLocalRing.ResidueField R)
      K K M).symm.toAddEquiv.trans <|
    (q.baseChange (IsLocalRing.ResidueField R) K _ _).toAddEquiv.trans
      (TensorProduct.comm (IsLocalRing.ResidueField R) K _).toAddEquiv

private theorem quotientModuleEquiv_tmul
    (R K M : Type u) [CommRing R] [IsLocalRing R] [CommRing K] [Algebra R K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [AddCommGroup M] [Module R M] (x : M) (c : K) :
    quotientModuleEquiv R K M (x ⊗ₜ[R] c) =
      (Submodule.Quotient.mk x) ⊗ₜ[IsLocalRing.ResidueField R] c := by
  change (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R))
    (1 ⊗ₜ[R] x) ⊗ₜ[IsLocalRing.ResidueField R] c = _
  exact congrArg (fun y ↦ y ⊗ₜ[IsLocalRing.ResidueField R] c)
    (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul
      (M := M) (IsLocalRing.maximalIdeal R) x)

private noncomputable def residueModuleEquiv (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) :
    let := residueFieldAction A i
    A.residueTensorModule i ≃+
      (A.stageResidueModule i ⊗[IsLocalRing.ResidueField (A.R.obj i)] A.residueField) :=
  let := residueFieldAction A i
  let := residueFieldTower A i
  quotientModuleEquiv (↥(A.R.obj i)) A.residueField (↥(A.M.obj i))

private noncomputable def residueLimitEquiv (A : LocalAlgebraApproximationSystem.{u}) :
    A.limitResidueTensorModule ≃+ A.limitResidueModule :=
  (TensorProduct.tensorQuotEquivQuotSMul (↥A.μ.pt) (IsLocalRing.maximalIdeal A.r.pt)).toAddEquiv

private theorem tensorComparison_linear (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :
    let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    let := tensorLimitAction A i
    ∀ (a : A.residueTensorRing i) (x : A.residueTensorModule i),
      tensorComparison A i (a • x) = a • tensorComparison A i x := by
  let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let := tensorLimitAction A i
  dsimp only
  intro a
  induction a using TensorProduct.induction_on with
  | zero => intro x; simp
  | add a b ha hb => intro x; simp [add_smul, ha, hb]
  | tmul a c =>
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul x e =>
      rw [baseChangeAction_tmul, tensorComparison_tmul, tensorComparison_tmul]
      change (@id A.μ.pt (A.μ.ι.app i (a • x))) ⊗ₜ[A.r.pt] (c * e) =
        (a ⊗ₜ[A.R.obj i] c) • ((@id A.μ.pt (A.μ.ι.app i x)) ⊗ₜ[A.r.pt] e)
      rw [tensorLimitAction_tmul]
      exact congrArg (fun y : A.μ.pt ↦ y ⊗ₜ[A.r.pt] (c * e))
        (A.coconeSemilinear i a x)

private noncomputable def tensorLinearComparison (A : LocalAlgebraApproximationSystem.{u})
    (i : A.I) :
    let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    let := tensorLimitAction A i
    A.residueTensorModule i →ₗ[A.residueTensorRing i] A.limitResidueTensorModule :=
  let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let := tensorLimitAction A i
  { tensorComparison A i with map_smul' := tensorComparison_linear A i }

private noncomputable def residueRingEquiv (A : LocalAlgebraApproximationSystem.{u}) (i : A.I) :
    let := residueFieldAction A i
    let := residueRingAction A i
    A.residueTensorRing i ≃+*
      (A.stageResidueRing i ⊗[IsLocalRing.ResidueField (A.R.obj i)] A.residueField) := by
  let := residueFieldAction A i
  let := residueRingAction A i
  let := residueFieldTower A i
  let : IsScalarTower (A.R.obj i) (IsLocalRing.ResidueField (A.R.obj i))
      (A.stageResidueRing i) := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let e : IsLocalRing.ResidueField (A.R.obj i) ⊗[A.R.obj i] A.S.obj i ≃ₐ[
      IsLocalRing.ResidueField (A.R.obj i)] A.stageResidueRing i :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A.S.obj i)
      (IsLocalRing.maximalIdeal (A.R.obj i))).symm
  exact (Algebra.TensorProduct.comm (A.R.obj i) (A.S.obj i) A.residueField).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange (↥(A.R.obj i))
      (IsLocalRing.ResidueField (A.R.obj i)) A.residueField A.residueField
      (↥(A.S.obj i))).symm.toRingEquiv.trans <|
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : A.residueField ≃ₐ[A.residueField] A.residueField) e).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm (IsLocalRing.ResidueField (A.R.obj i))
      A.residueField (A.stageResidueRing i)).toRingEquiv

private theorem residueRingEquiv_tmul (A : LocalAlgebraApproximationSystem.{u}) (i : A.I)
    (a : A.S.obj i) (c : A.residueField) :
    let := residueFieldAction A i
    let := residueRingAction A i
    residueRingEquiv A i (a ⊗ₜ[A.R.obj i] c) =
      Ideal.Quotient.mk _ a ⊗ₜ[IsLocalRing.ResidueField (A.R.obj i)] c := by
  let := residueFieldAction A i
  let := residueRingAction A i
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A.S.obj i)
    (IsLocalRing.maximalIdeal (A.R.obj i))).symm (1 ⊗ₜ[A.R.obj i] a) ⊗ₜ
      c = _
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, AlgEquiv.symm_apply_apply]

private theorem tensor_colimit (A : LocalAlgebraApproximationSystem.{u})
    (Q : AddCommGrpCat.{u}) (f : ∀ i : A.I, A.residueTensorModule i →+ Q)
    (hf : ∀ (i j : A.I) (h : i ≤ j), (f j).comp (tensorTransition A i j h) = f i) :
    ∃! g : A.limitResidueTensorModule →+ Q,
      ∀ i : A.I, g.comp (tensorComparison A i) = f i := by
  let b (i : A.I) : A.M.obj i →+ (A.residueField →+ Q) :=
    { toFun := fun x ↦
        { toFun := fun c ↦ f i (x ⊗ₜ[A.R.obj i] c)
          map_zero' := by simp
          map_add' := by intros; simp [TensorProduct.tmul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [TensorProduct.add_tmul] }
  have hb (i j : A.I) (h : i ≤ j) (x : A.M.obj i) (c : A.residueField) :
      b j (A.M.map (homOfLE h) x) c = b i x c := by
    simpa only [b, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply,
      tensorTransition_tmul] using
      DFunLike.congr_fun (hf i j h) (x ⊗ₜ[A.R.obj i] c)
  let coc : Cocone A.M :=
    { pt := AddCommGrpCat.of (A.residueField →+ Q)
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom (b i)
          naturality := by
            intro i j h
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            apply AddMonoidHom.ext
            intro c
            exact hb i j (leOfHom h) x c } }
  let B : A.μ.pt →+ (A.residueField →+ Q) := (A.colimitM.desc coc).hom
  have hB (i : A.I) (x : A.M.obj i) (c : A.residueField) :
      B (@id A.μ.pt (A.μ.ι.app i x)) c = f i (x ⊗ₜ[A.R.obj i] c) := by
    exact DFunLike.congr_fun (ConcreteCategory.congr_hom (A.colimitM.fac coc i) x) c
  have rep (x : A.μ.pt) : ∃ i : A.I, ∃ y : A.M.obj i, A.μ.ι.app i y = x := by
    let : IsFiltered A.I := inferInstance
    let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u}) :=
      preservesFilteredColimitsOfSize_shrink _
    exact Concrete.isColimit_exists_rep A.M A.colimitM x
  have balance (r : A.r.pt) (x : A.μ.pt) (c : A.residueField) :
      B (r • x) c = B x (r • c) := by
    obtain ⟨i, a, ha⟩ := A.repR r
    obtain ⟨j, y, hy⟩ := rep x
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    have hal : A.r.ι.app l (A.R.map (homOfLE hil) a) = r :=
      (ConcreteCategory.congr_hom (A.r.w (homOfLE hil)) a).trans ha
    have hyl : A.μ.ι.app l (A.M.map (homOfLE hjl) y) = x :=
      (ConcreteCategory.congr_hom (A.μ.w (homOfLE hjl)) y).trans hy
    let al := A.R.map (homOfLE hil) a
    let yl := A.M.map (homOfLE hjl) y
    have hr : r • x = (@id A.μ.pt (A.μ.ι.app l (al • yl))) := by
      rw [A.limit_base_semilinear, hal, hyl]
      rfl
    have hc : r • c = al • c := by
      rw [Algebra.smul_def, Algebra.smul_def, A.residueAlgebraMap]
      change IsLocalRing.residue A.r.pt r * c =
        IsLocalRing.residue A.r.pt (A.r.ι.app l al) * c
      rw [hal]
    rw [hr, hB, hc]
    calc
      f l ((al • yl) ⊗ₜ[A.R.obj l] c) = f l (yl ⊗ₜ[A.R.obj l] (al • c)) := by
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      _ = B x (al • c) := by
        have he := (hB l yl (al • c)).symm
        change f l (yl ⊗ₜ[A.R.obj l] (al • c)) =
          B (@id A.μ.pt (A.μ.ι.app l yl)) (al • c) at he
        simpa only [yl, hyl, id_eq] using he
  let g : A.limitResidueTensorModule →+ Q := TensorProduct.liftAddHom B balance
  have hg (i : A.I) : g.comp (tensorComparison A i) = f i := by
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x c =>
      change g (tensorComparison A i (x ⊗ₜ[A.R.obj i] c)) = _
      rw [tensorComparison_tmul]
      exact hB i x c
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply AddMonoidHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x c =>
    obtain ⟨i, y, hy⟩ := rep x
    rw [← hy]
    have he := DFunLike.congr_fun (hg' i) (y ⊗ₜ[A.R.obj i] c)
    simp only [AddMonoidHom.comp_apply, tensorComparison_tmul] at he
    exact he.trans (hB i y c).symm

private theorem tensorRingHom_ext
    {R S K T : Type u} [CommRing R] [CommRing S] [CommRing K] [CommRing T]
    [Algebra R S] [Algebra R K] {f g : S ⊗[R] K →+* T}
    (h : ∀ a c, f (a ⊗ₜ[R] c) = g (a ⊗ₜ[R] c)) : f = g := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a c => exact h a c

private noncomputable def tensorIteratedEquiv
    (R R' S K : Type u) [CommRing R] [CommRing R'] [CommRing S] [CommRing K]
    [Algebra R R'] [Algebra R S] [Algebra R K] [Algebra R' K]
    [IsScalarTower R R' K] :
    let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    ((S ⊗[R] R') ⊗[R'] K) ≃+* (S ⊗[R] K) := by
  let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.congr
    (Algebra.TensorProduct.commRight R R' S).symm (AlgEquiv.refl : K ≃ₐ[R'] K)).toRingEquiv.trans
    ((Algebra.TensorProduct.comm R' (R' ⊗[R] S) K).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R R' K K S).toRingEquiv.trans
        (Algebra.TensorProduct.comm R K S).toRingEquiv))

private theorem tensorIteratedEquiv_tmul
    (R R' S K : Type u) [CommRing R] [CommRing R'] [CommRing S] [CommRing K]
    [Algebra R R'] [Algebra R S] [Algebra R K] [Algebra R' K]
    [IsScalarTower R R' K] (a : S) (b : R') (c : K) :
    let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    tensorIteratedEquiv R R' S K ((a ⊗ₜ[R] b) ⊗ₜ[R'] c) =
      a ⊗ₜ[R] (algebraMap R' K b * c) := by
  simp [tensorIteratedEquiv, Algebra.smul_def]

private theorem tensor_ring_localization (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) [Algebra (A.R.obj i) (A.R.obj j)]
    (ha : algebraMap (A.R.obj i) (A.R.obj j) = (A.R.map (homOfLE h)).hom)
    (W : Submonoid (A.S.obj i ⊗[A.R.obj i] A.R.obj j))
    (g : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.S.obj j)
    (hg : ∀ (a : A.S.obj i) (b : A.R.obj j),
      g (a ⊗ₜ[A.R.obj i] b) =
        A.S.map (homOfLE h) a * algebraMap (A.R.obj j) (A.S.obj j) b)
    (hl : @IsLocalization _ _ W _ _ g.toAlgebra) :
    ∃ θ : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.residueTensorRing i,
      (∀ (a : A.S.obj i) (b : A.R.obj j),
        θ (a ⊗ₜ[A.R.obj i] b) = a ⊗ₜ[A.R.obj i]
          IsLocalRing.residue A.r.pt (A.r.ι.app j b)) ∧
      @IsLocalization _ _ (W.map θ) _ _ (tensorRingTransition A i j h).toAlgebra := by
  let B := A.S.obj i ⊗[A.R.obj i] A.R.obj j
  let : Algebra (A.R.obj j) B := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower (A.R.obj i) (A.R.obj j) A.residueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [ha]
      exact residue_transition A i j h a
  let β := tensorIteratedEquiv (↥(A.R.obj i)) (↥(A.R.obj j))
    (↥(A.S.obj i)) A.residueField
  let θ : B →+* A.residueTensorRing i :=
    β.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
  have hθ (a : A.S.obj i) (b : A.R.obj j) :
      θ (a ⊗ₜ[A.R.obj i] b) = a ⊗ₜ[A.R.obj i]
        IsLocalRing.residue A.r.pt (A.r.ι.app j b) := by
    change β ((a ⊗ₜ[A.R.obj i] b) ⊗ₜ[A.R.obj j] 1) = _
    change tensorIteratedEquiv (↥(A.R.obj i)) (↥(A.R.obj j))
      (↥(A.S.obj i)) A.residueField ((a ⊗ₜ[A.R.obj i] b) ⊗ₜ[A.R.obj j] 1) = _
    rw [tensorIteratedEquiv_tmul, mul_one]
    exact congrArg (fun c : A.residueField ↦ a ⊗ₜ[A.R.obj i] c)
      (DFunLike.congr_fun (A.residueAlgebraMap j) b)
  let : Algebra B (A.S.obj j) := g.toAlgebra
  have : IsScalarTower (A.R.obj j) B (A.S.obj j) :=
    IsScalarTower.of_algebraMap_eq fun b ↦ by
      change algebraMap (A.R.obj j) (A.S.obj j) b = g (1 ⊗ₜ[A.R.obj i] b)
      simp [hg]
  let f : B →ₐ[A.R.obj j] A.S.obj j :=
    { toRingHom := g
      commutes' := by
        intro b
        change g (1 ⊗ₜ[A.R.obj i] b) = _
        simp [hg] }
  let F := Algebra.TensorProduct.map f (AlgHom.id (A.R.obj j) A.residueField)
  let : Algebra (B ⊗[A.R.obj j] A.residueField) (A.residueTensorRing j) :=
    F.toRingHom.toAlgebra
  let : Algebra B (A.residueTensorRing j) :=
    { toSMul := TensorProduct.leftHasSMul
      algebraMap := (Algebra.TensorProduct.includeLeftRingHom :
        A.S.obj j →+* A.residueTensorRing j).comp g
      commutes' := fun _ _ ↦ mul_comm _ _
      smul_def' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp_all [smul_add, mul_add]
        | tmul b c =>
          change (g a * b) ⊗ₜ[A.R.obj j] c =
            (g a ⊗ₜ[A.R.obj j] 1) * (b ⊗ₜ[A.R.obj j] c)
          simp [Algebra.TensorProduct.tmul_mul_tmul] }
  have : IsScalarTower B (B ⊗[A.R.obj j] A.residueField) (A.residueTensorRing j) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (g a ⊗ₜ[A.R.obj j] 1) = F (a ⊗ₜ[A.R.obj j] 1)
      simp only [F, Algebra.TensorProduct.map_tmul, map_one]
      rfl
  let : IsLocalization W (A.S.obj j) := hl
  have : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[A.R.obj j] A.residueField) W)
      (A.residueTensorRing j) :=
    IsLocalization.tensorProduct_tensorProduct (↥(A.R.obj j)) A.residueField W
      (↥(A.S.obj j)) (by
        apply RingHom.ext
        intro c
        change F (1 ⊗ₜ[A.R.obj j] c) = 1 ⊗ₜ[A.R.obj j] c
        simp only [F, Algebra.TensorProduct.map_tmul, map_one]
        rfl)
  let := (tensorRingTransition A i j h).toAlgebra
  refine ⟨θ, hθ, ?_⟩
  apply IsLocalization.of_ringEquiv_left β.symm
    (M₁ := Algebra.algebraMapSubmonoid (B ⊗[A.R.obj j] A.residueField) W)
    (M₂ := W.map θ)
  · change (W.map θ).map β.symm.toRingHom =
      W.map (Algebra.TensorProduct.includeLeftRingHom : B →+* _)
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, (β.symm_apply_apply _).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨θ a, ⟨a, ha, rfl⟩, β.symm_apply_apply _⟩
  · intro x
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [β.symm_apply_apply]
    change tensorRingTransition A i j h (β y) = F y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a c =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb
      | tmul a b =>
        change tensorRingTransition A i j h
          (tensorIteratedEquiv (↥(A.R.obj i)) (↥(A.R.obj j))
            (↥(A.S.obj i)) A.residueField ((a ⊗ₜ[A.R.obj i] b) ⊗ₜ[A.R.obj j] c)) = _
        rw [tensorIteratedEquiv_tmul]
        simp only [tensorRingTransition, Algebra.TensorProduct.mapRingHom_tmul,
          RingHom.id_apply, F, Algebra.TensorProduct.map_tmul]
        change (A.S.map (homOfLE h) a) ⊗ₜ[A.R.obj j]
          (algebraMap (A.R.obj j) A.residueField b * c) = g (a ⊗ₜ[A.R.obj i] b) ⊗ₜ c
        rw [hg]
        rw [← Algebra.smul_def, ← TensorProduct.smul_tmul,
          Algebra.smul_def, mul_comm (algebraMap _ _ b)]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_transition_baseChange (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) :
    let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
    let := (tensorRingTransition A i j h).toAlgebra
    ∃ e : (A.residueTensorRing j ⊗[A.residueTensorRing i] A.residueTensorModule i)
        ≃ₗ[A.residueTensorRing j] A.residueTensorModule j,
      ∀ (a : A.residueTensorRing j) (x : A.residueTensorModule i),
        e (a ⊗ₜ[A.residueTensorRing i] x) = a • tensorTransition A i j h x := by
  let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
  let := (tensorRingTransition A i j h).toAlgebra
  let : Algebra (A.S.obj i) (A.S.obj j) := (A.S.map (homOfLE h)).hom.toAlgebra
  let : Algebra (A.S.obj i) (A.residueTensorRing j) :=
    { toSMul := TensorProduct.leftHasSMul
      algebraMap := (Algebra.TensorProduct.includeLeftRingHom :
        A.S.obj j →+* A.residueTensorRing j).comp (A.S.map (homOfLE h)).hom
      commutes' := fun _ _ ↦ mul_comm _ _
      smul_def' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp_all [smul_add, mul_add]
        | tmul b c =>
          change (((A.S.map (homOfLE h)).hom a) * b) ⊗ₜ[A.R.obj j] c =
            (((A.S.map (homOfLE h)).hom a) ⊗ₜ[A.R.obj j] 1) * (b ⊗ₜ[A.R.obj j] c)
          simp [Algebra.TensorProduct.tmul_mul_tmul] }
  have : IsScalarTower (A.S.obj i) (A.S.obj j) (A.residueTensorRing j) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  have : IsScalarTower (A.S.obj i) (A.residueTensorRing i) (A.residueTensorRing j) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (_ : A.residueTensorRing j) = tensorRingTransition A i j h (a ⊗ₜ _)
      simp only [tensorRingTransition, Algebra.TensorProduct.mapRingHom_tmul]
      rfl
  have : IsScalarTower (A.S.obj i) (A.residueTensorRing j) (A.residueTensorRing j) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp
  let : Module (A.S.obj i) (A.M.obj j) :=
    Module.compHom (A.M.obj j) (A.S.map (homOfLE h)).hom
  have : IsScalarTower (A.S.obj i) (A.S.obj j) (A.M.obj j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨e, he⟩ := A.moduleBaseChange i j h rfl
  let el : (A.S.obj j ⊗[A.S.obj i] A.M.obj i) ≃ₗ[A.S.obj j] A.M.obj j :=
    { toFun := fun t ↦ e (TensorProduct.comm _ _ _ t)
      invFun := fun x ↦ (TensorProduct.comm _ _ _).symm (e.symm x)
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intros; simp
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp_all [smul_add]
        | tmul b x => simp [TensorProduct.smul_tmul', he, mul_smul] }
  let ei := (baseChangeEquiv (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField
    (↥(A.M.obj i))).symm.linearEquiv (A.residueTensorRing i)
  let ej := (baseChangeEquiv (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField
    (↥(A.M.obj j))).symm.linearEquiv (A.residueTensorRing j)
  let E := (ei.baseChange (A.residueTensorRing i) (A.residueTensorRing j) _ _).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange (↥(A.S.obj i))
      (A.residueTensorRing i) (A.residueTensorRing j) (A.residueTensorRing j)
      (↥(A.M.obj i))).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (↥(A.S.obj i))
        (↥(A.S.obj j)) (A.residueTensorRing j) (A.residueTensorRing j)
        (↥(A.M.obj i))).symm.trans
        ((el.baseChange (A.S.obj j) (A.residueTensorRing j) _ _).trans ej.symm)))
  refine ⟨E, ?_⟩
  intro a x
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp_all [TensorProduct.add_tmul, add_smul]
  | tmul b c =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp_all [TensorProduct.tmul_add, smul_add]
    | tmul x e' =>
      simp [E, ei, ej, el, baseChangeEquiv, he, tensorTransition_tmul,
        baseChangeAction_tmul, Algebra.smul_def,
        Algebra.TensorProduct.tmul_mul_tmul, RingHom.algebraMap_toAlgebra,
        tensorRingTransition, mul_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem module_localization_of_baseChange
    {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (W : Submonoid R) [IsLocalization W S]
    (p : M →+ N) (E : S ⊗[R] M ≃ₗ[S] N)
    (hE : ∀ (a : S) (x : M), E (a ⊗ₜ[R] x) = a • p x) :
    let : Module S (LocalizedModule W M) := LocalizedModule.moduleOfIsLocalization
      (S := W) (T := S)
    ∃ e : LocalizedModule W M ≃ₗ[S] N,
      ∀ (x : M) (w : W), ∃ b : S, algebraMap R S w * b = 1 ∧
        e (LocalizedModule.mk x w) = b • p x := by
  let : Module S (LocalizedModule W M) := LocalizedModule.moduleOfIsLocalization
    (S := W) (T := S)
  let f := LocalizedModule.mkLinearMap W M
  have hf : IsBaseChange S f := IsLocalizedModule.isBaseChange W S f
  let e := hf.equiv.symm.trans E
  have he (x : M) : e (LocalizedModule.mk x 1) = p x := by
    change E (hf.equiv.symm (f x)) = p x
    rw [IsBaseChange.equiv_symm_apply, hE, one_smul]
  refine ⟨e, fun x w ↦ ?_⟩
  obtain ⟨b, hb⟩ := (IsLocalization.map_units S w).exists_right_inv
  refine ⟨b, hb, ?_⟩
  have hx : algebraMap R S (w : R) • e (LocalizedModule.mk x w) = p x := by
    rw [← map_smul, IsScalarTower.algebraMap_smul]
    rw [LocalizedModule.smul'_mk]
    exact (congrArg e (LocalizedModule.mk_cancel w x)).trans (he x)
  calc
    e (LocalizedModule.mk x w) = (b * algebraMap R S (w : R)) •
        e (LocalizedModule.mk x w) := by rw [mul_comm, hb, one_smul]
    _ = b • p x := by rw [mul_smul, hx]

private theorem tensor_localization (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) [Algebra (A.R.obj i) (A.R.obj j)]
    (ha : algebraMap (A.R.obj i) (A.R.obj j) = (A.R.map (homOfLE h)).hom)
    (W : Submonoid (A.S.obj i ⊗[A.R.obj i] A.R.obj j))
    (g : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.S.obj j)
    (hg : ∀ (a : A.S.obj i) (b : A.R.obj j),
      g (a ⊗ₜ[A.R.obj i] b) =
        A.S.map (homOfLE h) a * algebraMap (A.R.obj j) (A.S.obj j) b)
    (hl : @IsLocalization _ _ W _ _ g.toAlgebra) :
    let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
    ∃ θ : (A.S.obj i ⊗[A.R.obj i] A.R.obj j) →+* A.residueTensorRing i,
      (∀ (a : A.S.obj i) (b : A.R.obj j),
        θ (a ⊗ₜ[A.R.obj i] b) = a ⊗ₜ[A.R.obj i]
          IsLocalRing.residue A.r.pt (A.r.ι.app j b)) ∧
      ∃ hloc : @IsLocalization _ _ (W.map θ) _ _ (tensorRingTransition A i j h).toAlgebra,
        let := (tensorRingTransition A i j h).toAlgebra
        let := hloc
        let : Module (A.residueTensorRing j)
            (LocalizedModule (W.map θ) (A.residueTensorModule i)) :=
          LocalizedModule.moduleOfIsLocalization (S := W.map θ) (T := A.residueTensorRing j)
        ∃ e : LocalizedModule (W.map θ) (A.residueTensorModule i)
            ≃ₗ[A.residueTensorRing j] A.residueTensorModule j,
          ∀ (x : A.residueTensorModule i) (w : W.map θ),
            ∃ b : A.residueTensorRing j, tensorRingTransition A i j h w * b = 1 ∧
              e (LocalizedModule.mk x w) = b • tensorTransition A i j h x := by
  let := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let := baseChangeAction (↥(A.R.obj j)) (↥(A.S.obj j)) A.residueField (↥(A.M.obj j))
  obtain ⟨θ, hθ, hloc⟩ := tensor_ring_localization A i j h ha W g hg hl
  let := (tensorRingTransition A i j h).toAlgebra
  let := hloc
  obtain ⟨E, hE⟩ := tensor_transition_baseChange A i j h
  exact ⟨θ, hθ, hloc, module_localization_of_baseChange (W.map θ)
    (tensorTransition A i j h) E hE⟩

private theorem tensor_comparison_compatible (A : LocalAlgebraApproximationSystem.{u})
    (i j : A.I) (h : i ≤ j) :
    (tensorComparison A j).comp (tensorTransition A i j h) = tensorComparison A i := by
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x c =>
    simp only [AddMonoidHom.comp_apply, tensorTransition_tmul, tensorComparison_tmul]
    exact congrArg (fun y : A.μ.pt ↦ y ⊗ₜ[A.r.pt] c)
      (ConcreteCategory.congr_hom (A.μ.w (homOfLE h)) x)

private theorem tensor_eventually_injective (A : LocalAlgebraApproximationSystem.{u}) :
    ∀ i₀ : A.I, ∃ i₁ : A.I, i₀ ≤ i₁ ∧ ∀ j : A.I, i₁ ≤ j →
      Function.Injective (tensorComparison A j) := by
  classical
  let (i : A.I) := baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i))
    A.residueField (↥(A.M.obj i))
  let (i : A.I) := tensorLimitAction A i
  have loc (i j : A.I) (h : i ≤ j) :
      ∃ (W : Submonoid (A.residueTensorRing i))
        (hloc : @IsLocalization _ _ W _ _ (tensorRingTransition A i j h).toAlgebra),
        let := (tensorRingTransition A i j h).toAlgebra
        let := hloc
        let : Module (A.residueTensorRing j)
            (LocalizedModule W (A.residueTensorModule i)) :=
          LocalizedModule.moduleOfIsLocalization (S := W) (T := A.residueTensorRing j)
        ∃ e : LocalizedModule W (A.residueTensorModule i)
            ≃ₗ[A.residueTensorRing j] A.residueTensorModule j,
          ∀ (x : A.residueTensorModule i) (w : W),
            ∃ b : A.residueTensorRing j, tensorRingTransition A i j h w * b = 1 ∧
              e (LocalizedModule.mk x w) = b • tensorTransition A i j h x := by
    let : Algebra (A.R.obj i) (A.R.obj j) := (A.R.map (homOfLE h)).hom.toAlgebra
    obtain ⟨W, g, hg, hl⟩ := A.localization i j h rfl
    obtain ⟨θ, _, hl, e, he⟩ := tensor_localization A i j h rfl W g hg hl
    exact ⟨W.map θ, hl, e, he⟩
  choose W hloc E hE using loc
  intro i₀
  apply localization_system_kernel_stabilization.{u, u, u, u, u}
    A.I (fun i j ↦ exists_ge_ge i j) A.residueTensorRing (tensorRingTransition A)
    ?_ ?_ A.residueTensorModule (fun i ↦ inferInstance) (tensorTransition A)
    ?_ ?_ (tensorTransition_semilinear A) A.limitResidueTensorModule
    (fun i ↦ tensorLimitAction A i) ?_ (tensorLinearComparison A)
    (tensor_comparison_compatible A) ?_ i₀ ?_ W (fun _ _ _ ↦ (W _ _ _).one_mem)
    (fun _ _ _ _ _ ha hb ↦ (W _ _ _).mul_mem ha hb) hloc (fun i j h ↦ ⟨E i j h, hE i j h⟩)
  · intro i
    apply tensorRingHom_ext
    intro a c
    simp [tensorRingTransition]
  · intro i j k hij hjk
    apply tensorRingHom_ext
    intro a c
    simp only [RingHom.comp_apply, tensorRingTransition,
      Algebra.TensorProduct.mapRingHom_tmul, RingHom.id_apply]
    exact congrArg (fun a : A.S.obj k ↦ a ⊗ₜ[A.R.obj k] c)
      (ConcreteCategory.congr_hom (A.S.map_comp (homOfLE hij) (homOfLE hjk)) a).symm
  · intro i
    apply AddMonoidHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x c => simp [tensorTransition_tmul]
  · intro i j k hij hjk
    apply AddMonoidHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x c =>
      simp only [AddMonoidHom.comp_apply, tensorTransition_tmul]
      exact congrArg (fun x : A.M.obj k ↦ x ⊗ₜ[A.R.obj k] c)
        (ConcreteCategory.congr_hom (A.M.map_comp (homOfLE hij) (homOfLE hjk)) x).symm
  · intro i j h a x
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp_all [add_smul]
    | tmul a c =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all [smul_add]
      | tmul x e =>
        simp only [tensorRingTransition, Algebra.TensorProduct.mapRingHom_tmul,
          RingHom.id_apply, tensorLimitAction_tmul]
        exact congrArg (fun a : A.s.pt ↦ (a • x) ⊗ₜ[A.r.pt] (c * e))
          (ConcreteCategory.congr_hom (A.s.w (homOfLE h)) a)
  · intro Q _ f hf
    exact tensor_colimit A (AddCommGrpCat.of Q) f hf
  · let := residueTensor_noetherian A i₀
    let := baseChange_finite (↥(A.R.obj i₀)) (↥(A.S.obj i₀))
      A.residueField (↥(A.M.obj i₀))
    infer_instance

/-- The residue tensor diagram of a local algebra approximation system has all the
specified quotient identifications, finiteness and localization properties, is a group
colimit, and has eventually injective comparison maps.

Source: Stacks Project, Algebra, Tag 046Y, middle proof paragraph
(blueprint: lem-trf-eventual-residue-tensor-comparison-injective).

Proof plan, following the seven steps of the node:
1. Locality induces `k_i → k`. Apply tensor-over-quotient and tensor commutativity to
   obtain the two stage quotient identifications and `P ≃ M/mM`. Their pure tensor
   formulas identify the comparison with `[x] ⊗ [r] ↦ [r μ_i(x)]`.
2. Write `S_i` as a localization of a finite type `R_i`-algebra `B_i`. The algebra
   `B_i ⊗[R_i] k` is finite type over the field `k`, hence Noetherian by the Hilbert
   basis theorem. Localization base change identifies `D_i` with its localization:
   `(b ⊗ c) ⊗ s ↦ bs ⊗ c`, inverse `s ⊗ c ↦ (1 ⊗ c) ⊗ s`.
3. Finite generators `x_t` of `M_i` give generators `x_t ⊗ 1` over `D_i`. The pure
   tensor action makes `ψ_i` linear; its kernel is finite over the Noetherian `D_i`.
4. For `A_ij = S_i ⊗[R_i] R_j`, identify `D_i ⊗[A_ij] S_j` with `D_j` by
   `(a ⊗ c) ⊗ s ↦ s_ji(a)s ⊗ c`, inverse `s ⊗ c ↦ (1 ⊗ c) ⊗ s`. Localization
   base change gives the ring localization at the specified image of `W_ji`.
5. Identify `(M_i ⊗[R_i] R_j) ⊗[A_ij] S_j` with `M_i ⊗[S_i] S_j` by
   `(x ⊗ b) ⊗ s ↦ x ⊗ φ_j(b)s`, inverse `x ⊗ s ↦ (x ⊗ 1) ⊗ s`. The assumed
   scalar extension isomorphism identifies this with `M_j`. Apply localization
   tensor-over-base first to this module and then tensor with `k`. The source
   identifies with `P_i` by `(x ⊗ b) ⊗ c ↦ x ⊗ r_j(b)c`, with the displayed inverse.
6. Construct the additive colimit factorization directly from a compatible family
   on the tensors. Descend the bilinear maps on `M_i × k` through the given group
   colimit of the `M_i`; stage representatives and a common upper bound prove the
   required balance over `R`. Tensor universality supplies the unique map on `P`.
7. Apply localization-system-kernel-stabilization to `D_i`, `P_i`, `P`, `d`, `p`,
   and `ψ`. Their formulas give semilinearity, identity/composition, compatible
   actions and the cocone laws; steps 4--5 give localization transitions, step 6
   the group colimit, and step 3 a finite kernel at each starting index. This gives
   a common later index after which every comparison is injective.
-/
theorem eventual_residue_tensor_comparison_injective
    (A : LocalAlgebraApproximationSystem.{u}) : Nonempty (ResidueTensorComparison A) := by
  classical
  let stage (i : A.I) :=
    baseChangeAction (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
  let lim (i : A.I) := tensorLimitAction A i
  let rf (i : A.I) := residueFieldAction A i
  let qr (i : A.I) := residueRingAction A i
  let qm (i : A.I) := residueQuotientModule (↥(A.R.obj i)) (↥(A.M.obj i))
  let psi (i : A.I) := tensorLinearComparison A i
  let me (i : A.I) := residueModuleEquiv A i
  let le := residueLimitEquiv A
  let qc (i : A.I) := le.toAddMonoidHom.comp
    ((psi i).toAddMonoidHom.comp (me i).symm.toAddMonoidHom)
  refine ⟨{
    stageAction := stage
    limitAction := lim
    stageAction_tmul := fun i ↦ baseChangeAction_tmul _ _ _ _
    limitAction_tmul := tensorLimitAction_tmul A
    d := tensorRingTransition A
    p := tensorTransition A
    ψ := psi
    d_tmul := by intros; simp [tensorRingTransition]
    p_tmul := tensorTransition_tmul A
    ψ_tmul := tensorComparison_tmul A
    noetherian := residueTensor_noetherian A
    finite := fun i ↦ baseChange_finite _ _ _ _
    finite_kernel := ?_
    residueFieldAlgebra := rf
    residueFieldAlgebra_map := by intros; rfl
    quotientRingAlgebra := qr
    quotientRingAlgebra_map := by intros; rfl
    quotientModule := qm
    quotientModule_smul := by intros; rfl
    ringEquiv := residueRingEquiv A
    ringEquiv_tmul := residueRingEquiv_tmul A
    moduleEquiv := me
    moduleEquiv_tmul := ?_
    limitEquiv := le
    limitEquiv_tmul := ?_
    quotientComparison := qc
    quotientComparison_tmul := ?_
    comparison_square := by intro i x; simp [qc]
    localization := ?_
    compatible := ?_
    colimit := ?_
    eventually_injective := ?_ }⟩
  · intro i
    let := residueTensor_noetherian A i
    let := baseChange_finite (↥(A.R.obj i)) (↥(A.S.obj i)) A.residueField (↥(A.M.obj i))
    exact inferInstance
  · intro i x c
    let := residueFieldTower A i
    exact quotientModuleEquiv_tmul _ _ _ x c
  · intro x b
    exact TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ _ _
  · intro i x b
    let := residueFieldTower A i
    have he : me i (x ⊗ₜ[A.R.obj i] IsLocalRing.residue A.r.pt b) =
        (Submodule.Quotient.mk x : A.stageResidueModule i) ⊗ₜ
          IsLocalRing.residue A.r.pt b := quotientModuleEquiv_tmul _ _ _ _ _
    rw [← he]
    dsimp only [qc, AddMonoidHom.comp_apply]
    change le (psi i ((me i).symm (me i
      (x ⊗ₜ[A.R.obj i] IsLocalRing.residue A.r.pt b)))) = _
    rw [AddEquiv.symm_apply_apply]
    change residueLimitEquiv A (tensorComparison A i
      (x ⊗ₜ[A.R.obj i] IsLocalRing.residue A.r.pt b)) = _
    rw [tensorComparison_tmul]
    exact TensorProduct.tensorQuotEquivQuotSMul_tmul_mk
      (M := ↥A.μ.pt) (IsLocalRing.maximalIdeal A.r.pt) _ b
  · intro i j h _ ha W g hg hl
    obtain ⟨θ, hθ, hloc, he⟩ := tensor_localization A i j h ha W g hg hl
    let := (tensorRingTransition A i j h).toAlgebra
    let := hloc
    let : Module (A.residueTensorRing j)
        (LocalizedModule (W.map θ) (A.residueTensorModule i)) :=
      LocalizedModule.moduleOfIsLocalization (S := W.map θ) (T := A.residueTensorRing j)
    obtain ⟨e, he⟩ := he
    exact ⟨θ, hθ, hloc, e.toAddEquiv, he⟩
  · intro i j h
    apply AddMonoidHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x c =>
      change tensorComparison A j (tensorTransition A i j h (x ⊗ₜ[A.R.obj i] c)) =
        tensorComparison A i (x ⊗ₜ[A.R.obj i] c)
      rw [tensorTransition_tmul, tensorComparison_tmul, tensorComparison_tmul]
      change (@id A.μ.pt (A.μ.ι.app j (A.M.map (homOfLE h) x))) ⊗ₜ[A.r.pt] c =
        (@id A.μ.pt (A.μ.ι.app i x)) ⊗ₜ[A.r.pt] c
      exact congrArg (fun y : A.μ.pt ↦ y ⊗ₜ[A.r.pt] c)
        (ConcreteCategory.congr_hom (A.μ.w (homOfLE h)) x)
  · exact tensor_colimit A
  · exact tensor_eventually_injective A

end LocalAlgebraApproximationSystem
