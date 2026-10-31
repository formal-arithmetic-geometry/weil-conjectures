/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.LocalModuleArrowNoetherianDescent
import WeilConjectures.TraceFormula.EventualResidueTensorComparisonInjective
import WeilConjectures.RingTheory.NoetherianArrowEventualInjectiveFlatCokernel
import WeilConjectures.RingTheory.LocalizedArrowInjectiveFlatCokernelLimit
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Algebra.Equiv

/-!
# Closed-fibre injectivity over an essentially finitely presented local algebra

Source: Stacks Project, Algebra, Tag 046Y (`lemma-mod-injective-general`), statement and proof
(blueprint: lem-trf-valuation-general-mod-injective).
-/

@[expose] public section

set_option autoImplicit false

universe u v p w z

namespace Algebra

open scoped _root_.TensorProduct in
/-- Tensoring with the residue field gives the quotient by maximal-ideal multiples;
its canonical equivalences intertwine the two induced arrows. -/
private theorem residue_tensor_injective
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    (h : Function.Injective
      (Submodule.mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) f
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) f))) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) := by
  let eM := _root_.TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)
  let eN := _root_.TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal R)
  let fQ := Submodule.mapQ
    (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) f
    (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) f)
  have comm : eN.toLinearMap.comp (f.lTensor (IsLocalRing.ResidueField R)) =
      fQ.comp eM.toLinearMap := by
    apply _root_.TensorProduct.ext'
    intro r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    change eN ((IsLocalRing.residue R r) ⊗ₜ[R] f x) =
      fQ (eM ((IsLocalRing.residue R r) ⊗ₜ[R] x))
    dsimp only [eM, eN, IsLocalRing.ResidueField, IsLocalRing.residue]
    rw [_root_.TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      _root_.TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    exact congrArg Submodule.Quotient.mk (f.map_smul r x).symm
  intro x y hxy
  apply eM.injective
  apply h
  have hcomm := LinearMap.congr_fun comm
  exact (hcomm x).symm.trans ((congrArg eN hxy).trans (hcomm y))

open CategoryTheory CategoryTheory.Limits in
open scoped _root_.TensorProduct in
/-- Assemble the four existing Tag 046Y approximation, residue, stage and limit lemmas
when all carriers have been placed in a common universe. -/
private theorem local_criterion_same_universe
    {R S P M N : Type u}
    [CommRing R] [CommRing S] [CommRing P] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (W : Submonoid P) [IsLocalization W S]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    [Module R M] [Module R N] [IsScalarTower R S M] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    (u : M →ₗ[S] N) [Module.Flat R N]
    (h_fibre : Function.Injective
      ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) := by
  have data := RingHom.exists_local_module_arrow_noetherian_descent
    (algebraMap R S) W (algebraMap P S)
    (IsScalarTower.algebraMap_eq R P S).symm
    (by rw [_root_.toAlgebra_algebraMap]; infer_instance) u
  rcases data with ⟨I, hpre, hne, hdir, Ri, Si, ρ, π, data⟩
  rcases data with ⟨κ, Md, Nd, μ, ν, hM, hN, ui, data⟩
  rcases data with ⟨hlocalR, hlocalS, hlocalρ, hlocalRt, hlocalSt, hlocalπ, hlocalκ,
    hsquare, data⟩
  rcases data with ⟨hm_smul, hn_smul, hmu_smul, hnu_smul, hstage, hlimit, hnoethR,
    hnoethS, data⟩
  rcases data with ⟨hfiniteZ, hess, hfpM, hfpN, hcR, hcS, hcM, hcN, data⟩
  rcases data with ⟨hrepR, hrepS, heqR, heqS, hrepM, hrepN, heqM, heqN, data⟩
  rcases data with ⟨hloc, hbase, hlocLimit, hbaseLimit⟩
  let cR : Cocone Ri := Cocone.mk (CommRingCat.of R) π
  let cS : Cocone Si := Cocone.mk (CommRingCat.of S) κ
  let cM : Cocone Md := Cocone.mk (AddCommGrpCat.of M) μ
  let cN : Cocone Nd := Cocone.mk (AddCommGrpCat.of N) ν
  let : ∀ i, Algebra (Ri.obj i) (Si.obj i) := fun i => (ρ.app i).hom.toAlgebra
  let : ∀ i, Algebra (Ri.obj i) R := fun i => (π.app i).hom.toAlgebra
  let : ∀ i, Algebra (Si.obj i) S := fun i => (κ.app i).hom.toAlgebra
  let : ∀ i, Algebra (Ri.obj i) S := fun i =>
    ((algebraMap R S).comp (π.app i).hom).toAlgebra
  have htowerR : ∀ i, IsScalarTower (Ri.obj i) R S := fun i =>
    IsScalarTower.of_algebraMap_eq fun r => rfl
  have htowerS : ∀ i, IsScalarTower (Ri.obj i) (Si.obj i) S := by
    intro i
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact congrArg (fun f : Ri.obj i ⟶ CommRingCat.of S => f.hom r) (hsquare i).symm
  let : ∀ i, Module (Ri.obj i) (Md.obj i) := fun i =>
    Module.compHom (Md.obj i) (ρ.app i).hom
  let : ∀ i, Module (Ri.obj i) (Nd.obj i) := fun i =>
    Module.compHom (Nd.obj i) (ρ.app i).hom
  have htowerM : ∀ i, IsScalarTower (Ri.obj i) (Si.obj i) (Md.obj i) :=
    fun i => IsScalarTower.of_algebraMap_smul fun r x => rfl
  have htowerN : ∀ i, IsScalarTower (Ri.obj i) (Si.obj i) (Nd.obj i) :=
    fun i => IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hfiniteM : ∀ i, Module.Finite (Si.obj i) (Md.obj i) := fun i => inferInstance
  have hfiniteN : ∀ i, Module.Finite (Si.obj i) (Nd.obj i) := fun i => inferInstance
  let : ∀ i, Algebra (Ri.obj i) (IsLocalRing.ResidueField R) := fun i =>
    ((IsLocalRing.residue R).comp (π.app i).hom).toAlgebra
  let A : LocalAlgebraApproximationSystem.{u} := {
    I := I, R := Ri, S := Si, r := cR, s := cS,
    colimitR := hcR.some, colimitS := hcS.some,
    transitionLocalR := hlocalRt, transitionLocalS := hlocalSt,
    coconeLocalR := hlocalπ, coconeLocalS := hlocalκ,
    square := fun i j h => by
      exact congrArg CommRingCat.Hom.hom (ρ.naturality (homOfLE h)).symm
    coconeSquare := fun i => by
      exact congrArg CommRingCat.Hom.hom (hsquare i).symm
    repR := hrepR, eqR := fun i j x y h => (heqR i j x y).mp h,
    repS := hrepS, eqS := fun i j x y h => (heqS i j x y).mp h,
    M := Md, μ := cM, colimitM := hcM.some,
    semilinear := hm_smul, coconeSemilinear := hmu_smul,
    essentiallyFiniteType := fun i => (RingHom.essFiniteType_algebraMap.mp (hess i)),
    residueAlgebraMap := fun i => rfl,
    localization := by
      intro i j h alg halg
      have heq : alg = ((Ri.map (homOfLE h)).hom.toAlgebra) :=
        Algebra.algebra_ext _ _ fun r => congrArg (fun f => f r) halg
      cases heq
      let : Algebra (Ri.obj i) (Ri.obj j) := (Ri.map (homOfLE h)).hom.toAlgebra
      obtain ⟨q, hq, V, hV⟩ := hloc i j h
      exact ⟨V, q, hq, hV⟩
    moduleBaseChange := by
      intro i j h alg halg
      have heq : alg = ((Si.map (homOfLE h)).hom.toAlgebra) :=
        Algebra.algebra_ext _ _ fun r => congrArg (fun f => f r) halg
      cases heq
      let : Algebra (Si.obj i) (Si.obj j) := (Si.map (homOfLE h)).hom.toAlgebra
      obtain ⟨eM, eN, heM, heN, he⟩ := hbase i j h
      refine ⟨(_root_.TensorProduct.comm (Si.obj i) (Md.obj i) (Si.obj j)).toAddEquiv.trans
        eM.toAddEquiv, ?_⟩
      intro x s
      exact heM s x }
  obtain ⟨C⟩ := A.eventual_residue_tensor_comparison_injective
  obtain ⟨i₁, _, hinj⟩ := C.eventually_injective (Classical.choice hne)
  have hsource : ∀ j : I, i₁ ≤ j →
      ∃ Ψ : (IsLocalRing.ResidueField R ⊗[Ri.obj j] Md.obj j) →ₗ[IsLocalRing.ResidueField R]
          (IsLocalRing.ResidueField R ⊗[R] M),
        (∀ c x, Ψ (c ⊗ₜ[Ri.obj j] x) =
          c ⊗ₜ[R] (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app j)) x) ∧
          Function.Injective Ψ := by
    intro j hj
    let e := _root_.TensorProduct.comm (Ri.obj j) (IsLocalRing.ResidueField R) (Md.obj j)
    let f := _root_.TensorProduct.comm R M (IsLocalRing.ResidueField R)
    let ψj : (Md.obj j ⊗[Ri.obj j] IsLocalRing.ResidueField R) →+
        (M ⊗[R] IsLocalRing.ResidueField R) := (C.ψ j).toAddMonoidHom
    let ψ := f.toAddEquiv.toAddMonoidHom.comp (ψj.comp
      e.toAddEquiv.toAddMonoidHom)
    refine ⟨{ ψ with map_smul' := ?_ }, ?_, ?_⟩
    · intro c t
      induction t using _root_.TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        change f (C.ψ j (x ⊗ₜ[Ri.obj j] (c * a))) =
          c • f (C.ψ j (x ⊗ₜ[Ri.obj j] a))
        rw [C.ψ_tmul, C.ψ_tmul]
        rfl
      | add x y hx hy =>
        change ψ (c • (x + y)) = c • ψ (x + y)
        change ψ (c • x) = c • ψ x at hx
        change ψ (c • y) = c • ψ y at hy
        rw [smul_add, map_add, map_add, smul_add, hx, hy]
    · intro c x
      exact congrArg f (C.ψ_tmul j x c)
    · exact f.injective.comp ((hinj j hj).comp e.injective)
  have hring : ∀ (i j : I) (h : i ≤ j) (r : Ri.obj i),
      (Si.map (homOfLE h)).hom (algebraMap (Ri.obj i) (Si.obj i) r) =
        algebraMap (Ri.obj j) (Si.obj j) ((Ri.map (homOfLE h)).hom r) := by
    intro i j h r
    exact congrArg (fun f : Ri.obj i ⟶ Si.obj j => f.hom r)
      (ρ.naturality (homOfLE h)).symm
  have hmid : ∀ (i : I) (x : Md.obj i), (Md.map (homOfLE le_rfl)).hom x = x := by
    intro i x
    change Md.map (𝟙 i) x = x
    simp
  have hnid : ∀ (i : I) (x : Nd.obj i), (Nd.map (homOfLE le_rfl)).hom x = x := by
    intro i x
    change Nd.map (𝟙 i) x = x
    simp
  have hmcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Md.obj i),
      (Md.map (homOfLE hjk)).hom ((Md.map (homOfLE hij)).hom x) =
        (Md.map (homOfLE (hij.trans hjk))).hom x := by
    intro i j k hij hjk x
    exact congrArg (fun f : Md.obj i ⟶ Md.obj k => f.hom x)
      (Md.map_comp (homOfLE hij) (homOfLE hjk)).symm
  have hncomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Nd.obj i),
      (Nd.map (homOfLE hjk)).hom ((Nd.map (homOfLE hij)).hom x) =
        (Nd.map (homOfLE (hij.trans hjk))).hom x := by
    intro i j k hij hjk x
    exact congrArg (fun f : Nd.obj i ⟶ Nd.obj k => f.hom x)
      (Nd.map_comp (homOfLE hij) (homOfLE hjk)).symm
  have hmucomp : ∀ (i j : I) (h : i ≤ j) (x : Md.obj i),
      (μ.app j).hom ((Md.map (homOfLE h)).hom x) = (μ.app i).hom x := by
    intro i j h x
    exact congrArg (fun f : Md.obj i ⟶ AddCommGrpCat.of M => f.hom x)
      (cM.w (homOfLE h))
  have hnucomp : ∀ (i j : I) (h : i ≤ j) (x : Nd.obj i),
      (ν.app j).hom ((Nd.map (homOfLE h)).hom x) = (ν.app i).hom x := by
    intro i j h x
    exact congrArg (fun f : Nd.obj i ⟶ AddCommGrpCat.of N => f.hom x)
      (cN.w (homOfLE h))
  have hloc' : ∀ (i j : I) (h : i ≤ j),
      let := (Ri.map (homOfLE h)).hom.toAlgebra
      ∃ (q : Si.obj i ⊗[Ri.obj i] Ri.obj j →+* Si.obj j)
        (V : Submonoid (Si.obj i ⊗[Ri.obj i] Ri.obj j)),
        (∀ s r, q (s ⊗ₜ[Ri.obj i] r) =
          (Si.map (homOfLE h)).hom s * algebraMap (Ri.obj j) (Si.obj j) r) ∧
        (let := q.toAlgebra; IsLocalization V (Si.obj j)) := by
    intro i j h
    obtain ⟨q, hq, V, hV⟩ := hloc i j h
    exact ⟨q, V, hq, hV⟩
  obtain ⟨i₂, _, htail⟩ :=
    Module.eventually_injective_flat_cokernel_of_noetherian_local_stages
      Ri Si cR cS hcR.some hcS.some hlocalRt hlocalSt (fun _ => rfl) (fun _ => rfl)
      hring hrepR hrepS
      (fun i j x y h => (heqR i j x y).mp h)
      (fun i j x y h => (heqS i j x y).mp h)
      (fun i => Md.obj i) (fun i => Nd.obj i) ui
      (fun i j h => (Md.map (homOfLE h)).hom)
      (fun i j h => (Nd.map (homOfLE h)).hom)
      hm_smul hn_smul hmid hnid hmcomp hncomp hstage M N
      (fun i => (μ.app i).hom) (fun i => (ν.app i).hom)
      hmu_smul hnu_smul hmucomp hnucomp u hlimit hrepM hrepN
      (fun i j x y h => (heqM i j x y).mp h)
      (fun i j x y h => (heqN i j x y).mp h)
      hloc'
      (fun i j h => by obtain ⟨e, f, he, hf, hu⟩ := hbase i j h; exact ⟨e, he⟩)
      (fun i j h => by obtain ⟨e, f, he, hf, hu⟩ := hbase i j h; exact ⟨f, hf⟩)
      h_fibre i₁ hsource
  choose alpha beta halpha hbeta harrow using hbaseLimit
  have hlocLim : ∀ i : I,
      ∃ (q : Si.obj i ⊗[Ri.obj i] R →+* S)
        (V : Submonoid (Si.obj i ⊗[Ri.obj i] R)),
        (∀ a r, q (a ⊗ₜ[Ri.obj i] r) =
          algebraMap (Si.obj i) S a * algebraMap R S r) ∧
        (∀ w : V, IsUnit (q w)) ∧
        (∀ s : S, ∃ (a : Si.obj i ⊗[Ri.obj i] R) (w : V), s * q w = q a) ∧
        (∀ a : Si.obj i ⊗[Ri.obj i] R, q a = 0 →
          ∃ w : V, (w : Si.obj i ⊗[Ri.obj i] R) * a = 0) := by
    intro i
    obtain ⟨q, hq, V, hV⟩ := hlocLimit i
    let := q.toAlgebra
    have : IsLocalization V S := hV
    refine ⟨q, V, hq, IsLocalization.map_units S, ?_, ?_⟩
    · intro s
      obtain ⟨⟨a, w⟩, hw⟩ := IsLocalization.surj V s
      exact ⟨a, w, hw⟩
    · intro a ha
      exact (IsLocalization.map_eq_zero_iff V S a).mp ha
  obtain ⟨hinjective, hflat, _⟩ :=
    Module.injective_flat_cokernel_of_localized_directed_limit
      Ri Si cR cS hcR.some hcS.some (fun _ => rfl) (fun _ => rfl) hring
      (fun i => Md.obj i) (fun i => Nd.obj i) ui
      (fun i j h => (Md.map (homOfLE h)).hom)
      (fun i j h => (Nd.map (homOfLE h)).hom)
      hm_smul hn_smul hmid hnid hmcomp hncomp hstage M N
      (fun i => (μ.app i).hom) (fun i => (ν.app i).hom)
      hmu_smul hnu_smul hmucomp hnucomp u hlimit hrepM hrepN
      (fun i j x y h => (heqM i j x y).mp h)
      (fun i j x y h => (heqN i j x y).mp h)
      alpha beta (fun i x s => halpha i s x) (fun i y s => hbeta i s y)
      (fun i t => by
        induction t using _root_.TensorProduct.induction_on with
        | zero => simp
        | tmul s x => exact harrow i s x
        | add x y hx hy => simp only [map_add, hx, hy])
      hlocLim i₂ (fun j hj => ⟨(htail j hj).2.2.1, (htail j hj).2.2.2⟩)
  exact ⟨hinjective, hflat⟩

/-- A map of finitely presented modules over an essentially finitely presented local algebra,
with flat target and injective closed fibre, is injective with flat cokernel. The algebra `P`
and submonoid `W` witness essential finite presentation; `IsLocalization W S` expresses the
localization up to its canonical isomorphism, compatibly with the `R`-algebra structures.

Source: Stacks Project, Algebra, Tag 046Y (`lemma-mod-injective-general`)
(blueprint: lem-trf-valuation-general-mod-injective).

Proof:
1. Lift all five carriers to a common universe by `ULift`. Ring equivalences preserve
   local rings, local maps, finite presentation and localization. Linear equivalences
   preserve finite presentation and flatness. The induced semilinear equivalences on
   residue fields and tensors carry the original closed-fibre injection to the lifted one.
2. Apply [lem-trf-local-module-arrow-noetherian-descent] simultaneously to the source,
   target and arrow. Use its actual ring and additive-group colimits, local maps,
   transition localizations and canonical module base-change equivalences.
3. Package the source diagram as a `LocalAlgebraApproximationSystem`. Apply
   [lem-trf-eventual-residue-tensor-comparison-injective]. Tensor symmetry converts its
   comparisons into the residue-field-linear maps used by the Noetherian stage lemma;
   the pure-tensor formulas prove linearity and identify the comparison maps.
4. Apply [lem-trf-noetherian-arrow-eventual-injective-flat-cokernel] to get a common
   tail of injective arrows with flat cokernels. The diagram functors and cocones
   supply all identity, composition and compatibility laws.
5. Apply [lem-trf-localized-arrow-injective-flat-cokernel-limit]. The approximation
   supplies its limit localization and module equivalences; tensor induction extends
   their arrow compatibility from pure tensors to arbitrary tensors. The stage lemma
   supplies its tail hypothesis. This gives injectivity and flat cokernel at the limit.
6. Transport injectivity through `ULift.down`. Restrict scalars from the lifted base
   ring, then use the quotient equivalence induced by `ULift.moduleEquiv` to obtain
   flatness of the original cokernel. No new intermediate statement is assumed.
-/
theorem local_essentially_finite_presentation_mod_injective
    {R : Type u} {S : Type v} {P : Type p} {M : Type w} {N : Type z}
    [CommRing R] [CommRing S] [CommRing P] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (W : Submonoid P) [IsLocalization W S]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    [Module R M] [Module R N] [IsScalarTower R S M] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    (u : M →ₗ[S] N) [Module.Flat R N]
    (h_fibre : Function.Injective
      (Submodule.mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N))
        (u.restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal R) (u.restrictScalars R)))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) := by
  classical
  let R' := ULift.{max u v p w z} R
  let S' := ULift.{max u v p w z} S
  let P' := ULift.{max u v p w z} P
  let M' := ULift.{max u v p w z} M
  let N' := ULift.{max u v p w z} N
  let : Algebra R' S' := ULift.algebra' R S'
  let : Algebra R' P' := ULift.algebra' R P'
  let : Algebra P' S' := ULift.algebra' P S'
  let : Algebra S' S := ULift.algebra' S S
  let : Algebra P' S := ULift.algebra' P S
  have : IsLocalHom (ULift.ringEquiv : R' ≃+* R).toRingHom :=
    ⟨fun a h => h.map (ULift.ringEquiv : R' ≃+* R).symm.toRingHom⟩
  have : IsLocalHom (ULift.ringEquiv : S' ≃+* S).symm.toRingHom :=
    ⟨fun a h => h.map (ULift.ringEquiv : S' ≃+* S).toRingHom⟩
  have : IsScalarTower R' P' S' :=
    ⟨fun r q s => ULift.ext _ _ (smul_assoc r.down q.down s.down)⟩
  have : IsScalarTower S' S M := inferInstance
  have : IsScalarTower S' S N := inferInstance
  have : IsLocalRing R' := (ULift.ringEquiv : R' ≃+* R).symm.isLocalRing
  have : IsLocalRing S' := (ULift.ringEquiv : S' ≃+* S).symm.isLocalRing
  have : IsLocalHom (algebraMap R' S') := by
    change IsLocalHom ((algebraMap R S).ulift)
    dsimp only [RingHom.ulift]
    infer_instance
  have : Algebra.FinitePresentation R' P' := by
    apply RingHom.finitePresentation_algebraMap.mp
    exact (RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : P' ≃+* P).symm.toRingHom)
      ULift.ringEquiv.symm.bijective).comp
      ((RingHom.finitePresentation_algebraMap.mpr
        (inferInstance : Algebra.FinitePresentation R P)).comp
        (RingHom.FinitePresentation.of_bijective
          (f := (ULift.ringEquiv : R' ≃+* R).toRingHom) ULift.ringEquiv.bijective))
  let W' : Submonoid P' := W.map (ULift.ringEquiv : P' ≃+* P).symm
  have : IsLocalization W' S' := by
    have h := IsLocalization.isLocalization_of_base_ringEquiv W S
      (ULift.ringEquiv : P' ≃+* P).symm
    have h' : IsLocalization W' S := by
      convert h using 1
      apply Algebra.algebra_ext
      intro r
      rfl
    exact IsLocalization.isLocalization_of_algEquiv W'
      (ULift.algEquiv (R := P') (A := S)).symm
  have : Module.FinitePresentation S' S := by
    let e : S' ≃ₗ[S'] S :=
      { ULift.ringEquiv.toAddEquiv with map_smul' := fun _ _ => rfl }
    exact Module.FinitePresentation.of_equiv e
  have : Module.FinitePresentation S' M := Module.FinitePresentation.trans S' M S
  have : Module.FinitePresentation S' N := Module.FinitePresentation.trans S' N S
  have : Module.FinitePresentation S' M' :=
    Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm
  have : Module.FinitePresentation S' N' :=
    Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm
  have : Module.Flat R' N' := Module.Flat.ulift_left_iff.mpr inferInstance
  let u' : M' →ₗ[S'] N' :=
    (ULift.moduleEquiv (R := S')).symm.toLinearMap.comp
      ((u.restrictScalars S').comp (ULift.moduleEquiv (R := S')).toLinearMap)
  let er : R' ≃+* R := ULift.ringEquiv
  have : RingHomInvPair er.toRingHom er.symm.toRingHom := ⟨er.symm_comp, er.comp_symm⟩
  have : RingHomInvPair er.symm.toRingHom er.toRingHom := ⟨er.comp_symm, er.symm_comp⟩
  let ek : IsLocalRing.ResidueField R' ≃ₛₗ[er.toRingHom]
      IsLocalRing.ResidueField R := {
    (IsLocalRing.ResidueField.mapEquiv er).toAddEquiv with
    map_smul' := by
      intro r c
      change IsLocalRing.ResidueField.map er.toRingHom
        ((IsLocalRing.residue R' r) * c) =
        (IsLocalRing.residue R (er r)) * IsLocalRing.ResidueField.map er.toRingHom c
      rw [map_mul, IsLocalRing.ResidueField.map_residue]
      rfl }
  let em : M' ≃ₛₗ[er.toRingHom] M :=
    { AddEquiv.ulift with map_smul' := fun _ _ => rfl }
  let en : N' ≃ₛₗ[er.toRingHom] N :=
    { AddEquiv.ulift with map_smul' := fun _ _ => rfl }
  let eM := _root_.TensorProduct.congr ek em
  let eN := _root_.TensorProduct.congr ek en
  have hf := residue_tensor_injective (u.restrictScalars R) h_fibre
  have hf' : Function.Injective
      ((u'.restrictScalars R').lTensor (IsLocalRing.ResidueField R')) := by
    have comm : eN.toLinearMap.comp
        ((u'.restrictScalars R').lTensor (IsLocalRing.ResidueField R')) =
        ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R)).comp
          eM.toLinearMap := by
      apply _root_.TensorProduct.ext'
      intro c x
      rfl
    intro x y h
    apply eM.injective
    apply hf
    have hcomm := LinearMap.congr_fun comm
    exact (hcomm x).symm.trans ((congrArg eN h).trans (hcomm y))
  obtain ⟨hi, hflat⟩ := local_criterion_same_universe W' u' hf'
  refine ⟨?_, ?_⟩
  · intro x y h
    exact congrArg ULift.down (hi (show u' (ULift.up x) = u' (ULift.up y) from
      congrArg ULift.up h))
  · have : Module.Flat R (N' ⧸ LinearMap.range (u'.restrictScalars R')) :=
      Module.Flat.ulift_left_iff.mp hflat
    let e : N' ≃ₗ[R] N := ULift.moduleEquiv
    let Q := (LinearMap.range (u'.restrictScalars R')).restrictScalars R
    have he : Q.map e.toLinearMap =
        LinearMap.range (u.restrictScalars R) := by
      ext y
      constructor
      · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
        exact ⟨a.down, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨u' (ULift.up a), ⟨ULift.up a, rfl⟩, rfl⟩
    have : Module.Flat R (N' ⧸ Q) := Module.Flat.of_linearEquiv
      (Submodule.Quotient.restrictScalarsEquiv R
        (LinearMap.range (u'.restrictScalars R')))
    exact Module.Flat.of_linearEquiv
      (Submodule.Quotient.equiv Q _ e he).symm

end Algebra
