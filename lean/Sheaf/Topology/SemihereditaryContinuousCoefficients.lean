/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.TAdmissibleCoefficientModels
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation

import Sheaf.RingTheory.SemihereditaryFiniteFreeSubmodule
import Sheaf.RingTheory.SemihereditaryTorsionlessFlat
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Admissibility of semihereditary continuous coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemmas 6.7(1)
and 6.10, Definition 6.1 (blueprint: lem-sfb-semihereditary-topological-coefficients-admissible).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace Profinite

-- The existing finite-free construction in ScalarPerfectCohomologyAndPidModels
-- applies equally to finite projective terms.
private theorem twoTermResolution {R : Type u} [CommRing R]
    (K F : ModuleCat.{u} R) [Module.Projective R K] [Module.Finite R K]
    [Module.Projective R F] [Module.Finite R F] (u : K ⟶ F) (M : ModuleCat.{u} R)
    (q : F ⟶ M)
    (hw : u ≫ q = 0)
    (hex : (ShortComplex.mk u q hw).Exact)
    [Mono u] [Epi q] :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (_hge : P.IsStrictlyGE (-1)) (_hle : P.IsStrictlyLE 0),
      (∀ i : ℤ, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ∃ (em : P.X (-1) ≅ K)
        (e0 : P.X 0 ≅ F),
        P.d (-1) 0 = em.hom ≫ u ≫ e0.inv ∧
        ∃ ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M,
          QuasiIso ε ∧
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = e0.hom ≫ q ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) := by
  classical
  let f : K ⟶ F := u
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let P : CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.double f hrel
  let em := HomologicalComplex.doubleXIso₀ f hrel
  let e0 := HomologicalComplex.doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (P.X i) :=
    HomologicalComplex.isZero_double_X f hrel i hm h0
  have hge : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hterms (i : ℤ) : Module.Projective R (P.X i) ∧ Module.Finite R (P.X i) := by
    by_cases hm : i = -1
    · subst i
      exact ⟨Module.Projective.of_equiv em.toLinearEquiv.symm,
        Module.Finite.equiv em.toLinearEquiv.symm⟩
    · by_cases h0 : i = 0
      · subst i
        exact ⟨Module.Projective.of_equiv e0.toLinearEquiv.symm,
          Module.Finite.equiv e0.toLinearEquiv.symm⟩
      · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero (hz i hm h0)
        exact ⟨inferInstance, inferInstance⟩
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
  let ε : P ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ L.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, show f ≫ q = 0 from hw, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by
    simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have hmono : Mono (P.d (-1) 0) := by
    dsimp [P]
    rw [HomologicalComplex.double_d f hrel (by omega)]
    infer_instance
  have hε : QuasiIso ε := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
        ((hL (-1) (by omega)).eq_of_src _ _)
        ((hL 1 (by omega)).eq_of_tgt _ _)).2
      have heq : P.d (-1) 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm]
        simp [hεi (-1) (by omega)]
      let S := ShortComplex.mk (P.d (-1) 0) (ε.f 0) heq
      let T := ShortComplex.mk f q hw
      let iso : S ≅ T := ShortComplex.isoMk em e0 e
        (by dsimp [S, T, P, em, e0]; rw [HomologicalComplex.double_d f hrel (by omega)]; simp)
        hε0.symm
      have hs : S.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
      have : Epi (ε.f 0) := by
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)
  exact ⟨P, hge, hle, hterms, em, e0,
    HomologicalComplex.double_d f hrel (by omega), ε, hε, hε0, hεi⟩

private theorem perfect_of_semihereditary {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → Module.Projective R I)
    (N : ModuleCat.{u} R) [Module.FinitePresentation R N] :
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R N
  have : Module.Finite R K := Module.Finite.of_fg hK
  have : Module.Projective R K :=
    Submodule.projective_of_finite_of_projective_ideals R hR n K
  let f : ModuleCat.of R K ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom K.subtype
  let q : ModuleCat.of R (Fin n → R) ⟶ N := ModuleCat.ofHom (e.symm.toLinearMap.comp K.mkQ)
  have hw : f ≫ q = 0 := by ext x; simp [f, q]
  have hq : Function.Surjective q := e.symm.surjective.comp K.mkQ_surjective
  have hex : (ShortComplex.mk f q hw).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp [f, q, LinearMap.ker_comp]
  have : Mono f := (ModuleCat.mono_iff_injective f).2 K.injective_subtype
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 hq
  obtain ⟨P, hlo, hhi, ht, _, _, _, ε, hε, _, _⟩ :=
    twoTermResolution (ModuleCat.of R K) (ModuleCat.of R (Fin n → R)) f N q hw hex
  have : QuasiIso ε := hε
  exact ⟨P, -1, 0, hlo, hhi, ht, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩

private theorem projective_ideals_of_equiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : S ≃+* R)
    (hR : ∀ I : Ideal R, I.FG → Module.Projective R I)
    (I : Ideal S) (hI : I.FG) : Module.Projective S I := by
  have : Module.Projective R (I.map e) := hR _ (Ideal.FG.map hI e.toRingHom)
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (↑e : S →+* R) (↑e.symm : R →+* S)
  let eI : I ≃ₛₗ[(↑e : S →+* R)] I.map e :=
    { toFun := fun x ↦ ⟨e x, Ideal.mem_map_of_mem e x.property⟩
      invFun := fun y ↦ ⟨e.symm y, by
        obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_of_equiv e (y : R)).mp y.property
        rw [← hxy, e.symm_apply_apply]
        exact hx⟩
      left_inv := fun _ ↦ Subtype.ext (e.symm_apply_apply _)
      right_inv := fun _ ↦ Subtype.ext (e.apply_symm_apply _)
      map_add' := fun _ _ ↦ Subtype.ext (e.map_add _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (e.map_mul _ _) }
  exact Module.Projective.of_equiv eI.symm

-- The counit-transported multiplication recovers the original section multiplication.
private theorem continuous_section_ring_equiv
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (S : Profinite.{u}) :
    let := isCommMonObj_continuousMapRingObjOfUniverse R
    ∃ e : (AlgebraicGeometry.ProEtale.CondensedRing.scalarRingSheaf
      { X := continuousMapRingObjOfUniverse.{u, u} R
        mon := continuousMapRingObjOfUniverseMonObj R }).obj.obj (op S) ≃+*
      ULift.{u + 1} C(S, R), ∀ x, e x = x := by
  let := isCommMonObj_continuousMapRingObjOfUniverse R
  let A := continuousMapRingObjOfUniverse.{u, u} R
  let J := coherentTopology Profinite.{u}
  let : MonObj A.obj :=
    Functor.monObjCompForget₂ (continuousMapRingPresheafOfUniverse.{u, u} R)
  let e : (AlgebraicGeometry.ProEtale.CondensedRing.scalarRingSheaf
      { X := A, mon := continuousMapRingObjOfUniverseMonObj R }).obj.obj (op S) ≃+*
      ULift.{u + 1} C(S, R) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := by
        intro x y
        have h := Sheaf.μ_comp_map_mul (J := J) A
        have h' := congrArg (fun f ↦ (f.app (op S)).hom (x ⊗ₜ[ℤ] y)) h
        exact h' }
  exact ⟨e, fun _ ↦ rfl⟩

/-- A T1 topological commutative ring with projective finitely generated ideals gives
regular coherent scalar coefficients and a t-admissible continuous-function condensed ring.
The perfect degree-zero condition is precisely a finite resolution by finitely generated
projectives. The profinite flatness clause uses all continuous functions, with no image
restriction, and an independent universe for the profinite test sets. Evaluation at the
unique point is the specified scalar identification. No completeness, local compactness,
Noetherian or domain hypothesis is imposed.

Source: Hemo--Richarz--Scholbach, Lemmas 6.7(1), 6.10 and Definition 6.1
(blueprint: lem-sfb-semihereditary-topological-coefficients-admissible).

Proof: a finitely generated ideal is projective by hypothesis and hence finitely presented
by `Module.finitePresentation_of_projective` (lem-weil-pbc-finite-projective-finitely-presented).
For a finitely presented module, choose a presentation by two finite free modules. Its
relation submodule is finitely generated and projective by
lem-sfb-semihereditary-finite-free-submodule. The resulting two-term finite projective
resolution represents the module in degree zero, giving the perfectness clause.
For each profinite P, evaluation embeds C(P,R) R-linearly into the unrestricted product
of copies of R indexed by P. By lem-sfb-semihereditary-torsionless-flat this module is flat,
which means the constant-function ring map is flat. Evaluation at the point is a ring
isomorphism, with inverse the lifted constant function. Under this scalar identification,
the first two clauses and flatness on extremally disconnected profinite sets are exactly
the three clauses of def-zl-t-admissible-coefficient-models. -/
theorem semihereditary_continuous_coefficients_admissible
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]
    (hR : ∀ I : Ideal R, I.FG → Module.Projective R I) :
    (∀ I : Ideal R, I.FG → Module.FinitePresentation R I) ∧
    (∀ N : ModuleCat.{u} R, Module.FinitePresentation R N →
      DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N)) ∧
    (∀ P : Profinite.{v}, (algebraMap R C(P, R)).Flat) ∧
    (∃ e : (continuousMapRingSheafOfUniverse.{u, u} R).obj.obj
        (op (Profinite.of PUnit.{u + 1})) ≃+* R,
      ∀ f, e f = f.down PUnit.unit) ∧
    @AlgebraicGeometry.ProEtale.CondensedRing.IsTAdmissible.{u}
      { X := continuousMapRingObjOfUniverse.{u, u} R
        mon := continuousMapRingObjOfUniverseMonObj R }
      (isCommMonObj_continuousMapRingObjOfUniverse R) := by
  have hfp (I : Ideal R) (hI : I.FG) : Module.FinitePresentation R I := by
    have : Module.Projective R I := hR I hI
    have : Module.Finite R I := Module.Finite.of_fg hI
    exact Module.finitePresentation_of_projective R I
  have hperfect (N : ModuleCat.{u} R) (hN : Module.FinitePresentation R N) :
      DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N) := by
    have := hN
    exact perfect_of_semihereditary hR N
  have hflat (P : Profinite.{v}) : (algebraMap R C(P, R)).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    let e : C(P, R) →ₗ[R] (P → R) :=
      { toFun := fun f ↦ f
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.Flat.of_injective_pi_of_projective_fg_ideals hR e
      (fun _ _ h ↦ ContinuousMap.ext (congrFun h))
  refine ⟨hfp, hperfect, hflat, ?_, ?_⟩
  · let e : C(Profinite.of PUnit.{u + 1}, R) ≃+* R :=
      { toFun := fun f ↦ f PUnit.unit
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext (fun x ↦ by cases x; rfl)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
    exact ⟨ULift.ringEquiv.trans e, fun _ ↦ rfl⟩
  · let := isCommMonObj_continuousMapRingObjOfUniverse R
    let Λ : Profinite.CondensedRing.{u} :=
      { X := continuousMapRingObjOfUniverse.{u, u} R
        mon := continuousMapRingObjOfUniverseMonObj R }
    let T := ⊤_ Profinite.{u}
    let i : T ≅ Profinite.of PUnit.{u + 1} :=
      terminalIsTerminal.uniqueUpToIso isTerminalPUnit
    let : Unique T :=
      { default := i.inv.hom PUnit.unit
        uniq := fun _ ↦ (ConcreteCategory.bijective_of_isIso i.hom).1 (Subsingleton.elim _ _) }
    choose k hk using continuous_section_ring_equiv R
    let ev : C(T, R) ≃+* R :=
      { toFun := fun f ↦ f default
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext (fun x ↦ congrArg f (Subsingleton.elim _ _))
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
    let e : AlgebraicGeometry.ProEtale.CondensedRing.scalarRing Λ ≃+* R :=
      (k T).trans (ULift.ringEquiv.trans ev)
    have hS := projective_ideals_of_equiv e hR
    refine ⟨?_, ?_, ?_⟩
    · intro I hI
      have := hS I hI
      have : Module.Finite _ I := Module.Finite.of_fg hI
      exact Module.finitePresentation_of_projective _ I
    · intro N hN
      have := hN
      exact perfect_of_semihereditary hS N
    · intro P _
      have hm : AlgebraicGeometry.ProEtale.CondensedRing.scalarSectionMap Λ P =
          (k P).symm.toRingHom.comp (ULift.ringEquiv.symm.toRingHom.comp
            ((algebraMap R C(P, R)).comp e.toRingHom)) := by
        apply RingHom.ext
        intro x
        apply (k P).injective
        change _ = (k P) ((k P).symm (ULift.up (ContinuousMap.const P (e x))))
        rw [RingEquiv.apply_symm_apply]
        rw [hk P]
        apply ULift.ext
        apply ContinuousMap.ext
        intro p
        change x.down ((terminal.from P).hom p) = (k T x).down default
        rw [hk T]
        exact congrArg x.down (Subsingleton.elim _ _)
      rw [hm]
      apply RingHom.Flat.comp
      · apply RingHom.Flat.comp
        · apply RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective)
          rw [RingHom.flat_algebraMap_iff]
          let f : C(P, R) →ₗ[R] (P → R) :=
            { toFun := fun g ↦ g
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          exact Module.Flat.of_injective_pi_of_projective_fg_ideals hR f
            (fun _ _ h ↦ ContinuousMap.ext (congrFun h))
        · exact RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective
      · exact RingHom.Flat.of_bijective (k P).symm.bijective

end Profinite
