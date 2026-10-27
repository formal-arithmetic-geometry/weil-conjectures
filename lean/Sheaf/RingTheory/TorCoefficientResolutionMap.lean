/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.RingTheory.TorResolutionCoefficientActions
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The coefficient map on Tor in free-resolution coordinates

Source: Stacks Project, Algebra, Tags 00LY/00LZ and 00M7(1), the map-identification
part of Tag 00M8 adapted to a fixed base ring.
(blueprint: lem-trf-tor-coefficient-resolution-map).

The homology module below transports the existing coefficient action through the
canonical resolution isomorphism. Its multiplication formula identifies it with
the action on cycles. Tensor factors are written `B ⊗[A] T`, using tensor symmetry
with the node's `T ⊗[A] B`. The unique pair of maps is characterized on pure tensors;
no arbitrary choice of a comparison map or flatness assumption occurs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators

namespace ModuleCat

/-- The unaugmented tensor complex of the supplied resolution.
Source: Stacks Project, Algebra, Tag 00LY.
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
abbrev torResolutionCoefficientComplex (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ProjectiveResolution M) :=
  ((tensorRight (ModuleCat.of R S)).mapHomologicalComplex (.down ℕ)).obj P.complex

/-- Tensoring the coefficient homomorphism gives the specified chain map.
Source: Stacks Project, Algebra, Tags 00LY and 00M7.
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
def torResolutionCoefficientChain (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M) :
    torResolutionCoefficientComplex R A M P ⟶ torResolutionCoefficientComplex R B M P :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat.{u} R)).map
      (ofHom ((IsScalarTower.toAlgHom R A B).toLinearMap))) (.down ℕ)).app P.complex

/-- The underlying additive canonical resolution-computation isomorphism.
Source: Stacks Project, Algebra, Tags 00LY/00LZ.
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
noncomputable def torResolutionCoefficientAddEquiv (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (n : ℕ) :
    torCoefficientModule R S M S n ≃+
      (torResolutionCoefficientComplex R S M P).homology n :=
  (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R S)) n).toLinearEquiv.toAddEquiv

/-- The coefficient module structure on the existing homology group, transported
through the canonical resolution-computation isomorphism. The following theorem
identifies its action with multiplication in the coefficient factor.
Source: Stacks Project, Algebra, Tags 00LY and 00M7(1).
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
noncomputable def torResolutionHomologyModule (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (n : ℕ) :
    ModuleCat.{u} S := by
  letI := (torResolutionCoefficientAddEquiv R S M P n).symm.module S
  exact ModuleCat.of S ((torResolutionCoefficientComplex R S M P).homology n)

/-- The canonical resolution isomorphism, with its transported coefficient linearity.
Source: Stacks Project, Algebra, Tags 00LY/00LZ and 00M7(1).
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
noncomputable def torResolutionCoefficientIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (n : ℕ) :
    torCoefficientModule R S M S n ≃ₗ[S] torResolutionHomologyModule R S M P n :=
  ((torResolutionCoefficientAddEquiv R S M P n).symm.linearEquiv S).symm

/-- The transported homology action is exactly multiplication in the coefficient
factor of the tensor complex, on all homology classes.
Source: Stacks Project, Algebra, Tag 00M7(1).
Proof: write a homology class as the image of its unique inverse under the canonical
resolution isomorphism. Apply lem-trf-tor-resolution-coefficient-actions to that inverse
and the scalar. The inverse identities identify its two sides with this formula.
Thus this construction gives the multiplication action, including on cycle sums.
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
theorem torResolutionHomologyModule_smul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    [∀ j : ℕ, Module.Free R (P.complex.X j)] (n : ℕ)
    (s : S) (x : torResolutionHomologyModule R S M P n) :
    s • x = (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R s)))
        (.down ℕ)).app P.complex) n).hom x := by
  have h := tor_resolution_coefficient_smul R S M P n s
    ((torResolutionCoefficientIso R S M P n).symm x)
  change torResolutionCoefficientIso R S M P n
      (s • (torResolutionCoefficientIso R S M P n).symm x) =
    (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R s)))
        (.down ℕ)).app P.complex) n).hom
      (torResolutionCoefficientIso R S M P n
        ((torResolutionCoefficientIso R S M P n).symm x)) at h
  simpa only [map_smul, LinearEquiv.apply_symm_apply] using h

/-- The canonical coefficient comparison square, including its cycle formula.
The unique pair consists of `c_n` and `alpha_n`, with the tensor factors exchanged.
The first two clauses give the pure-tensor formula and A-linearity of the chain map.
The formulas in the unique-existence clause specify the two B-linear extensions,
then their commuting square, and finally both values on every finite cycle sum.

Source: Stacks Project, Algebra, Tags 00LY/00LZ, 00M7(1) and the map-identification
part of 00M8, adapted to the fixed base R.
Proof:
1. Tensor universality defines phi; on generators its formula is p tensor g(a).
Multiplication by a before phi equals multiplication by g(a) afterwards. Its
components commute with differentials and hence preserve cycles and boundaries.
2. Free terms are projective (lem-weil-pbc-free-module-projective). Apply clause (2)
of lem-weil-pbc-tor-map-via-resolution-lift, ProjectiveResolution.leftDerived_app_eq,
to g, on this supplied resolution. It gives iota_B Tor(M,g) = H(phi) iota_A.
3. By lem-trf-tor-resolution-coefficient-actions, iota is coefficient-linear and
the A-action on coefficient-B Tor is restriction of its B-action. Both pairings
(t,b) to b Tor(M,g)(t) and (x,b) to b H(phi)(x) are therefore A-balanced.
Tensor universality gives their unique B-linear extensions c and alpha.
4. Coefficient linearity and step 2 identify the two composites on every pure tensor,
hence everywhere. For a cycle sum, phi applies g to each coefficient and multiplication
by b gives the displayed sum. Chain compatibility ensures it is a cycle. Its class
is independent of boundaries. No exactness after tensoring or invertibility is used.
(blueprint: lem-trf-tor-coefficient-resolution-map). -/
theorem tor_coefficient_resolution_map (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) [∀ j : ℕ, Module.Free R (P.complex.X j)] (n : ℕ) :
    (∀ (j : ℕ) (p : P.complex.X j) (a : A),
      ((torResolutionCoefficientChain R A B M P).f j).hom (p ⊗ₜ[R] a) =
        p ⊗ₜ[R] algebraMap A B a) ∧
    (∀ (j : ℕ) (a : A) (x : (torResolutionCoefficientComplex R A M P).X j),
      ((torResolutionCoefficientChain R A B M P).f j).hom
          (TensorProduct.map (LinearMap.id : P.complex.X j →ₗ[R] P.complex.X j)
            (LinearMap.mulLeft R a) x) =
        TensorProduct.map (LinearMap.id : P.complex.X j →ₗ[R] P.complex.X j)
          (LinearMap.mulLeft R (algebraMap A B a))
          (((torResolutionCoefficientChain R A B M P).f j).hom x)) ∧
    ∃! maps :
        (B ⊗[A] torCoefficientModule R A M A n →ₗ[B] torCoefficientModule R B M B n) ×
        (B ⊗[A] torResolutionHomologyModule R A M P n →ₗ[B]
          torResolutionHomologyModule R B M P n),
      (∀ (b : B) (t : torCoefficientModule R A M A n),
        maps.1 (b ⊗ₜ[A] t) = b • @id (torCoefficientModule R B M B n)
          (torCoefficientLinearMap R A M A B n (Algebra.ofId A B) t)) ∧
      (∀ (b : B) (x : torResolutionHomologyModule R A M P n),
        maps.2 (b ⊗ₜ[A] x) = b • @id (torResolutionHomologyModule R B M P n)
          ((HomologicalComplex.homologyMap
            (torResolutionCoefficientChain R A B M P) n).hom x)) ∧
      (torResolutionCoefficientIso R B M P n).toLinearMap.comp maps.1 =
        maps.2.comp (LinearMap.baseChange B
          (torResolutionCoefficientIso R A M P n).toLinearMap) ∧
      (∀ (k : ℕ) (p : Fin k → P.complex.X n) (a : Fin k → A)
          (z : (torResolutionCoefficientComplex R A M P).cycles n),
        ((torResolutionCoefficientComplex R A M P).iCycles n).hom z =
            ∑ i, p i ⊗ₜ[R] a i →
        ∀ b : B, ∃ w : (torResolutionCoefficientComplex R B M P).cycles n,
          ((torResolutionCoefficientComplex R B M P).iCycles n).hom w =
              ∑ i, p i ⊗ₜ[R] (algebraMap A B (a i) * b) ∧
          torResolutionCoefficientIso R B M P n
              (maps.1 (b ⊗ₜ[A] (torResolutionCoefficientIso R A M P n).symm
                (((torResolutionCoefficientComplex R A M P).homologyπ n).hom z))) =
            ((torResolutionCoefficientComplex R B M P).homologyπ n).hom w ∧
          maps.2 (b ⊗ₜ[A] @id (torResolutionHomologyModule R A M P n)
              (((torResolutionCoefficientComplex R A M P).homologyπ n).hom z)) =
            ((torResolutionCoefficientComplex R B M P).homologyπ n).hom w) := by
  classical
  let φ := torResolutionCoefficientChain R A B M P
  let iA := torResolutionCoefficientIso R A M P n
  let iB := torResolutionCoefficientIso R B M P n
  have hφ (j : ℕ) (p : P.complex.X j) (a : A) :
      (φ.f j).hom (p ⊗ₜ[R] a) = p ⊗ₜ[R] algebraMap A B a := by
    rfl
  refine ⟨hφ, ?_, ?_⟩
  · intro j a x
    change (φ.f j).hom
        (TensorProduct.map (LinearMap.id : P.complex.X j →ₗ[R] P.complex.X j)
          (LinearMap.mulLeft R a) x) =
      TensorProduct.map (LinearMap.id : P.complex.X j →ₗ[R] P.complex.X j)
        (LinearMap.mulLeft R (algebraMap A B a)) ((φ.f j).hom x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul p a' =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
        hφ, map_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  · have hnat (t : torCoefficientModule R A M A n) :
        iB (torCoefficientLinearMap R A M A B n (Algebra.ofId A B) t) =
          (HomologicalComplex.homologyMap φ n).hom (iA t) := by
      have h := P.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} R)).map
          (ofHom ((IsScalarTower.toAlgHom R A B).toLinearMap))) n
      have hc :
          (((Tor' (ModuleCat.{u} R) n).obj M).map
            (ofHom ((IsScalarTower.toAlgHom R A B).toLinearMap))) ≫
            (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R B)) n).hom =
          (P.isoLeftDerivedObj (tensorRight (ModuleCat.of R A)) n).hom ≫
            HomologicalComplex.homologyMap φ n := by
        rw [Tor'_obj_map, h]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl
      exact ConcreteCategory.congr_hom hc t
    let : Module A (torCoefficientModule R B M B n) :=
      (torCoefficientModule R A M B n).isModule
    let : IsScalarTower A B (torCoefficientModule R B M B n) :=
      ⟨fun a b t ↦ by
        simpa only [Algebra.smul_def, id_eq] using
          (tor_resolution_coefficient_actions R A B M n).2 a b t⟩
    let f : torCoefficientModule R A M A n →ₗ[A] torCoefficientModule R B M B n :=
      torCoefficientLinearMap R A M A B n (Algebra.ofId A B)
    let c := f.liftBaseChange B
    let α := iB.toLinearMap.comp
      (c.comp (LinearMap.baseChange B iA.symm.toLinearMap))
    have hc (b : B) (t : torCoefficientModule R A M A n) :
        c (b ⊗ₜ[A] t) = b • f t := by
      exact LinearMap.liftBaseChange_tmul B f b t
    have hα (b : B) (x : torResolutionHomologyModule R A M P n) :
        α (b ⊗ₜ[A] x) = b • @id (torResolutionHomologyModule R B M P n)
          ((HomologicalComplex.homologyMap φ n).hom x) := by
      change iB (c (LinearMap.baseChange B iA.symm.toLinearMap (b ⊗ₜ[A] x))) = _
      rw [LinearMap.baseChange_tmul, hc, map_smul]
      have h := hnat (iA.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      exact congrArg (b • ·) h
    have hsquare : iB.toLinearMap.comp c =
        α.comp (LinearMap.baseChange B iA.toLinearMap) := by
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b t =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, hc, hα, map_smul, id_eq]
        exact congrArg (b • ·) (hnat t)
      | add y z hy hz => simp only [map_add, hy, hz]
    refine ⟨(c, α), ⟨hc, hα, hsquare, ?_⟩, ?_⟩
    · intro k p a z hz b
      let μ := (NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} R)).map (ofHom (LinearMap.mulLeft R b)))
        (.down ℕ)).app P.complex
      let w := (HomologicalComplex.cyclesMap (φ ≫ μ) n).hom z
      have hμ (p' : P.complex.X n) (b' : B) :
          (μ.f n).hom (p' ⊗ₜ[R] b') = p' ⊗ₜ[R] (b * b') := by
        rfl
      have hw : ((torResolutionCoefficientComplex R B M P).iCycles n).hom w =
          ∑ i, p i ⊗ₜ[R] (algebraMap A B (a i) * b) := by
        have hi := ConcreteCategory.congr_hom
          (HomologicalComplex.cyclesMap_i (φ ≫ μ) n) z
        change ((torResolutionCoefficientComplex R B M P).iCycles n).hom w =
          (μ.f n).hom ((φ.f n).hom
            (((torResolutionCoefficientComplex R A M P).iCycles n).hom z)) at hi
        rw [hi, hz, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hφ, hμ, mul_comm]
      have hwH : b • @id (torResolutionHomologyModule R B M P n)
          ((HomologicalComplex.homologyMap φ n).hom
            (((torResolutionCoefficientComplex R A M P).homologyπ n).hom z)) =
          ((torResolutionCoefficientComplex R B M P).homologyπ n).hom w := by
        rw [torResolutionHomologyModule_smul R B M P n]
        have hπ := ConcreteCategory.congr_hom
          (HomologicalComplex.homologyπ_naturality (φ ≫ μ) n) z
        simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
          LinearMap.comp_apply, id_eq, μ, w] using hπ
      refine ⟨w, hw, ?_, ?_⟩
      · change iB (c (b ⊗ₜ[A] iA.symm _)) = _
        rw [hc, map_smul]
        have h := hnat (iA.symm
          (((torResolutionCoefficientComplex R A M P).homologyπ n).hom z))
        rw [LinearEquiv.apply_symm_apply] at h
        exact (congrArg (b • ·) h).trans hwH
      · exact (hα b _).trans hwH
    · rintro ⟨c', α'⟩ ⟨hc', hα', _, _⟩
      apply Prod.ext
      · apply LinearMap.ext
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b t => exact (hc' b t).trans (hc b t).symm
        | add y z hy hz => simp only [map_add, hy, hz]
      · apply LinearMap.ext
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => exact (hα' b x).trans (hα b x).symm
        | add y z hy hz => simp only [map_add, hy, hz]

end ModuleCat
