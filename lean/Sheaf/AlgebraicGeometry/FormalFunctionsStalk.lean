/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary
import Sheaf.AlgebraicGeometry.TheoremFormalFunctions
import Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # The theorem on formal functions at a point of the base

Source: Stacks Project, Cohomology of Schemes, Lemma 02OD, with the canonical-map
identification in the proof of Tag 0G7X
(blueprint: lem-weil-pbc-formal-functions-stalk).

The index n represents the positive level n+1. The maps theta_n are the canonical stalk
maps, tied by `IsFormalFunctionsTheta`; the isomorphism is specified on every limit
projection, so it is the canonical one.
-/

@[expose] public section

universe uS

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Comparing scalar actions on restricted cohomology modules needs extra elaboration.
private theorem completion_map_linear {X Y : Scheme.{uS}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ)
    (θ : ∀ n : ℕ, formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n)
    (φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
      (formalFunctionsStalk f y F p) →+ ↥(limit (formalFibreCohomologySystem f y F p)))
    (hφ : ∀ (n : ℕ) (x : AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (formalFunctionsStalk f y F p)) (z : formalFunctionsStalk f y F p),
      AdicCompletion.eval (maximalIdeal (Y.presheaf.stalk y))
        (formalFunctionsStalk f y F p) (n + 1) x = Submodule.Quotient.mk z →
      (limit.π (formalFibreCohomologySystem f y F p) (op n)) (φ x) = θ n z)
    (r : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    (x : AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
      (formalFunctionsStalk f y F p)) : φ (r • x) = r • φ x := by
  let I := maximalIdeal (Y.presheaf.stalk y)
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I (Y.presheaf.stalk y) r
  obtain ⟨z, rfl⟩ := AdicCompletion.mk_surjective I (formalFunctionsStalk f y F p) x
  apply Concrete.limit_ext (formalFibreCohomologySystem f y F p)
  intro j
  obtain ⟨n⟩ := j
  have hx : AdicCompletion.eval I (formalFunctionsStalk f y F p) (n + 1)
      (AdicCompletion.mk I (Y.presheaf.stalk y) a •
        AdicCompletion.mk I (formalFunctionsStalk f y F p) z) =
      Submodule.Quotient.mk (a.val (n + 1) • z.val (n + 1)) := by
    change (AdicCompletion.mk I (Y.presheaf.stalk y) a).val (n + 1) •
      (AdicCompletion.mk I (formalFunctionsStalk f y F p) z).val (n + 1) = _
    rw [AdicCompletion.val_smul_eq_evalₐ_smul, AdicCompletion.evalₐ_mk]
    rfl
  rw [hφ n _ _ hx, map_smul]
  change _ = (limit.π (formalFibreCohomologySystem f y F p) (op n)).hom
    (AdicCompletion.mk I (Y.presheaf.stalk y) a • φ _)
  rw [LinearMap.map_smul, hφ n _ (z.val (n + 1)) rfl]
  let t : (RingedSpace.moduleCohomology (formalFibre f y n).toRingedSpace p).obj
      ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) := θ n (z.val (n + 1))
  change (formalFibreScalarMap f y n
      (Ideal.Quotient.mk (formalFibreIdeal Y y n) (a.val (n + 1)))) • t =
    (formalFibreScalarMap f y n
      (AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I (Y.presheaf.stalk y) a))) • t
  rw [AdicCompletion.evalₐ_mk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Transport through limits and restriction of scalars needs extra elaboration.
/-- The canonical maps theta_n : M → H^p(X_n, F_n) are compatible with the transitions,
kill m^(n+1) M, and induce an isomorphism over the completed local ring from the
completion of M to the inverse limit, whose composite with M → M^ is (theta_n)_n.
Source: Stacks, Tag 02OD (blueprint: lem-weil-pbc-formal-functions-stalk).

Proof (the node's nine steps):
1. A=O_(Y,y) is Noetherian. The canonical map c: Spec A → Y is flat and its image is
contained in every neighbourhood of y (spec-local-ring-canonical-morphism).
2. Base change gives a proper map X' → Spec A with coherent pullback F'
(proper-fp-permanence, locnoeth-lft, coherent-ft-locnoeth, module-pullback-quasi-coherent).
3. Flat base change identifies the stalk M with H^p(X',F'). The identification on germs
is pullback on each f⁻¹V (flat-base-change-cohom, flat-base-change-map-sections,
higher-direct-image-presheaf, module-stalk). The local spectrum has no proper open
containing its closed point, which computes the final stalk as global cohomology.
4. Pasting fibre products identifies X_n over Y with the quotient base change over A.
Its ideal on X' is m^n O_X', and its module is the pullback of F'
(quotient-base-change-closed-immersion-ideal, module-pullback).
5. Cohomology-fmap functoriality identifies theta_n with restriction from X' and gives
transition compatibility. Quotient scalar action makes theta_n kill m^n M
(module-cohomology-fmap-functorial, module-cohomology-fmap-basic-properties).
6. The closed immersion unit identifies its pushed-forward module with F'/m^n F'.
The affine cohomology edge is an isomorphism, preserving the quotient restriction maps
(closed-immersion-unit-quotient, affine-morphism-cohomology-edge).
7. These identifications commute with every transition: the two h-maps agree after
the epimorphic quotient map, so their cohomology maps agree (fmap-functoriality).
8. Apply theorem-formal-functions over A and m to the coherent F' and compose with
the inverse-system identifications.
9. Complete the isomorphism from step 3. The component formula follows from steps 5--8.
The completed ring acts through A/m^n on each component, so the comparison is linear
over A-completion. Its composite with M → M-completion has components theta_n. -/
theorem formal_functions_stalk {X Y : Scheme.{uS}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (F : SheafOfModules.{uS} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    ∃ θ : ∀ n : ℕ, formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y F p n,
      (∀ n : ℕ, IsFormalFunctionsTheta f y F p n (θ n)) ∧
      (∀ (n : ℕ) (x : formalFunctionsStalk f y F p),
        formalFibreCohomologyTransition f y F p n (θ (n + 1) x) = θ n x) ∧
      (∀ n : ℕ, (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) • ⊤ :
        Submodule (Y.presheaf.stalk y) (formalFunctionsStalk f y F p)) ≤
          LinearMap.ker (θ n)) ∧
      ∃ e : ModuleCat.of
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
            (formalFunctionsStalk f y F p)) ≅
          limit (formalFibreCohomologySystem f y F p),
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
            (formalFunctionsStalk f y F p)) (z : formalFunctionsStalk f y F p),
          AdicCompletion.eval (maximalIdeal (Y.presheaf.stalk y))
            (formalFunctionsStalk f y F p) (n + 1) x = Submodule.Quotient.mk z →
          (limit.π (formalFibreCohomologySystem f y F p) (op n)) (e.hom x) = θ n z) ∧
        (∀ (n : ℕ) (z : formalFunctionsStalk f y F p),
          (limit.π (formalFibreCohomologySystem f y F p) (op n))
            (e.hom (AdicCompletion.of (maximalIdeal (Y.presheaf.stalk y))
              (formalFunctionsStalk f y F p) z)) = θ n z) := by
  classical
  let A := Y.presheaf.stalk y
  let I := maximalIdeal A
  let X' := pullback (Y.fromSpecStalk y) f
  let f' := pullback.fst (Y.fromSpecStalk y) f
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f'
  let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f'.appTop).hom
  let S := formalFibreCohomologySystem f y F p
  let R := ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))
  obtain ⟨hF', a, b, θ, hθ, hb⟩ := formalFunctions_local_dictionary f F hF y p
  obtain ⟨q, hq, _, e, he⟩ := theorem_formal_functions I f' J rfl F' hF' p
  let c := ((AdicCompletion.congr I a).restrictScalars A).toModuleIso
  let d := HasLimit.isoOfNatIso b
  let g := preservesLimitIso R S
  let v := c ≪≫ e ≪≫ d ≪≫ g.symm
  have hv : ∀ (n : ℕ) (x : AdicCompletion I (formalFunctionsStalk f y F p))
      (z : formalFunctionsStalk f y F p),
      AdicCompletion.eval I (formalFunctionsStalk f y F p) (n + 1) x =
        Submodule.Quotient.mk z → (limit.π S (op n)) (v.hom x) = θ n z := by
    intro n x z hx
    change (limit.π S (op n)) (g.inv (d.hom (e.hom (c.hom x)))) = _
    have hg := congrArg (fun k ↦ k (d.hom (e.hom (c.hom x))))
      (preservesLimitIso_inv_π R S (op n))
    simp only [ConcreteCategory.comp_apply] at hg
    change (limit.π S (op n)) (g.inv (d.hom (e.hom (c.hom x)))) =
      (limit.π (S ⋙ R) (op n)) (d.hom (e.hom (c.hom x))) at hg
    rw [hg]
    have hd := congrArg (fun k ↦ k (e.hom (c.hom x)))
      (HasLimit.isoOfNatIso_hom_π b (op n))
    simp only [ConcreteCategory.comp_apply] at hd
    rw [hd]
    have hh := congrArg (fun k ↦ k (c.hom x)) (he n)
    simp only [ConcreteCategory.comp_apply] at hh
    change (limit.π (formalCompletionSystem J F' ⋙ C) (op n))
      (e.hom (c.hom x)) = q n (AdicCompletion.eval I (C.obj F') (n + 1) (c.hom x)) at hh
    rw [hh]
    have hc : AdicCompletion.eval I (C.obj F') (n + 1) (c.hom x) =
        Submodule.Quotient.mk (a z) := by
      change a.toLinearMap.reduceModIdeal (I ^ (n + 1))
        (AdicCompletion.eval I (formalFunctionsStalk f y F p) (n + 1) x) = _
      rw [hx]
      rfl
    rw [hc]
    have hqn := LinearMap.congr_fun (hq n) (a z)
    change q n (Submodule.Quotient.mk (a z)) =
      (C.map (formalModuleQuotientπ J (n + 1) F')) (a z) at hqn
    rw [hqn]
    exact (hb n z).symm
  have hcomp : ∀ (n : ℕ) (z : formalFunctionsStalk f y F p),
      (limit.π S (op n)) (v.hom (AdicCompletion.of I _ z)) = θ n z := by
    intro n z
    exact hv n _ z rfl
  refine ⟨θ, hθ, ?_, ?_, ?_⟩
  · intro n z
    rw [← hcomp (n + 1) z, ← hcomp n z]
    have hw := congrArg (fun k ↦ k (v.hom (AdicCompletion.of I _ z)))
      (limit.w S (homOfLE (Nat.le_succ n)).op)
    have hm : S.map (homOfLE (Nat.le_succ n)).op =
        formalFibreCohomologyTransition f y F p n :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [hm] at hw
    exact hw
  · intro n z hz
    have hx : AdicCompletion.eval I (formalFunctionsStalk f y F p) (n + 1)
        (AdicCompletion.of I _ z) = Submodule.Quotient.mk 0 := by
      change Submodule.Quotient.mk z = Submodule.Quotient.mk 0
      simpa only [Submodule.Quotient.mk_zero] using
        (Submodule.Quotient.mk_eq_zero _).mpr hz
    have hvz := hv n _ 0 hx
    rw [hcomp, map_zero] at hvz
    exact hvz
  · let w : AdicCompletion I (formalFunctionsStalk f y F p) ≃ₗ[AdicCompletion I A]
        ↥(limit S) :=
      { v.toLinearEquiv.toAddEquiv with
        map_smul' := completion_map_linear f y F p θ v.hom.hom.toAddMonoidHom hv }
    exact ⟨w.toModuleIso, hv, hcomp⟩

/-- In degree zero for O_X, the comparison is the inverse limit of actual global
sections. It sends every germ of a section to the pullbacks of that section.
Source: Stacks, Tags 02OD and 0G7X (blueprint: lem-weil-pbc-formal-functions-stalk).

Proof: apply the preceding nine-step argument in degree zero to O_X. Tensor pullback
of the unit module is the unit module, H^0 is global sections, and R^0 f_* is f_*.
The cohomology-fmap-basic-properties degree-zero formula is the section pullback.
These identifications commute with quotient transitions and preserve the base scalar
actions, so the resulting completed-ring isomorphism has the displayed germ formula. -/
theorem formal_functions_stalk_structureSheaf {X Y : Scheme.{uS}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (y : Y) :
    ∃ e : ModuleCat.of
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))) ≅
        limit (formalFibreSectionsSystem f y),
      ∀ (n : ℕ) (V : Y.Opens) (hy : y ∈ V)
        (hV : (⊤ : (formalFibre f y n).Opens) ≤ (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
        (t : Γ(X, f ⁻¹ᵁ V)),
        (limit.π (formalFibreSectionsSystem f y) (op n))
          (e.hom (AdicCompletion.of (maximalIdeal (Y.presheaf.stalk y))
            ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
            (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
              V y hy t))) = (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hF : RingedSpace.IsCoherent X.toRingedSpace
      (SheafOfModules.unit X.ringCatSheaf) := by
    have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{uS, uS, uS} _
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
      ⟨SheafOfModules.isQuasicoherent_unit.{uS, uS, uS}, inferInstance⟩
  obtain ⟨θ, hθ, _, _, e, _, he⟩ :=
    formal_functions_stalk f (SheafOfModules.unit X.ringCatSheaf) hF y 0
  obtain ⟨a, b, hab⟩ := formalFunctions_degreeZero_dictionary f y
  let c := (AdicCompletion.congr (maximalIdeal (Y.presheaf.stalk y)) a).toModuleIso
  let d := HasLimit.isoOfNatIso b
  refine ⟨c ≪≫ e ≪≫ d, ?_⟩
  intro n V hy hV t
  let z := TopCat.Presheaf.germ
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
    V y hy t
  change (limit.π (formalFibreSectionsSystem f y) (op n))
    (d.hom (e.hom (c.hom (AdicCompletion.of (maximalIdeal (Y.presheaf.stalk y)) _
      z)))) = _
  have hc : c.hom (AdicCompletion.of (maximalIdeal (Y.presheaf.stalk y)) _
      z) =
      AdicCompletion.of (maximalIdeal (Y.presheaf.stalk y)) _
        (a z) := by
    exact AdicCompletion.map_of _ _ _
  rw [hc]
  have hd := congrArg (fun k ↦ k (e.hom (AdicCompletion.of
    (maximalIdeal (Y.presheaf.stalk y)) _ (a z))))
    (HasLimit.isoOfNatIso_hom_π b (op n))
  change (limit.π (formalFibreSectionsSystem f y) (op n)) (d.hom _) = _ at hd
  simp only [ConcreteCategory.comp_apply] at hd
  rw [hd, he]
  exact hab n (θ n) (hθ n) V hy hV t

end AlgebraicGeometry
