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
import Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary
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
  sorry

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
