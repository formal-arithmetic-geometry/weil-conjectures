/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Flat.Basic

/-! # Flat extension of an invertible base-tensor comparison

Source: Stacks Project, Tag 08IB, local affine reduction, and Tag 00HD.
(blueprint: lem-pc-flat-localized-base-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB uD v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModuleCat.BaseDerivedTensorCohomologyModel

variable {R : Type uR} {A : Type uA} {B : Type uB} {D : Type uD}
  [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} B)]
  {Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ}

/-- Source: Stacks Project, Tag 08IB, local affine reduction; Tag 00HD,
flat tensor preserves exactness.
(blueprint: lem-pc-flat-localized-base-comparison).

Proof: Flatness of D makes extension E → D exact, where E = A ⊗[R] B.
It therefore preserves the kernel/image sequences of the ordinary tensor complex
C = E ⊗[A] Q, giving D ⊗[E] H^i(C) ≅ H^i(D ⊗[E] C).
Associativity identifies D ⊗[E] C with D ⊗[A] Q degreewise. Its unit map
sends e tensor q to the image of e tensor q, so ordinaryToLocalized_tmul
identifies it with the model's ordinaryToLocalized. Transpose localized_eq
under extension/restriction adjunction. It identifies localizedComparison with
the extension of comparison followed by the exact homology comparison and the
associativity isomorphism on homology. Extension preserves the assumed
isomorphisms comparison, and both subsequent maps are isomorphisms, so the
composite is invertible. There is no boundedness, projectivity or Tor hypothesis.
This also works when D is the zero ring and when Q is unbounded or zero. -/
theorem localizedComparison_isIso_of_flat
    (M : BaseDerivedTensorCohomologyModel R A B Q D)
    (hflat : Module.Flat (A ⊗[R] B) D)
    (hcomparison : ∀ i : ℤ, IsIso (M.comparison i)) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by
  intro i
  have := hcomparison i
  have : Module.Flat (A ⊗[R] B) D := hflat
  let f := algebraMap A (A ⊗[R] B)
  let g := algebraMap (A ⊗[R] B) D
  let F := extendScalars.{_, _, max uR uA uB uD v} g
  let G := restrictScalars.{max uR uA uB uD v} g
  let adj := extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} g
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have : PreservesFiniteLimits F := by
    have hex (S : ShortComplex (ModuleCat.{max uR uA uB uD v} (A ⊗[R] B)))
        (hS : S.Exact) : (S.map F).Exact := by
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
      let DD := (restrictScalars.{uD} g).obj (ModuleCat.of D D)
      have hm : Module.compHom D g = (inferInstance : Module (A ⊗[R] B) D) := by
        apply Module.ext
        funext r x
        exact (Algebra.smul_def r x).symm
      have : Module.Flat (A ⊗[R] B) DD := by
        change @Module.Flat (A ⊗[R] B) D _ _ (Module.compHom D g)
        rw [hm]
        exact hflat
      exact Module.Flat.lTensor_exact DD hS
    exact (((Functor.exact_tfae F).out 1 3 :
      (∀ S : ShortComplex _, S.Exact → (S.map F).Exact) ↔
        PreservesFiniteLimits F ∧ PreservesFiniteColimits F).mp hex).1
  let K := ((extendScalars.{_, _, max uR uA uB uD v} f).mapHomologicalComplex (.up ℤ)).obj Q
  let T := ((extendScalars.{_, _, max uR uA uB uD v} (g.comp f)).mapHomologicalComplex
    (.up ℤ)).obj Q
  let c : extendScalars.{_, _, max uR uA uB uD v} (g.comp f) ≅
      extendScalars.{_, _, max uR uA uB uD v} f ⋙ F :=
    (conjugateIsoEquiv
      ((extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} f).comp adj)
      (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (g.comp f))).symm
      (restrictScalarsComp f g).symm
  have hc (N : ModuleCat.{max uR uA uB uD v} A) :
      (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (g.comp f)).homEquiv _ _ (c.hom.app N) =
        (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} f).unit.app N ≫
          (restrictScalars.{max uR uA uB uD v} f).map (adj.unit.app _) ≫
          (restrictScalarsComp.{max uR uA uB uD v} f g).inv.app _ := by
    change (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (g.comp f)).unit.app N ≫
      (restrictScalars.{max uR uA uB uD v} (g.comp f)).map
        (((conjugateEquiv
          ((extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} f).comp adj)
          (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (g.comp f))).symm
            (restrictScalarsComp.{max uR uA uB uD v} f g).inv).app N) = _
    simpa only [Adjunction.comp_unit_app, Functor.comp_obj,
      Category.assoc, extendScalars] using
      (unit_conjugateEquiv_symm
        ((extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} f).comp adj)
        (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (g.comp f))
        (restrictScalarsComp.{max uR uA uB uD v} f g).inv N).symm
  have hct (N : ModuleCat.{max uR uA uB uD v} A) (q : N) :
      c.hom.app N ((1 : D) ⊗ₜ[A, g.comp f] q) =
        (1 : D) ⊗ₜ[A ⊗[R] B,g] ((1 : A ⊗[R] B) ⊗ₜ[A,f] q) := by
    change (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _}
      (g.comp f)).homEquiv _ _ (c.hom.app N) q = _
    rw [hc]
    rfl
  let e : ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅ T :=
    (Functor.mapHomologicalComplexCompIso c.symm (.up ℤ)).app Q
  let φ := M.ordinaryToLocalized
  have htrans (j : ℤ) : φ.f j = (adj.homEquiv _ _) (e.hom.f j) := by
    apply ExtendScalars.hom_ext
    intro q
    erw [M.ordinaryToLocalized_tmul j 1 q, map_one]
    change (1 : D) ⊗ₜ[A, g.comp f] q =
      (c.inv.app (Q.X j)) ((1 : D) ⊗ₜ[A ⊗[R] B,g] ((1 : A ⊗[R] B) ⊗ₜ[A,f] q))
    rw [← hct]
    exact (c.app (Q.X j)).toLinearEquiv.symm_apply_apply _ |>.symm
  have ht : IsIso ((adj.homEquiv _ _).symm
      (HomologicalComplex.homologyMap φ i ≫ ((T.sc i).mapHomologyIso G).hom)) := by
    let S := K.sc i
    let U := T.sc i
    let ψ : S.map F ⟶ U := (HomologicalComplex.shortComplexFunctor _ _ i).map e.hom
    have : IsIso ψ := inferInstance
    let τ : S ⟶ U.map G := (HomologicalComplex.shortComplexFunctor _ _ i).map φ
    let h := S.homologyData.left
    let k := U.homologyData.left
    let γ : ShortComplex.LeftHomologyMapData ψ (h.map F) k := default
    let δ : ShortComplex.LeftHomologyMapData τ h (k.map G) :=
      { φK := (adj.homEquiv _ _) γ.φK
        φH := (adj.homEquiv _ _) γ.φH
        commi := by
          change (adj.homEquiv _ _) γ.φK ≫ G.map k.i = h.i ≫ τ.τ₂
          rw [← adj.homEquiv_naturality_right]
          change _ = h.i ≫ φ.f i
          rw [htrans i]
          change _ = h.i ≫ (adj.homEquiv S.X₂ U.X₂) ψ.τ₂
          erw [← adj.homEquiv_naturality_left]
          exact congrArg (adj.homEquiv _ _) γ.commi
        commf' := by
          rw [ShortComplex.LeftHomologyData.map_f']
          change h.f' ≫ (adj.homEquiv _ _) γ.φK = τ.τ₁ ≫ G.map k.f'
          rw [← adj.homEquiv_naturality_left]
          change _ = φ.f ((ComplexShape.up ℤ).prev i) ≫ G.map k.f'
          rw [htrans, ← adj.homEquiv_naturality_right]
          change (adj.homEquiv S.X₁ k.K) (F.map h.f' ≫ γ.φK) =
            (adj.homEquiv S.X₁ k.K) (ψ.τ₁ ≫ k.f')
          apply congrArg (adj.homEquiv S.X₁ k.K)
          simpa only [ShortComplex.LeftHomologyData.map_f'] using γ.commf'
        commπ := by
          change h.π ≫ (adj.homEquiv _ _) γ.φH =
            (adj.homEquiv _ _) γ.φK ≫ G.map k.π
          rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
          exact congrArg (adj.homEquiv _ _) γ.commπ }
    have hγ : IsIso γ.φH :=
      (γ.quasiIso_iff).1 inferInstance
    have heq : ((adj.homEquiv _ _).symm
        (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)) =
        F.map h.homologyIso.hom ≫ γ.φH ≫ k.homologyIso.inv := by
      apply (adj.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
        adj.homEquiv_naturality_right]
      change ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom = _
      rw [δ.homologyMap_eq, k.mapHomologyIso_eq G]
      simp [δ, Category.assoc]
      rfl
    rw [heq]
    infer_instance
  have hloc : M.localizedComparison i =
      F.map (M.comparison i) ≫ (adj.homEquiv _ _).symm
        (HomologicalComplex.homologyMap φ i ≫ ((T.sc i).mapHomologyIso G).hom) := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    dsimp only [HomologicalComplex.homology] at *
    rw [Equiv.apply_symm_apply]
    change adj.unit.app _ ≫ _ = _
    exact M.localized_eq i
  rw [hloc]
  infer_instance


end ModuleCat.BaseDerivedTensorCohomologyModel
