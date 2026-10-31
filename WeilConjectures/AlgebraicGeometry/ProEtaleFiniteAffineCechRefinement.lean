/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Finite affine Čech refinements over separated pro-étale objects

Source: the affine-cover step in the proper closed-injective cohomology calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private theorem isPullback_product {S : Scheme.{u}} {V : S.ProEt} (A B : Over V) :
    IsPullback (prod.fst : A ⨯ B ⟶ A).left.left (prod.snd : A ⨯ B ⟶ B).left.left
      A.hom.left B.hom.left := by
  have h : IsPullback (prod.fst : A ⨯ B ⟶ A).left (prod.snd : A ⨯ B ⟶ B).left
      A.hom B.hom :=
    IsPullback.of_iso_pullback ⟨by rw [Over.w, Over.w]⟩ (Over.prodLeftIsoPullback A B)
      (Over.prodLeftIsoPullback_hom_fst A B) (Over.prodLeftIsoPullback_hom_snd A B)
  exact h.map (ProEt.forget S ⋙ Over.forget S)

private theorem affineHom_pi {S : Scheme.{u}} {V : S.ProEt}
    {J : Type} [Finite J] (U : J → Over V)
    (hU : ∀ j, IsAffineHom (U j).hom.left) : IsAffineHom (∏ᶜ U).hom.left := by
  let P : ObjectProperty (Over V) := fun A ↦ IsAffineHom A.hom.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B := by
    have : IsAffineHom A.hom.left := h
    have : IsIso e.inv.left.left :=
      inferInstanceAs (IsIso ((Over.forget V ⋙ ProEt.forget S ⋙ Over.forget S).map e.inv))
    have hw : e.inv.left.left ≫ A.hom.left = B.hom.left :=
      congrArg (fun f ↦ f.left) (Over.w e.inv)
    change IsAffineHom B.hom.left
    rw [← hw]
    infer_instance
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) (inferInstanceAs (IsAffineHom (𝟙 V.left)))⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    have : IsAffineHom (h.diag.obj ⟨.left⟩).hom.left := h.prop_diag_obj ⟨.left⟩
    have : IsAffineHom (h.diag.obj ⟨.right⟩).hom.left := h.prop_diag_obj ⟨.right⟩
    have : IsAffineHom
        (prod.snd : h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ ⟶ _).left.left :=
      MorphismProperty.of_isPullback (isPullback_product _ _) inferInstance
    change IsAffineHom _
    rw [← congrArg (fun f ↦ f.left)
      (Over.w (prod.snd : h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ ⟶ _))]
    change IsAffineHom
      ((prod.snd : h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ ⟶ _).left.left ≫
        (h.diag.obj ⟨.right⟩).hom.left)
    infer_instance⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

private theorem affine_cechNerve {S : Scheme.{u}} {V : S.ProEt}
    [V.left.IsSeparated] {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ a, IsAffine (U a).left.left) (k : ℕ) (y : Fin (k + 1) → Fin n) :
    IsAffine (Presheaf.cechNerveObj U y).left.left := by
  have hmap (a : Fin n) : IsAffineHom (U a).hom.left := by
    have := hU a
    have : IsAffineHom ((U a).hom.left ≫ terminal.from V.left) := by
      rw [terminal.comp_from]
      infer_instance
    exact IsAffineHom.of_comp (U a).hom.left (terminal.from V.left)
  have hprod : IsAffineHom (Presheaf.cechNerveObj U y).hom.left :=
    affineHom_pi _ (fun j ↦ hmap (y j))
  have hcomp : (Pi.π (fun j ↦ U (y j)) 0).left.left ≫ (U (y 0)).hom.left =
      (Presheaf.cechNerveObj U y).hom.left :=
    congrArg (fun f ↦ f.left) (Over.w (Pi.π (fun j ↦ U (y j)) 0))
  have : IsAffineHom ((Pi.π (fun j ↦ U (y j)) 0).left.left ≫ (U (y 0)).hom.left) := by
    rw [hcomp]
    exact hprod
  have : IsAffineHom (Pi.π (fun j ↦ U (y j)) 0).left.left :=
    IsAffineHom.of_comp _ (U (y 0)).hom.left
  have := hU (y 0)
  exact isAffine_of_isAffineHom (Pi.π (fun j ↦ U (y j)) 0).left.left

/-- Every covering sieve of a quasi-compact separated pro-étale object has a finite
refinement all of whose Čech intersections are affine.
Source: the finite affine cover argument; Stacks, Tags 01K3 and 03F9.
(blueprint: lem-sp-proetale-finite-affine-cech-refinement).

Proof: refine the sieve by finitely many affine opens of its covering members, using
quasi-compactness. Every map from an affine scheme to the separated target is affine,
by cancellation against the target's separated structure map. Affine morphisms are
closed under base change and finite products in the slice. Each nonempty finite
intersection projects affinely to an affine member, and is therefore affine. This
applies to every Čech degree; when the family is empty there are no tuples. -/
theorem exists_finite_affine_cech_of_mem_topology {S : Scheme.{u}} {V : S.ProEt}
    [CompactSpace V.left] [V.left.IsSeparated] {R : Sieve V}
    (hR : R ∈ topology S V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
        IsAffine (Presheaf.cechNerveObj U y).left.left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology S V := by
  obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_topology hR
  exact ⟨n, fun a ↦ Over.mk (g a),
    fun k y ↦ affine_cechNerve (fun a ↦ Over.mk (g a)) hU k y, hRg, hg⟩

end AlgebraicGeometry.Scheme.ProEt
