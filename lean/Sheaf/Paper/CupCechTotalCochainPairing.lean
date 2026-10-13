/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.CupCechTotalComplex
public import Sheaf.Paper.CechCupProduct
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Paper.CupCechTotalCochainAxes
import Sheaf.Paper.CupCechTotalCochainMapExists

/-! # The signed Cech total cochain morphism

Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cup-cech-total-cochain-pairing)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
noncomputable section

/-- The signed Alexander-Whitney morphism of the total Cech complexes of a resolution
pairing preserves restrictions of global sections and coefficient augmentations.
Source: Stacks Project, equation 07MB, and the flasque diagram in Lemma 0FKV.
(blueprint: lem-sc-cup-cech-total-cochain-pairing)

Proof: on a tensor of summands with bidegrees (r,i) and (s,j), restrict the
front i-face and back j-face to their common intersection, apply D.pair r s,
multiply by (-1)^(i*s), and include in the target summand (r+s,i+j).
These bilinear formulas extend across the tensor product and finite coproducts
in every total degree. For the resolution differential, D.leibniz and the
Koszul factor (-1)^(i*s) give the tensor cochain identity. For the Cech
differential, expand the alternating omitted-vertex sums: the front and back
terms agree with the respective input differentials, and the two middle
terms cancel. Restriction compatibility of D.pair permits each composition of
restrictions to be replaced by its composite. These calculations prove the
cochain identity on pure tensors in each summand, hence on the whole total
term. On alpha summands i=j=0 all signs are one and restriction compatibility
gives the first equation. On beta summands r=s=0 the signs are again one;
D.augmentation_pair gives the second equation tuple by tuple. The same
finite-diagonal formulas cover degree zero, empty covers and zero sheaves. -/
theorem exists_cupCech_total_cochain_pairing {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G) :
    let A := (cupCechDouble U D.left.K).total (ComplexShape.up ℕ)
    let B := (cupCechDouble U D.right.K).total (ComplexShape.up ℕ)
    let C := (cupCechDouble U D.target.K).total (ComplexShape.up ℕ)
    ∃ h : HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
        (ComplexShape.up ℕ) ⟶ C,
      (∀ (p q : ℕ) (a : (cupSections D.left).X p) (b : (cupSections D.right).X q),
        h.f (p + q)
          (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
            (ComplexShape.up ℕ) p q (p + q) rfl
            (((cupCechAlpha U D.left).f p a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechAlpha U D.right).f q b))) =
        (cupCechAlpha U D.target).f (p + q) (D.pair p q ⊤ a b)) ∧
      (∀ (p q : ℕ)
        (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
        (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q),
        h.f (p + q)
          (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
            (ComplexShape.up ℕ) p q (p + q) rfl
            (((cupCechBeta U D.left).f p a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechBeta U D.right).f q b))) =
        (cupCechBeta U D.target).f (p + q) (cechCupCochain U F G p q a b)) := by
  obtain ⟨h, hh⟩ := exists_cupCech_total_cochain_map U D
  exact ⟨h, cupCech_total_cochain_axes U D h hh⟩

end
end AlgebraicGeometry.Scheme.Modules
