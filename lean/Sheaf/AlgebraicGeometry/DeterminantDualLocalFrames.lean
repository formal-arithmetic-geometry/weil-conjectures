/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Finite-free exterior frames on a trivializing open
(blueprint: lem-sc-exterior-dual-local-frames)
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Finite-free exterior sheaves admit wedge bases, and internal dual evaluation identifies
sections of the dual exterior sheaf with the linear dual of its sections.
Source: local pairing node proof steps 1-2, expanding the determinant inversion used in
Stacks Project, Tag 0BRT (lemma-smooth-proper); Mathlib `Module.Basis.exteriorPower` and
`exteriorPower.basis_coord`.
(blueprint: lem-sc-exterior-dual-local-frames).

Proof: restrict `e` along `g`. The finite free sheaf has a basis on every smaller open,
obtained by restricting its generators; its sections on `V` are the finite product of
`O_X(V)`, giving `a`. A linear functional on these sections extends uniquely to a sheaf
morphism on the localized site: apply its coefficients to the restricted generators.
Conversely such a morphism is determined by these generators. In particular the coordinate
functionals give sections `φ` of the internal dual, with the asserted evaluation formula.
Apply the increasing-wedge construction to the generators and their duals. The sectionwise
exterior presheaves of these finite free sheaves are finite products of the structure sheaf,
indexed by the n-element subsets of `Fin r`. Their coordinate restriction maps commute with
all open restrictions, and these presheaves are already sheaves. Restriction to the localized
site commutes with sheafification: the same unit has its universal factorization property
against sheaves there, since the localized covers are exactly the covers of smaller opens.
Thus the sheafification unit identifies the increasing wedges with bases `b` and `d` of the
exterior sheaf sections. Finally repeat the coordinate reconstruction of morphisms for the
finite free sheaf with basis `d`, giving the evaluation equivalence `c` and its formula.
For n=0 the index set is a singleton and the empty wedge is 1; for n>r it is empty and both
exterior section modules are zero. No nontrivial-ring assumption is used, and the argument
also applies to empty opens. -/
theorem exterior_dual_local_frames (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op V)) (M.val.obj (op V)))
      (φ : Fin r → (Scheme.Modules.dual M).val.obj (op V))
      (b : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n).val.obj (op V)))
      (d : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorSheaf M n).val.obj (op V)))
      (c : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op V) ≃ₗ[
        X.presheaf.obj (op V)] Module.Dual (X.presheaf.obj (op V))
          ((Scheme.Modules.exteriorSheaf M n).val.obj (op V))),
      (∀ (j : Fin r) (x : M.val.obj (op V)),
        (φ j).app (op (Over.mk (𝟙 V))) x = a.coord j x) ∧
      (∀ s, b s = Scheme.Modules.exteriorSheafSection (Scheme.Modules.dual M) n V
        (φ ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ s, d s = Scheme.Modules.exteriorSheafSection M n V
        (a ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ (ψ : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op V))
        (x : (Scheme.Modules.exteriorSheaf M n).val.obj (op V)),
        c ψ x = ψ.app (op (Over.mk (𝟙 V))) x) := by sorry

end AlgebraicGeometry
