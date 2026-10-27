/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction
public import WeilConjectures.CategoryTheory.CompactObject
import Sheaf.CategoryTheory.DgAdjunctionCompactUnit
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Full faithfulness from compact DG bimodules and their self extensions

Source: Stacks Project, `dga.tex`, Tag 09R9, lemma-tensor-with-compact-fully-faithful
(blueprint: lem-sfb-dg-compact-bimodule-full-faithfulness).

The action hypothesis is specified on every cycle, using the actual left action.
Thus an abstract isomorphism between the two abelian groups does not suffice.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite

namespace CategoryTheory.DgAlgebra

/-- Restrict a DG bimodule to its specified right action, retaining its complex.
The unit and associativity proofs are the bimodule's existing right-action laws.
Source: Stacks Project, `dga.tex`, Tag 09R9, notation from Tag 09LT
(blueprint: lem-sfb-dg-compact-bimodule-full-faithfulness). -/
def bimoduleRightModule {A B : Algebra.{u}} (N : Bimod A B) : RightModule B where
  X := mop N.X
  mod :=
    { smul := N.actRight.mop
      one_smul := congrArg (fun f ↦ f.mop) N.actRight_one
      mul_smul := congrArg (fun f ↦ f.mop) N.right_assoc }

/-- Tensoring with a compact DG bimodule is fully faithful if its canonical action
map identifies every cohomology group of A with the corresponding self extensions.
The functor T and comparison α are any total left derived functor of the actual
balanced tensor F: its universal property is `IsRightKanExtension α`, exactly as
in `bimodule_derived_tensor_hom_adjunction`. These binders specify the derived
construction, not extra flatness, boundedness, or adjunction hypotheses.

For each k, S is a DG representative of N[k], and φ is an additive equivalence.
Its equation on every cycle z requires a DG map f whose homogeneous coordinates
are precisely n ↦ zn. The second equation says that φ sends the cohomology class
of z to the localized class of this very map. Since `homologyπ` is surjective,
this specifies the canonical action map, including independence of boundaries.
No generation assumption on N is made.

Source: Stacks Project, `dga.tex`, Tag 09R9
(blueprint: lem-sfb-dg-compact-bimodule-full-faithfulness).

Proof plan (the five steps of the node):
1. Use lem-sfb-dg-bimodule-derived-adjunction to obtain the exact right adjoint U
and shift-compatible adjunction T ⊣ U. DG coproducts are computed by direct sums
(lem-sfb-dg-derived-admissible-triangles, lem-sfb-dg-sequential-colimit-triangle).
As a left adjoint, T preserves them (lem-weil-pbc-left-adjoint-preserves-colimits).
2. Apply lem-sfb-dg-semifree-bimodule-tensor-computation to each one-step semi-free
A[k]. The isomorphism A[k] tensor N ≅ N[k] sends x tensor n to xn, with inverse
n ↦ 1 tensor n. It takes tensoring the map x ↦ ax to the specified map n ↦ an.
3. By lem-sfb-dg-free-module-hom-cohomology, the self-extension hypothesis makes
Hom(A,η_A[k]) bijective: adjunction transposes T(f) to η composed with f, and
shift compatibility identifies this with the shifted unit map.
4. Represent η_A by a DG map using lem-sfb-dg-free-shift-derived-hom. Naturality
of the free-module cohomology formula identifies the preceding bijections with
its cohomology maps. Hence this representative is a quasi-isomorphism and η_A
is invertible in the specified localization.
5. Apply lem-sfb-dg-adjunction-compact-unit with target D(B). The image of A is N,
which is compact by hypothesis. Its conclusion gives bijectivity on every Hom
set. No generation of D(B) by N enters this argument. -/
theorem derived_tensor_fully_faithful_of_compact_bimodule
    (A B : Algebra.{u}) [DerivedStructure A] [DerivedStructure B]
    (N : Bimod A B) (F : RightModule A ⥤ RightModule B)
    (_tensor : BalancedTensorModel N F)
    (T : Derived A ⥤ Derived B) (α : Q A ⋙ T ⟶ F ⋙ Q B)
    [T.IsRightKanExtension α]
    (hcompact : IsCompactObject.{u} ((Q B).obj (bimoduleRightModule N)))
    (hself : ∀ k : ℤ, ∃ (S : RightModule B)
      (e : ShiftComparison B k (bimoduleRightModule N) S)
      (φ : A.X.homology k ≃+
        ((Q B).obj (bimoduleRightModule N) ⟶ ((Q B).obj (bimoduleRightModule N))⟦k⟧)),
      ∀ z : A.X.cycles k, ∃ f : bimoduleRightModule N ⟶ S,
        (∀ (p : ℤ) (n : N.X.X p),
          HEq (shiftedElement k (bimoduleRightModule N) S e p
            ((((underlying B).map f).f p) n))
            ((N.actLeft.f (k + p))
              ((HomologicalComplex.ιTensorObj A.X N.X k p (k + p) rfl)
                (TensorProduct.tmul (ULift.{u} ℤ) ((A.X.iCycles k) z) n)))) ∧
        φ ((A.X.homologyπ k) z) =
          (Q B).map f ≫ (DerivedStructure.shiftIso k (bimoduleRightModule N) S e).hom) :
    ∀ M P : Derived A,
      Function.Bijective (T.map : (M ⟶ P) → (T.obj M ⟶ T.obj P)) := by
  sorry

end CategoryTheory.DgAlgebra
