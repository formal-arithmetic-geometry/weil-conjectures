module

public import Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction

/-!
# Semi-free modules compute derived bimodule tensor

Source: Stacks Project, `dga.tex`, Tag 09LS, proof of lemma-derived-bc, and
Tag 09KK, section-P-resolutions
(blueprint: lem-sfb-dg-semifree-bimodule-tensor-computation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DgAlgebra

/-- The semi-free filtration appearing in this node, reindexed with `stage 0 = 0`
and `stage (p+1) = F_p`. Inclusions into P are injective, compatible with the
transitions and exhaustive degree by degree, so the stages are DG submodules of P.
Retractions are graded right A-linear maps, without a chain-map requirement.
The exact surjections to `layer p` identify it with the successive DG quotient.
Its cell maps exhibit it, degree by degree, as the direct sum of the specified
shifts of the regular DG module. Since these maps are DG A-linear, this is a
direct sum of DG modules, with the actual shifted differentials and actions.
The index sets may be empty and have arbitrary cardinality in universe u.

Source: Stacks Project, `dga.tex`, Tag 09KK, section-P-resolutions
(blueprint: lem-sfb-dg-semifree-bimodule-tensor-computation). -/
structure SemiFreeFiltration (A : Algebra.{u}) (P : RightModule A) where
  stage : ℕ → RightModule A
  inclusion (p : ℕ) : stage p ⟶ P
  injective (p : ℕ) (n : ℤ) :
    Function.Injective (((underlying A).map (inclusion p)).f n)
  initial (n : ℤ) : Subsingleton (((underlying A).obj (stage 0)).X n)
  transition (p : ℕ) : stage p ⟶ stage (p + 1)
  compatibility (p : ℕ) : transition p ≫ inclusion (p + 1) = inclusion p
  exhaustive (n : ℤ) (x : ((underlying A).obj P).X n) :
    ∃ (p : ℕ) (y : ((underlying A).obj (stage p)).X n),
      (((underlying A).map (inclusion p)).f n) y = x
  retraction (p : ℕ) (n : ℤ) :
    ((underlying A).obj (stage (p + 1))).X n →+
      ((underlying A).obj (stage p)).X n
  retraction_left_inverse (p : ℕ) (n : ℤ) (x : ((underlying A).obj (stage p)).X n) :
    retraction p n ((((underlying A).map (transition p)).f n) x) = x
  retraction_action (p : ℕ) (n m : ℤ)
      (x : ((underlying A).obj (stage (p + 1))).X n) (a : A.X.X m) :
    retraction p (n + m) (act A (stage (p + 1)) n m x a) =
      act A (stage p) n m (retraction p n x) a
  layer : ℕ → RightModule A
  quotient (p : ℕ) : stage (p + 1) ⟶ layer p
  quotient_surjective (p : ℕ) (n : ℤ) :
    Function.Surjective (((underlying A).map (quotient p)).f n)
  quotient_exact (p : ℕ) (n : ℤ) :
    Function.Exact (((underlying A).map (transition p)).f n)
      (((underlying A).map (quotient p)).f n)
  index : ℕ → Type u
  shift (p : ℕ) : index p → ℤ
  cell (p : ℕ) : index p → RightModule A
  cell_shift (p : ℕ) (i : index p) :
    ShiftComparison A (shift p i) (regular A) (cell p i)
  cellMap (p : ℕ) (i : index p) : cell p i ⟶ layer p
  cells_colimit (p : ℕ) (n : ℤ) :
    Nonempty (IsColimit (Cofan.mk (((underlying A).obj (layer p)).X n)
      (fun i : index p ↦ (((underlying A).map (cellMap p i)).f n))))

/-- The canonical total-left-derived comparison is invertible on every semi-free
module, naturally in maps between such modules. `BalancedTensorModel` fixes the
balanced DG tensor, its induced maps and its right B-action. The comparison is
the universal counit `α` used in the derived-adjunction dependency, not an
arbitrary isomorphism. The conclusion lives in D(B), retaining that action.

Source: Stacks Project, `dga.tex`, Tag 09LS, lemma-derived-bc, proof
(blueprint: lem-sfb-dg-semifree-bimodule-tensor-computation).

Proof plan:
1. Regard A as a one-object DG category and reindex the filtration. Apply
lem-coef-dg-semi-free-homotopically-projective, then
lem-sfb-dg-homotopically-projective-hom-derived, to obtain bijectivity of
Hom_K(P,X) to Hom_D(P,X) on semi-free sources.
2. Lem-sfb-dg-property-p-resolution gives a semi-free resolution of every module,
with its cell sets in u. Its image in the localization is invertible.
3. Balanced tensor descends from DG modules to their homotopy category:
the homotopy h tensor id is balanced and B-linear. The two terms containing
d_N cancel, since their signs are (-1)^(degree(p)-1) and (-1)^degree(p).
4. Apply lem-sfb-projective-localization-left-derived to this functor into D(B),
using steps 1 and 2. Its universal counit is invertible on semi-free objects.
The total left derived functor of lem-sfb-dg-bimodule-derived-adjunction is this
same universal pair, so its canonical comparison is invertible as well.
5. Counit naturality gives the displayed square. All maps are in D(B);
the tensor model identifies F.map f with f tensor id_N. No flatness over Z,
boundedness, countability, compactness or self-extension condition is used. -/
theorem semifree_bimodule_tensor_computation
    (A B : Algebra.{u}) [DerivedStructure A] [DerivedStructure B]
    (N : Bimod A B) (F : RightModule A ⥤ RightModule B)
    (_t : BalancedTensorModel N F) (T : Derived A ⥤ Derived B)
    (α : Q A ⋙ T ⟶ F ⋙ Q B) [T.IsRightKanExtension α] :
    (∀ (P : RightModule A), Nonempty (SemiFreeFiltration A P) → IsIso (α.app P)) ∧
    (∀ (P P' : RightModule A), Nonempty (SemiFreeFiltration A P) →
      Nonempty (SemiFreeFiltration A P') → ∀ f : P ⟶ P',
        T.map ((Q A).map f) ≫ α.app P' = α.app P ≫ (Q B).map (F.map f)) := by
  sorry

end CategoryTheory.DgAlgebra
