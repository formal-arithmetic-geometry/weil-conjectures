/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.SemiRepresentableObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# Objects of compatible simplicial maps in semi-representable objects

Source: Stacks Project, Tags 017J and 017K, applied to the category of formal étale
families using Tag 01G2 (blueprint: lem-weil-pbc-simplicial-hom-object-exists).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- The compatible families indexed by a finite simplicial set are represented by a
semi-representable object. Source: Stacks Project, Tags 017J, 017K and 01G2
(blueprint: lem-weil-pbc-simplicial-hom-object-exists).

Proof:
1. Form the category of simplices `(n, s)` of `S`, with arrows `(m, t) → (n, s)`
   given by monotone maps `φ : [m] → [n]` satisfying `S(φ)(s) = t`. Its opposite
   carries the diagram with value `K_n` and arrow `K(φ)`. By
   def-weil-pbc-simplicial-set and def-weil-pbc-semi-representable-object, cones
   with vertex `W` are exactly the compatible families in the statement (017J).
2. Finitely many nondegenerate simplices give a degree bound `m₀`. By
   lem-weil-pbc-simplicial-index-finite-initial, the opposite of the full subcategory
   of degrees at most `2 m₀` is finite and initial. The same node's limit-comparison
   clause (002R) reduces the full diagram's limit to this finite restriction (017K).
3. By lem-weil-pbc-semi-representable-finite-limits, applied to the small étale
   site as in def-weil-pbc-semi-representable-object, that finite limit exists (01G2).
   Let `H` be its vertex. Initiality extends its universal cone to all degrees,
   yielding the maps `u_s` and their compatibility equations. The cone correspondence
   in step 1 and the limit's universal property give the unique map `g` for every
   compatible family `f_s`, with `g ≫ u_s = f_s`. -/
theorem exists_simplicial_hom_object (X : Scheme.{u})
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t})
    [S.Finite] (hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌)))
    (hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))) :
    ∃ (H : FormalCoproduct.{w} X.Etale)
      (u : ∀ (n : ℕ), S.obj (op ⦋n⦌) → (H ⟶ K.obj (op ⦋n⦌))),
      (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
        u n s ≫ K.map φ.op = u m (S.map φ.op s)) ∧
      (∀ (W : FormalCoproduct.{w} X.Etale)
        (f : ∀ (n : ℕ), S.obj (op ⦋n⦌) → (W ⟶ K.obj (op ⦋n⦌))),
        (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
          f n s ≫ K.map φ.op = f m (S.map φ.op s)) →
        ∃! g : W ⟶ H, ∀ (n : ℕ) (s : S.obj (op ⦋n⦌)), g ≫ u n s = f n s) := sorry

end AlgebraicGeometry.Scheme
