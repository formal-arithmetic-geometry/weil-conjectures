/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams
import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

/-! # Canonical augmentation of the enlarged finite-piece bar union

Source: the finite-subcomplex and target-chain portions of
`lem-sc-compact-flat-telescope-bar-enlargement`.
(blueprint: lem-sc-compact-flat-bar-union-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The geometric part of bar enlargement: a split flat bar tower with compatible
augmentations whose union augmentation is a homotopy equivalence. This statement
contains no split exact presentation of its union.

Source: the finite-piece and target-chain paragraphs of
`lem-sc-compact-flat-telescope-bar-enlargement`, originally expanded in
`lem-sc-flat-telescope-target-refinement`.

Proof. Use the supplied stage-filtered diagrams D_n of finite complexes. Their
specified colimit cocones have vertices L_n and commute strictly with l_n. Each
D_n is filtered, every object has finitely many nonzero degrees with finite
compact-flat summands, and its objects have a common stage upper bound. Use the
one global indexing preorder to include D_n into D_(n+1); no new generator
choices or subcomplex closure argument is needed.
Take the unnormalized bar total R_n, placing simplicial degree p in degree -p.
Exactness of filtered colimits gives a quasi-isomorphism c_n to L_n. A common
upper bound for stages at most n bounds this total above; its terms are sums of
flat sheaves. Inclusion of stage-labelled diagrams gives s_n, strictly compatible
with the augmentations. Labelled copies avoid requiring the source generator
choices to be compatible with the tower maps.

Write T as its supplied telescope. The finite cone blocks C_k use source indices
at most k and target indices at most k+1. They are flat and bounded above, with
degreewise split inclusions and union T. Every finite source diagram object factors
through a block, by compactness in its finitely many nonzero degrees. The factor
is a chain map because the block inclusion is monic. Enlarge the union diagram
by this target chain, putting an arrow from a source object to k exactly when
its augmentation factors through C_k. There is a least such k, monotone in the
source object; it is left adjoint to target-chain inclusion. Insert the unit in
bar strings with alternating signs to get the corresponding bar homotopy.
Let F_n be the full-subdiagram bar total using D_n and target indices at most n.
Bar inclusions give u_n and a_n; each u_n is degreewise split since its bar
summands form a subset of the next bar summands. Their augmentations q_n into T
satisfy the two stated identities strictly. F_n is flat and bounded above by
the common bound on this finite segment.

The union bar total is the cokernel of identity minus shift: its relations
identify each simplex with the same simplex at the next stage. Compare the bar
resolution of the augmented constant right functor on the target chain with the
two-term representable resolution by identity minus shift. Projective comparison
lifts yield maps and homotopies lifting its identity. Tensor them with C_k;
every input has finite support, so they totalize. The finite-block telescope
augmentation to T is a homotopy equivalence, since its degreewise split union
sequence has contractible cone kernel. Consequently the target-chain bar
augmentation is a homotopy equivalence. Cancel the unit-insertion bar equivalence
to conclude this for the enlarged union's canonical augmentation as well.
Identify the union with the displayed cokernel by its universal property. This
identification carries its augmentation to cokernel.desc of Sigma.desc q.
The zero relation follows from compatibility of q. Its chosen proof is
irrelevant, so the asserted isomorphism holds for every hzero. No witness is
chosen as the data of a definition.
(blueprint: lem-sc-compact-flat-bar-union-augmentation). -/
theorem exists_compact_flat_bar_union_augmentation (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, L n ⟶ T)
    (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ L n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ l n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      (∀ (n : ℕ) (i : ℤ), IsSplitMono ((u n).f i)) ∧
      ∃ q : ∀ n : ℕ, F n ⟶ T,
        (∀ n : ℕ, u n ≫ q (n + 1) = q n) ∧
        (∀ n : ℕ, a n ≫ q n = c n ≫ p n) ∧
        ∀ hzero : flatTelescopeDifferential F u ≫ Sigma.desc q = 0,
          IsIso (Q.map
            (cokernel.desc (flatTelescopeDifferential F u) (Sigma.desc q) hzero)) := by sorry

end AlgebraicGeometry
