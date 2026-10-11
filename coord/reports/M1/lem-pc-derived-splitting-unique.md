## Worker report

The module `Sheaf.Paper.DerivedSplittingUnique` states `CategoryTheory.derivedSplittingUnique`.
It uses `DerivedCategory (ModuleCat R)` and a bounded cochain complex `P` as the
projective representative of `L`. The hypothesis `Projective (P.X i)` renders
projectivity, `IsZero (P.X i)` outside `[a,b]` renders the degree bound, and
`Nonempty (L ≅ DerivedCategory.Q.obj P)` renders the derived isomorphism.
Derived homology vanishing is rendered by `IsZero ((DerivedCategory.homologyFunctor
(ModuleCat R) i).obj K)`. The first conclusion is the zero morphism statement
under vanishing for all `i ≥ a`. The second is the compatible biproduct
isomorphism for every distinguished `Triangle` under vanishing for all
`i ≥ a+1`; its equations are `T.mor₁ ≫ e.hom = biprod.inl` and
`T.mor₂ = e.hom ≫ biprod.snd`. The third conclusion states equality of any two
such compatible isomorphisms under vanishing for all `i ≥ a`.

Dependency declarations used: `DerivedCategory` from
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (the dependency node
`def-weil-abstract-derived-category`); `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`
from `Mathlib.CategoryTheory.Triangulated.Pretriangulated` (the dependency node
`lem-pc-derived-zero-third-split`). The precise-vanishing node is used by the
source proof but is not needed to type this statement.

Edge cases checked: arbitrary ring `R`; arbitrary integer bounds including
`a > b` and `a = b`; empty/zero complexes via `IsZero`; zero derived objects;
and arbitrary universe `v` for module carriers. No extra mathematical
hypothesis is introduced beyond the typeclass instance selecting the derived
category universe.

Searches made: `msearch.py leanfinder` and `loogle` for derived-category
projective splitting (no exact match); grep of Mathlib homology/triangulated
modules and `WeilConjectures/` for splitting-unique (no project declaration).
The exact Mathlib zero-third-map declaration was read at
`Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`.

STATEMENT-DISPUTED: none.

## Earlier second reading (a previous round; superseded)

The theorem was reread against Tag 0BCG. The three clauses preserve the two
separate cohomology thresholds (`a` for vanishing and uniqueness, `a+1` for
splitting), and all triangle compatibility equations are explicit.

## Second reading by M1

Read against Stacks, More on Algebra, Tag 0BCG, including its explanation of
projective amplitude in the proof. Item-by-item match:

- Ring `R`: `{R : Type u} [Ring R]`; verdict: arbitrary ring.
- Derived category `D(R)`: `DerivedCategory (ModuleCat.{v} R)` with its chosen
  localization `[HasDerivedCategory.{w} ...]`; verdict: the Mathlib dependency
  `def-weil-abstract-derived-category` specializes to modules, with no field,
  finiteness, or Noetherian assumption.
- Objects `K,L`: `(K L : DerivedCategory ...)`; verdict: exact.
- Integers `a,b`: `(a b : ℤ)`; verdict: exact.
- Projective amplitude of `L`: `hL` chooses a complex `P`, projective at every
  degree, zero outside `[a,b]`, and an isomorphism from `L` to its image under
  `DerivedCategory.Q`; verdict: the representative specified in Tag 0BCG,
  without finite generation.
- Clause (1): homology of `K` is zero at every `i ≥ a`, expressed by `IsZero`
  after `homologyFunctor`; every `f : L ⟶ K` equals zero; verdict: exact.
- Clause (2): homology of `K` is zero at every `i ≥ a+1`; every distinguished
  triangle with objects `K,M,L` has `e : M ≅ K ⊞ L` satisfying both
  `T.mor₁ ≫ e.hom = biprod.inl` and `T.mor₂ = e.hom ≫ biprod.snd`;
  verdict: exact, including compatibility with both triangle maps.
- Clause (3): under vanishing at every `i ≥ a`, any two isomorphisms satisfying
  those compatibility equations are equal. Existence follows from clause (2),
  since vanishing from `a` implies vanishing from `a+1`; verdict: equivalent to
  the source's "exists and is unique".

Edge cases: `ℤ` includes zero and negative bounds; `a > b` forces a zero
representative; zero modules, zero derived objects, and zero triangles are
included. There is no nonempty-index, nonzero, characteristic, or fixed-small-
universe restriction; `u`, `v`, and `w` are bound explicitly.

Independent searches: `msearch.py` with LeanFinder for bounded projective
derived-category triangle splitting returned K-projective orthogonality and
single-complex vanishing, but no exact theorem; Loogle for derived projective
triangle biproduct uniqueness returned no hit; grep through Mathlib, the source
`WeilConjectures/`, and `lean/Sheaf/` found no exact splitting-unique theorem.
The zero-third-map dependency was checked directly at
`Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`: it gives exactly
both compatibility equations. The derived-category dependency was checked at
`Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`.

No statement mismatch was found. I expanded the theorem docstring to carry
the node's four proof steps and left its signature and node record unchanged.

## Reviewer fix (R-dsu0759)

The delivered conclusion `(C1) ∧ V(a+1) → (C2) ∧ V(a) → (C3)` parsed, since `∧`
binds tighter than `→`, as `(C1 ∧ V(a+1)) → ((C2 ∧ V(a)) → C3)`: clauses (1) and
(2) were hypotheses, not conclusions (checked by printing the elaborated type).
Each clause is now parenthesised as its own conjunct `(V → C)`, so the theorem
destructures into the three implications of Tag 0BCG; the objects, hypotheses
and compatibility equations are unchanged. Unused `open`s dropped.
