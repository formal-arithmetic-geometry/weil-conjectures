## Worker report

The module `Sheaf.Algebra.Homology.ZigzagModuleFunctorial` states
`HomologicalComplex₂.zigzagModule_functorial`, with a single `sorry` and no new definitions.
The item's node copy changes only `lean`; no statement correction or dependency module is needed.
The server compile completed cleanly (1.4 seconds, exit 0).

Hypotheses and objects, matched to the node:

- The arbitrary commutative ring is `{R : Type u} [CommRing R]`.
- The three first-quadrant homological double complexes are `A B C :
  HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)`.
  This uses the precise specialization in `def-weil-pbc-module-double-complex.mathlib_match`.
  The module universe `v` and ring universe `u` are explicitly declared and independent.
- The two double-complex morphisms are `(Φ : A ⟶ B) (Ψ : B ⟶ C)`; the category structure
  already supplies linear component maps commuting with both differentials.
- Every nonnegative degree is covered by `(n : ℕ)`.
- `T_n`, `D_{n+1}`, `Z_n`, `B_n`, and `H_n` use respectively `zigzagTotal`,
  `zigzagBoundary`, `zigzagCycles`, `zigzagBoundaries`, and `zigzagModule` from the
  recorded dependency. `zigzagTotalMap Φ n` is its componentwise linear action.

Every conclusion, matched to the node:

- (a) `zigzagBoundaries A n ≤ zigzagCycles A n` is the boundary inclusion.
  `zigzagCycles A n ⊓ zigzagBoundaries A n = zigzagBoundaries A n` explicitly states
  the resulting simplification of the denominator. The recorded `zigzagModule` is the
  quotient of `Z` by the comap of `B` along `Z.subtype`; this comap is precisely `B`
  viewed inside `Z` once the inclusion holds. No distinct quotient type is introduced.
- (b) `(zigzagCycles A n).map (zigzagTotalMap Φ n) ≤ zigzagCycles B n` is preservation
  of cycles; `(zigzagTotalMap Φ n).comp (zigzagBoundary A n) =
  (zigzagBoundary B n).comp (zigzagTotalMap Φ (n + 1))` is `Φ D = D Φ` with its exact
  domain `T_{n+1}(A)` and codomain `T_n(B)`; the next submodule-map inclusion states
  preservation of boundaries.
- (c) The first universally quantified formula states that the existing linear map
  `zigzagMap Φ n` sends `Submodule.Quotient.mk a` to `Submodule.Quotient.mk b`
  whenever `a : zigzagCycles A n`, `b : zigzagCycles B n`, and
  `b.val = zigzagTotalMap Φ n a.val`. By (b), for every `a` such a `b` exists;
  its subtype proof is irrelevant. Thus the formula covers all cycle representatives.
  Existence is supplied by the recorded, fully defined `zigzagMap`; the following
  universal implication says that every linear map `f` with this representative formula
  equals `zigzagMap Φ n`. Together these state exactly existence and uniqueness.
- (d) `zigzagMap (Φ ≫ Ψ) n = (zigzagMap Ψ n).comp (zigzagMap Φ n)` states the
  composition law with the category's order of composition, and
  `zigzagMap (𝟙 A) n = LinearMap.id` states the identity law.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.HomologicalBicomplex`: `HomologicalComplex₂`, its full
  abbreviation, constructors, `d_comm` and `comm_f` were read. This is the Mathlib
  match of `def-weil-pbc-module-double-complex`; no specialization is redefined.
- `Sheaf.Algebra.Homology.ZigzagModule`: every signature and docstring was read;
  the statement uses `zigzagCycles`, `zigzagBoundaries`, `zigzagBoundary`,
  `zigzagTotalMap`, `zigzagModule`, and `zigzagMap`. The existing
  `zigzagTotalMap_preserves` has only preservation inclusions, not all clauses of this
  item, so it cannot serve as an existing realization of the whole statement.
- `Mathlib.LinearAlgebra.Quotient.Basic`: `Submodule.Quotient.mk` is the quotient class
  notation. The definitions and signatures of `mapQ`, `mapQ_apply`, `mapQ_mkQ`,
  `mapQ_comp`, and `mapQ_id` were read for the node's natural-language proof route.

Edge cases checked before writing:

- At `n = 0` there are no adjacent zig-zag equations, so all of `A_{0,0}` is `Z_0`;
  the boundary comes from the two possible degree-one positions. The statement imposes
  no extra condition on degree zero.
- At either axis, the dependency's boundary omits the negative-index term, matching
  the zero convention. No off-quadrant tuple is required by the signature.
- Zero modules, zero complexes, zero morphisms, and the zero ring are allowed.
  No nontriviality, characteristic, finite generation, or row/column exactness assumption
  is added. Exact rows/columns are needed for the later cokernel-homology comparison,
  not for these four elementary functoriality clauses.
- All sums use the finite diagonal index `ZigzagIndex n` already defined by the dependency;
  no new finiteness constraint is imposed on the double complexes.

Searches (real queries recorded in `searches.jsonl`):

- LeanSearch: `morphism of double complexes induces functorial linear map on zig-zag
  modules modulo trivial zig-zags` returned Internal Server Error (unavailable).
- LeanFinder: `trivial zig-zags belong to zig-zag cycles and induced quotient maps compose`
  returned eight graph/quiver connected-component declarations; no module zig-zag match.
- Loogle: `Submodule.mapQ, Submodule.mapQ_comp` returned `Submodule.mapQ_comp`, the generic
  quotient composition lemma, not the double-complex statement.
- Mathlib grep via msearch: `zigzag|zig-zag` in `Algebra/Homology` returned only
  `LocalCohomology.lean:202`, categorical `zigzag_isConnected`.
- `rg` over `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `zigzagMap|zigzagBoundaries|zig-zag|lem-weil-pbc-double-complex-zigzag-module-functorial`
  found only the recorded Sheaf dependency, including its partial preservation theorem.
- `rg` for the new full name `zigzagModule_functorial` across Mathlib, WeilConjectures,
  Sheaf, and the upstream-name index found no existing declaration.

Source: the local literature checkout is absent on this machine. Read the official
[Stacks Tag 00M1](https://stacks.math.columbia.edu/tag/00M1) online: its proof defines
zig-zag classes and states functoriality. Followed the plus-sign denominator in the
source display and the node, consistent with commuting squares. The source's later
signed-generator discrepancy is already documented by the dependency's node; it does
not dispute the current node's plus-sign convention. No node fault or
`STATEMENT-DISPUTED` finding.

## Second reading by F1

I independently read the node statement, its Stacks Tag 00M1 source place, the two
statement dependencies, and `ZigzagModuleFunctorial.lean`. The object and hypothesis
list is: a commutative ring `R` with `[CommRing R]`; first-quadrant homological
bicomplexes `A B C : HomologicalComplex₂ (ModuleCat.{v} R)
(ComplexShape.down ℕ) (ComplexShape.down ℕ)`; bicomplex morphisms `Φ : A ⟶ B` and
`Ψ : B ⟶ C`; and `n : ℕ`. The Lean signature renders these exactly, with independent
ring/module universes and no Noetherian, characteristic, finiteness, or nonzero
assumption.

The conclusion is checked clause by clause. Clause (a) is rendered by
`zigzagBoundaries A n ≤ zigzagCycles A n` and
`zigzagCycles A n ⊓ zigzagBoundaries A n = zigzagBoundaries A n`, giving the stated
quotient simplification. Clause (b) is rendered by the cycle-map inclusion, the exact
commuting equation
`(zigzagTotalMap Φ n).comp (zigzagBoundary A n) =
(zigzagBoundary B n).comp (zigzagTotalMap Φ (n + 1))`, and the boundary-map inclusion.
Clause (c) is rendered by the universal representative formula over cycle subtypes
`a` and `b` with `b.val = zigzagTotalMap Φ n a.val`, followed by universal uniqueness
of every linear map `f`; the preceding cycle inclusion supplies such a `b` for each
`a`, so this is equivalent to existence and uniqueness of the induced map in the node.
Clause (d) is rendered by the composition equality in categorical order and the
identity equality to `LinearMap.id`. The declarations used are precisely
`zigzagTotal`, `zigzagBoundary`, `zigzagCycles`, `zigzagBoundaries`, `zigzagModule`,
`zigzagTotalMap`, and `zigzagMap` from `Sheaf.Algebra.Homology.ZigzagModule`, with
`HomologicalComplex₂` from Mathlib.

Edge cases were checked: for `n = 0` the cycle condition is empty; boundary terms at
both axes use the dependency's zero convention; zero modules, zero complexes, zero
maps, and the zero commutative ring remain allowed; and the finite diagonal index is
provided by `ZigzagIndex n`. No universe restriction excludes any case in the node.

I searched Mathlib, `WeilConjectures`, project `lean/Sheaf`, and
`dag/lean_names_upstream.json` using LeanSearch, LeanFinder, Loogle, and `rg` for
`zigzagModule_functorial`, zig-zag notions, and quotient-induced maps. Only the
recorded zig-zag dependency and generic Mathlib quotient lemmas were found; no
existing declaration states this result. The source checkout is absent locally, so I
checked the official Tag 00M1 page recorded in the worker report.

No mismatch was found. The module and node were unchanged. Compilation with
`scompile.py` succeeded with no errors (only the permitted `sorry` declaration).
