## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleSeparatedStratifiedFinite.lean` states
`AlgebraicGeometry.exists_finite_etale_stratification`.  It introduces schemes `V` and
`Y`, a morphism `f : V ⟶ Y`, and hypotheses `QuasiCompact (𝟙 Y)` and
`QuasiSeparated (𝟙 Y)` for the quasi-compact quasi-separated target, together with
`Etale f`, `IsSeparated f`, and `QuasiCompact f`.  The conclusion chooses a natural
number `n`, schemes `Y_r : Fin n → Scheme`, and immersions `i r : Y_r r ⟶ Y`.

For every `r`, `IsImmersion (i r)` gives the subscheme structure and
`Set.range (i r).base` is its image; `IsLocallyClosed` and
`Topology.IsConstructible` render the two required properties.  The clause
`∀ r s, r ≠ s → Disjoint ...` gives pairwise disjoint strata, and
`(⋃ r, Set.range (i r).base) = Set.univ` gives their union equal to `Y`.
For each `r`, the pullback `pullback.snd f (i r)` is the projection
`V ×_Y Y_r → Y_r` (using the Mathlib pullback convention), and the conjunction
`IsFinite ... ∧ Etale ...` is exactly the finite étale condition.  `Fin n` is a
finite index type; `n = 0` correctly represents the empty-target edge case, while
nonempty targets force a nonempty union.

The dependency notions are used through their recorded Mathlib declarations:
`AlgebraicGeometry.Etale`, `IsLocallyClosed`, `Topology.IsConstructible`,
`AlgebraicGeometry.IsClosedImmersion`/`IsImmersion`,
`AlgebraicGeometry.IsFinite`, and `CategoryTheory.Limits.pullback`/`pullback.snd`.
The scheme-conventions node supplies the meanings of quasi-compact, quasi-separated,
and separated; no private copy of any notion was introduced.  The finite étale
category node is rendered by the conjunction of `IsFinite` and `Etale` on each
base-change projection, as its object condition specifies.

Edge cases checked: an empty scheme admits `n = 0`; pairwise disjointness is stated
only for distinct indices; arbitrary finite index cardinality is represented by
`Fin n`; and the pullback orientation has second projection to `Y_r`.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
“separated etale quasi-compact quasi-separated morphism finite etale on a
constructible stratification” found only generic étale/separated/base-change facts;
`msearch.py ... loogle` for `AlgebraicGeometry.IsSeparated` found no stratification
result; grep of Mathlib AlgebraicGeometry/Topology for
`stratify.*flat.*fp.*qf|finite.*etale.*strat|constructible.*strat` found no theorem;
`rg` over `WeilConjectures/` and `lean/Sheaf/` found no declaration of this result.
Thus a new statement module was required.  No `STATEMENT-DISPUTED` issue was found.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, every hypothesis is present: target
quasi-compactness and quasi-separatedness, étaleness, separatedness, and
quasi-compactness of `f`.  The finite family of subschemes is represented by
`Fin n`; each image is explicitly the range of an immersion, and local closedness
and constructibility are asserted for that same image.  The disjointness and union
clauses give exactly a partition, and `pullback.snd f (i r)` has codomain `Y_r r`,
so its finite and étale predicates state the required base-change conclusion.
No mismatch was found.

## Second reading by H1

The node introduces a quasi-compact, quasi-separated target `Y`, a morphism
`f : V ⟶ Y`, and hypotheses that `f` is étale, separated, and quasi-compact.
These are rendered by `hYqc : QuasiCompact (𝟙 Y)`, `hYqs : QuasiSeparated (𝟙 Y)`,
`hfet : Etale f`, `hfsep : IsSeparated f`, and `hfqc : QuasiCompact f`; the
explicit identity-morphism predicates express the node's scheme conventions
without adding hypotheses. The conclusion introduces `n : ℕ`, schemes
`Y_r : Fin n → Scheme`, and morphisms `i r : Y_r r ⟶ Y`. For each index,
`IsImmersion (i r)` supplies the subscheme structure and `Set.range (i r).base`
is its image, with `IsLocallyClosed` and `Topology.IsConstructible` giving the
two stated subset properties. The next clause gives pairwise disjoint images,
the union clause gives all of `Y`, and the last clause says
`pullback.snd f (i r)` is both `IsFinite` and `Etale`, exactly the finite étale
base-change conclusion. Quantifiers and conjunction nesting match the node.

Edge cases were checked: `Fin 0` permits the empty target; a nonempty target
cannot satisfy the union clause with `n = 0`; equal indices are excluded from
the disjointness implication; `n` is an unrestricted natural number; and no
characteristic, nonemptiness, or universe restriction is added. The pullback
orientation is the second projection to `Y_r`, as required.

I searched with `msearch.py`/LeanFinder for finite étale stratification, with
Loogle for `AlgebraicGeometry.IsSeparated`, and with `rg` through Mathlib,
`WeilConjectures`, and `lean/Sheaf`; only generic étale, separatedness,
constructibility, and pullback results were found. The Stacks source (More on
Morphisms, Tag 07RZ, together with Etale Cohomology Tag 03S9) agrees with the
six proof steps recorded in the declaration docstring.

The only delivery mismatch was an unrelated stale copy of
`lem-weil-pbc-etale-stratified-finite.json` in the sandbox; it was removed. The
item theorem required no statement change. Its docstring was expanded to record
the node's proof steps explicitly; no hypotheses or conclusion clauses changed.
