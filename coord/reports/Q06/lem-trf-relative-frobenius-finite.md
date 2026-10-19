## Worker report

Handoff recovery: the retained sandbox contained only dispatcher markers. No module, node
copy, report, or second-reading section was present. I reconstructed the missing stage-2
packet from the shared reviewed stage-1 node; no earlier stage-2 author text is claimed.

The node states finiteness of the n-fold relative Frobenius. Its objects and hypotheses are rendered by
`relativeFrobenius_finite` in `lean/Sheaf/AlgebraicGeometry/RelativeFrobeniusFinite.lean`:

- `p : ℕ` and `hS : S.IsCharacteristic p` render a prime `p` and a characteristic-
  `p` base scheme `S`.
- `f : X ⟶ S` with `[LocallyOfFiniteType f]` renders the locally finite type morphism.
- `n : ℕ` with `hn : 1 ≤ n` renders the positive iterate.
- `S.iterateFrobenius hS.1 (hS.2 ⊤) n` and
  `X.iterateFrobenius hX.1 (hX.2 ⊤) n` render the n-fold absolute Frobenius maps;
  `hX : X.IsCharacteristic p` is existentially supplied because the source
  characteristic pulls back along `f` and is needed by the recorded upstream
  Frobenius interface.
- `pullback f (S.iterateFrobenius hS.1 (hS.2 ⊤) n)` renders
  `X ×_{S,F_S^n,S} S`, with `pullback.fst` and `pullback.snd` as its projections.
- The two displayed equalities specify the relative Frobenius, the final
  `∀ s, ... → ... → s = r` clause specifies uniqueness, and `IsFinite r` is the
  asserted conclusion.

The proof is deliberately postponed as `by sorry`, with the proof plan in the theorem
docstring. It follows Tags 0CCB, 0CCD and 0CCG: iterate one-step relative Frobenius maps,
use integrality and composition, identify the iterated map by its projections, cancel local
finite type from the composite, and apply finite iff integral plus locally finite type. The
statement dependencies are `Scheme.IsCharacteristic`, `LocallyOfFiniteType`,
`Scheme.iterateFrobenius`, `pullback`, and `IsFinite`; the proof dependencies are the
relative-Frobenius integrality theorem and the recorded integral-composition,
finite-type-cancellation, and finite-criterion nodes.

I read the Stacks source `literature/stacks-project/varieties.tex`, Tags 0CCD and 0CCG,
and all dependency statements and declarations. The inherited searches found no exact
Mathlib or project theorem. Independent Q06 searches were run with `msearch.py`: LeanFinder
for “finite n-fold relative Frobenius for a locally finite type morphism of characteristic p
schemes” returned only generic finite-morphism infrastructure; LeanSearch returned only
ring/field Frobenius declarations; Loogle reported zero hits (unknown identifier `IsFinite`);
a subsequent valid Loogle string query `"frobenius", "IsFinite"` returned zero hits;
and grep for `relativeFrobenius|relative_frobenius|iterateFrobenius` in AlgebraicGeometry
returned zero hits. The slopmaster2 relative-Frobenius theorem requires finite absolute
Frobenius maps or finite-field models and therefore is not this arbitrary-base statement.

Edge cases checked are `n = 1` (the one-step result), `n = 0` excluded by `hn`, `X = S`
(identity structure map), empty and zero schemes, nilpotent schemes, imperfect bases whose
absolute Frobenius is not finite, and infinite disjoint unions. No reducedness,
Noetherianity, separatedness, perfection, quasi-compactness, nonempty index, or finite
absolute-Frobenius hypothesis is introduced.

## Review by Q25 (retained from the first reading)

The first reading checked Tags 0CCD, 0CCB, 0CCG and 0CC7, the finite-type cancellation
clause 01T8, integral composition 01WK, and the finite criterion 01WJ. It verified the
successive-twist universal-property calculations, integrality of each one-step map, the
projection induction identifying the n-fold map, and the local-finite-type cancellation.
It found no statement dispute, source error, duplicate, or dependency cycle, and checked
empty schemes, nilpotents, identity and imperfect-base examples. Its full search and source
notes are retained in the Q25 report history.

## Second reading by Q06

I rechecked the reconstructed module against the node statement, its source place, and
every statement dependency; the missing handoff made reconstruction necessary. The source list is: prime `p`; a scheme `S` with
`S.IsCharacteristic p`; a morphism `f : X ⟶ S` carrying only `[LocallyOfFiniteType f]`;
positive integer `n`; the n-fold absolute Frobenius maps; the fibre product
`X ×_{S,F_S^n,S} S`; the unique map with first projection `F_X^n` and second projection
`f`; and the conclusion that this map is finite. The Lean renders these item by item with
`p`, `S`, `X`, `hS`, `f`, the typeclass, `n`, `hn`, `pullback`, both projection equations,
`IsFinite r`, and the explicit uniqueness quantifier. The existential `hX` is the necessary
characteristic witness for the existing `Scheme.iterateFrobenius` declaration; it adds no
mathematical hypothesis and is exactly the pattern used by the recorded one-step
relative-Frobenius interface. No mismatch was found and no node field other than `lean` was
changed.

I checked the dependency declarations directly: `Scheme.IsCharacteristic` includes
primality and vanishing on every open (including the empty scheme); `Scheme.iterateFrobenius`
is identity on points and raises sections to `p^n`; `pullback` has the stated universal
property and projections; `LocallyOfFiniteType f` is the Mathlib finite-type notion; and
`IsFinite r` is the affine-local finite morphism predicate. The proof docstring names every
source and proof dependency and keeps the five DAG proof steps available for stage 3.
The final module compiles cleanly under `scompile.py`, without errors or warnings.
It has exactly one postponed theorem, matching this DAG node, and no definitions.

I repeated the duplicate search in the project and slopmaster2 sources for the item id,
relative Frobenius, and Frobenius finiteness. The only nearby declarations are finite-field
or conditional relative-Frobenius results, so this module is needed. I checked the edge cases
again: `n=1`, identity `X=S`, empty/zero schemes, nilpotents, imperfect bases, and infinite
disjoint unions. The `n=0` case is correctly excluded. The conclusion is neither weakened
(the map is explicitly finite) nor strengthened by adding any geometric hypothesis.

Changes made in this second reading: reconstructed the missing module and node `lean` record
from the retained reviewed statement, recorded the exact normalized signature, and added
this independent review. No correction to the node statement, dependencies, or source was
needed.

The unrestricted `universe u` and `S X : Scheme.{u}` use the standard scheme category's
universe convention; there is no independent smaller test-object universe and no
equality imposed between otherwise independent universes. No index set or zero object
is quantified in this statement. `p = 0`, `p = 1`, and composite `p` are excluded exactly
by the source's primality assumption `hS.1`, while zero section rings are permitted.
The module uses globally recorded notions, no local notation, private definitions, or
local instances; the proof is solely `by sorry`. There are no new definition nodes,
dependency repairs, statement corrections, or citer audits required.

Final mechanical audit: the normalized full theorem signature equals `lean.statement`;
the item differs from the reviewed base only in `lean`; all Lean lines are at most
100 characters; source/blueprint markers are intact; and the only proof body is `sorry`.
The five numbered proof steps and their imports were rechecked after recovery.
