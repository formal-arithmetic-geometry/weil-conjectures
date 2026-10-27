## What changed

The item theorem `finitePerfectAdic_actual_level_descent` now has a complete
assembly proof. It constructs the objects, bounds, finite locally constant
homology and geometric-stalk markings using the new proved theorem
`finitePerfectAdic_marked_origin`, obtains arrows and actual realizations from
one remaining transition lemma, and supplies coherence using the existing proved
`etaleNormalization_coherence`. Its statement and the descent structure are unchanged.

`FinitePerfectAdicMarkedOrigin` defines the fixed-scalar coordinates of the actual
quotient by an explicit composite of existing exact functors. From a marking
cover, its proof descends finite homology sheaves, invokes bounded truncation
induction, retains the comparison isomorphism, reflects bounds and lisse
cohomology, and constructs the inhabited Isom stalk using a lifted geometric
point and the comparison adjunction. This is genuine Lean proof, including the
local-to-global boundedness and stalk construction; there is no new sorry in it.

The unclaimed existing `FinitePerfectAdicActualLevelObjects` theorem is also
proved as a weaker consequence of this construction. Its only change besides
the proof is replacing its private proof import. All its signatures and public
imports remain identical. Its unchanged sole direct importer
`FinitePerfectAdicActualLevels` is compiled against this delivery and its temporary
sandbox copy was removed afterwards. All five modules compiled cleanly remotely: marked
origin 20.8 s, auxiliary objects 3.7 s, transition statement 5.1 s, unchanged
ActualLevels importer 6.7 s, and the item 11.5 s.

The remaining `FinitePerfectAdicCoordinateTransitions` statement starts with
specified bounded-below etale origins and specified isomorphisms to the actual
quotients. It only descends their consecutive maps and realizes them compatibly
with the strict tower. It does not supply object existence, lisse cohomology,
finite bounds or stalk markings. These are now constructed in the proved module,
so this is the arrow/realization part of the argument, not a renaming of the
original existence statement. Its docstring supplies the tensor-pullback,
full-faithfulness and scalar-compositor proof in words.

The unit route is unchanged. The finite-model sheaf descent theorem used as a
tool is `lem-sf-proetale-origin-from-finite-models` (unit sk-prop-sf-comparison);
this does not replace any realized step of the proper-base-change unit.

## Proved and sorry left

Closed existing bodies:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_actual_level_objects`: proved using
  the proved retained-origin construction; no replacement object-existence hole.
- `AlgebraicGeometry.Scheme.finitePerfectAdic_actual_level_descent`: complete
  assembly from the proved object/stalk construction and the remaining arrow
  step. This closure is a decomposition, not a claim of a complete proof of the
  original theorem without sorry dependencies.

Added proved theorem:
`AlgebraicGeometry.Scheme.finitePerfectAdic_marked_origin`.

One hole added and left in this packet:
`AlgebraicGeometry.Scheme.finitePerfectAdic_descend_coordinate_transitions`, node
`lem-weil-pbc-finite-perfect-adic-coordinate-transitions`. Its proof is exactly
`by sorry` in its own new module. The item and the auxiliary object module have
zero textual holes. Across the changed modules, two old holes are closed and one
strictly smaller hole is added: net one hole closed, plus one decomposition.
No definition contains sorry or chooses data from an unproved mere existence.

## No longer needed

The direct proof route no longer uses
`lem-weil-pbc-finite-ring-constructible-derived-origin` or its module
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`: the marked finite homology
models give a shorter application of the existing finite-model heart descent and
bounded-heart induction. Its private import is removed from
`FinitePerfectAdicActualLevelObjects`, and both affected node proof-dependency
lists are updated.

The parent proof now cites the two new steps and general etale-normalization
coherence. Its old derived scalar-extension and ringed-topoi tensor-pullback
proof dependencies belong to the new transition node's remaining proof plan.
The scalar-coherence theorem is used in that statement and its remaining plan.
No unnecessary private imports of these unimplemented proofs are retained.

The proof does not use `finitePerfectAdic_actual_levels`,
`finitePerfectAdic_actual_level_stalk` or
`finitePerfectAdic_actual_level_transitions`. The original public ActualLevels
import is retained because the item statement uses its data structure. Thus these
modules still occur in the library import closure: no global withdrawal or module
pruning is claimed. No DAG node or source-library declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The original plan's constructible-derived-origin theorem alone does not retain
the needed comparison with the actual quotient. Constructing fixed-scalar
coordinates first, and retaining the isomorphism throughout homology descent,
resolves that gap without choosing an unrelated etale origin.

STATEMENT-DISPUTED: the existing `finitePerfectAdic_actual_level_stalk` claims
Isom stalks for arbitrary supplied K, without requiring a comparison to the
actual marked quotient. Taking K=0 and a nonzero constant marked model shows why
that claim cannot be used. Likewise
`finitePerfectAdic_actual_level_transitions` quantifies over arbitrary K and
claims universal consecutive arrows; a zero source and nonzero next quotient
need not admit a universal such arrow. These declarations are not used in the
proof terms of this delivery. They are reported here for their owners; their
signatures are not weakened or changed in this packet.

The new coordinate-transition hypothesis is the missing actual comparison: it
relates every supplied K_n to the actual quotient. Boundedness is restricted to
these origins, so the lemma does not assume M itself is bounded. The construction
was checked conceptually on empty charts, zero coefficient rings and zero
complexes; these require no additional nonemptiness assumptions.

## New nodes

`lem-weil-pbc-finite-perfect-adic-marked-origin` records the explicit quotient
coordinates and the proved retained-origin/stalk construction. Its proof follows
Stacks Tags 09AL, 09B1 and the finite quotient step of 09C6, with explicit local
homology and geometric-fiber arguments.

`lem-weil-pbc-finite-perfect-adic-coordinate-transitions` records only the
remaining descent of arrows and compatible scalar realizations between specified
origins. Its source is the arrow and balancing step of Tag 09C6, using 09AL and
06YY. Both new records include logged genuine Mathlib searches of multiple kinds.

Change record: `coord/changes/K3-finite-perfect-adic-retained-origin.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicActualLevelDescent": "d6543634fb5b652d2550cf6a14eb2fdc80e874fb", "Sheaf.Paper.FinitePerfectAdicActualLevelObjects": "0dcdd4cefe00c68d24635f9d369b31081660e547", "Sheaf.Paper.FinitePerfectAdicCoordinateTransitions": "ff468404bd83454e0b40eae5df88c6e287c5cc4f", "Sheaf.Paper.FinitePerfectAdicMarkedOrigin": "8ebc1a05a6918a08be591623f171fddffb881382"}, "results": {"Sheaf.Paper.FinitePerfectAdicActualLevels": {"hash": "1c3131a76896c3bbb141c94ecf5c492b4a8f2048", "status": "OK"}}, "seconds": 36, "time": "2026-10-28T06:32:26+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
