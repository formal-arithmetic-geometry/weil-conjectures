## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource`
states `AlgebraicGeometry.locallyOfFiniteType_of_flat_lfp_source`, with its entire
proof postponed by `sorry`. It introduces no definitions or helper theorems.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

| Node text | Lean |
| --- | --- |
| Schemes X, Y, S | `{X Y S : Scheme.{u}}`, with explicitly declared `universe u` |
| Morphism q : X → Y | `(q : X ⟶ Y)` |
| q flat | `[Flat q]` |
| q locally of finite presentation | `[LocallyOfFinitePresentation q]` |
| q surjective on underlying points | `[Surjective q]`; the class field is `Function.Surjective q` |
| Morphism h : Y → S | `(h : Y ⟶ S)` |
| h composed with q locally of finite type | `[LocallyOfFiniteType (q ≫ h)]` |
| h locally of finite type | conclusion `LocallyOfFiniteType h` |
| No quasi-compactness or separation restrictions | No such binders, including no affine, Noetherian, nonempty, or base-field restriction |

The source was read in `literature/stacks-project/descent.tex`, lines 4352–4417:
Tag 02KL is the arbitrary commutative source triangle, and its locally finite type
alternative is exactly this statement; Tag 0367 is its ring-algebra input.
The declaration docstring records all seven proof steps and their node citations.

Dependency declarations read and used directly:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Flat.iff_flat_stalkMap` identifies its affine-pair definition with the dependency's
  stalkwise definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the recorded affine-local notion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, using the dependency's recorded match.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.

Proof dependencies with Mathlib declarations are made available by non-public imports:
`AffineScheme` (affine-open basis and compactness), `RingHomProperties` (pointwise
criterion), `UniversallyOpen` (flat lfp openness), `QuasiSeparated` (the affine
quasi-separatedness clause), `Limits` (scheme coproducts and finite product spectra),
and `RingTheory.Flat.FaithfullyFlat.Basic` (faithful flatness criterion). The affine-pair
criteria already occur in the public statement imports. At the time of writing,
`lem-a1-finite-type-fppf-source-algebra` has neither a Lean record nor a Mathlib match;
it is only a proof dependency, requires no notion for this signature, and is therefore
not imported. It remains explicitly named in the proof docstring.

Edge cases checked before writing:

- Empty Y: the local criterion is vacuous; the theorem includes it.
- Empty X: surjectivity forces Y empty, again a valid case. No Nonempty instance is required.
- Identity q: all cover properties hold, and the conclusion agrees with the composite premise.
- Non-quasi-compact q, including an infinite disjoint union of copies of Y onto Y:
  the signature still applies. Finite selection is only over each affine target neighbourhood.
- Nonseparated schemes and morphisms are allowed. No intersection of affine opens is
  assumed affine in the proof outline.
- Zero affine chart rings: the faithful-flatness criterion used in the outline has
  a vacuous maximal-ideal condition. There is no nontriviality or characteristic binder.
- The scheme universe u is arbitrary and explicitly bound, matching Mathlib's category
  of schemes; there is no independent test-object universe or smallness condition.

Searches made on 2026-10-18:

1. `msearch.py ... leanfinder` with query “A scheme morphism is locally of finite type
   if its composite with a flat surjective locally finitely presented source morphism
   is locally of finite type”: eight hits, headed by `locallyOfFiniteType_of_comp`.
   Read its signature: it concludes local finite type of the FIRST arrow, not h.
2. `msearch.py ... loogle` with query `"LocallyOfFiniteType", "Flat", "Surjective"`:
   one hit, the fpqc `DescendsAlong` instance in `LocalFlatDescent`.
3. `msearch.py ... leansearch` with query “Locally finite type descends along a flat
   locally finitely presented surjective map on the source”: eight hits, including
   the fppf `DescendsAlong` instance in `FlatDescent` and the definition constructors.
   Read `DescendsAlong.of_isPullback`: it assumes a cartesian square and concerns
   base descent, whereas our input is an arbitrary source triangle.
4. `msearch.py ... grep` of AlgebraicGeometry with query
   `locallyOfFiniteType.*(of_comp|surjective|flat)|LocallyOfFiniteType.*(of_comp|surjective|Flat)`:
   two hits, the first-arrow theorem and the same base-descent instance.
5. `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for local finite type,
   composition, descent and source: no exact source-triangle theorem found.
   Read upstream `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`;
   its declarations concern sections, dimension, or composition over a base.
   Read side `Sheaf/AlgebraicGeometry/Morphisms/LocallyOfFiniteTypeOfFpqcCover.lean`:
   it assumes finite type of pullback projections and states base-cover descent.
6. `rg` for this item id in upstream `WeilConjectures`: no match.
   `dag/lean_names_upstream.json` mentions `AlgebraicGeometry.locallyOfFiniteType_of_comp`,
   the first-arrow theorem checked above.
7. Exact-name `rg` for `locallyOfFiniteType_of_flat_lfp_source` in Mathlib, upstream
   `WeilConjectures`, and side `lean/Sheaf`: no collision.

No statement dispute, source defect, dependency repair, or new node was needed.

## Second reading by Q27

Author self-check under the direct-dispatch brief; an independent reading belongs to
the maintainer's review. No second worker or sub-agent was started.

Reopened the node and module together: the argument order q then h makes `q ≫ h`
precisely h composed with q. The three cover assumptions attach to q only, and the
finite-type premise attaches to the composite only. The conclusion is local finite
type of h. The four recorded statement dependency declarations are used directly.
No quasi-compactness, separation, affineness, Noetherian condition, nonemptiness,
field, or implicit universe hypothesis has been inserted. All variables and the
universe are explicitly bound. There is exactly one theorem with exactly one sorry;
there are no definitions to hide data. The proof outline retains the finite affine
selection and faithful-flatness steps, including the empty and zero-ring cases.
No mismatch was found and no mathematical correction was made.

## Validation

`scompile.py Q27 lem-a1-lft-flat-lfp-source-descent` compiled the delivered module
successfully (exit 0), with no compiler diagnostics. A JSON comparison confirms that
only the item's `lean` field changed. Every Lean line is at most 100 characters.

The first delivery dry run found that its signature reader excludes the terminating
`:=`; removed that delimiter from `lean.statement` to match the reader exactly.
The Lean module and its mathematical statement did not change.
