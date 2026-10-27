## Worker report

The module `Sheaf.AlgebraicGeometry.RegularSchemeStalkCriterion` states
`AlgebraicGeometry.isRegularSchemeMorphism_iff_stalkMap`, with a single `sorry`.
No definition, dependency interface, or mathematical statement was changed.

Hypothesis and clause correspondence:

- “A morphism f : X → Y of schemes” is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The explicit universe `u` is arbitrary.
- “Locally Noetherian schemes” is `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]`.
  Both hypotheses are retained; neither global Noetherianity nor finite type is assumed.
- The induced local homomorphism O_{Y,f(x)} → O_{X,x} is exactly
  `(f.stalkMap x).hom`. `Scheme.Hom.stalkMap` is the map inherited from the morphism
  of locally ringed spaces, and its `IsLocalHom` instance is already supplied by Mathlib.
- “f is a regular scheme morphism” is `IsRegularSchemeMorphism f`.
- “if and only if” is `↔`, retaining both directions.
- “a regular ring map for every x in X” is
  `∀ x : X, (f.stalkMap x).hom.IsRegular`. This uses the existing ring-map predicate
  directly, without introducing a new algebra structure or selecting another stalk map.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Hom.stalkMap` (whose full signature and docstring were read).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  the every-affine-open form equivalent to the node's affine-cover definition.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, inherited by `Scheme.Hom`, including
  its locality field; also read the recorded `RingedSpace` and `PresheafedSpace.Hom`.
  These scheme and locally ringed space modules are already public transitive imports.
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`:
  `AlgebraicGeometry.IsRegularSchemeMorphism`. Its definition is flatness together with
  regularity of every residue-field fibre after each finite field extension.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular`. Its definition is flatness
  and Noetherian geometrically regular prime fibres. The same module's
  `Algebra.IsGeometricallyRegular` tests finite purely inseparable field extensions.

Already stated proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.AffineScheme`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
`WeilConjectures.RingTheory.RegularLocalMaximal`, and
`WeilConjectures.RingTheory.RegularRingEquiv`. No module is yet recorded for the
proof-only node `lem-per-regular-morphism-affine-criterion`, so there is no import
for that node. Its mathematical role is preserved explicitly in the proof docstring.
The proof follows all three node steps: identify the germ/fraction square, localize
regular affine-chart maps, and conversely recover chart regularity from all stalks.
The locally Noetherian affine-section result and affine basis come from the imported
Noetherian and AffineScheme modules.

Source checked directly in `literature/stacks-project/more-morphisms.tex`,
`lemma-regular` (07R8), and `more-algebra.tex`, `lemma-regular-local` (07C0).
The former identifies geometric-fibre regularity with the affine-chart criterion;
the latter compares a ring map with all target-prime localizations when its target
is Noetherian. The node accurately cites their combination, not an explicit stalk
clause in 07R8. The current blueprint unit `_section.md` was also read.

Edge cases checked before writing:

- Empty X: the universal point condition is vacuous, as are the fibres; the unique
  morphism from the empty scheme is flat, so this case is retained.
- Identity and open immersions: their stalk maps are isomorphisms, hence regular;
  the scheme morphisms are regular. No surjectivity condition is added.
- Spec(k) → Spec(k[ε]/ε²): the local map is not flat, so both sides fail.
- A nontrivial finite purely inseparable field extension: the map is flat but its
  geometric fibre is nonreduced. Both regularity predicates reject it; the statement
  has no characteristic restriction and keeps geometric, rather than ordinary, regularity.
- Non-quasi-compact locally Noetherian schemes remain included: no global finiteness
  assumption is present.

Searches for an existing statement (the launcher also records the exact responses
in `searches.jsonl`):

- `msearch.py ... leanfinder`, query “A morphism of locally Noetherian schemes is
  regular if and only if its homomorphism on every stalk is a regular ring map”:
  eight hits, including `HasRingHomProperty.of_stalkMap`, `.stalkMap`, and `stalkwise`.
  These are general infrastructure, not the requested regularity equivalence.
- `msearch.py ... loogle`, query
  `AlgebraicGeometry.IsRegularSchemeMorphism, RingHom.IsRegular`: zero hits;
  the project predicate is unknown to the service index.
- `msearch.py ... grep`, query
  `IsRegularSchemeMorphism|isRegular.*stalk|IsRegular.*stalk|regular.*stalkMap`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch`, query “A morphism of locally Noetherian schemes is
  regular if and only if all induced maps on stalks are regular ring maps”:
  eight hits. `Flat.iff_flat_stalkMap` states only flatness; other hits give the
  actual stalk map or generic stalkwise machinery. None states this theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `IsRegularSchemeMorphism|isRegularSchemeMorphism_iff|regular.*stalkMap|stalkMap.*IsRegular`:
  finds the definition and consumers, but no equivalence. In particular,
  `ResolutionStrata.regular_pullback_geometry` gives one direction with extra reduced,
  Noetherian and quasi-excellence hypotheses, so it is not an exact existing match.
- `rg` in `lean/WeilConjectures` for the exact node id: no occurrence.

No statement dispute, correction, new node, or dependency repair is needed.

## Second reading by Q05

The dispatcher forbids starting other agents, so this is a separate rereading by
this worker, not a claim of an independent agent review. The maintainer performs
its independent review after delivery.

Reopened the node and final module and checked every clause: the arbitrary scheme
morphism and both locally Noetherian hypotheses are explicit; the left side uses
the recorded regular-scheme predicate; the right side quantifies over every source
point and uses the canonical stalk homomorphism and the recorded ring regularity
predicate. The equivalence retains both implications. There is no extra finiteness,
characteristic, surjectivity, regularity of X or Y, or choice of chart. The proof
docstring retains each of the node's three steps and its empty-source case.
No mismatch or correction was found. The node copy differs only in `lean`.
