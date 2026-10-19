## Worker report

The module `Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne` states
`AlgebraicGeometry.normal_modification_codimension_one`, with its entire proof `sorry`.
It introduces no new definition. The theorem docstring records all eight proof steps of
this node, with the same dependencies. I read the statement and complete proof of Stacks
Project, Varieties, Tag 0BFP in `literature/stacks-project/varieties.tex`, starting at
`lemma-modification-normal-iso-over-codimension-1`. The statement agrees with the source,
including clause (4). No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:

- The schemes are `{X Y : Scheme.{u}}`, and the given morphism is `(f : Y ⟶ X)`.
- Noetherian means `[IsLocallyNoetherian X] [CompactSpace X]`. The first is the recorded
  locally Noetherian notion; the second is topological quasi-compactness (every open cover
  has a finite subcover). No separation or integrality hypothesis is imposed on `X`.
- Properness is `[IsProper f]`, and reducedness of the source is `[IsReduced Y]`.
- Bijectivity of the map on generic points of components is
  `hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X)`. Mathlib's `genericPoints`
  is the set of points whose singleton closure is an irreducible component; its
  `genericPoints.isGenericPoint` gives the dependency's `IsGenericPoint` relation.
  `Set.BijOn` includes that generic points map to generic points, injectivity on them,
  and surjectivity onto those of `X`.
- The isomorphisms on their local rings are
  `hstalk : ∀ y ∈ genericPoints Y, IsIso (f.stalkMap y)`. These are the actual local
  homomorphisms induced by this `f`, rather than arbitrary isomorphisms of stalk rings.
- The given maximal open is `(U : X.Opens)`, with `hU : IsIso (f ∣_ U)` and
  `hmax : ∀ V : X.Opens, IsIso (f ∣_ V) → V ≤ U`. Thus `U` is itself an isomorphism
  open and contains every such open. These binders unpack the source's given maximal
  open; the theorem does not replace it by a smaller neighbourhood.
- Clause (1) is the first conjunct:
  `∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0 → x ∈ U`.
- Clause (2) is the second conjunct: for any `x`, the binders
  `[IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]`
  express the dependency's DVR notion, and
  `ringKrullDim (X.presheaf.stalk x) = 1 → x ∈ U` supplies precisely the codimension-one
  condition and membership conclusion. The domain binder is required by the DVR class.
- Clause (3) is the third conjunct: `IsDomain (X.presheaf.stalk x)` and
  `IsIntegrallyClosed (X.presheaf.stalk x)` express normality of this local ring;
  `(f ⁻¹' {x}).Finite` is finiteness of the underlying fibre; the conclusion is `x ∈ U`.
  The source explicitly uses normal domain for the stalk. For a local ring its normal-ring
  condition is equivalent to being a normal domain, as the normal-ring record prescribes.
- Clause (4) is the fourth conjunct: the same normal-local-ring hypotheses and
  `∃ y : Y, f y = x ∧ f.IsQuasiFiniteAtPoint y` imply `x ∈ U`. This uses exactly the
  recorded Stacks quasi-finite-at-a-point predicate, including the finite-type condition.
- In both codimension clauses `ringKrullDim` is the recorded Krull dimension of the actual
  local ring, not a dimension of a chosen affine neighbourhood or of its closure.

Dependency declarations used in the signature (their full definitions/signatures and
source docstrings were read):

| Node | Module | Declaration |
| --- | --- | --- |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsReduced |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint, via genericPoints and genericPoints.isGenericPoint |
| def-weil-locally-ringed-space-morphism | Mathlib.Geometry.RingedSpace.LocallyRingedSpace | AlgebraicGeometry.LocallyRingedSpace.Hom, via Scheme.Hom.stalkMap |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic | IsDiscreteValuationRing |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsDomain and IsIntegrallyClosed, the prescribed normal-domain inline form |
| pqf-def-quasifinite | Sheaf.AlgebraicGeometry.QuasiFiniteMorphism | AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |

The public imports provide the signature's notions. The nonpublic imports preserve the
available proof dependencies: spreading out and injective germs, function fields, affine
stalk localization and local-spectrum morphisms, proper and finite morphism properties,
finite integral algebras, PID normality, and the two quasi-finite localization/subalgebra
lemmas. The proper-finite-fibre module was read with `scompile.py --source
WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`, because it is missing from
the older local source checkout. The two genuinely unstated proof dependencies
`lem-per-birational-isomorphism-dense-open` and
`lem-per-generically-finite-proper-near-dimension-one` have no recorded modules to import;
they are explicitly identified in the proof docstring and are not needed to type the
statement. No statement dependency needs a new interface or a replacement module.

Edge cases checked:

- An empty target admits no source points under `f`; every conclusion is vacuous. No
  `Nonempty` assumption on either scheme or generic-point set was introduced.
- A nonempty target cannot receive an empty-source birational map, because `Set.BijOn`
  requires surjectivity on generic points. No extra fibre-nonemptiness hypothesis is used.
- Reducible targets and sources are retained: `genericPoints` and `Set.BijOn` quantify over
  all components, and there is no `IsIntegral` hypothesis.
- Nonreduced targets are retained. Only `Y` is required to be reduced. Omitting source
  reducedness would be false (embedded nilpotents over a closed point can survive a
  generically isomorphic proper map), so the hypothesis is retained.
- Normality is assumed only at the point in clauses (3) and (4), and a quasi-finite point
  above `x` is existential, not a universal quasi-finiteness requirement on the fibre.
- Finite fibres include the empty set in clause (3); surjectivity follows from the other
  hypotheses in the proof, so it must not be added as a separate assumption.
- Fields are excluded by the DVR dependency itself; dimension zero and one are kept
  separate. No closed-point or regularity requirement has been added.
- The single explicitly bound universe `u` applies to arbitrary schemes of that size.
  There is no smaller universe of test objects that could make a hypothesis vacuous.

Searches for an existing statement or notion:

1. `msearch.py`, LeanFinder: “A proper birational morphism of schemes with reduced source
   and noetherian target is an isomorphism near generic points, DVR points of codimension
   one, and normal points with finite fibre or a quasi-finite preimage”. Eight hits, all
   integral morphisms or normalization constructions; none states the four-clause result.
2. `msearch.py`, Loogle: `AlgebraicGeometry.IsBirational,
   AlgebraicGeometry.Scheme.Hom.isIsoLocus, AlgebraicGeometry.IsProper`. Zero hits;
   `AlgebraicGeometry.IsBirational` is unknown. No declaration match.
3. `msearch.py`, grep in `AlgebraicGeometry`:
   `IsBirational|isIsoLocus|birational|isomorphismLocus`. Eight hits in Mathlib's
   Birational modules. `Scheme.Birational` concerns existence of a partial isomorphism
   between schemes, not componentwise birationality of this specified morphism or 0BFP.
4. `msearch.py`, LeanSearch: “A proper birational morphism with reduced source over a
   noetherian scheme is an isomorphism near normal points where a source point is quasi
   finite”. Eight hits, namely the ordinary quasi-finite/proper predicates and normalization
   operations. None is the requested theorem.
5. `rg` in `WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` with
   `IsBirational|isIsoLocus|birational|isomorphismLocus`: the existing proper-birational
   curve and finite-normal isomorphism statements are narrower (integral curves or finite
   maps). `IsBirationalQuasiModification` requires an integral source and does not define
   this general componentwise notion. No matching statement was found.
6. Exact item-id search in upstream `WeilConjectures` and `lean/Sheaf` found no module for
   this node. Searches for `isIso_of_proper_birational|normal_modification_codimension_one`
   in the source, project modules and `dag/lean_names_upstream.json` found no collision.
7. Mathlib source search found the existing `genericPoints` definition in
   `Mathlib.Topology.Sober`; its source and `Set.BijOn` were read and used directly.
   No new birationality or maximal-open definition is necessary: their conditions are
   inline hypotheses on the given morphism and open.

Validation: `scompile.py N9 lem-per-normal-modification-codimension-one` compiled the delivered
file both as sandbox and library module (2.8 s and 2.5 s), without errors or warnings.
Every variable and universe is explicit; all lines in the Lean file are at most 100
characters. The node copy changes only `lean`; the statement is copied verbatim from the
file's theorem signature. There is no maintenance repair note for this item and no matching
entry in the group's returns. The prior worker's gate failure concerned the already
split/reviewed stage-1 record; this packet adds the previously absent Lean record and module.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
