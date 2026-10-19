## Worker report

The delivery states lem-trf-toric-monoid-comparison in
`Sheaf.AlgebraicGeometry.ToricMonoidComparison`, in namespace
`AlgebraicGeometry.Monoscheme`. Five named theorems carry precisely its ideal,
blowup and smoothness assertions. Every theorem proof is `sorry`; definitions
contain actual data or choose an object from an explicit uniqueness theorem.
There is no statement correction and no disputed statement.

The source was read directly: ILO, Travaux de Gabber, Exposé VIII, printed
pp.98–106 (PDF pages 104–112), especially 3.1.17–3.1.23, 3.2.2, 3.2.4,
3.2.9, 3.2.12, 3.2.14–3.2.19. The source is the PDF named in the DAG;
`pdftotext -f 104 -l 112 ... -` read it without creating a literature file.
The full item, all its proof steps, its sole statement dependency and its
recorded 670-line source module were read. No maintenance repair note exists
for this item in `coord/repair-notes`.

Hypotheses and clauses:

* Fine monoschemes with finite affine covers are exactly the recorded
  `Monoscheme.Fine`: `space` is a sheafed monoidal space, its `Chart` uses
  `FineFan.IsFine`, and `finiteCover` supplies a finite cover, allowing n=0.
  `hM : M.IsTorsionFree` is torsion-freeness of every stalk group completion.
  `(k : Type u) [Field k]` and `realization k M` render the field and X=k[M].
  As in the recorded dependency, schemes and monoid data use the same arbitrary
  universe u. This does not bound mathematical sizes: choose a common larger
  universe for both data sets. The rational field is lifted to that universe.
* Clause (i), coherence allowing emptiness, is `IsCoherentIdeal I` in the
  repaired dependency, with a finite local generating list `Fin n` and no
  positivity requirement on n. The map is the dependency's existing
  `ringIdeal k I`, not a second monomial-ideal construction.
  The first conjunct of `toric_ideal_comparison` gives finite generation on
  every affine scheme open and `IsTorusEquivariant k M (ringIdeal k I)`.
  The second gives a unique coherent inverse image for every coherent
  equivariant J; the third explicitly gives injectivity on coherent ideals.
  Ring ideals use `Scheme.IdealSheafData`, the existing quasi-coherent ideal
  sheaves, with affine finite generation expressing coherence here.
* `ringIdeal k (emptyIdeal M) = ⊥` is the empty/zero case. `emptyIdeal` has
  no sections on nonempty opens and the unique section on the empty open,
  as required of a subsheaf; it is not the constantly empty presheaf.
  The fourth quantified clause states
  `ringIdeal k I = ⊤ ↔ I = wholeIdeal M`. Its component clause uses
  `(ringIdeal k I).comap (componentι k C) ≠ ⊥` iff an ideal stalk is
  nonempty at some x with `ConnectedComponents.mk x = C.component`.
  This is nonvanishing on exactly that connected component.
* Component tori and equivariance are the recorded `ToricComponent`,
  `torus`, `componentRealization`, `componentι`, `torusAction` and
  `IsTorusEquivariant`, all on actual components of the given M.
* The final conjunct of `toric_ideal_comparison` quantifies over every
  fine N and every `f : Hom N M`. It states coherence of `pullbackIdeal f I`
  and equality of its ring ideal with the `comap (realizationMap k f)` of
  the original ring ideal. Open localization maps are included; no
  smoothness, flatness or torsion-freeness of N is added to this clause.
* Clause (ii), nonempty on every component, is
  `hI : IsNonemptyCoherentIdeal I`: local finite nonempty generation at
  every point. For a coherent ideal on a fine monoscheme, this is the
  componentwise condition, because every affine monoid chart is connected
  with a generic point and has a smallest neighborhood at each point.
  `toric_blowup_comparison` first supplies a `B : Fine` and `b : Hom B M`
  with the existing `IsSaturatedBlowup b I`. The type Fine already supplies
  fineness and a finite affine cover; `B.IsTorsionFree` states the remaining
  preservation claim, for any supplied representative of that blowup.
* The canonical identification is the unique isomorphism e from
  `realization k B` to `(ringIdeal k I).normalizedBlowup` with
  `e.hom ≫ normalizedBlowupMap = realizationMap k b`. Its inverse is
  the direction displayed in the node. The underlying normalized blowup
  and map are the existing construction, not an existential replacement.
* `IsToricComparison` spells out the additional geometry of this e.
  For each actual component C, `toricActionDomain k C f` is
  T times the inverse image of the component of k[M]. `toricActionBase`
  is the original coaction-defined action after the projection from
  that product. Existence and uniqueness of μ and ν with
  `μ ≫ f = toricActionBase ...` specify the induced torus actions on
  both modifications. The map a has all three projections specified,
  so it is precisely T times the restriction of e. The equation
  `μ ≫ e.hom = a ≫ ν` is torus equivariance.
  The open immersions j and l have domain the original `torus k C`;
  their composites to k[M] equal `torusEmbedding k C`, and j followed
  by e equals l. Their image closures are the respective inverse-image
  components. Thus the original dense torus is unchanged, including its
  embedding, rather than merely replaced by an abstractly isomorphic torus.
* The final blowup clause takes every smooth f:N→M and every saturated
  blowup b' of N along the pulled-back ideal. It supplies the induced
  monoscheme map g over f and scheme normalized-blowup map q. The
  `IsPullback q normalizedBlowupMap normalizedBlowupMap (realizationMap k f)`
  asserts actual smooth base change. For any two canonical comparison
  isomorphisms e,e', `e'.hom ≫ q = realizationMap k g ≫ e.hom` is the
  naturality square. This includes localizations, which are smooth with
  isomorphic stalk maps, and identities and composites, since each
  comparison is unique over its base. No normalization under arbitrary
  base change is asserted.
* Clause (iii), first sentence, is the separate `realizationMap_smooth`:
  arbitrary fine N,M, a `Hom N M` and `hf : f.IsSmooth` imply
  `Smooth (realizationMap k f)`. No torsion-freeness is imposed here.
* The converse is `isSmooth_of_realization_smooth`: for torsion-free M,
  `Smooth (realizationToBase k M)` implies the recorded `M.IsSmooth`.
  The rational consequence is `isSmooth_of_rational_realization_regular`,
  with `IsRegularScheme (realization (ULift.{u} ℚ) M)` and exactly the
  conclusion that every actual stalk is multiplicatively equivalent to
  `Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)` for natural r,t.
  Multiplicative notation is the additive direct sum of the node;
  no sharpness or zero unit rank is imposed.

Dependency declarations used: all the monoscheme objects, ideals, pullbacks,
realization, torus and saturated blowup notions above are from
`Sheaf.AlgebraicGeometry.MonoschemeToricRealization`; their monoid stalks and
chart saturation are `FineFan.stalk`, `FineFan.saturatedChart`,
`FineFan.chartInclusion` from `Sheaf.AlgebraicGeometry.FineFanBlowup`.
The normalized scheme objects/maps are
`Scheme.IdealSheafData.normalizedBlowup` and `normalizedBlowupMap` from
`Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`, already imported by the
dependency. `Smooth` is Mathlib's scheme smoothness, and `IsRegularScheme`
is the recorded scheme regularity notion, already imported there too.
All recorded proof dependency modules are imported: affine blowup chart
cover, affine monoid algebra normalization, finite saturation, smooth
geometric normality, finite birational normal isomorphism, face sharpening,
finite-type domain dimension and regular-perfect-field smoothness. Mathlib
provides the finite free group and regular local cotangent inputs through
the explicitly imported PID/cotangent/dimension modules (PID is imported by
the normalization module). The source-local smoothness lemma is in the
smoothness imports. No proof dependency import is omitted for a cycle.
Legacy imports are retained because the recorded monoscheme and fan modules
are legacy files, as their published record expressly notes.

Edge cases checked before writing and on rereading: empty monoscheme and
empty finite cover; zero generators and the empty-open section of the empty
ideal; zero and unit ring ideals; ideals zero on only some components;
disconnected components with different torus ranks; n=0 and zero-rank monoid
or lattice factors; arbitrary characteristic, including positive
characteristic; nonsaturated monoids such as the cusp monoid; unit-ideal
saturated blowup (it is saturation/normalization and need not be identity);
identity and composite pullbacks; localization maps; smooth morphisms
between fine monoschemes with torsion. There is no separatedness or
saturation hypothesis on M, and the last rational clause uses full regular
scheme structure. The comparisons are over the original base, which pins
them even in the nonsaturated unit-ideal case.

Searches performed (all against the prescribed read-only sources):

* `msearch.py NN lem-trf-toric-monoid-comparison leanfinder` with
  "The toric realization of a fine torsion free monoscheme identifies
  coherent monoid ideals with torus equivariant ideals and saturated
  blowups with normalized blowups": 8 hits, on Proj/Spec formulas,
  normalization and ordinary localization diagrams; no statement of
  this comparison or monoscheme realization functor.
* `msearch.py ... loogle 'MonoidAlgebra, Ideal, Smooth'`: 0 hits,
  unknown identifier Smooth in that service's query context.
* `msearch.py ... grep 'Monoscheme|toric.*(blowup|smooth)|equivariant.*ideal'`:
  0 Mathlib hits.
* `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `Monoscheme|toric.*(blowup|smooth)|lem-trf-toric-monoid-comparison`:
  no hits. Broader comparison-name search found unrelated monoidal
  category comparisons, not monoscheme geometry.
* `rg` in `lean/Sheaf/AlgebraicGeometry` for `IsCoherentIdeal`,
  `realizationMap`, `toric_monoid_comparison`, `torusEmbedding`: no
  prior declarations. The recorded dependency was read fully: it
  gives only `IsNonemptyCoherentIdeal` and no realization-on-morphisms
  or dense torus embedding, which is the reason for the repair below.
* `dag/lean_names_upstream.json` was included in the comparison-name
  search; no existing declaration of this node was found.

Validation: scompile.py compiled both delivered modules separately, in
dependency order. The first run found only an unused set-builder variable
in emptyIdeal; it was renamed `_s`. The final clean compile and deliver2
preflight are recorded below when completed.

## Dependency modules

`def-trf-monoscheme-toric-realization`: the existing module's interface was
insufficient for its full stated notion: it provided only nonempty coherent
ideals, no functorial realization map, and no actual dense torus embedding.
Under §1(B), the sandbox copy preserves all 71 published declarations and
appends eight declarations: `IsCoherentIdeal`, `emptyIdeal`,
`Hom.sectionMap`, `IsRealizationMap`, `existsUnique_realizationMap`,
`realizationMap`, `existsUnique_torusEmbedding`, `torusEmbedding`.
Coherence is the same local finite-generation condition as before, allowing
zero generators. The section map is the actual sheaf-map component followed
by restriction. The induced scheme map is pinned on all incident affine
charts by Spec of that section map's monoid algebra map. It is chosen only
from its explicit existence-and-uniqueness characterization. Similarly the
torus embedding is pinned on every component affine chart by Spec of the
existing degree map, i.e. localization to the generic lattice. These are
parts of the dependency's already stated construction, not independent new
notions. Both postponed obligations are named, documented theorems with
the dependency's blueprint id and complete gluing proofs. Only the node's
lean field changes, with the required explanation in lean.note.

## Second reading by NN

A separate rereading pass in this worker compared the complete node text
and all five theorem signatures, the three comparison helper definitions,
and the eight appended dependency declarations. No other agent was started,
as the dispatcher explicitly forbids that; the maintainer's independent
review remains the independent reading of this delivery.

The pass verified each correspondence listed above, in particular the
otherwise easy-to-drop arbitrary pullback in (i), zero ring ideal, component
nonvanishing, unit ideal over a nonsaturated base, smooth pullback square,
unchanged dense torus with equivariance, arbitrary torsion in the first
smoothness assertion, and both finite ranks in the rational conclusion.
The only compiler finding was the unused emptyIdeal section binder; naming
it `_s` fixes the warning without changing its predicate. No mathematical
statement or previously published dependency declaration was altered.
