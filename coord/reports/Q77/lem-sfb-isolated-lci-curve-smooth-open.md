## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen`, with main
statement `AlgebraicGeometry.ProperCurveModuli.exists_isolated_lci_curve_smooth_open`.
Its only theorem proof is `sorry`. The helper `IntegerSchemePointIn` is a real
Prop-valued definition, not a chosen classifying map or an arbitrary family.

Q75's existing delivery was a stage-1 split and review, not a Lean statement. The
base item has no `lean` record. This packet supplies that missing record and one
module; it does not redeliver Q75's unchanged node. There is no repair note for
the item. The natural-language statement and proof are unchanged.

Clause-by-clause correspondence:

* Schemes over Spec Z are `Over (Spec (.of (ULift.{u} ℤ)))`. The universe lift is
  Mathlib's standard universe-polymorphic integers; `specULiftZIsTerminal.from`
  supplies the unique structure map of each field spectrum. No characteristic
  or choice of a noncanonical field-to-base map is assumed.
* The groupoid C is the existing `ProperCurveModuli.category`. Its objects keep
  `ProperCurveFamily.space : AlgebraicSpace S` and their projections. Its
  `IsProperCurveFamily` explicitly tests flatness, locally finite type and locally
  finite presentation on etale scheme charts, quasi-compactness on affine tests,
  properness by closed diagonal and universally closed point maps, and
  quasi-separatedness by quasi-compact diagonal. It bounds the dimension of all
  algebraically closed field base changes by one. The total category's arrows
  are `IsPullback` squares of presheaves, hence precisely isomorphisms to base
  changes, and the fibre arrows are base-preserving isomorphisms.
* The hypothesis that C is algebraic is `halgebraic : IsAlgebraicModuliStack ...`:
  stack descent, algebraic-space diagonal, and an actual smooth surjective scheme
  atlas. Smoothness is checked on the space base changes of that specified atlas.
* Existence of L as a full open substack is `∃ L : OpenModuliSubstack ...`.
  `OpenModuliSubstack.open_pullback` represents every scheme test by an open
  immersion, compatibly with its projection; its predicate is pullback stable.
* Smooth over Z is `IsSmoothModuliStack L.category`: a smooth surjective atlas
  whose composite `U.hom` to the same integer base is smooth. The atlas is the recorded `IsSmoothModuliAtlas`, using `SpaceMapIsSmooth`
  on every etale chart and the specified 2-base-change projection.
* Every field, proper scheme and dimension bound are exactly the binders
  `(K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K))`,
  followed by `IsProper f → topologicalKrullDim C ≤ 1 →`.
* Belonging to L is `IntegerSchemePointIn L K C f`. It asks for a family over
  Spec K isomorphic to the represented scheme, with the projection equation over
  that field, whose total object satisfies `L.property`. This is membership of
  the classifying object, retaining automorphisms, not membership of an arbitrary
  isomorphic underlying space with a different structure map.
* The iff is literal `↔`. The first right conjunct gives an affine open cover
  indexed by `I : Type u`, with rings `A i`, specified `Algebra K (A i)` and
  `Algebra.FiniteType K (A i)`, open immersions from their spectra, the equations
  saying these are K-morphisms, pointwise coverage, and the recorded
  `Algebra.IsLocalCompleteIntersection` for every chart.
* The second right conjunct is `∃ S : Set C, S.Finite ∧ ∀ x ∉ S, ...` with an
  open neighborhood whose restricted structure map `U.ι ≫ f` is smooth. This is
  precisely smooth except at finitely many points; it adds no requirement that
  the chosen exceptional set consist of closed points.
* Empty and disconnected schemes remain allowed: neither the moduli object nor
  the theorem imposes nonemptiness, connectedness, integrality, reducedness or
  pure dimension. Universe `u` is explicitly declared and autoImplicit is
  false in the module. Fields, schemes and chart indices are in the universe
  of the existing big site, not a smaller independently quantified universe.

Dependencies read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections, used through the recorded geometric-fibre and family interfaces.
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, with empty dimension ⊥.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, scheme-test
  `IsRepresentableWith`, `IsEtale`, the etale site and the fppf-sheaf objects.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.FiniteType`,
  `.Proper`, `.Smooth`: `Flat`, `LocallyOfFinitePresentation`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsProper`, `IsSeparated`, `UniversallyClosed`, `Smooth`.
* `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection`, `Algebra.IsLocalCompleteIntersection`.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`,
  `ProperCurveModuli.category`, `AlgebraicSpace.IsProperCurveFamily`.
* `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`, `.category`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`, `SpaceMapIsSurjective`,
  `discreteModuli`, `ModuliTwoIso` and the actual 2-fibre-product projections.
* `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`.
* Proof imports are the recorded
  `Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme` and
  `WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension`.
  The other five proof dependencies have no Lean record in the read base; they
  remain named in the full six-step proof docstring and are not invented imports.

The three added statement-dependency ids for proper curve moduli, open substacks
and algebraic moduli stacks already exist and have landed Lean records and modules. They expose the same concrete notions
used by the statement, without private copies. The size convention is implemented
by explicit universe levels and the existing site interface.

Edge cases checked: the empty scheme admits the empty affine cover and S empty;
a disconnected union has no extra connectedness condition; zero-dimensional and
nonreduced lci components are permitted; smooth curves use S empty; a curve with
a positive-dimensional nonsmooth locus fails the finite-exception condition; an
isolated singularity which is not lci fails the affine-cover conjunct. Arbitrary
imperfect fields and both characteristics zero and positive are included. The
atlas is not required quasi-compact, and may be empty for an empty stack.

Searches: prescribed `msearch.py` LeanFinder query "Open smooth substack of proper
flat finitely presented curves with isolated local complete intersection
singularities" returned scheme/ring smooth-locus results, no moduli assertion.
Loogle "AlgebraicGeometry.Smooth, CategoryTheory.BasedCategory" returned no hits.
Mathlib grep "IsAlgebraicStack|SmoothModuliAtlas|Smooth.*Substack|isolated.*lci"
returned no hits. Project searches for the item id and the general algebraic-stack
and smooth-atlas names found no existing assertion. Searches did find and reuse
ProperCurveModuli and OpenModuliSubstack. The retained search log records the fresh LeanSearch, LeanFinder and Mathlib
grep queries; the existing dependency node retains its own original searches. General scheme smoothness, or the existing finite-type DM atlas over a
field, does not define the needed general atlas over Spec Z.

The source was read directly: moduli-curves.tex, lemma-big-smooth-part-curves,
Tag 0DZX, precisely clauses (1) and (3) and its intersection/unobstructedness proof;
algebraic.tex, definition-algebraic-stack and the following etale/fppf discussion;
stacks-morphisms.tex, section-smooth and definition-smooth. No statement correction
or statement dispute is needed.

Validation: the prescribed initial dry run of the retained packet passed preflight
and compiled both saved modules, producing dry-run commit f32c58f6df3 without pushing.
The final repaired packet contains only the item module; its compile and final dry-run
results are checked by the prescribed wrappers before delivery.

## Returned delivery repair

The return at immutable head 59b8ec3bca84 said that the added statement dependency
`def-sfb-algebraic-moduli-stack` was neither new in the delivery nor landed with a
Lean record on its base. I compared the saved packet with the current base. The
current base now has Q18's landed Lean record for that node, with module
`Sheaf.AlgebraicGeometry.AlgebraicModuliStack` and declaration
`CategoryTheory.IsAlgebraicModuliStack`. Its source was read both locally and with
`scompile.py --source Sheaf.AlgebraicGeometry.AlgebraicModuliStack`; they agree.

The saved packet's dependency module would replace that now usable landed interface.
I removed its module and dependency-node copy from this delivery. The item imports
the landed module and uses its `IsAlgebraicModuliStack` and `IsSmoothModuliStack`
directly. Its `IsSmoothModuliAtlas` retains the actual 2-base-change projection,
chartwise smoothness and point surjectivity. The algebraic-stack predicate includes
etale descent and the algebraic-space diagonal. Smoothness over the base is the
existence of such an atlas with smooth structural composite, exactly as the item
states; the open substack inherits descent from the ambient algebraic stack.

All three added dependencies now have landed Lean records on the current base.
The final packet changes only the item's lean record and stmt_deps, its own module,
and this report. It adds no new nodes, delivers no dependency modules and changes
no natural-language statement. This concretely repairs the returned dependency
eligibility defect without replacing the landed definition.

## Second reading by Q77

I reread the item, its retained module, and the landed dependency definitions with
the source Stacks Tag 0DZX(1),(3) open. The hypothesis `halgebraic` is algebraicity
of the existing proper-curve category over Spec Z. The existential `L` is the
recorded full open substack, and `IsSmoothModuliStack L.category` asks for the
smooth atlas with smooth structural composite. The quantified field K, proper
scheme C, structure map f and dimension bound have no extra restrictions.
`IntegerSchemePointIn` retains the field structure map and the representing
isomorphism. The iff retains both directions; its affine-cover clause retains
finite-type K-algebras, K-linear open immersions, coverage and the recorded lci
predicate. Its second conjunct permits a finite exceptional set and a smooth open
neighborhood of every other point. Empty and disconnected schemes, imperfect
fields and all characteristics remain included. The helper has real Prop-valued
data and the only postponed theorem has the full six-step DAG proof docstring.
The repair removes the obsolete duplicate dependency interface and uses the
current landed one; no statement correction is needed.
