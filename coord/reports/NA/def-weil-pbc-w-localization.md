## Worker report

The module `Sheaf.RingTheory.PrincipalWLocalization` defines the concrete diagram in
`def-weil-pbc-w-localization` and its chosen colimit
`PrincipalWLocalization.algebra`. No statement correction, new DAG node, or dependency
module is needed. The blueprint definition at order 1222 was read in full, together
with the item's expanded statement and every statement-dependency record.

Hypotheses and clauses, matched against the node:

- A commutative ring is `A : Type u` with `[CommRing A]`. There is no nontriviality,
  field, or Noetherian assumption. All universes are explicit. `PrimeSpectrum A`
  is the underlying space of `Spec A`; no choice of affine scheme data is needed.
- `D(f)` is the existing `PrimeSpectrum.basicOpen f`, whose carrier is exactly
  `{p | f ∉ p.asIdeal}`. Constructibility is the dependency's recorded
  `Topology.IsConstructible` on the Zariski topology. On an affine spectrum its
  open retrocompact generators are precisely finite unions of principal opens;
  its finite Boolean combinations therefore give the node's constructible sets.
- `Index.parts : Finset (Set (PrimeSpectrum A))` is a finite set of parts.
  `Index.nonempty` excludes empty parts, `Index.constructible` requires each part
  to be constructible, and `Index.partition` gives exactly one part containing
  each prime. This expresses both coverage and pairwise disjointness. The empty
  partition is permitted exactly when the spectrum is empty.
- `Index.denominator : parts → A` and `Index.nonvanishing` give one `f_E` per
  part and the inclusion `E ⊆ D(f_E)`.
- `Stage i` is the full Pi type `(E : i.parts) → Localization.Away
  (i.denominator E)`. Standard Pi commutative ring and algebra instances supply
  componentwise operations and the diagonal structural map. The empty Pi type
  has one element and hence is the zero ring, as requested.
- `Refines i j` requires for every child `F` a parent `E` with `F ⊆ E` and
  `i.denominator E ∣ j.denominator F`. A child's nonemptiness and the unique
  membership in `i.partition` make this parent unique. `indexPreorder` uses this
  exact relation; the standard preorder category has one arrow per relation.
- `parent` selects the parent from the relation itself, not from a postponed
  existence proof. `parent_dvd` is its named divisibility proof obligation.
- `transition h` is `AlgHom.pi` of the projection `Pi.evalAlgHom` followed by
  `IsLocalization.Away.liftAlgHom`. The target image of the source denominator
  is a unit by `IsLocalization.Away.isUnit_of_dvd`. This is precisely the
  universal-property map in the node: on a fraction `a/f^n`, localization lift
  evaluates to the image of `a` times the inverse unit image of `f` to power `n`.
  If `g = f*h`, its inverse is the image of `h` times the inverse image of `g`.
- `transition_id` and `transition_comp` state the required identity and
  composition laws as named theorems. `diagram` packages these same stages and
  maps into a functor to `CommAlgCat.{u} A`; no unspecified maps are parameters.
- `index_isFiltered` states filteredness, with the node's nonempty-intersection
  and product-denominator construction in its proof outline. This gives a
  filtered diagram with `Index A : Type u`, a small index in the ring universe.
- `algebra A := colimit (diagram (A := A))` takes the chosen colimit in
  commutative A-algebras. Its coercion to a type has the bundled commutative ring
  and A-algebra instances; `algebraMap A (algebra A)` is the structural map.
  Since both stages and colimit arrows are in `CommAlgCat A`, this is the map
  induced by the stage diagonal maps.
- `isIndPrincipalZariski` states exactly the indicated principal ind-Zariski
  presentation, using the dependency's predicate. No claim of faithful flatness,
  w-locality, connected components, or behavior of points is made.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.ProEtale.WLocal`, `IsWLocalRing`, read with its
  docstring and full class. For this construction only the recorded supporting
  notions `Topology.IsConstructible` and `PrimeSpectrum.basicOpen` are used;
  no hypothesis `IsWLocalRing A` is imposed. Their definitions were read in
  `Mathlib/Topology/Constructible.lean:178` and
  `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:509` respectively.
- `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`, read at
  line 142 with its docstring: localization at `Submonoid.powers`.
  The ring-localization instances come through
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.RingTheory.Localization.Defs`, `IsLocalization.lift` and
  `IsLocalization.ringHom_ext`, read with docstrings at lines 488 and 543 and
  their evaluation/uniqueness lemmas. The specialization actually used to
  construct algebra maps is `IsLocalization.Away.liftAlgHom`, whose full
  definition at Away/Basic.lean:169 was read, together with
  `IsLocalization.Away.isUnit_of_dvd` at line 139.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`
  (and the cocone/universal-property infrastructure `Cocone`, `IsColimit`).
  The latter structures were read in Cones.lean:133 and IsLimit.lean:62.
  `CategoryTheory.IsFiltered` was read in Filtered/Basic.lean:95.
- `Mathlib.Algebra.Category.CommAlgCat.Basic`, `instHasColimitsCommAlgCat`,
  read in the final instances of the file: small colimits in `CommAlgCat.{u} A`
  exist in the same universe as A. `CommAlgCat.of`, `ofHom`, and its category
  and algebra structures were also read there.
- `Sheaf.RingTheory.IndPrincipalZariski`, `Algebra.IsIndPrincipalZariski`, read
  in full. It requires a small filtered colimit presentation with each term
  algebra-isomorphic to a finite product of principal localizations, allowing
  the empty product. This is the predicate used by the last theorem.

Edge cases checked before writing:

- The zero ring has empty spectrum, and its sole possible partition has no
  parts or denominators. The Pi product is a one-element ring. There is no
  artificial nonempty-spectrum or nonempty-index-of-parts assumption.
- For a nonempty spectrum, the singleton partition with denominator 1 meets
  all fields, giving a nonempty index category. A field is allowed without
  excluding its single-point spectrum.
- Zero divisors cause no problem: the only hypothesis needed for a component
  map is divisibility of denominators, which implies invertibility of the
  parent's image after localizing at the child's denominator. No cancellation
  or domain hypothesis is used. A nilpotent denominator cannot occur on a
  nonempty part, by the nonvanishing field.
- Empty intersections are omitted from common refinements. A nonempty
  intersection belongs to a unique pair of original parts, so attaching the
  product denominator is well-defined. This includes redundant or unit
  denominators and repeated equal denominators on distinct parts.
- The preorder need not be antisymmetric: mutually divisible denominators can
  give distinct indices. A preorder category, rather than a poset quotient,
  retains exactly the indices the node specifies.

Searches performed (msearch.py, group NA, this item; actual results):

- LeanFinder: `filtered diagram finite constructible partitions prime spectrum
  products principal localizations ring w localization`. Eight hits, including
  `PrimeSpectrum.BasicConstructibleSetData.g`, general filtered-colimit results,
  and `PrimeSpectrum.PiLocalization`; none defines the specified diagram.
- Loogle: `Localization.awayMap, IsLocalization.Away.lift`. Zero hits for this
  combined query. The required localization lift was found by direct source
  inspection instead; this zero result is not evidence that the lift is absent.
- Mathlib grep: `WLocalization|ProdStrata|constructible.*[Pp]artition`.
  Zero hits.
- LeanSearch: `w localization ring constructible partitions`. Service unavailable
  with Internal Server Error; recorded as unavailable, not as no match.
- Direct `rg` of the source project's `WeilConjectures`, the group's
  `lean/WeilConjectures/RingTheory/ProEtale`, and `lean/Sheaf` for
  `WLocalization|wLocalization|ProdStrata|def-weil-pbc-w-localization` found the
  upstream `WLocalization` construction, but no declaration of this node's
  diagram. Direct `grep -rn` for the exact node id in the source project found
  no hit. `rg` of `dag/lean_names_upstream.json` and `lean/Sheaf` for the node id
  and `PrincipalWLocalization` found no existing declaration.
- Additional direct `rg` for `constructible.*[Pp]artition|
  [Pp]artition.*[Ll]ocalization|PrincipalWLocalization` found constructible-sheaf
  stratification material, not this algebra diagram. Source inspection in
  `WeilConjectures/RingTheory/ProEtale/WLocalization/Basic.lean:34,429,638,650`
  checked the possible upstream match: `Generalization` inverts the submonoid
  of elements unit in `(A/I)_f`, `ProdStrata` is a product of those objects,
  and `WLocalization.commAlgCat` is their colimit over finite subsets of A.
  It therefore does not have this node's principal-localization stages and
  partition/denominator index preorder, and was not silently substituted.

All definitions contain concrete data. The only postponed proofs are
`refines_refl`, `refines_trans`, `parent_dvd`, `transition_id`, `transition_comp`,
`index_isFiltered`, and `isIndPrincipalZariski`; each is a named theorem with
`:= by sorry`, a source/blueprint docstring and its proof outline. The instances
and the functor use these named proof obligations. No theorem was proved.

Validation: scompile.py compiled the delivered module cleanly on the server,
1.7 seconds, nice 19, two threads, 60 seconds per file. It compiled the side-only
`IndPrincipalZariski` import into its private overlay first (1.3 seconds).

## Second reading by NA

I independently read the expanded DAG statement, the blueprint definition at order
1222, all six dependency records, and the delivered Lean file. The source named by
this node is the blueprint markdown, rather than a Stacks tag. I also read Stacks
`proetale.tex`, lemma-localization through equation-colimit-ring, lemma-refine,
and remark-slightly-stronger. Stacks assumes only a commutative ring here, but its
actual w-localization uses generalization submonoids; it is not the principal
partition construction specified by this blueprint node. This distinction is
respected by the module. No statement correction or extra dependency is needed.

Object/hypothesis/clause inventory, with the Lean rendering and verdict:

- Arbitrary commutative ring A and X = Spec A: `A : Type u`, `[CommRing A]`,
  and `PrimeSpectrum A`. Exact: the definition only needs the underlying
  topological spectrum, not a bundled scheme or any geometric hypothesis.
- Principal open D(f) and constructible subsets: `PrimeSpectrum.basicOpen` and
  `Topology.IsConstructible` in `Index.nonvanishing` and `Index.constructible`.
  Exact. I read their Mathlib definitions: the former means f is not in the
  prime ideal; the latter is the Boolean algebra generated by open retrocompact
  sets. On an affine spectrum these generators are quasi-compact opens, hence
  finite unions of principal opens (the compact basic-open basis in
  Spectrum/Prime/Topology.lean). This is the node's finite Boolean algebra.
- Finite partition into nonempty constructible parts: `Index.parts`,
  `Index.nonempty`, `Index.constructible`, and `Index.partition`. Exact.
  Unique membership means coverage and pairwise disjointness; no enumeration
  or chosen cardinality restricts the partitions.
- One element f_E per part, nonvanishing on that part: `Index.denominator`
  and `Index.nonvanishing`. Exact, with no additional relation between parts
  and their denominators.
- B_i = product of A[1/f_E]: `Stage i` is the dependent Pi of the recorded
  `Localization.Away` objects. Exact. I read `Localization.Away` at powers,
  its ring-localization instances, and `Pi.algebra`: operations are
  componentwise and `algebraMap` is the diagonal of the localization maps.
- Preorder and one arrow per refinement/divisibility relation: `Refines`,
  `refines_refl`, `refines_trans`, `indexPreorder`, and the standard thin
  category on a preorder. Exact. For each child the existential parent is
  unique because the child is nonempty and parent parts are disjoint.
- Component transitions: `parent h F` selects that parent from the actual
  refinement hypothesis; `parent_dvd` exposes its divisibility clause.
  `transition` projects with `Pi.evalAlgHom` and then uses
  `IsLocalization.Away.liftAlgHom`, with invertibility supplied by
  `IsLocalization.Away.isUnit_of_dvd`. Exact. I read these definitions and
  `IsLocalization.lift`, `lift_mk'`, and `ringHom_ext`; they give exactly
  a/f^n mapping to a times the inverse image of f to the nth power.
- Identity and composition of the specified maps: `transition_id` and
  `transition_comp`, used in `diagram.map_id` and `diagram.map_comp`.
  Exact: the latter compares the direct transition with child-after-parent
  composition, and both laws concern these concrete localization maps.
- Nonempty small filtered index: `index_isFiltered : IsFiltered (Index A)`.
  Exact. Its docstring gives the singleton/empty partition witnesses,
  nonempty-intersection common refinement with product denominators, and
  thinness to equalize parallel arrows. `Index A : Type u`; no independent
  index universe or nonempty-spectrum hypothesis is imposed.
- Diagram of commutative A-algebras and its chosen colimit: `diagram` and
  `algebra A := colimit (diagram (A := A))` in `CommAlgCat.{u} A`. Exact.
  I read the recorded colimit and commutative-algebra colimit-existence
  declarations. The bundled algebra structure supplies the requested
  structural map; colimit coprojections are A-algebra morphisms, so this
  map agrees with every stage diagonal.
- Principal ind-Zariski presentation: `isIndPrincipalZariski` uses precisely
  `Algebra.IsIndPrincipalZariski`. Exact. I opened the landed dependency
  module and checked its existential small filtered `ColimitPresentation`
  and algebra equivalences with products indexed by `Fin n`, including n=0.
- Scope of assertions: the module states no conclusion about points,
  connected components, faithful flatness, or w-locality. Exact.

Edge cases: the empty spectrum permits exactly the empty partition, and its
empty Pi stage is the zero ring; nonempty spectra admit the singleton partition
with denominator 1. The category is nonempty in both cases. Empty intersections
are omitted in common refinements; any remaining intersection has unique parents,
so repeated set intersections cannot create conflicting denominator choices.
No nontriviality, domain, characteristic, finiteness, or Noetherian assumption
appears. Divisibility supplies units even with zero divisors. Nilpotent
nonvanishing denominators cannot label a nonempty part. Repeated denominators,
unit denominators, mutually divisible denominators, and all characteristics are
allowed. Every universe and binder is explicit; n=0 in the presentation is
allowed. All helper theorem statements have the stated elementary proofs.

Independent searches: msearch LeanFinder query `finite decomposition of prime
spectrum with denominators defining a filtered localization algebra` returned
eight unrelated quasi-finiteness/general-localization hits, no such diagram.
msearch grep `partition.*denominator|denominator.*partition` returned zero hits.
Direct `rg` for `partition.*denominator|denominator.*partition|
finite.*partition.*localiz` over all Mathlib, the source project's
WeilConjectures, and lean/Sheaf returned no existing construction. Searches
for WLocalization and stratifications led to the upstream candidate, which I
opened at `Generalization.submonoid`, `Generalization`, `ProdStrata`,
`commAlgCat`, and `WLocalization`. Its factors invert all elements unit in
(A/I)_f, rather than just powers of f; its index is finite subsets of A.
It therefore cannot replace this definition. The first worker's independent
LeanSearch attempt is recorded as service unavailable, not absence evidence.

No mathematical mismatch was found; no Lean or node changes were made. There
are no new nodes or dependency modules in this delivery. Definitions contain
concrete data, and choice in `parent` selects from the supplied relation, not
an undetermined sorry existence theorem. The colimit choice is fixed up to its
universal isomorphism. All seven theorem proofs remain `sorry`, as required for
stage 2; their docstrings include source, blueprint id, and proof outlines.
The main `lean.statement` is verbatim the `def algebra` signature, following
the project's signature-reader convention that omits `noncomputable`.

Validation: fresh scompile.py server compilation passed without errors or
warnings: PrincipalWLocalization 1.7 seconds, with its side-only
IndPrincipalZariski import compiled in the private overlay in 1.3 seconds;
nice 19, two threads, 60 seconds per file. The only change from this second
reading is this detailed independent review report.
