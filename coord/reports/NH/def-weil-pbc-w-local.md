## Worker report

Existing declaration delivery: no new Lean module, no proofs, no new nodes, and no statement
correction. The primary declaration is `IsWLocalRing` in
`WeilConjectures.RingTheory.ProEtale.WLocal`, read together with `WLocalSpace` in
`WeilConjectures.Topology.SpectralSpace.WLocal.Basic`. Both source signatures and docstrings
were read. The existing ring class applies to commutative semirings; applying it to the node's
commutative ring does not impose or remove a hypothesis. Universes are polymorphic.

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-w-local.md (the complete definition).

Clause-by-clause correspondence:

- The commutative ring A is the argument of `IsWLocalRing A` with `[CommRing A]` supplying
  its required `CommSemiring A`. The affine scheme is `AlgebraicGeometry.Spec
  (CommRingCat.of A)` (`Mathlib.AlgebraicGeometry.Scheme`), whose underlying topological
  space is `PrimeSpectrum A` with its Zariski topology. No choice of affine presentation
  or additional field, finiteness, or nonzero hypothesis is needed.
- D(f) is `(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))`, defined by
  `f ∉ x.asIdeal`. V(f) is `PrimeSpectrum.zeroLocus {f}`, defined by `{f} ⊆ x.asIdeal`.
  `PrimeSpectrum.basicOpen_eq_zeroLocus_compl` gives their complement relation.
  These declarations are in `Mathlib.RingTheory.Spectrum.Prime.Topology` and `.Basic`.
- The patch topology is the dependency's `constructibleTopology (PrimeSpectrum A)` in
  `Mathlib.Topology.Spectral.ConstructibleTopology`: its subbasis is the compact opens
  and their complements. This is exactly the node's D(f), V(f) topology: basic opens
  are compact (`PrimeSpectrum.isCompact_basicOpen`) and form a topological basis
  (`PrimeSpectrum.isTopologicalBasis_basic_opens`); every compact open is a finite
  union of basic opens (`PrimeSpectrum.isCompact_isOpen_iff`). Thus both subbases
  generate the same topology, including the empty and whole basic opens.
- Constructible E is `Topology.IsConstructible E` from `Mathlib.Topology.Constructible`,
  as recorded by def-weil-constructible-subset. It is Boolean closure of retrocompact
  opens. On the affine spectrum, quasi-separatedness makes open retrocompact subsets
  precisely compact opens, each a finite union of basic opens as above. Consequently
  its Boolean closure is exactly finite Boolean combinations of D(f) and V(f).
- Closed points use the dependency's `closedPoints (PrimeSpectrum A)` from
  `Mathlib.Topology.JacobsonSpace`, defined by `IsClosed {x}`. The ring class's field
  `wLocalSpace_primeSepectrum` supplies `WLocalSpace (PrimeSpectrum A)`; the latter's
  `isClosed_closedPoints` is exactly the node's first w-local clause.
- The second clause is the equivalent existing `WLocalSpace` formulation:
  `eq_of_specializes` says that any two closed specializations of one point are equal.
  The spectral-space superclass adds no restriction to an affine spectrum.
  `WLocalSpace.isHomeomorph_connectedComponents_closedPoints` in
  `WeilConjectures.Topology.SpectralSpace.WLocal.ConnectedComponents` proves that
  closed points map bijectively (indeed homeomorphically) onto connected components.
  Thus every component has exactly one closed point. Conversely, in a spectral space
  each point has a closed specialization; all specializations of a point lie in its
  connected component, so the node's component condition implies `eq_of_specializes`.
  Both closedness and components are in the original Zariski topology: the class does
  not replace the topological-space instance with `constructibleTopology`.
  Mathlib's `connectedComponent` is the maximal connected subset containing a point
  (`Mathlib.Topology.Connected.Basic`, definition and docstring read).

Dependency declarations were read in full: `AlgebraicGeometry.Spec` and `Spec.map`,
`constructibleTopology` and its `constructibleTopologySubbasis`, `Topology.IsConstructible`,
and `closedPoints`. The scheme-conventions dependency is explicitly a convention record
with no declaration; it introduces no extra notion that needs a module. All five recorded
dependencies are respected, with their existing declarations rather than private copies.

Edge cases checked mathematically: the zero ring has empty spectrum and satisfies both
w-local clauses vacuously, as does the existing class (no Nonempty requirement). A field
has one point and satisfies both. A local ring has a unique maximal ideal, every prime
specializes to it, and the whole spectrum is its connected component. A disconnected
spectrum permits different closed points in different components; the definition does not
require a globally unique closed point. A connected spectrum with two maximal ideals
fails both equivalent conditions. D(0) and V(1) are empty; D(1) and V(0) are the whole
space. No Noetherian hypothesis was introduced, and constructibility was not replaced
by the broader finite-union-of-locally-closed condition.

Searches (all through msearch.py unless indicated):

- leanfinder, "w-local affine scheme closed points connected component patch topology":
  eight related scheme/local-affine hits, no direct w-local definition.
- loogle, "constructibleTopology WithConstructibleTopology Scheme": zero hits and an
  application-type-mismatch diagnostic; no conclusion drawn from this failed query.
- leansearch, "w-local topological space closed points unique closed point connected component":
  service unavailable (Internal Server Error); recorded as unavailable, not a negative result.
- grep, "WLocal|wLocal|w-local|IsWLocal": four unrelated Mathlib metaprogramming hits.
- Initial grep with subdirectory WeilConjectures: zero hits (not used as evidence about
  the separate source checkout). Direct rg searches of the actual WeilConjectures tree
  for w-local/WLocal/IsWLocal found the existing `WLocalSpace` and `IsWLocalRing` modules,
  their defining fields, and the connected-components equivalence; all were opened.
- Direct rg of lean/Sheaf found no competing definition; incidental new-local node tags
  were excluded. Direct rg of dag/nodes found downstream uses/searches, not another
  definition node carrying this same notion. The upstream name inventory was searched
  for WLocalSpace/IsWLocalRing, with no matching entry; source declarations take precedence.

Validation: the explicit existing-declaration probe compiled cleanly through scompile.py
on the server (nice 19, two threads, 60 seconds per file), checking the primary class,
all supporting definitions, Spec, and the connected-components theorem. No local Lean
compiler was run. No disputed statement or dependency fault remains.

## Second reading by NH

Independent second reader: I opened the sandbox node and the complete blueprint source,
then the existing class definitions and the connected-components theorem in the read-only
slopmaster2 source. I also read Stacks `proetale.tex`, Definition 096A and its following
paragraph, and `topology.tex`, Definition 005G, Lemma 005H, Definition 08YG and the following
constructible-topology paragraph. The blueprint assumes only an affine scheme; Stacks
assumes a spectral space, which every affine spectrum is. There is no hidden Noetherian,
field, nonzero, characteristic, or finiteness hypothesis.

Here is my object/hypothesis/clause checklist, matched against the actual declarations:

1. A commutative ring A and X = Spec A: `AlgebraicGeometry.Spec (CommRingCat.of A)`.
   Its carrier is `PrimeSpectrum A` (`Spec_carrier`); `IsWLocalRing A` requires only
   `CommSemiring A`, supplied by `CommRing A`. The greater generality of the existing
   class does not restrict the node's rings. Verdict: exact on the stated domain.
2. Each f in A and D(f) = {p | f not in p}: `PrimeSpectrum.basicOpen f` has precisely
   this carrier in its definition. Verdict: exact.
3. V(f) = X minus D(f): `PrimeSpectrum.zeroLocus {f}` has carrier {p | {f} subset p};
   `basicOpen_eq_zeroLocus_compl` gives exactly the required complement. Verdict: exact.
4. Patch topology generated by all D(f) and V(f): the dependency's
   `constructibleTopology (PrimeSpectrum A)` is generated by compact opens and their
   complements. `isCompact_basicOpen`, `isTopologicalBasis_basic_opens`, and
   `isCompact_isOpen_iff` say compact opens are precisely finite unions of D(f).
   Passing between these subbases preserves the generated topology. Verdict: exact.
5. Constructible subsets are finite Boolean combinations of those generators:
   `Topology.IsConstructible E` is membership in the Boolean subalgebra generated by
   retrocompact opens. On this spectral, compact space, open retrocompact subsets are
   exactly compact opens (Stacks' paragraph after 08YG), hence finite unions of D(f).
   Its Boolean closure is therefore exactly the node's finite Boolean combinations
   of D(f) and V(f). Verdict: exact; no locally-closed shortcut is used.
6. Closed points form a closed subset: the dependency's `closedPoints X` is defined by
   `IsClosed {x}`. `IsWLocalRing.wLocalSpace_primeSepectrum` supplies `WLocalSpace`,
   whose `isClosed_closedPoints` field says precisely this. Verdict: exact.
7. Every connected component has exactly one closed point: the `WLocalSpace` field
   `eq_of_specializes` gives uniqueness of closed specializations; existence follows
   from spectrality. I read the full theorem
   `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`: its map is exactly
   the inclusion of closed points followed by `ConnectedComponents.mk`, and its
   bijectivity proves the component condition. Conversely, closure of a singleton
   is connected; each closed specialization therefore lies in the component of the
   original point. The node's component uniqueness implies `eq_of_specializes`.
   Together with clause 6 and the existing spectral instance, this constructs all
   fields of the class. Verdict: equivalent in both directions, no stronger condition.
8. Zariski topology and maximal connected subsets: `WLocalSpace (PrimeSpectrum A)`
   uses the original Zariski instance, not `WithConstructibleTopology`.
   `connectedComponent` is the union of preconnected subsets containing its point,
   giving the maximal connected subset. Verdict: exact.

I opened all five dependency nodes. Their recorded notions are `Spec`/`Spec.map`,
`constructibleTopology`, `Topology.IsConstructible`, and `closedPoints`; the scheme
conventions node explicitly defines no independent notion. The listed declarations
use these same definitions. The primary signature in `lean.statement` is verbatim
from the source declaration's header. There are no new nodes or dependency modules,
no statement correction and hence no correction-citer verdicts to audit.

Edge cases: the zero ring has empty spectrum, no components and no closed points;
all class fields are vacuous except spectrality, supplied for every spectrum. Fields
and nonzero local rings have one closed point; products can have several components
with different closed points. A connected spectrum with two maximal ideals fails the
condition. D(0) and V(1) are empty, while D(1) and V(0) are the whole spectrum;
empty Boolean combinations are covered. There is no numeric degree or index-set
binder. Arbitrary characteristics and arbitrary ring universes are retained by Type*;
no auxiliary instance excludes any case.

Independent searches used different conceptual wording from the first worker:

- `msearch.py ... leanfinder "spectral space closed points bijection connected
  components unique specialization"`: eight results about sober spaces, prime spectra,
  and connected components, no replacement w-local class.
- `msearch.py ... loogle '"closedPoints"'`: twelve results, including the exact
  `closedPoints` definition and `mem_closedPoints_iff`; their source was checked.
- `msearch.py ... leansearch "Boolean algebra generated by compact open subsets prime
  spectrum constructible"`: unavailable (HTTP 521), not counted as negative evidence.
- Direct `rg` on Mathlib Topology/RingTheory and project `lean/Sheaf`, using
  `WLocalSpace|IsWLocalRing|w-local`, found no competing definition; incidental
  `new-local` tags are not w-local definitions. Direct source searches found
  `RingTheory/ProEtale/WLocal.lean` and `Topology/SpectralSpace/WLocal/{Basic,
  ConnectedComponents}.lean`; the definitions and equivalence above were read there.
  Searching DAG titles found this definition and distinct w-localization/cover/retraction
  nodes; none is another definition of this notion. The upstream name inventory contains
  no matching class entry, so I checked the actual source rather than trusting the index.

No mismatch was found. I preserved the existing declaration attachment and the worker
report, and added only this independent review. No hollow data definition, new proof,
private notion, or new local notation is introduced. Existing upstream declarations are
reused without rewriting their docstrings (H4); there is no new module needing H8 tags.
The existing-declaration scratch probe compiled cleanly via `scompile.py` on the server:
1.6 seconds, nice 19, two threads, hard 60-second limit, with no warnings or errors.
