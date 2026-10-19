## Worker report

The node is realized entirely by existing, sorry-free declarations in the published
`WeilConjectures` source, so this delivery contains no Lean module.  The primary
record is `WLocalSpace` in
`WeilConjectures.Topology.SpectralSpace.WLocal.Basic`; its `SpectralSpace` parent,
`eq_of_specializes` field, and `isClosed_closedPoints` field render the definition
of a spectral space whose closed points are closed and for which each point has at
most one closed specialization.  The spectral-space existence theorem supplies
that every point has a closed specialization, so together these fields give
“exactly one”.

The ring hierarchy is already defined by `IsWLocalRing` and
`IsWStrictlyLocalRing` in `WeilConjectures.RingTheory.ProEtale.WLocal`, and
`IsWContractibleRing` in `WeilConjectures.RingTheory.ProEtale.WContractible`.
`IsWLocalRing` carries `WLocalSpace (PrimeSpectrum R)`, which is the node's
w-local clause.  `IsWStrictlyLocalRing` extends it with
`IsStrictlyHenselianLocalRing (Localization.AtPrime m)` for every maximal ideal
`m`, rendering the w-strictly-local clause.  `IsWContractibleRing` extends that
class with
`ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))`, rendering the
w-contractible clause and the quotient-topology interpretation of pi-zero.

The dependency declarations checked were:

- `SpectralSpace` (`Mathlib.Topology.Spectral.Basic`), matching the spectral-space
  definition.
- `AlgebraicGeometry.Spec` (`Mathlib.AlgebraicGeometry.Scheme`), matching the
  affine spectrum and its Zariski topology.
- `AlgebraicGeometry.Scheme.compactSpace_of_isAffine` and
  `AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` (the recorded Mathlib match
  for `lem-weil-pbc-affine-scheme-qcqs`), supplying the affine qcqs facts.
- `SpectralSpace` (the recorded Mathlib match for
  `lem-weil-pbc-qcqs-scheme-spectral`), supplying spectrality of a qcqs scheme.
- `Localization.AtPrime`, `Ideal.ResidueField`, and `Ideal.Fiber`
  (`Mathlib.RingTheory.Localization.AtPrime.Basic`), matching the localization
  notation used by the strict-local clause.
- `IsStrictlyHenselianLocalRing`
  (`WeilConjectures.Mathlib.RingTheory.Henselian`), matching the strict henselian
  predicate.
- `spectralSpace_connectedComponents_profinite`
  (`Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`), matching the
  profiniteness fact used for the connected-component space.

Edge cases checked against the definitions were the empty spectral space, the zero
ring (all universal maximal-ideal conditions are vacuous), and a field (its
spectrum has one point, and strict locality reduces to separable closedness of the
field).  The connected-components quotient agrees with `ConnectedComponents` in
Mathlib, including the one-point and empty cases.

Searches made:

- `msearch.py ... leanfinder "w-local spectral space closed points unique specialization w-strictly local w-contractible ring"`: no complete hierarchy match; only constituent spectrum/local-ring results.
- `msearch.py ... loogle "WLocalSpace, IsWLocalRing, IsWStrictlyLocalRing, IsWContractibleRing"`: no Mathlib identifiers.
- `msearch.py ... grep "\\b(WLocalSpace|IsWLocalRing|IsWStrictlyLocalRing|IsWContractibleRing)\\b" WeilConjectures`: no result from the prefixed search; direct source `rg` located the four declarations listed above.
- The node's recorded LeanFinder, LeanSearch, Loogle, and Mathlib grep searches likewise found no complete Mathlib hierarchy and identified the same source declarations.

No statement correction or `STATEMENT-DISPUTED` flag is needed.  The node copy changes
only its `lean` record, whose primary signature was checked as
`class IsWContractibleRing (R : Type*) [CommRing R] extends IsWStrictlyLocalRing R`.
The primary module imports the other three declarations transitively, so all four
recorded names are available to the delivery preflight.

## Second reading by ND

I read the node statement, its Stacks source place, and every recorded dependency before
checking the existing declarations. The four defining objects and their Lean renderings are:

1. For a type `T` with a topological space and spectral structure, the node introduces the
   closed-point set `T^c`, defines specialization by membership in the closure of a
   singleton, and requires that `T^c` be closed and that each point have exactly one closed
   specialization. `WLocalSpace (X : Type*) [TopologicalSpace X]` in
   `WeilConjectures.Topology.SpectralSpace.WLocal.Basic` extends `SpectralSpace X`, has
   `isClosed_closedPoints : IsClosed (closedPoints X)`, and has
   `eq_of_specializes` for any two closed specializations. The existence part of “exactly
   one” is supplied for every `SpectralSpace` by the standard spectral-space theorem
   `exists_isClosed_specializes`; the field supplies uniqueness. The relation `x ⤳ c` is
   the Mathlib specialization relation, definitionally the stated closure-membership
   formulation.
2. For a commutative ring `R`, the node uses the affine spectrum with its Zariski topology.
   Mathlib's `AlgebraicGeometry.Spec` has underlying carrier `PrimeSpectrum R`; the existing
   affine qcqs and qcqs-scheme spectral dependencies provide the stated quasi-compact,
   quasi-separated and spectral facts. `IsWLocalRing (R : Type*) [CommSemiring R]` has the
   field `wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)`. In the node's
   commutative-ring context, `[CommRing R]` supplies this semiring instance, so the carrier
   is exactly the underlying topological space of `Spec R` and no extra hypothesis is
   introduced.
3. The node defines w-strict locality by requiring w-locality and, for every maximal ideal
   `m`, strict henselianity of `R_m`. `IsWStrictlyLocalRing (R : Type*) [CommRing R]`
   extends `IsWLocalRing R` and has
   `isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
   IsStrictlyHenselianLocalRing (Localization.AtPrime m)`. `Localization.AtPrime m` is the
   recorded localization-at-a-prime notion, and the recorded
   `IsStrictlyHenselianLocalRing` is the strict-henselian local-ring predicate. The maximal
   ideal typeclass supplies the prime condition needed by `AtPrime`, exactly as in the node.
4. The node defines w-contractibility by w-strict locality plus extremal disconnectedness
   of the quotient space of connected components. `IsWContractibleRing (R : Type*)
   [CommRing R] extends IsWStrictlyLocalRing R` and its field is
   `extremallyDisconnected_connectedComponents :
   ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))`. Mathlib's
   `ConnectedComponents` carries the quotient topology; the existing
   `spectralSpace_connectedComponents_profinite` statement supplies compact Hausdorff
   total disconnectedness (profinite) from the inherited spectral structure. Thus the
   field is precisely the node's additional condition, and `ExtremallyDisconnected`
   is the closure-of-every-open-set-is-open predicate.

No mismatch was found. In particular, the broader `[CommSemiring R]` parameter of
`IsWLocalRing` is harmless when the node binds a commutative ring, and the class field
for uniqueness is not weaker because spectrality supplies existence of a closed
specialization. I changed only the node's missing `lean` record, recording the existing
upstream module and all four declarations; no Lean module or definition was added.

Edge cases checked: the empty spectral space satisfies the universal specialization and
closed-point conditions; the zero commutative ring has empty prime spectrum and no maximal
ideal, so the universal localization condition is vacuous; a field has the one-point
spectrum and its sole maximal localization is itself; connected spaces give a one-point
component quotient; and empty and one-point component quotients satisfy the profinite and
extremal-disconnected predicates. The declarations use `Type*` and do not impose an
unwanted universe equality. There is no integer parameter `n` or characteristic
hypothesis in this node.

For independent duplicate searches I ran:

- `msearch.py ND sk-def-pe-wlocal leanfinder "w-local spectral space unique closed specialization closed points WLocalSpace"`; it returned only `SpectralSpace` and constituent specialization results, not the w-local hierarchy.
- `msearch.py ND sk-def-pe-wlocal loogle "WLocalSpace IsWLocalRing IsWStrictlyLocalRing IsWContractibleRing"`; it returned no Mathlib identifier.
- `rg` over the pinned Mathlib, `WeilConjectures/`, and `lean/Sheaf/`; the four declarations occur in the upstream modules named above, while Mathlib and `Sheaf/` contain only uses or constituent notions. No second definition or complete competing statement exists.

The node's source is Stacks Tag 096A (`definition-w-local`) for the spectral w-local
condition, with the blueprint's strict-henselian and extremally-disconnected clauses
rendered by the corresponding existing classes. All dependency records were opened and
match their cited notions; no statement correction, new node, dependency repair, or
`STATEMENT-DISPUTED` mark is needed.
