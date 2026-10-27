## Worker report

The module `Sheaf.AlgebraicGeometry.T1FiniteHausdorffAffineCover` states
`AlgebraicGeometry.Scheme.exists_finite_hausdorff_affine_cover` with `sorry` as its
whole proof. It introduces no definitions. The node's statement, dependencies,
proof and other fields are unchanged; only its `lean` record is added.

Clause-by-clause rendering:

- A scheme: `(X : Scheme.{u})`.
- Quasi-compact underlying space: `[CompactSpace X]`, exactly the recorded
  declaration for `def-weil-pbc-quasi-compact-scheme`; this does not include Hausdorffness.
- Every singleton closed: `[T1Space X]`. Mathlib's sole `T1Space.t1` field is
  `∀ x, IsClosed ({x} : Set X)`.
- A finite index set: `∃ n : ℕ`, with all chart families indexed by `Fin n`.
  Any finite set can be enumerated this way, and no positive-cardinality condition occurs.
- Open subschemes: `U : Fin n → X.Opens`; their scheme structures are `(U i).toScheme`,
  the existing restriction construction, not separately supplied scheme structures.
- Affine charts: `∀ i : Fin n, IsAffineOpen (U i)`.
- Commutative rings: `A : Fin n → CommRingCat.{u}`. The same universe as `X` suffices
  because the coordinate rings can be the rings of sections on the affine opens.
- Scheme isomorphisms to the spectra of these same rings:
  `∀ i : Fin n, Nonempty ((U i).toScheme ≅ Spec (A i))`.
  This retains scheme isomorphisms, including structure sheaves, rather than only
  homeomorphisms. In an existential proposition the family of `Nonempty` types is
  equivalent to the existence of a family of isomorphisms.
- The charts cover all of `X`: `(⨆ i : Fin n, U i) = ⊤`. Supremum in `X.Opens`
  is union and the top open is the entire underlying space.
- Every prime of each displayed coordinate ring is maximal:
  `∀ (i : Fin n) (p : Ideal (A i)), p.IsPrime → p.IsMaximal`.
- Each chart is quasi-compact in its subspace topology:
  `∀ i : Fin n, CompactSpace (U i)`.
- Each chart is Hausdorff in that same topology:
  `∀ i : Fin n, T2Space (U i)`. Mathlib's `T2Space.t2` says exactly that distinct
  points have disjoint open neighbourhoods. Here the coerced type of an open is its
  subtype of `X`, with the inherited topology; the corresponding open subscheme
  uses the same underlying space.
- The empty index set is allowed by `n = 0`; there is no quasi-separatedness,
  Noetherianity, separatedness, finite-type, reducedness, or nonemptiness hypothesis.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- Existing support notions: `AlgebraicGeometry.IsAffineOpen` in
  `Mathlib.AlgebraicGeometry.AffineScheme`; `Scheme.Opens.toScheme` in
  `Mathlib.AlgebraicGeometry.Restrict`; `T1Space` in
  `Mathlib.Topology.Separation.Basic`; `T2Space` in
  `Mathlib.Topology.Separation.Hausdorff`; `Ideal.IsPrime` and `Ideal.IsMaximal`.

The stated proof dependencies are imported too: finite affine covers from
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
(`AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`);
prime closures and their irreducible-closed-set correspondence from
`Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.closure_singleton`, `PrimeSpectrum.pointsEquivIrreducibleCloseds`);
maximal-ideal existence from `Mathlib.RingTheory.Ideal.Maximal`
(`Ideal.exists_le_maximal`); and
`Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`
(`AlgebraicGeometry.Spec.profinite_of_isMaximal`). All proof-only modules are
plain imports; the maximal-ideal module is public because the conclusion names
`Ideal.IsMaximal`. The declaration docstring reproduces the four proof steps.

Sources checked: Stacks `properties.tex`, Tag 0CKV, `lemma-dimension-zero`,
opening proof paragraph (affine opens are profinite) and final paragraph (finite
cover of a quasi-compact open). The node's supplied maximal-prime argument
explains the equivalent closed-singleton formulation. No correction is needed.
The prescribed CompactObject example is now withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`, which was read for the current
public module format.

Edge cases checked mathematically before writing:

- Empty `X`: take `n = 0`; the empty supremum equals the top open of the empty
  scheme, and all indexed assertions are vacuous.
- A zero coordinate ring: its empty spectrum is allowed and the prime condition
  is vacuous; no nontrivial-ring assumption was introduced.
- A nonreduced zero-dimensional ring such as `k[ε]/(ε²)` has a singleton spectrum
  and fits; reducedness is unnecessary.
- Infinite Boolean rings give non-Noetherian compact Hausdorff spectra, potentially
  with infinitely many points. The theorem restricts the number of charts, not
  their cardinalities, and does not assert discreteness.
- Non-quasi-separated schemes with closed points are included: the conclusion
  concerns individual affine charts, without a condition on their intersections
  or a global Hausdorffness conclusion.

Searches for an existing exact declaration (2026-10-24):

- `msearch.py` LeanFinder: "A quasi compact scheme with closed points admits a
  finite affine open cover by compact Hausdorff charts with all prime ideals maximal".
  Eight hits, including `isCompact_iff_finite_and_eq_biUnion_affineOpens`,
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`, and the finite-subcover
  affine instance; none supplies the maximal-prime and Hausdorff conclusions.
- `msearch.py` LeanSearch: "A quasi compact T1 scheme admits finitely many compact
  Hausdorff affine open charts". Eight hits, all finite-cover/compactness or
  quasi-separatedness results; no exact match.
- `msearch.py` Loogle: `AlgebraicGeometry.Scheme, CompactSpace, T1Space`.
  Successful search, zero hits.
- `msearch.py` grep: `T1Space|T2Space|isMaximal` in `AlgebraicGeometry`.
  Six hits, including `IsAffineOpen.primeIdealOf_isMaximal_of_isClosed` and the
  domain-specific `PrimeSpectrum.t1Space_iff_isField`; none is the entire claim.
- Direct `rg` in `WeilConjectures` and `Sheaf` for
  `T1Space|finite.*[Hh]ausdorff|[Hh]ausdorff.*[Cc]over|t1_finite|lem-sfb-t1-finite-hausdorff-affine-cover`.
  Found the spectral T1 separation instance and the stronger-hypothesis affineness
  theorem `QcqsZeroDimensionalAffine`, but no exact finite-chart theorem.
- `grep -rn` of this node id in `WeilConjectures`: no hits.
- Direct `rg` for `exists_finite_hausdorff_affine_cover` in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`: no hits.

Validation: the single delivered module compiled cleanly through `scompile.py`
on the server, both under its sandbox name and its library module name (1.4 s
per check). The delivery wrapper repeats compilation and runs server preflight.
No disputed statement, missing notion, dependency repair, or additional node.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
