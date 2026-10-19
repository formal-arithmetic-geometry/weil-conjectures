## Worker report

The module `Sheaf.RingTheory.PseudoCoherentOfCohomology` states
`DerivedCategory.isPseudoCoherent_of_homology`, with its entire proof `sorry`.
It states precisely the pseudo-coherent clause of Stacks Tag 066B
(`more-algebra.tex`, lemma-cohomology-pseudo-coherent, read at lines 16252–16288).
No definition, dependency record, or mathematical statement was changed.

Hypothesis and conclusion correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- K in D(R): `[HasDerivedCategory.{w} (ModuleCat.{v} R)]` and
  `(K : DerivedCategory (ModuleCat.{v} R))`. The explicit localization binder
  implements the chosen morphism-size convention, not an extra mathematical condition.
- There is an integer b such that H^i(K) vanishes for i > b:
  `hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
  ((homologyFunctor (ModuleCat.{v} R) i).obj K)`.
- For every integer i, the R-module H^i(K), as a complex concentrated in degree zero,
  is pseudo-coherent: `hcoh : ∀ i : ℤ, IsPseudoCoherent
  (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
  ((homologyFunctor (ModuleCat.{v} R) i).obj K)))`.
  The single functor puts exactly this module in degree zero; Q views that complex in D(R).
- K is pseudo-coherent: conclusion `IsPseudoCoherent K`.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (recorded by
  def-weil-abstract-derived-category).
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`
  (def-pc-ring-pseudo-coherent-complex): existence of a strictly bounded-above,
  termwise finite free complex with derived image isomorphic to the given object.
- Mathlib's `DerivedCategory.homologyFunctor` (HomologySequence, also re-exported
  by RingPseudoCoherent) supplies cohomology, and `CochainComplex.singleFunctor`
  from `Mathlib.Algebra.Homology.Single` supplies the degree-zero complex.

The recorded proof dependencies are imported without `public`:
`Sheaf.CategoryTheory.TruncationTriangle` (`DerivedCategory.truncation_triangle`),
`Sheaf.RingTheory.PseudoCoherentIffAllM`
(`DerivedCategory.isPseudoCoherent_iff_forall_isMPseudoCoherent`),
`Sheaf.RingTheory.MPseudoCoherentShift`
(`DerivedCategory.isMPseudoCoherent_shift_one_iff`),
`Sheaf.RingTheory.MPseudoCoherentVanishingBase`
(`DerivedCategory.isMPseudoCoherent_of_homology_vanishes`),
`Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle`
(`CategoryTheory.isMPseudoCoherent_of_distinguished_triangle`), and
`Sheaf.RingTheory.MPseudoCoherent` (`DerivedCategory.IsMPseudoCoherent`).
The theorem docstring carries every step of the node's finite truncation induction.

Edge cases checked: zero complex and zero ring are allowed; every integer cutoff is
allowed, including negative bounds and b < m in the proof; cohomology can have gaps
and an unbounded lower tail. No Noetherian, Tor dimension, nonzero-cohomology, or
bounded-below hypothesis is introduced. Ring, module, and localization universes are
explicit and independent, matching the dependency definitions. There are no
auto-bound variables, new notions, or statement disputes.

Searches for reuse:

- `msearch.py` LeanFinder: “A bounded above derived complex with pseudo coherent
  cohomology modules is pseudo coherent”: eight hits on cohomological bounds,
  `DerivedCategory.isLE_iff`, `isGE_iff`, and K-projective/injective complexes;
  none is the finite-free pseudo-coherence criterion.
- `msearch.py` Loogle: `DerivedCategory.IsPseudoCoherent`: zero hits, unknown identifier.
- `msearch.py` grep: `PseudoCoherent|pseudo.?coherent`: zero Mathlib hits.
- `msearch.py` LeanSearch, same plain-language query: unavailable (Internal Server Error).
- `rg` of `IsPseudoCoherent|pseudo.?coherent` in the upstream WeilConjectures tree
  and `lean/Sheaf/RingTheory`: the project definition and related approximation,
  localization, and finite-free-model lemmas occur, but no cohomology criterion.
  The only upstream hit is an explanatory remark about Kiehl's theorem in
  AlgebraicGeometry/Cohomology/DirectImage/FiniteFreeComplex.lean.
- Upstream search for this exact node id: no hit.
- Exact proposed theorem/module name search in Mathlib, upstream, project Lean, and
  `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py NR lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent`
compiled the sole delivered module on the server in 1.0 seconds, nice 19, two threads,
60-second limit, with no errors or warnings. No local compilation was performed.


## Second reading by NR

I independently read the node, all six proof steps, the delivered module, the two
statement dependency nodes and their recorded declarations. I checked Stacks
`more-algebra.tex`, Tag 066B, lemma-cohomology-pseudo-coherent (lines 16252–16288),
including its D^-(R) hypothesis. The node deliberately takes the pseudo-coherent
clause for commutative rings, not the separate fixed-m clause. No source-wide
Noetherian, field, characteristic, or bounded-below assumption applies.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. A commutative ring R is `(R : Type u) [CommRing R]`. No field, nonzero ring,
   Noetherian, or coherence instance is imposed.
2. An arbitrary K in D(R) is `(K : DerivedCategory (ModuleCat.{v} R))`.
   I opened Mathlib `DerivedCategory.Basic`: `HasDerivedCategory.{w}` chooses a
   localization at quasi-isomorphisms with morphisms in the chosen universe;
   `HasDerivedCategory.standard` supplies the standard choice. This is precisely
   def-weil-abstract-derived-category and its size convention, not a finiteness
   condition on K. Ring, module and localization universes are explicitly bound.
3. There exists an integer upper cohomology bound is `hbounded : ∃ b : ℤ,
   ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj K)`.
   The order of quantifiers is correct, and b is not required to be nonnegative.
   I opened Mathlib `DerivedCategory.HomologySequence`: this homologyFunctor
   factors the cochain cohomology functor through Q, so it denotes H^i, with
   cohomological rather than homological indexing. IsZero is categorical zero
   in ModuleCat, hence exactly vanishing of the module.
4. For every integer i, H^i(K) as a degree-zero complex is pseudo-coherent is
   `hcoh : ∀ i : ℤ, IsPseudoCoherent (Q.obj
   ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
   ((homologyFunctor (ModuleCat.{v} R) i).obj K)))`.
   The single functor has this module in degree zero and zero elsewhere; Q
   takes its derived image. In particular the degree is 0, not i, and the
   hypothesis is not termwise finiteness of a chosen representative.
5. The sole conclusion is `IsPseudoCoherent K`. I opened
   `Sheaf.RingTheory.RingPseudoCoherent`: its real definition requires a complex
   E, an integer b, `E.IsStrictlyLE b`, `Module.Free` and `Module.Finite` in
   every degree, and `Nonempty (Q.obj E ≅ K)`. It is exactly the node's
   bounded-above finite-free-model notion. No alternate/private notion is used.

Edge cases: zero K, an acyclic representative, the zero ring, arbitrary
characteristic, negative or zero cutoffs and cohomology gaps are included.
No lower cohomology bound is imposed, so an infinite lower tail is included.
The docstring's B = max(b,m-1) handles b < m and the empty induction interval;
it never requires a largest nonzero cohomology group. There is no index family,
scheme, or natural-number parameter whose empty/zero cases could be excluded.
No universe equality is added relative to the recorded dependency definition.

Independent reuse searches, using different queries from the worker:

- `msearch.py ... leanfinder "A complex bounded above in cohomology whose
  homology has finite free resolutions admits a bounded above finite free
  resolution"`: eight hits on ordinary projective/injective resolutions and
  K-projective complexes. These do not assert finite-free pseudo-coherence.
- `msearch.py ... loogle '"coherent"'`: twelve hits on quotient coherence,
  topology and quasi-coherent sheaves, no ring-complex criterion.
- `msearch.py ... grep 'finite.*free.*homology|homology.*finite.*free'`:
  zero hits.
- Independent `rg` for pseudo-coherence throughout Mathlib and upstream
  WeilConjectures: no Mathlib notion, and only the upstream explanatory remark
  in `AlgebraicGeometry/Cohomology/DirectImage/FiniteFreeComplex.lean`.
- Independent `rg` on project `lean/Sheaf/RingTheory` and its cohomology/homology
  declarations found finite top cohomology, vanishing-base, all-m and localization
  results, not this theorem. The existing `IsPseudoCoherent` definition is used.

There are no new definition nodes or dependency modules in this delivery, no
statement_change and no altered citers to audit. I checked the non-public proof
imports against the proof plan, including the all-m equivalence, shift formula,
vanishing base, and triangle closure's second clause. The docstring carries each
of the six proof steps with its DAG references and source. The sole theorem body
is `sorry`; no definition, proof, local notation or private replacement is added.

Mismatches found: none. Changes: appended this independent second-reading report;
the correct Lean module and node record are preserved. I verified mechanically
that `lean.statement` is verbatim the theorem signature before `:=`, and by eye
that u, v, w, R, K, i and b are all bound.

Validation: I reran the sole delivered file through `scompile.py NR
lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent
lean/Sheaf/RingTheory/PseudoCoherentOfCohomology.lean`. The server passed in
1.1 seconds, nice 19, two threads, 60-second limit, with no errors or warnings.
No local compiler or library build was used.
