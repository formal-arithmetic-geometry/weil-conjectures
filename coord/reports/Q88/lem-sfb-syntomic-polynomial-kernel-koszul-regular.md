## Worker report

The module `Sheaf.RingTheory.SyntomicPolynomialKernelKoszulRegular` states
`Algebra.exists_koszulRegular_kernel_generators_of_syntomic`, with its only proof
`sorry`. It introduces no definition, extra node, or dependency repair. The item
is an accepted stage-1 split with no Lean record: the inherited stage-1 stale
dispatch ending is inapplicable to this stage-2 assignment (brief-stage2 §0).
No repair note is present. Only the item's `lean` field changes.

### Every hypothesis and clause

- Commutative rings and the map R → E: `{R : Type u} {E : Type v}`,
  `[CommRing R] [CommRing E] [Algebra R E]`. The map is `algebraMap R E`;
  arbitrary ring homomorphisms are represented by their induced algebra structure.
- Flatness: `[Module.Flat R E]`, equivalent to
  `RingHom.Flat (algebraMap R E)` by `RingHom.flat_algebraMap_iff`.
- Finite presentation: `[FinitePresentation R E]`, the recorded Mathlib class.
- For EVERY prime of R the fibre is a local complete intersection over its residue
  field: `hci : ∀ p : PrimeSpectrum R, IsLocalCompleteIntersection
  p.asIdeal.ResidueField (p.asIdeal.Fiber E)`.
  `Ideal.Fiber` is definitionally κ(p) ⊗[R] E, the project's FIBRE RING convention;
  tensor symmetry identifies this with the node's E ⊗[R] κ(p).
  `Ideal.ResidueField` is Mathlib's residue field of the localization at p, the
  affine ring version of the residue-field dependency, not a new definition.
  `FiniteStability` supplies the finite-type instance on each fibre from finite
  presentation, so the definition's finite-type argument adds no hypothesis.
- Any finite polynomial presentation: `(m : ℕ)` includes zero;
  `(β : MvPolynomial (Fin m) R →ₐ[R] E)` is an R-algebra map and
  `(hβ : Function.Surjective β)` supplies exactly surjectivity.
- J is `RingHom.ker β.toRingHom`, used directly without an auxiliary binder.
- Every prime q of P containing J: `(q : PrimeSpectrum (MvPolynomial (Fin m) R))`
  and `(hq : RingHom.ker β.toRingHom ≤ q.asIdeal)`.
- The principal neighbourhood: `∃ h : MvPolynomial (Fin m) R, h ∉ q.asIdeal ∧ ...`.
- The number and location of equations: `∃ (r : ℕ)
  (f : Fin r → Localization.Away h), ...`. Thus r may be zero.
- JP_h = (f₁,…,f_r): `(RingHom.ker β.toRingHom).map
  (algebraMap (MvPolynomial (Fin m) R) (Localization.Away h)) =
  Ideal.span (Set.range f)`.
- Every positive Koszul homology vanishes: `RingTheory.Sequence.IsKoszulRegular f`.
  Its recorded definition is `∀ i : ℕ, i ≠ 0 → IsZero (...homology i)`;
  this is exactly i > 0, with negative degrees already zero by the Koszul-complex
  convention. This is the displayed local condition, hence also the node's
  equivalent description of J as a Koszul-regular ideal.
- No `[Nontrivial E]`, `[Nontrivial R]`, Noetherian, positivity, dimension,
  regular-sequence, or extra fibre assumptions occur. Both universes are explicit
  and independent. `set_option autoImplicit false` forbids unbound variables.

### Dependency declarations read and used

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; the algebra-map type supplies
  the specified polynomial presentation (evaluation/uniqueness is not a separate
  conclusion of this item).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, imported
  through `Mathlib.RingTheory.Localization.Away.Basic` for its ring/algebra structure.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular` (full definition and docstring read).
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat`, `RingHom.Flat`, and
  `RingHom.flat_algebraMap_iff` (the last identifies the chosen encoding).
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection`, with the global complete-intersection
  definition it uses; both definitions and their docstrings were read.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, read and
  imported for the residue-field dependency; in this ring statement the affine
  residue field is the existing `Ideal.ResidueField` in Mathlib's
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`, which also provides `Ideal.Fiber`.
- `Mathlib.RingTheory.FiniteStability`: `Algebra.FiniteType.baseChange`, needed
  while elaborating the fibre condition; it adds no premise.

Stated proof dependencies are imported plainly: the flat-local-ring-maps
Mathlib match is in the already-public flat module;
`WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection`
provides `Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime`;
`Mathlib.RingTheory.Spectrum.Prime.Topology` provides
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` and `PrimeSpectrum.compactSpace`.
The complete-intersection definition is already public. The three new accepted
stage-1 proof lemmas (relative-global-ci-koszul-regular,
polynomial-presentation-principal-gluing, polynomial-presentation-independence)
have no recorded Lean declarations and are therefore not imported. Their complete
uses remain in the theorem's four-step proof docstring. They are proof-only inputs,
not missing notions required to type this statement.

### Source and edge cases

Read `more-algebra.tex` at `lemma-syntomic-lci` (07D3),
`definition-local-complete-intersection`, `lemma-koszul-independence-presentation`
(07CZ), `lemma-relative-global-complete-intersection-koszul` (07D2), and
`lemma-lci-local` (07D1). The source's forward argument gives exactly this
arbitrary-presentation conclusion, without a Noetherian condition.

Checked mathematically: m = 0 is a zero-variable presentation and is admitted;
r = 0 gives the zero ideal and a complex concentrated in degree zero. For β the
identity presentation one can take h = 1 and the empty sequence. If E = 0 then
J = ⊤, no prime contains J, and the conclusion is vacuous, as required. If R = 0,
its unital algebras are zero and the same check applies. Localizing away from an
h outside q ensures the neighbourhood contains q. No excluded characteristic
or implicit finiteness/Noetherian premise was introduced. No statement fault or
STATEMENT-DISPUTED flag is needed.

### Searches

All service searches used `batch2/msearch.py Q88
lem-sfb-syntomic-polynomial-kernel-koszul-regular`.

- LeanFinder: "The kernel of any finite polynomial presentation of a flat finitely
  presented algebra with local complete intersection fibres is locally generated
  by a Koszul regular sequence". Eight hits: standard-smooth results and
  `Algebra.Generators.fg_ker_of_finitePresentation`; no theorem giving Koszul
  regularity of syntomic presentation kernels.
- Loogle: `"IsKoszulRegular", "ker"`. Zero hits.
- Mathlib grep: `[Ss]yntomic|[Kk]oszul[Rr]egular` in RingTheory. Zero hits.
- LeanSearch: "A flat finitely presented algebra with local complete intersection
  fibres has Koszul regular polynomial presentation kernels". Eight hits,
  principally finite-presentation definitions and finite generation of kernels;
  none asserts the requested local regularity.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for syntomic/Koszul combinations,
  fibre complete-intersection signatures and kernel regularity: found the existing
  Koszul predicates and syntomic-lifting/fibre interfaces, no statement matching
  this item. A search for the exact item id in `lean/WeilConjectures` found none.
- `rg` for syntomic kernel/presentation names in `dag/lean_names_upstream.json`
  found no matching existing declaration. No new notion is introduced.

### Validation

Used only the required `scompile.py` for compilation. The first pass diagnosed
one missing finite-type base-change instance; added the public import of
`Mathlib.RingTheory.FiniteStability`. The final pass compiled the sandbox and
named library module cleanly (1.6 seconds each), with no errors or unexpected
warnings. All lines are at most 100 characters. The dry-run and push results
are checked by the prescribed delivery wrapper.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
