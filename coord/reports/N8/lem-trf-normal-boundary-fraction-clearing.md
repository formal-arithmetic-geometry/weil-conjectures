## Worker report

The delivery states `Ring.normal_boundary_fraction_clearing` in
`Sheaf.RingTheory.NormalBoundaryFractionClearing` and defines the canonical
height-one fraction order `Ring.weilFractionOrder` in
`Sheaf.RingTheory.HeightOneFractionOrder`. There is exactly one postponed theorem,
with proof `sorry`; the definition has real data and no postponed theorem dependency.
The natural-language item statement and its accepted four-step proof are unchanged.
The only additional statement dependency is the new fraction-order definition node.

### Stage handoff

The earlier BLOCKED ending confused stage-1 acceptance with stage-2 completion.
The live node has Q88's passing stage-1 review (ledger, 2026-10-23 11:35) but no
Lean record and no released repair note. The explicit stage handoff at the start of
coord/brief-stage2.md authorizes stating precisely this accepted split. No stage-1
fields are reopened. The retained sandbox contained no files when this attempt began.

### Hypothesis and conclusion correspondence

- A commutative Noetherian normal domain is `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]`. This is exactly the
  recorded normal-domain form, without a dimension bound on R.
- The fraction field K is the actual `FractionRing R`, with its canonical `algebraMap`.
- A finite set indexing distinct height-one primes is `(I : Type v) [Finite I]`,
  `p : I → Ring.WeilHeightOnePrime R`, and `hdistinct : Function.Injective p`.
  `WeilHeightOnePrime` has exactly the node's nonzero/minimal-prime-chain definition.
  No nonemptiness or enumeration is required; the index universe v is independent.
- The normalized additive valuation is `Ring.weilFractionOrder q x`. It subtracts
  the existing local length orders of a numerator and denominator in a genuine
  presentation of x. Tag 00PD proves v(a/b)=v(a)-v(b). For nonzero x the numerator
  and denominator are nonzero, and the height-one normal Noetherian localization
  is a DVR, so the orders are finite and this is the specified normalized valuation.
  Normalization is positive on a uniformizer, with value one; there is no sign reversal.
- The nonzero ring element τ is `(τ : R) (hτ : τ ≠ 0)`.
- Positive valuations at every listed prime are `hpositive : ∀ i : I,
  0 < weilFractionOrder (p i) (algebraMap R (FractionRing R) τ)`.
- Vanishing valuations of τ off the list are exactly `hτoutside`, quantified over
  every height-one prime q with `q ∉ Set.range p`.
- The nonzero fraction is `(f : (FractionRing R)ˣ)`. Every nonzero field element
  has exactly such a unit structure, so this covers the complete K^× of the node.
- Vanishing valuations of f off the list are exactly `hfoutside` on the same
  complement, using the coerced field element `(f : FractionRing R)`.
- The first conjunct is the existence of `N H : ℕ`. Natural exponents represent
  precisely the integers N,H≥0 of the node. It supplies `h h' : R` with their images
  equal respectively to `f * (algebraMap R K τ)^N` and
  `((f⁻¹ : Kˣ) : K) * (algebraMap R K τ)^H`.
- Its last equality `h * h' = τ ^ (N + H)` is in R itself, as requested.
- The second conjunct quantifies over EVERY `N H : ℕ` satisfying, for EVERY i,
  both `0 ≤ v_i(f) + (N : ℤ) * v_i(τ)` and
  `0 ≤ -v_i(f) + (H : ℤ) * v_i(τ)`. It gives the very same two membership
  witnesses and the very same product equality in R. Thus the more-precise clause
  is retained, not merely the existence of one convenient exponent pair.

No canonical map is replaced by an arbitrary map, no arbitrary valuation is a
hypothesis, and no additional dimension-one or DVR hypothesis is imposed on R.

### Dependency declarations and source inspection

Read the full item, all four stmt_deps, their recorded signatures/docstrings, and
the three distinct proof prerequisites. Used declaration interfaces:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with the standard `IsDomain` class for the normal-domain convention.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, used
  by the imported, existing `Ring.weilOrder` construction.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  its module is a public statement-dependency import and its notion explains the
  normalized valuation, although no extra DVR instance is a theorem hypothesis.
- `Sheaf.RingTheory.WeilDivisorClassGroup`: `Ring.WeilHeightOnePrime` and
  `Ring.weilOrder`, imported publicly by the new definition module.
- `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`; the imported
  `Mathlib.RingTheory.Localization.Defs` gives `IsLocalization.sec` and `sec_spec`.
- `WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`:
  `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span` (plain proof import).
- `WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes`:
  `Module.injective_pi_localization_associatedPrimes` (plain proof import).

The proof-only dependency `lem-trf-normal-domain-principal-divisor-kernel` has no
Lean record or Mathlib match in the live node. It is named in the proof docstring
but has no module to import. Nothing in this statement requires assuming its
conclusion: the valuation is independently constructed from the existing lengths.
Its future module import is for the maintainer when that theorem is stated.

Read Stacks algebra.tex at Tags 00PD, 031S, 031T, including the full denominator
argument for 031T(2). Read the latest blueprint's lem-trf-local-term-locality
statement/proof for the recorded ancestry. No source-based statement correction
was needed. No STATEMENT-DISPUTED issue was found.

### Edge cases checked before writing and in the second pass

- I empty: all index inequalities are vacuous, the outside condition applies to
  every height-one prime, and N=H=0 gives the source's unit conclusion. No `Nonempty`.
- R a field: the height-one type is empty. Injectivity forces I empty, and every
  nonzero fraction and its inverse already belong to R. No artificial dimension bound.
- R=k[t], boundary (t), τ=t, f=t^(-3): N≥3 and H≥0 meet the inequalities;
  N=3,H=0 gives h=1,h'=t^3 and product t^3. Larger admissible exponents are retained.
- τ a unit: positivity forces I empty; the outside hypotheses require the divisor
  of f to vanish. The theorem gives f and f inverse in R.
- R=k[x,y], boundary (x), τ=x, f=y/x: the outside valuation at (y) is nonzero,
  so the hypothesis correctly excludes this example. No Dedekind hypothesis is added.
- f=1, N=0 or H=0, and mixed positive/negative boundary values all have the stated
  signs. Distinctness is explicit. The zero ring is excluded by the domain hypothesis;
  f=0 and τ=0 are excluded exactly as in the node.

### Searches

Ran the prescribed msearch wrapper with LeanFinder for the full clearing statement;
results were Dedekind-domain adic valuations, finite support, and `Ring.ordFrac`.
No statement has both the general normal-domain scope and both clearing clauses.
Ran Loogle `Ring.ordFrac, IsIntegrallyClosed`: zero hits.
Ran grep `ordFrac|fraction.*clearing|clearing.*fraction` under Mathlib/RingTheory:
order-of-vanishing functions and general localization denominator helpers only.
Ran the item-id search in WeilConjectures: no hits. Ran rg and declaration-name
searches in both WeilConjectures and Sheaf: the affine prime/length declarations
above are the reusable exact prerequisites, and no item theorem exists.

For the new definition, raw wrapper results are embedded in its mathlib_searches:
LeanSearch for a normalized fraction order at a height-one prime of a Noetherian
normal ring; LeanFinder for extending the local length by numerator-minus-denominator;
Loogle as above; grep `weilFractionOrder|WeilHeightOnePrime|ordFrac`.
Read the actual returned `Ring.ordFrac` signature and implementation: it requires
`Ring.KrullDimLE 1` on its BASE ring. Applying it to R would exclude higher-dimensional
normal domains. Applying it to R_q requires dimension proof data not present in the
existing prime/order interface. Our small construction composes the already-owned
length orders with the standard fraction presentation and subtracts; it supplies no
second prime type, length, fraction ring, or arbitrary local valuation. Project DVR
norm and determinant formulas use ordFrac on an already-given DVR and are not this
normal-domain, prime-indexed interface.

Definition-node statement scan: no existing normalized height-one fraction-order
definition. `tools/blueprint_refs.py search 'fraction order'`: 0 matches;
`ancestor` confirms lem-trf-local-term-locality. The earlier kernel theorem mentions
valuations and asserts their properties but owns no definition module.

### Validation

scompile.py compiled BOTH delivered files separately in dependency order against
the live server library. Every reported sandbox/library compile passed cleanly,
with no errors or unexpected warnings; each reported compile took about 1.0–1.2 s.
All universes and variables are explicit. There are no file-local instances,
notations, private definitions, proof tactics beyond the one required sorry,
or delayed proofs used to supply definition data.

## New nodes

`def-trf-height-one-fraction-order` supplies the canonical integer order of a fraction
at a height-one prime of a Noetherian normal domain. Its source is the fraction
formula proved in Stacks 00PD and the length definition 02MD/02RJ. It uses the
existing `Ring.WeilHeightOnePrime` and `Ring.weilOrder` and Mathlib's actual `sec`
presentation; it does not pick a valuation by an unproved existence assertion.
The raw searches and the DAG/blueprint duplicate audit are recorded above and in
the node. The new node is a statement dependency of the item, and its own statement
dependencies cite the four original notions and the existing affine length-order
node. No existing node is redefined, and no dependency record needs repair.

### Dry-run repairs

The first server preflight found three metadata defects, all repaired: the live
blueprint ancestry includes lem-trf-complete-toric-monomial-factors (the older local
item ancestry omitted it); the live new-node schema requires `import_flags: []`;
and the signature parser records from `def`, excluding the `noncomputable` modifier.
No Lean statement or mathematical content changed. The new node's ancestry now
matches the current server item exactly.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
