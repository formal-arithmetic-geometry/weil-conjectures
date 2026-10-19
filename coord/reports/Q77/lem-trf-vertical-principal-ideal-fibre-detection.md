## Worker report

The new module `Sheaf.RingTheory.VerticalPrincipalIdealFibreDetection` states
`Ideal.span_singleton_eq_of_fibre_generic_localizations` with one `sorry` proof.
The node's statement, dependencies, proof, and all other existing fields are unchanged;
only `lean` is set. No new definition or dependency module is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fraction field is `(K : Type u) [Field K]`. The valuation domain is
  `(V : ValuationSubring K)`: this is the existing subring with the axiom
  `∀ x : K, x ∈ V ∨ x⁻¹ ∈ V`. Its canonical algebra map is the subring inclusion.
  Mathlib supplies both `IsDomain V` and `IsFractionRing V K`. The axiom at zero
  is automatic, so it is equivalent to the node's condition on nonzero elements.
- `[Finite (PrimeSpectrum V)]` says that there are finitely many prime ideals.
  Valuation-domain ideals are totally ordered, so the chain condition is already
  supplied by `ValuationSubring`. This retains the finite-chain assumption even
  though the recorded proof does not need its finiteness.
- `(B : Type v) [CommRing B] [Algebra V B]` supplies the commutative V-algebra,
  with no domain, nontriviality, or faithfulness assumption on B.
- `[Module.Flat V B]` is flatness, and `[Algebra.FinitePresentation V B]` is
  finite presentation. These are the ring counterparts of the recorded scheme
  dependencies: `AlgebraicGeometry.Flat.SpecMap_iff` identifies affine scheme
  flatness with the ring-map condition, and
  `AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff` identifies affine
  local finite presentation with ring finite presentation. Their recorded modules
  are publicly imported. No alternative flatness or finite-presentation definition
  is introduced, and no scheme universe equality is imposed.
- For every `p : PrimeSpectrum V`, its residue field is
  `p.asIdeal.ResidueField`, and its fibre ring is Mathlib's
  `p.asIdeal.Fiber B = p.asIdeal.ResidueField ⊗[V] B`.
- `hgeom` quantifies over every such p and field extension
  `(L : Type (max u v)) [Field L] [Algebra p.asIdeal.ResidueField L]`, and states
  `IsReduced (L ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B)`.
  Associativity, the canonical scalar extension, and tensor commutativity identify
  this with the node's `B ⊗[V] L`. There is no algebraicity, separability, or finite
  extension restriction. The common universe contains both the residue field and B;
  it includes the identity extension after universe lifting. Testing extensions in
  that universe is equivalent to testing arbitrary extensions: any purported
  nonzero nilpotent in a larger tensor product uses finitely many field coefficients;
  their generated subfield has size bounded by the residue field and countably many
  coefficients, and embeds into the larger field. Scalar extension between fields
  is injective on the underlying vector space, so the same nonzero nilpotent already
  appears over this small subfield. Thus the size convention loses no field tests.
  The explicit formulation avoids relying on an unstated arbitrary-extension API
  for `Algebra.IsGeometricallyReduced`.
- `(f g : B)` supplies the two elements. The generic fibre is literally `B ⊗[V] K`.
  `hf` and `hg` assert `IsUnit` of their images under the canonical `includeLeft`.
- `hlocal` quantifies over every p and every
  `ξ : PrimeSpectrum (p.asIdeal.Fiber B)`. Its premise
  `closure {ξ} ∈ irreducibleComponents (PrimeSpectrum (p.asIdeal.Fiber B))`
  is exactly the condition that ξ is a generic point of an irreducible component:
  by definition, ξ is generic for its closure, and every generic point of a component
  has that closure. Tensor commutativity identifies these points with the node's
  spectrum with the opposite tensor ordering.
- The inverse-image prime is
  `(ξ.comap (Algebra.TensorProduct.includeRight : B →ₐ[V] p.asIdeal.Fiber B)).asIdeal`.
  The binder `(q : PrimeSpectrum B)` is followed by the equality fixing it to this
  canonical contraction. This does not add a hypothesis to the theorem: `hlocal`
  universally quantifies over q, and its implication requires local equality only
  for that one canonical q. It avoids repeatedly unfolding the contracted prime
  inside the localization type. No arbitrary prime or comparison map is assumed.
- The two `Ideal.map` terms in `hlocal` extend `Ideal.span {f}` and `Ideal.span {g}`
  along `algebraMap B (Localization.AtPrime q.asIdeal)`. These are exactly `f B_q`
  and `g B_q`, including the case where either image is a unit.
  Using extension of ideals rather than spans of the localized images is the
  standard identical construction (`Ideal.map_span`).
- The conclusion `Ideal.span {f} = Ideal.span {g}` is precisely `fB = gB`.
  There is no added Noetherian, rank-one, discrete, nonempty-fibre, integral-B,
  or generic-domain hypothesis.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; ring rendering `Module.Flat` in
  `Mathlib.RingTheory.Flat.Basic`, with affine equivalence `Flat.SpecMap_iff`.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; ring rendering
  `Algebra.FinitePresentation`, with its `SpecMap_iff` equivalence.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`. For ring primes the more directly
  applicable dependency `def-weil-pbc-localization-at-prime` already records
  `Ideal.ResidueField`, so the statement uses that existing ring construction.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the underlying topological space is exactly
  `PrimeSpectrum`. The statement only needs this underlying space.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`, used literally.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`; `Ideal.Fiber`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`, all used literally.

The module docstring distinguishes the agent-reconstructed assertion from its
background reference, Stacks Tag 05CB (`lemma-zero-at-weakly-ass-zero`), whose source
was read. The theorem docstring includes all six proof steps, with denominator
cancellation, the quotient injection, weak-associated fibre identification,
reduced-fibre minimality, the annihilator-localization contradiction, and the two
ideal inclusions. The already stated proof dependencies are imported, including
`Module.Flat.rTensor_exact` / `lTensor_exact`, `TensorProduct`, `LocalizedModule`,
`PrimeSpectrum.zeroLocus_minimalPrimes`, the fibre-prime correspondence, and
`Ideal.nonempty_minimalPrimes`. The proof-only prerequisite
`lem-trf-flat-tensor-weakass-fibre` currently has neither a Lean record nor a
Mathlib match and is unsplit; it is not required to type the present statement,
and no nonexistent module is imported for it. Its prescribed role is explicitly
recorded in proof-plan step 3.

Edge cases checked before writing:

- V may itself be a field (`V = ⊤`); there is one base prime, retained in the test.
- B may be the zero ring. Its fibres and their prime spectra are empty, the local
  condition is vacuous, and its two principal ideals are equal. No binder excludes it.
- Individual fibres may be empty even when B is nonzero; universal quantification
  over their points is vacuous, exactly as in the node. No surjectivity is assumed.
- The identity residue-field extension is included (using a common universe lift).
  Positive characteristic, imperfect residue fields, inseparable extensions, and
  transcendental extensions are all allowed.
- The finite valuation chain need not have height one or be discrete or Noetherian.
- B can have several components and zero divisors; the test ranges over every
  generic point, and no associated-elements lemma requiring B to be a domain is used.
- f and g need not be nonzero as an extra assumption. Their generic-unit conditions
  handle exactly the degenerate cases, including the zero generic fibre.
- Universes u and v are explicit and independent; the extension test universe is
  their maximum, not an unrelated smaller universe.

Searches made (the wrapper's exact logs remain in sandbox `searches.jsonl`):

1. `msearch.py leanfinder`: "Equality of principal ideals in a flat finitely presented
   algebra over a valuation domain with geometrically reduced fibres is detected by
   localization at the generic points of all fibres". Eight hits, including
   `Algebra.ZariskisMainProperty`, `Algebra.HasGoingDown.of_flat`,
   `ideal_eq_bot_of_localization'`, Dedekind-domain localization results, and
   `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal`.
   None states detection of equality at fibre-generic primes.
2. `msearch.py leansearch`: "Equality of vertical principal ideals detected at generic
   points of fibres over valuation ring". Eight hits about principal valuation ideals,
   valuation bounds, and discrete/Dedekind valuations; none matches this statement.
3. `msearch.py loogle`: `IsValuationRing, Ideal.span, Localization.AtPrime` returned
   zero hits and noted that `IsValuationRing` is unknown. Corrected the expected name
   and searched `ValuationRing, Ideal.span`; zero hits. Local source then gave the
   correct directly applicable `ValuationSubring` construction.
4. `msearch.py grep`, subdirectory `RingTheory`:
   `IsGeometricallyReduced|GeometricallyReduced|span_singleton_eq` returned 25 hits,
   mostly principal-span lemmas. `Ideal.span_singleton_eq_span_singleton` assumes
   a domain and does not provide this detection assertion. Direct local searches
   additionally located `Algebra.IsGeometricallyReduced`; its source and docstring
   were read, and the theorem instead uses the node's explicit field-extension tests.
5. `rg` in Mathlib, upstream `WeilConjectures/`, and shared `lean/Sheaf/` searched
   `vertical.*principal|principal.*fibre|principal.*fiber|span.*eq.*fibre|span.*eq.*fiber`.
   Only unrelated principal-fibre results and this item's mention in
   `ValuationSmoothBranchesStrictChart.lean` appeared. That consumer was opened;
   it needs exactly equality of the two ideals on the overlap.
6. `grep -rn lem-trf-vertical-principal-ideal-fibre-detection` in upstream
   `WeilConjectures/` found no declaration. `rg` in `dag/lean_names_upstream.json`
   for expected geometric/valuation/detection names found no matching declaration.

No statement correction, new node, dependency repair, or statement dispute is needed.
The first compile reached the default elaboration-heartbeat limit while the fully
expanded contraction occurred repeatedly inside localization types. The statement
was rewritten with the universally bound q and its defining equality, as above; no
mathematical assumption was changed and no compile limit was increased. Compilation
and delivery validation are recorded below after running the wrappers.

## Second reading by Q77

The dispatcher explicitly forbids starting other agents and assigns the independent
reading to the maintainer after delivery. This section records the same worker's
second pass, not a claim of independent review. Reopened the complete node and final
module, and checked the correspondence above: the finite valuation chain, flatness,
finite presentation, all residue-field extensions, generic unit conditions, all
fibre-component generic points, canonical contractions, prime localizations, and
principal-ideal equality each occur with the same meaning. In particular the tensor
factor switch uses the canonical commutativity isomorphism, and no fibre is omitted.
No mismatch or change to the natural-language node was found.

## Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q77
lem-trf-vertical-principal-ideal-fibre-detection
<delivery>/lean/Sheaf/RingTheory/VerticalPrincipalIdealFibreDetection.lean`
passed both the sandbox-name and final-library-name checks, exit code 0, with no
errors or unexpected warnings. The wrapper retained its default 60-second limit
per Lean invocation; its reported elapsed times include shared-slot waiting.
The final node differs from the repository only in `lean`, its stored signature
matches the file verbatim, all variables and universes are explicitly bound, and
the maximum source line length is 93 characters.

The prescribed `deliver2.py Q77 lem-trf-vertical-principal-ideal-fibre-detection
--no-push` dry run printed `OK (dry run)`: its commit passed preflight and compiled;
nothing was pushed by that validation run.
