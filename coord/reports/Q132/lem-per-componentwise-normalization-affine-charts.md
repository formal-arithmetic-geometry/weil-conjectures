## Worker report

States `AlgebraicGeometry.componentwise_normalization_affine_charts` in
`Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts`. The theorem has `sorry`
as its entire proof. There are no new definitions, new nodes, dependency repairs, or
statement corrections. Only the item's `lean` field changes. Its earlier declaration
was deleted as dead code; it is absent from both current source roots, so this delivery
supplies its statement again using the current recorded interfaces.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-description-normalization` (Tag 035P), especially (1), (3), (4), and
`lemma-normalization-in-terms-of-components` (Tag 0CDV). The former identifies the
inverse image of an affine open with the integral closure in the total fraction ring,
and identifies that closure with the product of the closures of minimal-prime
quotients. The latter identifies the normalization with the componentwise coproduct.
No excellence, Nagata, finite-type, or module-finiteness hypothesis is present or added.

Hypotheses and clauses, matched against the node:

- Reduced locally Noetherian scheme: `(X : Scheme.{u}) [IsReduced X]
  [IsLocallyNoetherian X]`. These are the dependency nodes' Mathlib predicates.
- Componentwise normalization and its specified morphism: exactly
  `X.reducedNormalization` and `X.fromReducedNormalization` from the recorded
  `Sheaf.AlgebraicGeometry.ReducedNormalization`; no replacement normalization.
- Affine open U = Spec A: `(U : X.affineOpens)`; everywhere A is `Γ(X, U)`.
  `U.2.isoSpec` is the canonical identification with its affine spectrum.
- Finitely many minimal primes, with a repetition-free enumeration: existential `t : ℕ`
  and `p : ULift.{u} (Fin t) → PrimeSpectrum Γ(X, U)`, with `Function.Injective p`
  and `Set.range (fun i ↦ (p i).asIdeal) = minimalPrimes Γ(X, U)`.
  Prime-spectrum points bundle actual prime ideals; the range equation says precisely
  that they are all and only the minimal primes. ULift changes no finite indexing data
  and places the finite family in the universe required by Mathlib's `sigmaSpec`.
- Quotient domains and their fraction fields: `Γ(X, U) ⧸ (p i).asIdeal` and
  `FractionRing (Γ(X, U) ⧸ (p i).asIdeal)`. Each ideal is prime, so the quotient is
  a domain and this fraction ring is its field of fractions. There is no independently
  chosen field or arbitrary identification.
- Integral closures B_i: exactly `integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
  (FractionRing (Γ(X, U) ⧸ (p i).asIdeal))` at every occurrence. The existing
  Mathlib algebra structure is its canonical inclusion of the quotient.
- First isomorphism: `e₁` has source `(X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme`
  and target the scheme coproduct of `Spec (.of B_i)`.
- Second isomorphism: `e₂` has source that coproduct and target `Spec (.of (Π i, B_i))`.
  `e₂.hom = sigmaSpec ...` fixes the canonical finite-product comparison, including
  its coprojections as spectra of the evaluation maps.
- Structural ring map: `RingHom.pi` of the composites
  `(algebraMap (A ⧸ p_i) B_i).comp (Ideal.Quotient.mk p_i)` explicitly sends a to
  the tuple of its quotient classes, included in the integral closures. The displayed
  equation `e₁.hom ≫ e₂.hom ≫ Spec.map ... ≫ U.2.isoSpec.inv =
  X.fromReducedNormalization ∣_ U.1` makes the identifications isomorphisms over U,
  with exactly that structural map. Together with the canonical component coproduct
  and quotient maps it expresses the canonical affine chart identification.
- Empty U: `U.1 = ⊥ → t = 0 ∧ Subsingleton (Π i, B_i) ∧ IsEmpty (∐ ...) ∧
  IsEmpty (X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme` explicitly includes the
  empty enumeration, zero (one-element) product ring, empty coproduct, and empty preimage.
  The isomorphism also makes the spectrum of the empty product empty.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`:
  section-wise reducedness, with its stalk equivalence; renders def-pc-reduced-scheme.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`:
  every affine open has Noetherian sections; renders pqf-def-locnoeth.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`,
  `AlgebraicGeometry.Scheme.reducedNormalizationComponent`,
  `isIntegral_reducedNormalizationComponent`, `reducedNormalization`,
  `fromReducedNormalization`: reduced induced components and their normalization coproduct.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`:
  the actual spectra and contravariant ring-induced maps.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`:
  subalgebra of integral elements, with its actual ring and algebra structures.
- `Mathlib.AlgebraicGeometry.Limits`, the small-index coproduct instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι`, `sigmaSpec`, `ι_sigmaSpec`,
  and the finite-index `IsIso (sigmaSpec ...)` instance: the recorded coproduct-family
  match and finite affine coproduct match.

Proof dependency modules are imported: affine Noetherian rings in
`Mathlib.AlgebraicGeometry.Noetherian`; finite minimal primes in
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`; components of spectra in
`Mathlib.RingTheory.Spectrum.Prime.Topology`; open restriction and coverage of
components in `Mathlib.Topology.Irreducible`; the reduced induced structure in
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`; function fields
in `Mathlib.AlgebraicGeometry.FunctionField`. The normalization-in-extension
interface `Scheme.normalizationIn`/`fromNormalizationIn` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` is already exposed by
ReducedNormalization's public import. The declaration docstring carries all seven
proof steps and names their DAG dependencies.

Edge cases checked mathematically before writing: U empty, X empty, a normal domain
(one factor equal to A), a cusp k[t²,t³] (one factor k[t]), a node k[x,y]/(xy)
(two normalized components), and k×k (both factors retained). No `Nonempty U`,
`Nontrivial A`, positive t, or finiteness of normalization is assumed. In particular,
the empty case is possible and explicitly stated. All universe variables and theorem
binders are explicit; the only universe is u.

Searches actually run:

- msearch.py leanfinder: "Componentwise normalization of a reduced locally Noetherian
  scheme over an affine open is the spectrum of the product of integral closures of
  minimal prime quotients in their fraction fields". Eight hits, all relative
  normalization interfaces, not the componentwise chart theorem.
- msearch.py leansearch: "The normalization of a reduced locally Noetherian scheme on
  an affine open is the spectrum of the product of integral closures of minimal prime
  quotients". Eight hits, relative-normalization construction and maps only.
- msearch.py loogle: `"sigmaSpec"`. Eight hits, including the exact canonical finite
  coproduct comparison and its isomorphism instance, which this statement uses.
- msearch.py grep: `normalization.*[Aa]ffine|[Aa]ffine.*normalization|sigmaSpec`,
  Mathlib AlgebraicGeometry. Seventeen hits: relative normalization and sigmaSpec;
  no componentwise absolute-normalization chart theorem.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the declaration name,
  componentwise normalization, normalization/affine, and sigmaSpec. Current componentwise
  normalization definitions exist and are used; other affine normalization charts have
  different hypotheses or relative morphisms. No exact chart theorem exists. Exact
  blueprint-id grep in `lean/WeilConjectures` and declaration-name search in both roots
  and `dag/lean_names_upstream.json` return no match.

Validation: scompile.py Q132 lem-per-componentwise-normalization-affine-charts compiled
this file in both sandbox module mode (5.1 s) and its actual library module (8.9 s),
with exit code 0 and no compiler diagnostics. No local compiler or global build was run.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
