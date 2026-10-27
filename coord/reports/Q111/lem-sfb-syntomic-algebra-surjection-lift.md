## Worker report

The module `Sheaf.RingTheory.SyntomicAlgebraSurjectionLift` states
`Algebra.exists_syntomic_algebra_lift_of_surjective`, with its sole theorem proof
`sorry`. It formalizes Stacks 07M8(1), using the syntomic definition of 00SL and
the zero-ring convention of 00S9. No definitions or extra nodes are needed.
The accepted stage-1 statement, split, and dependencies are preserved verbatim;
the only node change is its Lean record.

Clause-by-clause correspondence:

- Commutative unital rings R and R₀: `{R : Type u} {R₀ : Type v}` and their
  `CommRing` instances. Ring homomorphisms in Lean preserve the identity.
- The surjection π: `(π : R →+* R₀) (hπ : Function.Surjective π)`.
- Its kernel I: `RingHom.ker π`, used directly rather than an extra parameter
  that would require the equation I = ker π.
- The commutative R₀-algebra B₀: `(B₀ : Type w) [CommRing B₀] [Algebra R₀ B₀]`.
- Flatness of R₀ → B₀: `[Module.Flat R₀ B₀]`. By the recorded
  `RingHom.flat_algebraMap_iff`, this is exactly flatness of its structure map.
- Finite presentation of R₀ → B₀: `[Algebra.FinitePresentation R₀ B₀]`.
- Every prime fibre is lci: `hci₀ : ∀ p : PrimeSpectrum R₀,
  IsLocalCompleteIntersection p.asIdeal.ResidueField
  (p.asIdeal.ResidueField ⊗[R₀] B₀)`.
  `PrimeSpectrum` ranges over all prime ideals. `Ideal.ResidueField` is the
  residue field of the localized local ring and has Mathlib's
  `IsFractionRing (R₀ ⧸ p.asIdeal)` instance, so it is precisely the field in
  the node. Mathlib's `Spec.residueFieldIso` identifies it with the scheme
  residue field recorded on the dependency. The tensor factors are exchanged
  relative to the displayed B₀ ⊗ κ(p) by the canonical commutativity algebra
  isomorphism; this is the standard fibre convention already used by
  `Ideal.Fiber`. No fibre or prime is omitted.
- Existence of a commutative R-algebra B: `∃ (B : Type u) (_ : CommRing B)
  (_ : Algebra R B)`. Using universe u is legitimate: a finite-presentation
  lift is a quotient of a finite polynomial algebra over R and can be chosen
  in R's universe. The input algebras have independent universes v and w;
  no equality between their universes is assumed.
- The lift is finitely presented: the existential instance
  `(_ : Algebra.FinitePresentation R B)`.
- The lift is flat: the conjunct `Module.Flat R B`.
- Every fibre of the lift is lci: the conjunct `∀ p : PrimeSpectrum R,
  IsLocalCompleteIntersection p.asIdeal.ResidueField
  (p.asIdeal.ResidueField ⊗[R] B)`. Finite type of both input and output
  fibres is inferred from finite presentation and Mathlib's base-change
  instances; it is not an additional hypothesis.
- IB is the extended ideal: `(RingHom.ker π).map (algebraMap R B)`.
- The isomorphism β is a ring equivalence from the quotient by this exact
  ideal to B₀. Its scalar equation, for every r : R, is
  `β (Ideal.Quotient.mk _ (algebraMap R B r)) = algebraMap R₀ B₀ (π r)`.
  This expresses exactly the R₀-algebra isomorphism in the node: for any
  r₀ choose a preimage r using hπ; the induced R₀-action on the quotient
  sends r₀ to the residue class of algebraMap R B r. Independence of the
  preimage is exactly quotienting by the image of ker π. Thus the equation
  is equivalent to β commuting with every R₀ scalar, and the inverse also
  preserves scalars. No arbitrary R₀-algebra structure is substituted.
- There are no nilpotence, Noetherianity, locality, characteristic, or
  nontriviality hypotheses on any ring. The stated absence of restrictions
  is implemented by having no corresponding binders.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`, and its `Module.Flat` notion.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and the algebra tensor-product
  API imported through `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`:
  `TensorProduct`, `Ideal.Fiber`.
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `AlgebraicGeometry.Scheme.Spec.residueFieldIso`; the ring-level
  `Ideal.ResidueField` interface is in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and supplies the fraction
  field of the prime quotient. The dependency's recorded scheme notion is
  usable via the existing affine comparison; no repair or duplicate is needed.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection` and
  `Algebra.IsLocalCompleteIntersection`; the latter is the actual predicate
  appearing in both fibre clauses, including its empty-spectrum/zero case.
- `Mathlib.RingTheory.FiniteStability` supplies finite presentation and finite
  type after scalar extension. This import resolves the otherwise missing
  finite-type instances required by the lci predicate.

The modules of all currently recorded proof dependencies are imported as plain
imports (apart from those already public statement imports):
`WeilConjectures.RingTheory.SymmetricProjectivePresentationConormal`,
`WeilConjectures.RingTheory.SymmetricAlgebraSmooth`,
`WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionFlat`,
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`,
`WeilConjectures.AlgebraicGeometry.LiftProjectiveModuleEtale`,
`WeilConjectures.RingTheory.SymmetricAlgebraBaseChange`, and
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`.
The following proof nodes have no recorded module on the read base, so there
is no module to import yet: lem-sfb-syntomic-presentation-conormal-fibre-rank,
lem-sfb-syntomic-smooth-composition, lem-weil-pbc-conormal-free-presentation-basis,
lem-sfb-equation-count-closed-fibre-localization,
lem-weil-pbc-presentation-base-change, and lem-sfb-syntomic-polynomial-fibre-cut.
They are preserved as proof dependencies; none is needed to type this statement.

Edge cases checked against the definitions and source:

- B₀ = 0: take the zero R-algebra, which is flat and finitely presented as
  R/(1); its fibres are zero and lci by 00S9. There is no Nontrivial binder.
- R₀ = 0 and I = R: its unital algebra B₀ is necessarily zero; the same
  construction applies. There are no primes in R₀, as required.
- I = 0 / π an isomorphism: transport B₀'s algebra structure along π; the
  quotient is by zero, and the scalar equation is the expected one.
- Arbitrary nonnilpotent kernel, e.g. Z → F_p: the statement places no
  nilpotence assumption on its kernel. Singular syntomic fibres such as
  F_p[x]/(x²) are allowed, so smoothness has not replaced syntomicity.
- Empty prime spectrum or empty principal-open covers: the existing lci
  definition and zero convention allow these. No nonempty cover is imposed.
- Zero variables, equations, and complement rank in the proof route are
  permitted; no positive integer or dimension restriction occurs here.
- Independent input universes u, v, w and the chosen small lift do not
  restrict the input or test-prime quantification.

Searches for an existing theorem (2026-10-23):

- `msearch.py leanfinder`, query “Every syntomic algebra over the target of a
  surjective ring homomorphism lifts to a syntomic algebra over its source”:
  eight hits, principally formally smooth lifting of maps with nilpotent
  kernels; none lifts syntomic algebra objects along arbitrary surjections.
- `msearch.py loogle`, query `Algebra.FinitePresentation, Function.Surjective`:
  eight hits on finite-presentation quotients and finite modules, not this
  syntomic object-lifting statement.
- `msearch.py leansearch`, query “Syntomic algebras lift along surjective ring
  maps”: eight hits on formally smooth map lifting with nilpotent kernels,
  formally etale surjections, and RingHom.liftOfSurjective; no exact match.
- `msearch.py grep`, query `syntomic|surjection.*lift|lift.*surjection`,
  subdirectory `RingTheory`: zero hits.
- Direct rg searches for `Syntomic|syntomic|surjection_lift|surjectionLift`
  in the upstream and Sheaf RingTheory directories found presentation,
  local kernel and filtered-colimit results, not arbitrary-surjection lifts.
- Direct rg over all `lean/WeilConjectures` for this blueprint id: no hit.
- Direct rg over all `lean/Sheaf` and `lean/WeilConjectures` for
  `surjection_lift|surjectionLift|exists_syntomic|lift.*syntomic` found only
  polynomial-fibre comparison and filtered-colimit descent.
- Direct rg for a syntomic definition across Mathlib, upstream, and Sheaf
  found the specialised `stageSyntomic` and scheme affine-chart predicates,
  not a general ring-level syntomic predicate needing reuse. The existing
  primitive notions suffice without a new notion.

Source checked: `smoothing.tex`, proposition-lift-smooth, entire statement and
proof (Tag 07M8); `algebra.tex`, definition-lci (00SL) and definition-lci-field
(00S9). The source agrees with every hypothesis and clause. No
STATEMENT-DISPUTED flag or statement correction is needed.

Validation: prescribed `scompile.py` compiled both the sandbox and the actual
module name successfully, within the 60 second per-file limit and with no
unexpected warnings. Every universe and variable is explicitly bound; there
are no diagnostic commands, private notions, or file-local instances.

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
