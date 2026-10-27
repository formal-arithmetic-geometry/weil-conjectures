## Worker report

States `IsDiscreteValuationRing.separable_residue_differential_basis` in
`Sheaf.RingTheory.DvrSeparableResidueDifferentialBasis`. The theorem has one `sorry`;
there are no definitions, helper theorems, axioms, or proved results. The node copy
changes only `lean`, with the signature copied verbatim from the module. No new
nodes, dependency repairs, or statement corrections are required.

The sources read are Stacks `curves.tex`, Tag 0C1E,
`lemma-uniformizer-works` (lines 2411–2430), and `algebra.tex`, Tag 00TU,
`lemma-computation-differential` (lines 38687–38737). The current blueprint is
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-finite-map/`:
its unit proof, third paragraph, explicitly uses separability of the residue
extension to conclude that the uniformizer differential generates. This module
states the local algebra used by that paragraph, with the full additional
conclusions in the assigned DAG node.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The ring is `(A : Type v) [CommRing A]`,
  with independent explicit universes `u v`. The map from the field into the ring
  is `[Algebra k A]`; its composition with the quotient map gives the induced
  residue-field algebra. There is no essentially-finite-type or smoothness
  assumption on this local algebra.
- `[IsNoetherianRing A]` states precisely Noetherianity.
  `[IsDomain A] [IsDiscreteValuationRing A]` states the DVR hypothesis.
  The recorded Mathlib DVR class extends `IsPrincipalIdealRing A` and
  `IsLocalRing A` and asserts that `IsLocalRing.maximalIdeal A` is nonzero.
  Thus locality is included without introducing a second local-ring instance.
- The maximal ideal is `IsLocalRing.maximalIdeal A`. Its residue field is
  Mathlib's `IsLocalRing.ResidueField A`, definitionally the quotient of A by
  that maximal ideal. Its field structure and induced k-algebra are canonical.
- Finiteness of the residue extension is
  `[Module.Finite k (IsLocalRing.ResidueField A)]`, i.e. finite vector-space
  dimension. Separable algebraicity is
  `[Algebra.IsSeparable k (IsLocalRing.ResidueField A)]`, exactly the recorded
  dependency; algebraicity follows already from this class (and from finiteness).
  The more general `Algebra.IsSeparableExtension` is used only by the proof plan.
- The universal differential module and derivation are
  `KaehlerDifferential k A` and `KaehlerDifferential.D k A`, respectively.
  The hypothesis `hfree : Nonempty (Module.Basis (Fin 1) A
  (KaehlerDifferential k A))` says that this module is free of rank one.
  It does not select a basis or impose a new property of the derivation.
- `(t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t})` quantifies over
  every generator of the maximal ideal, with exactly the node's equality m=tA.
- The first conjunct supplies `htmem : t ∈ IsLocalRing.maximalIdeal A` and says
  `(IsLocalRing.maximalIdeal A).toCotangent ⟨t, htmem⟩ ≠ 0`. This is the actual
  class in m/m² using Mathlib's `Ideal.Cotangent`, rather than a different
  quotient or an arbitrary map. The membership proof is existential because
  the element of m used by the quotient map requires it; it is implied by ht.
- The second conjunct is literally
  `(KaehlerDifferential.D k A t) ⊗ₜ[A] (1 : IsLocalRing.ResidueField A) ≠ 0`,
  in the order of the tensor factors specified in the node.
- The final conjunct quantifies over every rank-one basis
  `e : Module.Basis (Fin 1) A (KaehlerDifferential k A)`. Its sole vector is
  `e 0`. Indexing a singleton basis by `Fin 1` loses no choice of basis vector;
  every rank-one basis can be reindexed this way. It supplies `a : A` and states
  `D t = a • e 0`, together with
  `∀ a' : A, D t = a' • e 0 → a' = a`. These are existence and uniqueness of
  the coefficient, and `IsUnit a` states precisely that this coefficient is a unit.
- For each such basis and its unique coefficient, the conclusion supplies
  `φ : A ≃ₗ[A] KaehlerDifferential k A`, states
  `∀ b : A, φ b = b • KaehlerDifferential.D k A t`, and states the inverse
  formula `∀ c : A, φ.symm (c • e 0) = c * Ring.inverse a`.
  This is an A-linear isomorphism, with the specified forward and inverse maps.
  `Ring.inverse` is Mathlib's inverse on units, extended by zero to nonunits;
  `IsUnit a` makes it exactly the node's a⁻¹. The rank-one hypothesis ensures
  the universal quantification over e is inhabited, so the isomorphism assertion
  is not vacuous.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (definition and docstring at lines 193–197).
- `def-sc-discrete-valuation-ring`: its `mathlib_match`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`
  (docstring and full class at lines 56–60). There is no Lean record on this
  Mathlib leaf; its recorded match is used directly.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`
  (docstring and full fields at lines 89–100), with the canonical induced
  residue algebra. The residue carrier and quotient map were checked in
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs`, lines 23–39.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable` (docstrings and signatures, lines 533–570).
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation` (lines 145–158, 196–215,
  323–332). The module uses the recorded concrete universal construction.
- The extra statement notation is standard Mathlib: `Module.Basis`, whose full
  data are the coordinate linear equivalence (`LinearAlgebra.Basis.Defs`,
  lines 78–96), and `Ideal.toCotangent` (`RingTheory.Ideal.Cotangent`,
  lines 39–54). `Ring.inverse` was read with `inverse_of_isUnit` and the two
  cancellation lemmas (`Algebra.GroupWithZero.Units.Basic`, lines 75–106).
- Proof dependency imports are
  `WeilConjectures.FieldTheory.SeparableExtension`
  (`Algebra.IsSeparablyGenerated`, `Algebra.IsSeparableExtension`),
  `Mathlib.RingTheory.AlgebraicIndependent.Defs` (`IsTranscendenceBasis`),
  `WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective`
  (`Algebra.separable_residue_cotangent_injective`), and
  `Mathlib.LinearAlgebra.FreeModule.Basic` (`Module.Free`). Their signatures
  and docstrings were read. The cotangent injection assumes a Noetherian local
  k-algebra, finite field generation and general separability; the docstring's
  Step 2 explains explicitly how finite separable algebraicity supplies the last
  two hypotheses. The module docstring and theorem docstring name both source
  tags and the node; the theorem docstring carries all five DAG proof steps.

Edge cases checked mathematically before writing:

- A field cannot be a DVR here: Mathlib's class requires a nonzero maximal
  ideal. A zero ring is excluded by `IsDomain A`; a field base also excludes
  a zero field. No vacuous field case is accidentally added.
- t=0 cannot generate the nonzero maximal ideal. For a genuine generator,
  t=t²b would force 1=tb in m by domain cancellation, so the cotangent
  nonvanishing clause is correct.
- For A=k[T] localized at (T), with t=T, Ω is freely generated by dT;
  the coefficient is 1. Replacing t by any unit multiple still gives a unit
  residue coefficient and all clauses persist. In a basis e=u dT the coefficient
  for dT is u⁻¹; the displayed inverse sends c e to cu as required.
- At a nonrational separable closed point of the affine line, for an irreducible
  separable polynomial P, t=P(T) has dt=P'(T)dT. Its residue is nonzero and
  P'(T) is a unit of the local ring, so the statement includes nontrivial finite
  separable residue extensions and every characteristic.
- Separability is essential: over k=F_p(a), localization at (T^p-a) gives a
  uniformizer with zero differential. This fails the stated residue separability
  hypothesis, so it is correctly excluded without restricting characteristic.
- No assumption is made on completeness. A power-series example can only be
  used when its ordinary algebraic differential module satisfies the explicit
  rank-one hypothesis; continuous differentials are not substituted for Ω.
- The rank-one basis is nonempty and has exactly one index; arbitrary sets,
  zero-rank modules, or small-universe tests are not used in place of it.

Searches actually run for this delivery:

1. `msearch.py ... leanfinder`, query:
   `For a DVR over a field with finite separable residue field and free rank one Kahler differentials, the differential of any uniformizer is a basis`.
   Eight hits: submersive-presentation differential bases and generators'
   cotangent bases. Read the relevant `basisKaehler` and `basisKaehler_apply`
   signatures and docstrings in `Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`.
   These require presentations and do not state the assigned DVR theorem.
2. `msearch.py ... loogle`, query `KaehlerDifferential, IsDiscreteValuationRing`:
   zero hits.
3. `msearch.py ... grep`, query
   `uniformizer.*differential|differential.*uniformizer|cotangent.*Kaehler`,
   subdirectory `RingTheory`: fifteen hits, all in general smooth presentation,
   cotangent and Jacobi–Zariski code. None is this result.
4. `msearch.py ... leansearch`, query:
   `The differential of a uniformizer of a discrete valuation algebra with finite separable residue field freely generates its rank one Kahler differential module`.
   Eight hits: KaehlerDifferential, its derivation and categorical versions,
   a valuative uniformizer constructor and presentation differentials. None
   states the theorem.
5. `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
   `uniformizer.*differential|differential.*uniformizer|separable_residue_cotangent`,
   and for `uniformizer_differential_basis|dvr_separable_residue|separable_residue_differential`.
   The existing `AlgebraicGeometry.uniformizer_differential_basis` is geometric:
   a smooth integral curve and closed point, concluding only DVR and bijectivity.
   Its complete signature and docstring were read; it neither states the general
   local-algebra hypotheses nor the extra conclusions of this item. The
   existing cotangent injection is a proof input, not this statement. Other hits
   are callers or residue constructions. No exact attachment exists.
6. `rg` for the assigned node id in `lean/WeilConjectures` gave no hit.
   Searching `dag/lean_names_upstream.json`, `lean/WeilConjectures`, `lean/Sheaf`
   and Mathlib for `separable_residue_differential_basis` and
   `DvrSeparableResidueDifferentialBasis` gave no existing declaration or module.
   The assigned node and all five statement dependency records were read in full
   at their relevant statement/Lean interfaces. No released repair note exists.

Validation: the module compiled through the prescribed `scompile.py` against the
published live library, both as the sandbox probe and at its final module path,
with no errors or warnings (1.2 s and 1.1 s). `autoImplicit` is explicitly false;
all variables and universes are bound, the longest Lean line is 95 characters,
and the only postponed proof is the named main theorem. No statement dispute
or node fault was found. The mandatory delivery dry run is run before pushing.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
