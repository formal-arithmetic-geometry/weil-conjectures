## Worker report

This repair retains the saved node and the theorem name, and corrects its Lean rendering.
The node's mathematical statement, proof, and dependency lists are unchanged. The module
`Sheaf.TraceFormula.CompleteToricKatoRecognition` states
`complete_toric_kato_recognition` with exactly one `sorry` proof. Its only new data are
canonical chart maps and the actual principal quotient ring, built from existing maps.

The final self-check found these defects in the saved packet and repaired them:

- `[CommMonoid P]` and `[AddCommMonoid P]` were unrelated structures. The old fs
  hypothesis constrained the former, while the toric algebra used the latter. Now
  `[AddCommMonoid P]` is the only structure and
  `hP : IsFineSaturatedMonoid (Multiplicative P)` constrains that same monoid.
- Both coefficient rings and the Cohen congruence were required even for the field
  case. The new theorem has two independent universally quantified conjuncts,
  one for each alternative, as does the existing normality theorem.
- Equality of the carrier type of an arbitrary `R` with a model did not identify
  its ring operations. Each clause now uses the model's actual ring structure.
- The saved helpers duplicated the complete models already supplied by
  `lem-trf-log-regular-saturation-normality`. The duplicate polynomial ideal,
  completed ring, boundary ideal, and monomial functions have been removed.
  The canonical maps use the published model directly.
- The saved `lean.statement` lacked the theorem keyword and name. It now records
  the full declaration signature, excluding the final proof assignment delimiter,
  exactly as preflight extracts it. The docstring now contains all nine proof steps.
- The obsolete `Sheaf.RingTheory.CohenRing` import was replaced by the published
  upstream Cohen-ring dependency, obtained through the model module. This avoids
  importing two modules that define `IsCohenRing`.

Each hypothesis and clause is rendered as follows:

- The finitely generated, integral, saturated additive commutative monoid is
  `(P : Type u) [AddCommMonoid P]` and `hP` above. Reading the actual fs definition
  shows finite generation by `Submonoid.closure`, injectivity of the canonical
  Grothendieck-group map, and closure under positive integral roots. The
  `Multiplicative` tag changes notation, not the operation.
- Sharpness is `hsharp : ∀ q : P, IsAddUnit q → q = 0`.
- The nonnegative number of variables is `n : ℕ`; variables are indexed by `Fin n`
  in the published model.
- Finite monoid polynomials are `MvPolynomial (Fin n) (AddMonoidAlgebra L P)`.
  `AddMonoidAlgebra.localModelBoundaryIdeal` spans the nonzero monomials and the
  variable range. `localModelCompletionIdeal` adds the image of the coefficient
  maximal ideal, and `CompletedLocalModel` is `AdicCompletion` at that ideal.
  This is exactly the node's `B_L(P,n)`, rather than an abstract completed algebra.
- Alternative (i) is the first conjunct, `∀ (k : Type v) [Field k], ...`, using
  `CompletedLocalModel k P n` with its canonical ring structure.
- Alternative (ii) is the second conjunct, quantifying `(C : Type v) [CommRing C]
  [IsLocalRing C] (p : ℕ)` with `IsCohenRing p C`. The predicate includes
  `Nat.Prime p`, domain and DVR structures, the maximal-ideal equality with `(p)`,
  and `p`-adic completeness. It does not assume a perfect or finite residue field.
- The Cohen parameter is `θ : CompletedLocalModel C P n` with exactly
  `θ - (p : CompletedLocalModel C P n) ∈ completedLocalModelBoundaryIdeal C P n`.
  That boundary ideal is the image of the nonzero-monomial and variable ideal
  under the canonical completion map. `cohenCompleteToricRing` is precisely the
  quotient by `Ideal.span {θ}`; no quotient structure is assumed or chosen.
- The indicated monomial map is `completeToricChart`: the composite of
  `AddMonoidAlgebra.of L P`, `MvPolynomial.C`, and the canonical `algebraMap` into
  completion. The Cohen chart is that composite followed by `Ideal.Quotient.mk`.
  In particular its value at `Multiplicative.ofAdd q` is exactly the completed
  image of `MvPolynomial.C (AddMonoidAlgebra.single q 1)` (and its quotient image).
  There is no arbitrary chart or compatibility hypothesis in the final statement.
- The multiplicative set in each clause is `Submonoid.map chart ⊤`, which is the
  image of all chart monomials. The chart is a monoid homomorphism by composition
  of the existing homomorphisms, so this is exactly the stated multiplicative set.
- `Localization` is Mathlib's fraction localization with the node's equivalence
  relation, and the localization homomorphism is its canonical `algebraMap`.
- The left side is the inverse image of `{x | IsUnit x}` under that homomorphism.
  The right side is `{x | ∃ a : R, IsUnit a ∧ ∃ q : Multiplicative P,
  x = a * chart q}` for the actual ring of each alternative. Thus both inclusions
  and every monomial, including the identity, occur exactly as in the node.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` and its public dependency
  `Sheaf.AlgebraicGeometry.LogRegularPair` supply
  `AlgebraicGeometry.IsFineSaturatedMonoid` for `def-trf-fs-log-blowup`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra` supply `AdicCompletion`,
  its ring and algebra structures, and the canonical completion map for
  `def-weil-pbc-adic-completion`. `AdicCompletion.algebraMap_apply` identifies it
  with `AdicCompletion.of` on the original polynomial ring.
- `WeilConjectures.RingTheory.CohenRing` supplies the exact `IsCohenRing` predicate
  recorded for `def-weil-pbc-cohen-ring`; its current server source was read.
- `Sheaf.RingTheory.LogRegularSaturationNormality` supplies
  `AddMonoidAlgebra.CompletedLocalModel`, `localModelBoundaryIdeal`,
  `localModelCompletionIdeal`, and `completedLocalModelBoundaryIdeal`.
  It is already a proof dependency of the item. Its recorded source and current
  server source agree. Reuse of these definitions adds no normality hypothesis.
- The other available proof dependencies are imported without `public`:
  `Sheaf.GroupTheory.SharpConeLatticeIntersection`,
  `WeilConjectures.AlgebraicGeometry.Regular`,
  `WeilConjectures.AlgebraicGeometry.Curve.Divisor`,
  `Sheaf.RingTheory.SerreCriterionNormal`, and
  `Sheaf.RingTheory.SerreS2TotalFractionMembership`.
  The facet-valuation and boundary-injection nodes currently have no Lean record;
  their roles remain explicit in the proof docstring.

Source and edge cases: read ILO Exposé VI 1.1--1.6 directly from the local PDF
(text extraction retained in the sandbox). VI 1.4 gives the divisorial equality;
VI 1.6 gives the sharp fs monoid, the field completion, and the Cohen quotient
with precisely the parameter congruence. No change to the mathematical node is
needed. For trivial `P`, all chart monomials are 1, so the localization is at 1
and the asserted equality is the ordinary units. For `n = 0`, `Fin n` is empty
and there are no variables. If both are trivial, the models are respectively
`k` and `C/(p)`. Neither case is excluded. The two coefficient conjuncts cover
all field characteristics and all allowed Cohen residue fields independently.
Universes `u` and `v` are explicit and independent; the constructions live in
`Type (max u v)`. No type-equality transport, arbitrary ring structure, hidden
coefficient choice, hollow definition, or extra hypothesis remains.

Searches retained from the earlier packet: `msearch.py leanfinder` for complete
saturated monoid localization-unit recognition (no exact match); `msearch.py
leansearch` for divisorial log-regular recognition (no exact match);
`msearch.py loogle` for `IsLocalization, IsUnit, AddMonoidAlgebra` (no exact match);
`msearch.py grep` for `divisorial|log.?regular|toric.*monomial|monomial.*unit` in
Mathlib/RingTheory (ordinary localization hits only). The item's saved
`mathlib_searches` records the detailed results. This repair additionally ran
`rg` over the project and upstream for `IsFineSaturatedMonoid`,
`toricPolynomialRing`, `completeToricRing`, `CompletedLocalModel`, and the item
id. The model search found the existing normality helpers, now reused; the exact
recognition theorem search found no declaration. Reading Mathlib's
`Algebra/MonoidAlgebra/Defs.lean` found the canonical `AddMonoidAlgebra.of`,
so the chart maps are composed from existing homomorphisms.

The original timeout repair marked the saved polynomial-ideal and monomial helpers
`@[no_expose]` and compiled successfully (sandbox 14.3 s, library 8.5 s), then
passed dry preflight after signature synchronization. The final interface audit
superseded that intermediate patch by removing the duplicate definitions entirely.
Final validation is recorded below after compiling and checking the final packet.

Final `scompile.py Q148 lem-trf-complete-toric-kato-recognition` validation returned
exit code 0 for the final file, including the sandbox and library-file checks;
there were no Lean errors or warnings. Source self-check confirms exactly one
`sorry`, no lines over 100 characters, and an exact signature match in the node.
Only the node's `lean` field differs from the current shared node.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
