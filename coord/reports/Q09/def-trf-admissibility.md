## Worker report

The module `Sheaf.Paper.TraceExceptionalAdmissibility` defines the finite-stage
constructible exceptional adjunction datum `WeilConjectures.TrfExceptionalStage`,
its canonical composition and base-change conjugates, and the predicates
`IsExceptionallyAdmissibleAt` and `IsExceptionallyAdmissible`. There are no
postponed theorems or new independent notions. All definitions have actual data.
Only the item's `lean` field changes; its statement and dependency lists stay intact.

Source read: current blueprint main-20261015,
`sec-six-functors-basics/sk-def-sf-admissible/def-trf-admissibility.md`, together
with its containing unit and all twenty statement dependencies. The containing
unit distinguishes the stronger ambient datum from the constructible datum here.
The node's expanded statement is consistent with its current blueprint_update.

Hypotheses and clauses:

- The public predicates take `F : FiniteFieldDatum`, `l : ℕ`, `[Fact l.Prime]`,
  and `_hl : l ≠ F.p`. The global finite field, its algebraic closure and
  characteristic are the recorded datum, without choosing new fields.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` express the fixed finite coefficient extension.
  Every coefficient ring is the recorded `Padic.coefficientExtensionRing`.
  The fixed-scalar presentation uses its `ULift` at the actual module-value
  universe `u+1`, as prescribed by the canonical realization equivalence.
- Index `n : ℕ` means exponent `n+1`, so it ranges over exactly all positive
  stages. In particular index zero is A_(E,1). The existing
  `sfPositiveCoefficient_finite` supplies finiteness, using the recorded
  coefficient-extension finiteness theorem.
- `X Y : Over (Spec (.of F.k))` are k-schemes; the two
  `LocallyOfFiniteType` and `QuasiCompact` instances on their structure maps
  are precisely finite type over k. Their over-category morphism `f` is a
  k-morphism. `IsSeparated f.left`, `LocallyOfFiniteType f.left` and
  `QuasiCompact f.left` are separated finite type. No separatedness of Y's
  structure map appears. Compactifiability is obtained in each public
  predicate from `hasCompactification_of_finiteType_over_field`; it is not
  another hypothesis.
- `trfFiniteTorFixed` is literally the inverse image of the dependency's
  `finiteTorConstructible` under `sfIntrinsicDerivedEquivalence.functor`.
  Its full subcategory retains every ambient morphism. It does not use a
  replacement definition of constructibility or Tor amplitude. The `origin`
  field of the datum records the known origin property of these inputs,
  needed for the published canonical compact-support comparisons.
- `supportPreserves` concerns the existing `rightDerivedLowerShriek`, the
  actual compactification formula `Rp_* j_!`. `exceptionalPreserves` concerns
  `trfExceptional`, whose body is exactly `sfFiniteExceptionalAt` at the
  chosen compactification. The etale left-adjoint instance used by that
  definition is supplied by the existing finite-coefficient theorem.
  No pro-etale ambient right adjoint is chosen.
- `support` and `exceptional` are `ObjectProperty.lift` of those same ambient
  functors. `TrfExceptionalStage.adjunction` is their actual Mathlib
  `Adjunction`: its `unit`, `counit`, `left_triangle_components` and
  `right_triangle_components` give exactly the natural maps and both triangle
  identities in the statement. `IsExceptionallyAdmissibleAt` is nonemptiness
  of this datum, rather than nonemptiness of an unspecified right functor.
- The comparisons are canonical operations on the adjunction data, rather
  than freely stored isomorphisms. Given the same datum for h and hf,
  `TrfExceptionalStage.composition` restricts the dependency's
  `originCompositionAmbient` by full faithfulness and applies
  `conjugateIsoEquiv C.adjunction (D.adjunction.comp H.adjunction)`.
  Its type is `C.exceptional ≅ H.exceptional ⋙ D.exceptional`, exactly
  R(hf)^! ≅ Rf^! Rh^!. This is available for every composable separated
  finite-type geometric h, by applying the same adjunction datum to h and hf.
- For a Cartesian square, `baseChange` uses `IsPullback g' f' f g`.
  The ordinary operations in `TrfOrdinaryStage` are the actual derived
  `upperStar` and `lowerStar`. Their `adjunction` is the fully faithful
  restriction of `derivedUpperStarLowerStarAdjunction`; units and counits
  are inherited, rather than supplied arbitrarily. The preservation proofs
  for these restrictions are exactly what lem-sf-pullback-tor-amplitude and
  cor-sf-direct-image-ctf-proetale supply in the node's geometric scope.
- The left exchange in `baseChange` is the specified proper/open
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, restricted to
  finite-Tor inputs. Its componentwise invertibility comes from the existing
  finite-level theorem on origin inputs. This is the compact-support exchange
  transported in thm-cbc-finite-level-proetale: its proper component is the
  derived direct-image mate, followed by the inverse exact extension-by-zero
  exchange. A canonical compactification comparison then identifies the
  pulled-back compactification with the chosen one for f'.
- `trfOriginCompactificationComparison` uses the normalized
  `compactSupportSiteComparison` on both ends and the canonical ordinary
  etale compactification comparison in the middle, descending along the
  origin equivalence. In particular it avoids the older comparison built
  from an unspecified `Nonempty` site-comparison isomorphism.
- The right exchange is precisely
  `conjugateIsoEquiv (G'.adjunction.comp D'.adjunction)
    (D.adjunction.comp G.adjunction)` of that restricted left exchange.
  Its type is `D'.exceptional ⋙ G'.directImage ≅
    G.directImage ⋙ D.exceptional`, i.e. Rg'_* Rf'^! ≅ Rf^! Rg_*.
  The other exceptional mate, which need not be invertible, is not used.
- `IsExceptionallyAdmissible` has `∃ cminus cplus : ℤ, ∀ m : ℕ` before
  all input intervals and complexes. Thus one signed pair of shifts works
  for every positive exponent, independently of the coefficient level.
  For every `a ≤ b`, its first clause applies the recorded
  `constructibleInterval` to every constructible input and to the actual
  output, with endpoints `a+cminus`, `b+cplus`. Its second clause applies
  `HasProEtaleTorAmplitude` to every finite-Tor constructible input with
  Tor interval [a,b], and to the actual output with those same shifted
  endpoints. Finite-Tor constructible membership of the output is already
  part of the finite-stage datum.
- As in the source, availability of these data is a theorem of the other
  nodes. This definition-only node introduces no extra theorem or proof.
  The open-extension/direct-image results give the support restriction;
  the exceptional-existence and uniform-preservation results give the other
  restriction and adjunction. The definition contains neither FullCD on
  all sheaves nor the stronger exceptional-adjoint admissibility predicate.

Dependency declarations used directly or through the recorded finite-level
specializations:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtension`: `Padic.coefficientExtensionRing`;
  `CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`:
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originCompositionAmbient`, and the canonical
  `comparisonUpperStarPlusEtaleOrigin` equivalence it uses.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`:
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`;
  ordinary etale `rightDerivedLowerShriekOfCompactificationPlusιIso`.
- The finite-coefficient `Derived.UpperLowerStar` module:
  `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals` reexports
  `WeilConjectures.constructibleInterval` from `ConstructibleIntervalsUnordered`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction`, `Adjunction.comp`;
  `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`;
  `Mathlib.CategoryTheory.Adjunction.Restrict`: `Adjunction.restrictFullyFaithful`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`.

All recorded dependency statements and main declaration signatures/docstrings were
read. The finite-field/coefficient convention and scheme-property collection are
used via their actual constituent definitions: the trace-convention bundle's
separated X_0 is not imposed on arbitrary X and Y here. Integral and rational
operations in the broad dependency nodes are not part of this finite-stage datum.
No dependency record needed repair and no existing notion was redefined.

Edge cases checked before writing and again against the code: n=1 (index zero),
identity f, identity base change, zero complexes, empty source, empty target,
negative input intervals, negative signed lower shifts, and a nonseparated
finite-type target. No dimension or maximum of an empty chart family occurs.
The elliptic-curve example does not force an ambient right-adjoint premise:
only the full constructible finite-Tor categories carry the adjunction here.
No STATEMENT-DISPUTED issue or source correction was found.

Searches performed:

- msearch LeanFinder: "Constructible exceptional admissibility datum compact
  support adjunction finite Tor with canonical composition base change".
  Eight results, including solid modules and ordinary sheaf pushforward
  adjoints; no constructible exceptional admissibility bundle.
- msearch Loogle: "CategoryTheory.Adjunction, CategoryTheory.Functor".
  Twelve results give the generic adjunction structure and constructors;
  these were read and reused as ingredients, not mistaken for the datum.
- msearch grep: "ExceptionalAdmissible|exceptionalAdmissib|constructibleFiniteTor"
  in CategoryTheory. No matches.
- msearch LeanSearch: "Constructible exceptional inverse image right adjoint
  to compact support pushforward with uniform Tor amplitude bounds".
  Eight hits on ordinary sheaf adjunctions, none defining this datum.
- rg/grep in Mathlib, the source WeilConjectures tree and lean/Sheaf for
  exceptional-admissibility names and the exact proposed declaration names;
  no exact existing declaration. `grep -rn def-trf-admissibility` in the
  source WeilConjectures tree returned no matches. Related constructible
  exceptional, Tor, composition and comparison interfaces were opened and
  reused. The stronger ambient admissibility definition is a different notion.

Validation: the prescribed scompile wrapper checks the delivered module alone,
with the default 60-second per-file limit. An initial broad coefficient-convention
import reached an unrelated integral-coefficient overlay failure; the delivered
module imports only its actual finite-stage constructions. The compiler also
caught the non-definitional choice of a compactification after base change;
this was repaired with the canonical compactification comparison, rather than
identifying the two compactifications. Final `scompile.py` succeeded for both the isolated sandbox module and
its final library module, with no errors or warnings. The prescribed
`deliver2.py Q09 def-trf-admissibility --no-push` dry run also passed both
per-file compilation checks and the server preflight (dry-run commit
`207c37fdab`). A direct JSON comparison confirms that only the item
node's `lean` field changes.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
