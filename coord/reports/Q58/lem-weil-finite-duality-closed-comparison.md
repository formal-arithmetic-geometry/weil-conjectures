## Worker report

The module `Sheaf.SixFunctors.FiniteDualityClosedComparison` defines the transpose
`finiteDualityClosedComparisonAlpha` and the canonical component
`finiteDualityClosedComparisonDelta`.  The latter transports
`ProEtale.fixedComparisonDirectImageMatePlus` at a bounded-below lift through
`rightDerivedFunctorPlusCompatibility` and `mapDerivedCategoryPlusCompatibility`.  Its
postponed invertibility proof is the named theorem
`isIso_finiteDualityClosedComparisonDelta_proof`, registered as an instance by
`attribute [instance]` (maintainer review fix; no separate instance declaration).  The proof plan
uses `isIso_fixedComparisonDirectImageMatePlus` and the compatibility isomorphisms.  The theorem
`AlgebraicGeometry.finiteDualityClosedComparison` has a `sorry` proof and states the
corrected lift-indexed closed comparison.

The global finite-field hypothesis is now rendered by
`D : WeilConjectures.FiniteFieldDatum.{u}`, imported from
`Sheaf.Paper.FiniteFieldFiber`. Its fields give the prime `D.p`, positive exponent
`D.a`, `D.q = D.p ^ D.a`, the finite field `D.k₀` of cardinality `D.q`, and the
algebraic closure `D.k` with `[IsAlgClosure D.k₀ D.k]`. Thus the base is the specified
algebraic closure of a finite field. The coefficient-prime assumptions are
`l`, `hne : l ≠ D.p`, and `[Fact l.Prime]`.

`T`, `Z`, `U`, `aT`, `aZ`, and `aU` give schemes over `Spec D.k`.
`[LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]` and the corresponding
classes for `aZ` render the separated finite-type hypotheses on `T` and `Z`.
`i` with `[IsClosedImmersion i]` is the closed immersion, and
`j` with `[IsOpenImmersion j]` is the open immersion; `_hi : i ≫ aT = aZ` and
`_hj : j ≫ aT = aU` render compatibility with the same base.
`hij : IsCompl (Set.range i.base) (Set.range j.base)` says their images are
complementary. Quasi-compactness and quasi-separatedness instances for `i` and `j`
expose the consequences used by the canonical comparison API; these follow in the
source's Noetherian finite-type setting. No independent finite-type or separatedness
assumption is imposed on `aU`: it is the induced structure map of the open subscheme.
Finally `n`, `hn : 1 ≤ n`, `E`, `[Field E]`, `[Algebra (Padic l) E]`, and
`[FiniteDimensional (Padic l) E]` render the positive level and finite coefficient
extension data.

Inside the conclusion, `A` is `Padic.coefficientExtensionRing l E n` with the real finiteness
instance `Padic.finite_coefficientExtensionRing l E n hn`.  `Rₑ`, `Iₑ`, `Rₚ`, `Iₚ`, `F_T`, and
`F_Z` are respectively the etale right-derived closed direct image, its right adjoint, the
pro-etale right-derived direct image, the pro-etale closed upper-shriek right adjoint, and the
two comparison functors.  `adjₑ` and `adjₚ` are the recorded derived adjunctions.
For each constructible `M`, the first conjunct
`∃ L, Nonempty (Iₑ.obj M ≅ DerivedCategory.Plus.ι.obj L)` is the bounded-below clause,
independent of any comparison map.  For every explicit lift `e` the let-bound `δ` is
`finiteDualityClosedComparisonDelta`; `δIso := asIso δ` is its canonical isomorphism and
`α` is the `adjₚ` transpose of `δIso.inv` followed by the etale counit.  The three remaining
clauses render invertibility of `α`, the exceptional-counit equation, and naturality in a
morphism `h : M ⟶ N`, with an independently chosen bounded-below lift for `N`.

Dependency declarations used are `FiniteFieldDatum` from
`Sheaf.Paper.FiniteFieldFiber`, `Padic.coefficientExtensionRing` and
`Padic.finite_coefficientExtensionRing` from `Sheaf.NumberTheory.Padics.CoefficientExtension`
and `CoefficientExtensionFinite`, Mathlib's `IsClosedImmersion`, `IsOpenImmersion`,
`LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`, `IsSeparated`,
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` from
`Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`,
`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction` from
`WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion`, and
`fixedComparisonDirectImageMatePlus` plus
`isIso_fixedComparisonDirectImageMatePlus` from
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
The reviewer-returned interface issue is addressed by using the named Plus/full compatibility
maps in the new delta definition; this is the required §1(B) interface justification for the
recorded canonical mate.  The old `Mathlib.AlgebraicGeometry.Morphisms.Proper` import was removed.
The present repair restores `aU` together with its required base-compatibility equation.

Edge cases checked are (Z=T) (empty open complement), (Z=\varnothing), (i=\mathrm{id}_T),
(j=\mathrm{id}_T), and (U=\varnothing).  In every case the lift transport, adjunction
transpose, and counit equation remain well typed; no nonemptiness assumption is introduced.
The positivity condition `1 ≤ n` is retained before applying coefficient-ring finiteness.

Searches made: `rg` over `WeilConjectures/` and `lean/Sheaf/` for finite-duality and
closed-comparison names (no existing theorem); `msearch.py` leanfinder and Loogle searches
for exceptional etale/pro-etale comparison (no Mathlib match); `rg` for
`fixedComparisonDirectImageMatePlus` (found the canonical Plus mate and its invertibility
 theorem); and `scompile.py --source Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
to read the full compatibility signatures.  The two postponed proofs are `isIso_finiteDualityClosedComparisonDelta_proof` and
`finiteDualityClosedComparison`; both retain their intentional `sorry` proofs.

## Second reading by Q58

Repair of L's return on immutable head `b99f8253383d`, H3: the previous binders
allowed an arbitrary algebraically closed characteristic-p field, and the closed and
open immersions were not required to respect the specified structure maps.
With the node, its finite-field dependency, and the source paragraph open, this repair
replaces those field binders by the existing `FiniteFieldDatum` and adds `aU`, `_hi`,
and `_hj`. Its finite-field and algebraic-closure fields now supply exactly the source's
base, and both immersions commute with the structure maps. The saved canonical mate,
bounded-below existence clause, transpose, counit identity, and naturality clause are
retained verbatim. These changes repair the Lean rendering of hypotheses already in
the node; they do not change the mathematical statement or any dependency node.

The identity and empty closed/open cases still admit the induced structure maps and
satisfy the two compatibility equations. No nonempty scheme is required. The level
`n = 0` and coefficient prime `l = D.p` remain excluded exactly as in the node.
`D` retains arbitrary finite-field exponent and any chosen algebraic closure.
No field is replaced by a particular implementation of a finite field.
The initial saved-packet dry run passed at `7819e0403f`; this did not detect the
semantic H3 omission, which is repaired above before the final compile and dry run.

## Statement corrected

The old statement universally quantified an arbitrary natural isomorphism
`δ : Rₑ ⋙ F_T ≅ F_Z ⋙ Rₚ`; this did not render the source's canonical `δ_L` and made the
bounded-below clause vacuous if no such arbitrary isomorphism existed.  Following the source's
first proof paragraph, the corrected statement first asserts a bounded-below lift and then
quantifies an explicit lift `e`, constructs `δ` from `fixedComparisonDirectImageMatePlus` at
that lift through the named Plus/full compatibility isomorphisms, and states invertibility,
counit normalization, and naturality for that canonical map.  The citers are:

- `lem-weil-finite-duality-site-comparison` — holds: it uses boundedness and the canonical closed comparison.
- `lem-weil-finite-duality-locally-closed-comparison` — holds: it uses the bounded-below exceptional object and canonical site comparison.
- `lem-wf-open-curve-residue-sequence` — holds: it uses the comparison for bounded etale-origin inputs.

## Maintainer review fix

The second reader of the maintainer (cc review service) kept the statement and the record's
`statement` verbatim and changed only documentation and registration: the helper definitions
`finiteDualityClosedComparisonAlpha` and `finiteDualityClosedComparisonDelta` now carry `/-- -/`
docstrings with the source place and `(blueprint: lem-weil-finite-duality-closed-comparison)`;
the forwarding instance `isIso_finiteDualityClosedComparisonDelta` (a non-`sorry` proof without a
docstring) is replaced by `attribute [instance] isIso_finiteDualityClosedComparisonDelta_proof`;
stale comments from the earlier arbitrary-`δ` formulation are updated; and `lean.note` records why
the ModuleCat-encoded upstream adjunction `ProEtale.derivedLowerStarClosedUpperShriekAdjunction` is
used for `lem-exc-proetale-closed-support` instead of its intrinsic-encoding record.
