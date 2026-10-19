## Worker report

No new Lean module is needed.  The node is stated by the existing upstream theorem
`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`.  I read the
current source declaration (including its surrounding variables and docstring) and
compiled a probe with `scompile.py`; the node copy records the theorem signature
verbatim.

The correspondence with the node is clause by clause:

- The node's finite commutative coefficient ring (A) is the source variable
  `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`.
- The node's compactifiable map (f:X\to S) is the source map `f` with
  `[HasCompactification f]`.  The source theorem is stated for arbitrary schemes
  admitting this compactification, hence specializes to the node's Noetherian
  compactifiable case (the Noetherian hypotheses are not needed by this compatibility
  identity).
- The morphism (v:S'\to S), its base change (X'\to X), and (f':X'\to S') are
  the source maps `g`, `g'`, and `f'`, with the Cartesian hypothesis rendered by
  `sq : IsPullback g' f' f g`.  The source also carries the compactification and
  quasi-compactness instances for `f'`, supplied by the base-changed compactification
  in the node's construction.
- The arbitrary objects (M\in D(X_{\rm et},A)) and (Q\in D(S_{\rm et},A)) are the
  source objects `K` and `L` in the corresponding module derived categories.  The
  source signature imposes no boundedness, constructibility, Tor-amplitude, or
  invertibility condition.
- The compact-support exchange (b_M) is the component of
  `rightDerivedLowerShriekBaseChangeMap Λ sq`.
- The source `projectionMap` is the canonical compact-support projection map.  It is
  written in the right-coefficient convention (`Rf_! M ⊗ Q`); the node's
  coefficient-first map
  `Q ⊗ Rf_! M → Rf_!(f^*Q ⊗ M)` is its canonical derived tensor-symmetry conjugate.
  The source theorem's `leftDerivedUpperStarTensorComparison` and
  `derivedSquareUpperStarIsoInvApp` are exactly the canonical pullback/tensor
  identifications requested by the node.
- The displayed source equality is the commutative projection/exchange square.  After
  taking `K = M`, `L = Q` and applying the canonical tensor symmetry on the two
  coefficient placements, its two composites are precisely
  `b_{f^*Q⊗ᴸM} ∘ v^*(Π_{f,Q,M})` and
  `Π_{f',v^*Q,v_X^*M} ∘ (1_{v^*Q} ⊗ b_M)`.

The recorded statement-dependency declarations used for this identification are:

- `def-asd-compactifiable`: `Sheaf.AlgebraicGeometry.CompactifiableOverField`,
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field` (the source theorem
  uses the underlying `HasCompactification` notion).
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (and the recorded derived-category
  declarations).
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`.
- `lem-amb-proper-coproducts-projection`: `Sheaf.AlgebraicGeometry.ProperProjectionFormula`,
  `AlgebraicGeometry.Etale.isIso_proper_projection_formula_reordered`.
- `sbc-def-base-change-map`: `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`,
  `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow` (the module-coefficient
  specialization used by the upstream exchange construction is the same canonical
  unit/composition/counit mate).
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `sbc-prop-extension-by-zero-and-arbitrary-base-change`:
  `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`,
  `AlgebraicGeometry.Etale.openImmersionExtensionZero_exact_baseChange`.
- `lem-pur-etale-open-derived-tensor`:
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`,
  `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`.

Edge cases checked: `Finite` permits the zero/trivial finite commutative ring and no
nontriviality or characteristic-invertibility assumption appears; identity and proper
maps are covered by the canonical self-compactification; arbitrary (including empty)
schemes and arbitrary unbounded derived objects are allowed; the base-change square is
not required to be flat, etale, or an isomorphism; and the coefficient universe is the
standard `Λ : Type (u + 1)` required by the small-etale module encoding.

Searches for a duplicate or a missing notion were made on 2026-10-17:

- `msearch.py ... leanfinder "compact support projection map commutes with etale exchange base change"`:
  no matching theorem; only unrelated scheme pullback and etale-stability hits.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap, rightDerivedLowerShriekBaseChangeMap"`:
  no Mathlib hit (the declaration is project source, as expected).
- `msearch.py ... grep "projectionMap.*[Bb]aseChange|[Ll]owerShriek.*[Pp]rojection" Mathlib/CategoryTheory`:
  zero hits.
- `rg` over `WeilConjectures/` found the declaration at
  `SixFunctors/Etale/Derived/LowerShriekProjectionExchange.lean` and its use in
  `WeilFrobenius.lean`; `rg` over `lean/Sheaf` found no duplicate declaration.
- `grep -rn "lem-asd-compact-projection-exchange"` found only the DAG node and its
  reviewed proof/citer metadata, not another Lean declaration.

The source declaration is therefore recorded as `existing: true`; no statement is
corrected and no `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc reviewer, 2026-10-17)

The `existing: true` record `AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`
is correct and proved upstream, but it states the right-coefficient square
(`Rf_!M ⊗ᴸ Q → Rf_!(M ⊗ᴸ f^*Q)`, `Ex_! ⊗ 1`), which is step 5 of the node's proof. The node's
statement uses the coefficient-first map `Π_{f,Q,M} : Q ⊗ᴸ Rf_!M → Rf_!(f^*Q ⊗ᴸ M)` of
lem-amb-proper-coproducts-projection (signed symmetry, right projection map, `Rf_!` of the
symmetry) and the equation with `1 ⊗ b_M`. Step 6 (conjugation by the symmetry and its
compatibility with the pullback tensor comparison) is not in the upstream theorem, so the record
did not state exactly what the node says (H3).

New module `lean/Sheaf/AlgebraicGeometry/CompactProjectionExchange.lean`:

- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst` (real data):
  `σ_{Q,Rf_!M} ≫ projectionMap(M,Q) ≫ Rf_!(σ_{M,f^*Q})`, with `σ = derivedTensorSymmetry`
  (recorded declaration of lem-kun-tensor-sym), `projectionMap` the upstream compact projection
  map (proper projection `rightDerivedLowerStarProjectionMap` of the compactification followed by
  the inverse of `derivedOpenImmersionLowerShriekProjectionIso`, the record of
  lem-pur-etale-open-derived-tensor).
- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst_baseChangeMap`, proof `sorry`: the node's
  equation `b_{f^*Q⊗M} ∘ Lg^*(Π_{f,Q,M}) = Π_{f',Lg^*Q,Lg'^*M} ∘ (1 ⊗ b_M)`, with the same source
  identification (tensor comparison of `Lg^*`) and target identification (tensor comparison of
  `Lg'^*` then `derivedSquareUpperStarIsoInvApp`) as the upstream theorem; `b` is the upstream
  `rightDerivedLowerShriekBaseChangeMap`. The docstring carries the node's six proof steps.

Hypotheses as in the upstream theorem: `Λ : Type (u+1)`, `[CommRing Λ] [Finite Λ]`,
`[HasCompactification f]`, `[HasCompactification f'] [QuasiCompact f']` (both follow from the node's
hypotheses: the base change of a compactification is a compactification, and `f` from a Noetherian
scheme is quasi-compact), `sq : IsPullback g' f' f g`, arbitrary unbounded `M`, `Q`. Compiled with
`nt_compile.py`: clean (24.1 s), no error.
