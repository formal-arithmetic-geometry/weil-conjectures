## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude` states
`AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_torAmplitude` with `sorry`.
The only other declaration is the concrete functor
`AlgebraicGeometry.Etale.finiteCoefficientClosedExceptionalInverseImage`:
it installs the already recorded positive-level finiteness proof and evaluates
`Functor.rightAdjoint` on the actual unbounded derived closed direct image.
Its choice is determined up to the unique adjoint isomorphism by the universal property
of `lem-exc-closed-ambient`. It is not an assumed functor or an arbitrary map.
The helper introduces no independent mathematical notion and belongs to this node's
coefficient specialization; both declarations are listed in `lean.declarations`.
No definition has postponed data, and the single postponed theorem is this DAG node.

Source read: the blueprint's `sec-smooth-purity/sk-prop-a1-kummer/prop-exc-closed-tor.md`
(order 1913), from the available launcher literature mirror. The node's explicit
nonnegative bound and coefficient/site conventions agree with that source and its
proof. The mathematical statement and all dependency lists are unchanged.

Clause-by-clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`. The site is `Scheme.{u}` and the coefficients
  have the recorded universe `Type (u + 1)` used by all these ordinary etale interfaces.
- Valuation ring and chosen uniformizer: the existing
  `Padic.coefficientExtensionRing l E n` is the quotient of
  `Padic.coefficientExtensionIntegers l E` by the nth power of the ideal generated
  by `Padic.coefficientExtensionUniformizer l E`. These definitions were read in full.
- Positive level: `(n : ℕ) (hn : 1 ≤ n)`, including n=1. No auxiliary finiteness
  assumption is added: `Padic.finite_coefficientExtensionRing l E n hn` supplies
  each explicit `Finite` argument and the functor's internal instance.
- Schemes: `{Z T U : Scheme.{u}}`.
- Closed immersion: `(i : Z ⟶ T) [IsClosedImmersion i]`.
- Quasi-compact complementary open immersion: `(j : U ⟶ T)` with
  `[IsOpenImmersion j] [QuasiCompact j]`, and
  `_hij : Set.range i.base = (Set.range j.base)ᶜ`.
  This allows any chosen open immersion realizing the complement.
- Integer bounds and nonnegative c: `(a b c : ℤ) (_hc : 0 ≤ c)`.
  There is no added `a ≤ b` hypothesis.
- Every module sheaf and every degree above c: `_hcd` quantifies over every
  `M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)` and `q : ℤ`.
  For `c < q` it asserts `IsZero` of the qth homology of
  `R(lowerStar (ModuleCat A) j)` applied to `DerivedCategory.singleFunctor _ 0` at M.
  This is exactly R^q j_* M, with M in degree zero.
- Constructibility in every degree: `_hcons` quantifies over the same arbitrary M
  and every integer q, without a bound on q, and sends
  `Scheme.IsConstructibleEtaleModuleSheaf M` to that predicate on this same
  qth higher direct image. Explicit finiteness arguments use the existing theorem.
- K in the ordinary derived category: `K : DerivedCategoryModule A T`, the
  recorded derived category of `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- K bounded constructible: `_hK` is precisely the recorded
  `DerivedCategory.isBoundedConstructible A T K`, with its explicit finiteness proof.
  Its defining cohomology predicates use finite constant-value stratifications.
- K with Tor amplitude [a,b]: `_hTor : DerivedCategory.hasTorAmplitudeIn A T a b K`,
  the recorded upstream predicate testing every module sheaf in degree zero.
- Ri! is the ambient right adjoint: the helper's body is
  `(R(lowerStar (ModuleCat A) i)).rightAdjoint`, after deriving finiteness.
  Its existence is the recorded instance from `lem-exc-closed-ambient`.
- Output bounded constructible: the first conjunct is the same
  `DerivedCategory.isBoundedConstructible`, now on Z at the helper's value on K.
- Output Tor interval [a,b+c+1]: the second conjunct is
  `DerivedCategory.hasTorAmplitudeIn A Z a (b + c + 1)` on that identical value.

Dependency declarations used, with source signatures and docstrings read:

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its public construction module
  `Sheaf.NumberTheory.Padics.CoefficientExtension` with
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `coefficientExtensionIdeal`.
- `def-weil-pbc-scheme-conventions` is a convention record, without a module:
  the Mathlib notions `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`, `QuasiCompact`
  render the relevant clauses. Their existing definitions are used.
- `def-weil-pbc-derived-categories`:
  `Sheaf.AlgebraicGeometry.DerivedCategories`; the category is upstream
  `AlgebraicGeometry.Etale.DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, and cohomology is
  `DerivedCategory.homologyFunctor`.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`. The current upstream derived interface has
  replaced the old named `rightDerivedLowerStarPlus` with generic
  `Functor.rightDerivedFunctorPlus`; for the ordinary unbounded categories used
  here, the source explicitly prescribes `R(lowerStar A j)`, meaning
  `Functor.rightDerivedFunctor` on that same direct image. This current interface
  is read in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and imported
  through the ambient-adjoint module. No second direct image is defined.
- `lem-exc-closed-ambient`:
  `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
  The helper uses its global instance to obtain `Functor.rightAdjoint`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
  The cohomology constructibility is exactly its dependency
  `Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `def-kun-tor-amplitude`:
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` publicly imports the existing
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.

The module imports each currently recorded proof-dependency module, without `public`
when used only by the proof. Mathlib-only proof nodes import the files named by their
matches. The following proof nodes have neither a Lean record nor a Mathlib match in
this checkout: `lem-exc-closed-support-triangle`, `lem-exc-constant-tensor`, and
`lem-exc-residue-tor-test`; they are proof prerequisites, not prerequisites for this
statement, so no module is invented for them. Their complete roles are in the theorem's
seven-step proof docstring. No statement prerequisite is missing or repaired.

Edge cases checked before writing:

- If a>b the input is zero by testing the Tor condition on the unit, and the right
  adjoint sends zero to zero; no interval case is silently excluded.
- The zero object satisfies both conclusions for every interval.
- Z empty and Z=T (hence respectively U=T and U empty) are allowed, as are empty T
  and U. There is no nonempty-scheme or nonempty-open binder.
- c=0 gives exactly [a,b+1]; negative c is excluded explicitly as in the node.
- n=1 is allowed, and n=0 is excluded as in the node. No restriction on ell beyond
  primality, or invertibility of ell on the schemes, is introduced.
- Constructibility preservation is required in all integer degrees and the vanishing
  test is on all module sheaves, rather than just the constructible ones.
- No finite-type, Noetherian, regularity, properness, or `a ≤ b` assumption is added.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "finite Tor amplitude of exceptional inverse
  image for a closed immersion with bounded cohomological dimension of the open
  complement": eight generic derived t-structure hits, no matching theorem.
- `msearch.py ... loogle` with query `DerivedCategory, IsClosedImmersion, torAmplitudeIn`:
  zero hits; Loogle reported unknown identifier `IsClosedImmersion`.
- `msearch.py ... grep` with query `rightDerivedUpperShriek|closed.*tor|hasTorAmplitudeIn`
  in Mathlib CategoryTheory: 25 generic closed-monoidal-category hits, no match.
- `msearch.py ... leansearch` with query "exceptional inverse image along a closed
  immersion preserves finite Tor amplitude": service unavailable, Internal Server Error.
- `rg` for the node ID and the proposed declaration names in the upstream-name map,
  upstream `WeilConjectures`, and project `lean/Sheaf`: no declaration collision.
  `grep -rn prop-exc-closed-tor` in upstream `WeilConjectures` finds no declaration.
- Broader upstream/project searches for closed-support Tor statements find upstream
  `constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion` in
  `SixFunctors/Etale/Derived/Stability/UpperShriek.lean`. Its full signature assumes a
  finite-type scheme over a field, invertible exponent, compactification, and dimension
  bound, and has the numerical bound b+2d+1. It uses a different constructibility
  predicate and exceptional-functor interface. It is not this node's general ambient
  statement with arbitrary schemes and the supplied Rj_* bounds.
  `EtaleClosedSupportAmplitude` supplies cohomology bounds, not Tor amplitude, so is
  a proof dependency, not an existing match either.

No statement correction and no STATEMENT-DISPUTED issue.

Validation: `scompile.py N7 prop-exc-closed-tor` compiled this file cleanly in both its
sandbox and library-module positions, with all required overlay imports, under the
unchanged 60-second per-file limit. No warning was reported.

## Second reading by N7

The node, Lean signature, and original blueprint source place (`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/prop-exc-closed-tor.md`, order 1913, read from the server literature mirror) were compared directly. This node cites a blueprint Markdown source, not a Stacks tag. The source has the same arbitrary closed immersion, quasi-compact complementary open, all-module vanishing, all-degree constructibility, input Tor interval and output interval. The DAG makes its coefficient, ordinary-etale-site and nonnegative-bound conventions explicit; those conventions are retained. The correspondence is:

- The prime `ell` is `(l : Nat) [Fact l.Prime]`.
- The finite extension `E / Q_l` is `E : Type (u + 1)` with `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`. The coefficient ring is the recorded `Padic.coefficientExtensionRing l E n`, with its recorded integers, ideal, and uniformizer.
- The level is `(n : Nat) (hn : 1 ≤ n)`, so exactly the node's `n ≥ 1`.
- The schemes are `{Z T U : Scheme.{u}}`; `i : Z ⟶ T` has `[IsClosedImmersion i]`; `j : U ⟶ T` has `[IsOpenImmersion j] [QuasiCompact j]`; `_hij` states `Set.range i.base = (Set.range j.base)ᶜ`, the complementary-open clause.
- The integer bounds and nonnegative cohomological bound are `(a b c : Int) (_hc : 0 ≤ c)`, with no extra relation such as `a ≤ b`.
- `_hcd` quantifies over every `A`-module sheaf `M` on `U` and every `q : Int`, asserting `IsZero` of the `q`th homology of `R(lowerStar ... j)` on `singleFunctor ... 0 M` whenever `c < q`; this renders `R^q j_* M = 0` for `q > c`.
- `_hcons` quantifies over the same arbitrary `M` and every `q`, and maps the recorded constructibility predicate on `M` to the same predicate on the `q`th homology of `Rj_* M`, exactly the all-degree constructibility clause.
- `K : DerivedCategoryModule A T` is the ordinary unbounded derived category on the small etale site; `_hK` is the recorded bounded-constructible predicate and `_hTor` is the recorded Tor-amplitude predicate in `[a,b]`.
- The conclusion is a conjunction: the helper `finiteCoefficientClosedExceptionalInverseImage ... i` is the ambient `Functor.rightAdjoint` to the actual derived closed direct image, and its value on `K` is bounded constructible on `Z` and has Tor amplitude `[a, b + c + 1]`. Both predicates use the same coefficient ring and the same derived category as the hypotheses.

The helper is a canonical right adjoint selected by the universal property and the recorded closed-immersion adjoint instance; it is not an arbitrary map or a postponed-data definition. The theorem is the node statement with `sorry` only. All declarations have source and `(blueprint: prop-exc-closed-tor)` docstrings, and the theorem docstring reproduces the seven proof steps.

Edge cases checked: `n = 1` is included and `n = 0` is excluded; `c = 0` gives `[a,b+1]`; negative `c` is excluded; `a > b` and the zero object are allowed; `Z`, `T`, or `U` may be empty, including `Z = T` and `U = T`; no nonemptiness, finite-type, Noetherian, properness, regularity, or invertibility-of-ell hypothesis was added; arbitrary integer degrees and arbitrary module sheaves are retained. The coefficient and scheme universes are matched (`E : Type (u+1)`, `Scheme.{u}` and `ModuleCat.{u+1}`), so no case is lost through an independent smaller universe.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, and grep queries for closed-immersion Tor amplitude, exceptional inverse image, `rightDerivedUpperShriek`, and `hasTorAmplitudeIn`), `rg` over project `lean/Sheaf` and upstream `WeilConjectures`, and the upstream-name map. They found no exact statement or declaration collision. The upstream theorem `constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion` has different finite-type/field hypotheses, a different exceptional-functor interface, and bound `b + 2d + 1`, so it is not this node. The recorded dependency declarations were opened and used; no dependency repair or new definition node is needed.

No mismatch was found; the Lean module and node were left unchanged, and this audit was appended to the report. No new nodes or dependency modules are delivered. There is no `statement_change`, so no correction or citer audit is required. As an additional check, `thm-pur-general-admissibility` uses the conditional interval shift on affine charts, and `thm-sf-ctf-stability` applies it after independently obtaining the open bound `c = 2d`; both uses still hold. The other referring nodes are `def-exc-open-complement-bound` and `thm-pur-affine-line-orientation`. The prescribed `scompile.py` run passed. The final `deliver2.py N7 prop-exc-closed-tor --no-push` exited 0 and printed `OK (dry run): commit e8ec5be0dd passes the preflight and compiles; nothing pushed`. Only the item node, its Lean module, and this report were staged.

Second-reader search details: LeanFinder query `closed support functor exceptional restriction finite Tor dimension for arbitrary schemes and a bounded open direct image` returned eight generic derived t-structure results; Loogle query `"Sheaf", "tor"` returned twelve unrelated presheaf/Kan-extension results; Mathlib grep query `closedImmersion_rightAdjoint_torAmplitude|finiteCoefficientClosedExceptionalInverseImage` returned zero hits. Direct upstream/project searches were also read. The saved node `lean.statement` was compared to the literal theorem signature, including whitespace and line breaks, and is verbatim equal. The helper and theorem names were checked against the source tree and upstream-name map.
