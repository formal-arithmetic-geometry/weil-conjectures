## Worker report

The module states reality preservation and trace descent for constructible Weil sheaves under a positive finite extension of the constant field. It uses the actual common-stage constructible Weil heart. The statement is unchanged. There are no new nodes or dependency replacements.

Hypotheses and clauses:

- `D : FiniteFieldDatum.{u}` supplies p, a, q=p^a, the finite base k_0 and its fixed algebraic closure k. `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give the coefficient prime. `Ω : Type v`, its field, Padic-algebra and algebraic-closure instances, and `iota : Ω ≃+* ℂ` supply the specified algebraic closure and complex isomorphism. The coefficient universe v remains independent of the scheme universe u.
- `X₀ : Over (Spec (.of D.k₀))` with locally finite type, quasi-compact and separated structure morphism is precisely the separated finite-type model. `m : ℕ` and `hm : 1 ≤ m` supply every allowed extension degree.
- `constantExtensionDatum`, `constantExtensionModel`, `constantExtensionOriginalModel` and `constantExtensionProjection` are the existing finite subfield, base change, restriction of its base, and projection. No replacement scheme or arbitrary finite cover is used.
- `F : sfCommonStageWeilSheaf D l hl X₀ Ω` is the given constructible Weil sheaf. The existential equivalence `e` has `ConstantExtensionSheetSpec`; `ConstantExtensionRestrictionSpec` fixes the restriction to the actual iterated Weil map. The restriction is literally `zlWeilPull ... g ⋙ e.functor`, so applying the inverse equivalence recovers the actual k_0-Weil pullback.
- Preservation of finite limits and colimits by both directions of `e` expresses exactness and therefore correspondence of subobjects and quotients. The purity and mixedness equivalences for every N and every real w express preservation of purity weights and finite mixed filtrations, using the recorded definitions.
- The `SfIsReal ... F → SfIsReal ... restriction(F)` implication expresses reality preservation with characteristic factors including algebraic multiplicities.
- For every real w, mixedness of the restriction implies mixedness with that bound of `constantExtensionWeilPush.obj (zlWeilPull.obj F)`. This pushforward is specified as the right adjoint to the actual inverse image on the Weil heart. The helper `constantExtensionWeilPull_isLeftAdjoint` restricts the prescribed t-exact finite derived image and its induced Weil structure to that heart. Uniqueness of right adjoints with their adjunction identifies this universal-property construction with that restriction, including unit and counit. Its data are determined up to exactly the adjunction-compatible isomorphism used here; this is not a choice of an unconstrained functor or map.
- The trace `Tr` and normalized trace `r` are morphisms of constructible Weil sheaves. `constantExtensionWeilUnit` is the inverse/direct-image adjunction unit on the heart, identified with the derived adjunction unit under the unique adjunction-compatible comparison. The equations `unit ≫ Tr = m • 𝟙 F`, `m • r = Tr`, and `unit ≫ r = 𝟙 F` give the degree identity and the Weil-equivariant retraction. In this characteristic-zero linear setting, `m • r = Tr` is exactly r=m^{-1}Tr, without requiring an additional scalar-action typeclass on the fixed-pair heart.
- For every geometric point x, the actual lifts over x are enumerated by `Fin m`. For every such enumeration, the point-pullback of Tr is the sum of the canonical counit components. Each component uses the prescribed `zlPullComp`, the actual counit, and the equality z followed by g equals x. Applying the recorded point-fibre functor and H^0 gives exactly summation on the geometric stalks. This derived form does not replace the stalks by arbitrary modules or arbitrary identifications. Point pullback is t-exact on these constructible objects, so its degree-zero formulation is equivalent here.
- The final implication, separately for every real w and without a reality premise, gives descent of mixedness of the same upper weight bound to F. No lissity, connectedness or semisimplicity assumption occurs.

Definitions are real constructions. The only postponed proofs are the existence of the finite-image heart adjunction and the main theorem; their docstrings contain the relevant complete natural-language proof. All additional declarations are canonical helper constructions belonging to this node.

Dependency interfaces used:

- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight` and `SfIsMixedOfWeightsAtMost`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf` and the inherited coefficient-prime invertibility.
- `Sheaf.Paper.AdicLocalCharacteristicFactor`: `SfIsReal`.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: the finite-field datum and model constructions, projection, `constantExtensionRestriction`, `ConstantExtensionSheetSpec` and `ConstantExtensionRestrictionSpec`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`.
- `Sheaf.Paper.SfCommonStageDirectImage`, a further module owned by `def-weil-derived-direct-image`, supplies the prescribed derived direct-image framework imported for the heart restriction. The heart functor is characterized by adjunction to the dependency's actual inverse image, exactly as the published common-stage direct image is characterized by its derived adjunction.
- `Sheaf.Paper.WeilIndSheafCategory`: the existing `zlWeilPull`, `zlFiberMap` and reduction-normalized `zlPullComp`, available through the statement dependencies.

The module also imports all recorded proof-dependency modules, including finite direct-image exactness, finite-pushforward purity, mixed-weight stability, finite-clopen decomposition, the Weil operations and adjunction modules, and triangularization. The Mathlib finite-morphism permanence match is supplied by the imported finite-morphism module and its affine/proper imports.

Edge cases checked against the source and signatures: m=1 gives one sheet and identity trace; the empty scheme gives vacuous geometric-point clauses; the zero sheaf has an empty eigenvalue multiset and a length-zero mixed filtration; repeated filtration terms are permitted by the recorded mixedness predicate; Jordan blocks are allowed because the proof uses triangularization rather than diagonalization; residue degree is m/gcd(d,m), not m at every closed point; l dividing m causes no problem since the coefficients have characteristic zero. Reality and mixedness are separate implications, so reality is not silently added to the descent hypotheses.

Searches:

- `msearch.py leanfinder`: "Reality of constructible Weil sheaves is preserved by finite constant extension and mixedness descends by the trace retraction" returned eight unrelated condensed-module/sheaf constructions and no matching theorem.
- `msearch.py loogle`: "CategoryTheory.Adjunction, CategoryTheory.Limits.biproduct" returned zero hits.
- `msearch.py grep`: "Weil.*(trace|Trace)|constantExtension.*(mixed|Mixed|trace|Trace)|SfIsReal" returned zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the same families located the recorded reality predicate, the cyclic-sheet equivalence and existing Weil pullback, but no reality-and-mixedness descent theorem. Searching the item id in the upstream Lean root found no declaration. Reading the published common-stage direct-image module supplied the canonical functor and adjunction needed for the trace.

No statement dispute or source correction is needed. The source was read in full at `main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, especially paragraphs 1, 5 and the final descent sentence.

Validation: `scompile.py Q19 lem-zl-constant-extension-mixed-descent` compiled the complete module both as a sandbox module (26.6 s) and at its final library path (27.9 s), with no errors or non-sorry warnings. Every universe is explicitly declared; `autoImplicit` is disabled. The node copy changes only `lean`; there is no statement change.

Self-check: reread the full node and final Lean after compilation. Checked especially that the mixedness implication has no reality premise, the upper bound w is unchanged, the one-sheet restriction and m-sheet inverse image occur in their respective hearts, every trace and retraction is a Weil-heart morphism, the summation uses every actual lift and is independent of its enumeration, and the coefficient universe remains independent. The normalized trace is expressed by m times r equals Tr plus the retraction equation, exactly equivalent to division by m here. The direct-image functor is chosen only by its right-adjoint universal property, as in the existing common-stage framework; the prescribed adjunction determines the canonical comparison. The statement, source and dependency list required no correction. No independent second worker was started: the dispatcher assigns the independent reading to the maintainer.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
