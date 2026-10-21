## Worker report

Item: lem-coef-finite-compact-support-uniform-tor. Stage 2, Q52, 2026-10-21.
Module: Sheaf.Paper.FiniteCompactSupportUniformTor.
Main declaration: AlgebraicGeometry.ProEtale.finiteCompactSupport_uniformTor_after_denseRefinement.
The single postponed theorem is the item itself. Both helper definitions have real data.
The mathematical statement, proof, proof_deps and source are unchanged.

Source read: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-integral-compact-support.md, proof paragraph 1. It prescribes the scheme-theoretic closure, the dimension bound, the unchanged extension-by-zero Tor interval and the proper-image interval [a,b+2d]. The DAG's seven expanded proof steps are transcribed into the theorem docstring. The item is a child lemma, not the blueprint unit's own statement. There is no statement dispute or correction.

Clause-by-clause rendering:

- Global datum, algebraic closure of F_q and characteristic p: `D : WeilConjectures.FiniteFieldDatum.{u}`; its fields give the prime p, positive exponent, finite field of cardinality p^a, and its fixed algebraic closure D.k. It imposes no chosen presentation of that closure.
- Prime l distinct from p: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The ring of integers, chosen uniformizer and quotients are the existing coefficientExtension constructions, not new choices.
- Schemes X,Y over k: `{X Y : Scheme.{u}}` and their `Over (Spec (.of D.k))` instances. Their finite-type hypotheses are each pair `LocallyOfFiniteType` and `QuasiCompact` on the structure map. Neither X nor Y is assumed separated over k.
- Separated finite-type k-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- Arbitrary prescribed compactification: `(c₀ : Compactification f)`. This structure supplies the open immersion i, proper map g, and factorization. The original candidate F_n is the inlined `@sfIntrinsicCompactSupport X Y f c₀ (Padic.coefficientExtensionRing l E n) _ (Padic.finite_coefficientExtensionRing l E n hn)`, with its canonical finiteness witness. Unfolding sfIntrinsicCompactSupport is the exact termwise j_! followed by proEtaleConstantDerivedDirectImage g A_n, so this is Rg_* j_!, not an abstract functor parameter.
- Nonnegative d and dim X ≤ d: `(d : ℕ)` and `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. This retains the empty scheme's bottom-valued dimension.
- Specified dense refinement: every occurrence is `c₀.denseRefinement`, which is already a `Compactification f`. Its Z is definitionally `c₀.i.image`, its i is definitionally `c₀.i.toImage`, and its g is definitionally `c₀.i.imageι ≫ c₀.g`. These are not separate arbitrary existential choices. The type already states compactification of the same f and its two morphism properties.
- Finite type of the refined ambient scheme over k: the first two conjuncts are `LocallyOfFiniteType` and `QuasiCompact` of `c₀.denseRefinement.g ≫ (Y ↘ Spec (.of D.k))`. This composite is its prescribed k-structure, with no extra hypothesis or new choice of structure map.
- Topological density: `DenseRange c₀.denseRefinement.i`.
- Dimension equality and bound: the next conjuncts give `topologicalKrullDim c₀.denseRefinement.Z = topologicalKrullDim X` and `... ≤ (d : WithBot ℕ∞)`.
- Every positive level: `∀ (n : ℕ) (hn : 1 ≤ n)`. All coefficients are the actual `Padic.coefficientExtensionRing l E n`, not a freely chosen ring.
- Every ordered interval and intrinsically bounded constructible input: `∀ (a b : ℤ) (_hab : a ≤ b) (L : proEtaleDerivedCategory X A_n) (_hL : intrinsicFiniteTorsionConstructible ... X L) (_hTor : HasProEtaleTorAmplitude X A_n L a b)`. The intrinsic predicate uses finitely many nonzero cohomology sheaves and the recorded finite stratification notion; it is not replaced by etale origin. HasProEtaleTorAmplitude tests every degree-zero module sheaf on K-flat representatives and includes the ordered-interval condition.
- Refined output: the first pair inside this quantifier says `intrinsicFiniteTorsionConstructible ... Y` and `HasProEtaleTorAmplitude Y A_n ... a (b + 2 * (d : ℤ))` for the refined candidate's value, which is exactly Rp_* j_! L.
- Original output: the next pair gives exactly the same two predicates and interval for the prescribed F_n L.
- Canonical comparison: the final existential supplies an actual `O : RefinementFiniteLevelOrigin ... X`, an identification `w` of its specified intrinsic realization with L, and an isomorphism α between these two actual output objects. Its value is fixed by `α = finiteCompactSupportDenseComparison ... c₀ L O w`. Thus this is not an arbitrary Nonempty isomorphism or an etale-origin hypothesis imposed on the input. Existence of O,w is asserted for every intrinsic input, as in proof step 6.
- Uniformity: c₀ and d occur before `∀ n`; the construction c₀.denseRefinement contains neither n nor L. The displayed interval is exactly [a,b+2d] for all levels and all c₀. There is no compactification-dependent numerical existential.

The two helper definitions expose only constructions belonging to this item. `compactSupportDenseRefinementArrow` has the concrete hom c₀.i.imageι; its triangle fields are the published scheme-image factorization and reflexivity. `finiteCompactSupportDenseComparison` first applies the dense candidate to w inverse, applies sfIntrinsicCompactSupportComparison, applies the intrinsic realization to the published refinementComparisonAtWitness along that concrete arrow, applies the inverse original realization comparison, then applies the original candidate to w. The original refinement comparison is itself the proper compositor followed by the image of the inverse proper/open comparison. The coefficient comparison is normalized on constant sections and K-injective representatives. No data are selected from a mere existence theorem. Identity and arbitrary witness cases are retained.

Dependency declarations read and used:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum, including all its fields and instances.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing; Sheaf.NumberTheory.Padics.CoefficientExtension supplies coefficientExtensionRing, its integer ring, uniformizer and ideal.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType, QuasiCompact, Proper, Separated, QuasiSeparated: LocallyOfFiniteType, QuasiCompact, IsProper, IsSeparated, QuasiSeparated. The scheme-properties dependency is explicitly a convention collecting these notions.
- WeilConjectures.Compactification.Defs: AlgebraicGeometry.Compactification. WeilConjectures.Compactification.RefinementCategory: Compactification.Refinement and category (attachment repaired below).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology. The intrinsic derived/module categories preserve site object universe u+1 and morphism universe u.
- WeilConjectures.Compactification.BoundaryPreparation: Compactification.denseRefinement and isSchemeTheoreticallyDominant_denseRefinement_i.
- Mathlib.Topology.KrullDimension: topologicalKrullDim; WeilConjectures.Mathlib.Topology.KrullDimension: topologicalKrullDimAt (the latter is imported through the recorded dimension module, not used for the global bound).
- Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport: Scheme.sfIntrinsicCompactSupport, owned by the already cited def-compact-support-direct-image-detailed. Every use in the signature and helper body is inlined with the explicit positive-level finiteness witness. The abbreviation module Sheaf.Paper.FiniteCompactSupportConstructibility is not directly imported, and prop-finite-compact-support-constructibility is not a stmt_dep.
- Sheaf.Paper.IntrinsicFiniteTorsionConstructibility: Scheme.intrinsicFiniteTorsionConstructible.
- Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude (the recorded owning module, publicly importing ProEtaleTorAmplitude): Scheme.HasProEtaleTorAmplitude and HasFiniteProEtaleTorAmplitude, retained in the recorded declarations of def-weil-proetale-tor-amplitude; that definition node is added to stmt_deps. Neither finiteTorConstructible nor finiteTorConstructibleEtale is applied by this item. The live def-weil-finite-tor-amplitude record stays attached to NW's finiteTorConstructibleEtale: its sandbox replacement has been removed, so this delivery makes no change to it.
- Sheaf.Paper.RefinementComparisonIsomorphism: RefinementFiniteLevelOrigin, refinementFiniteLevelFixedObject, refinementComparisonAtWitness, refinementCoefficientEquivalence and refinementFixedWitnessIso. The already landed def-sf-refinement-comparison-isomorphism is added to stmt_deps because the statement retains its witness and canonical comparison.
- Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport: Scheme.sfIntrinsicDerivedEquivalence. Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange: ProEtale.sfIntrinsicCompactSupportComparison. The already landed definition node def-sf-intrinsic-compact-support-realization owns this exact normalized comparison and is cited in stmt_deps; cor-exc-base-change-open-immersion-general is not a stmt_dep.
- Proof-only imports retain all stated proof dependencies: Mathlib QuasiCompact.of_comp and immersion-to-image interfaces, denseRefinement theorem, Sheaf.AlgebraicGeometry.DimensionExtension, Sheaf.Paper.OpenExtensionFiniteTor, Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage, Sheaf.Paper.ProEtaleConstructibleOrigin and Sheaf.Paper.CompactificationCoherence. Their full signatures and docstrings were read. No imported proof hypothesis is added to the statement.

Edge cases checked before drafting: empty X (image/refinement empty; dimension bottom, no Nonempty hypothesis), empty Y (then X empty), zero complex and all shifts, a=b including negative a,b, n=1, d=0, f the identity, nonreduced X (scheme image rather than reduced topological closure), and c₀ containing extra components of arbitrarily larger dimension. Only the refined ambient scheme is bounded. For A¹ to a point with a flat constant coefficient in degree zero, compact support in degree two lies in [0,2], confirming the upper-shift sign. Neither schemes nor compactifications are assumed smooth, integral, reduced or separated over k. The exclusion l=p and positivity of n are explicit. No independent universe equality is imposed on the small site.

Searches made with the prescribed msearch.py, group Q52/item:

- leanfinder, `Finite compact support direct image preserves constructibility and Tor amplitude bounded by twice dimension after dense compactification`: eight hits, led by Scheme.Hom.isConstructible_image and topology constructible-image results, with HomologicalComplex support lemmas; no compact-support/Tor-bound theorem.
- loogle, `DerivedCategory, "tensor"`: zero hits.
- grep, `compact.*support|lowerShriek|torAmplitude` in Mathlib/AlgebraicGeometry: zero hits.
- leansearch, `Compact support direct image of constructible finite Tor complexes has uniform Tor amplitude bound twice source dimension`: eight hits on HomologicalComplex support, scheme kernel support, and topological HasCompactSupport; no match.
- rg over lean/WeilConjectures and lean/Sheaf, `uniform.*[Tt]or|denseRefinement|sfIntrinsicCompactSupport|finiteCompactSupport`: found the existing dense refinement, intrinsic candidate and finiteLevelCompactSupport abbreviation, the previously recorded direct-image Tor theorem, and other coefficient/tower results. None states this item's combination of the prescribed dense refinement, dimension equality, exact Tor interval and arbitrary-compactification comparison. `grep -rn lem-coef-finite-compact-support-uniform-tor lean/WeilConjectures` found no declaration.
- Further rg for sfIntrinsicCompactSupportComparison and refinement comparisons located the existing normalized realization and witness comparison, reused rather than redefined. Searching dense-refinement arrows found only inline constructions, not a named definition of this arrow.
- Read the source records and definitions for all original statement dependencies and all modules of stated proof dependencies. The retained comparison-definition edges and the direct Tor-amplitude definition edge do not make the statement depend on either theorem that had supplied only helper definitions. The normalized comparison module's import closure does not contain the parent IntegralCompactSupportPrescribedReductions module.

Validation of the original packet: prescribed scompile.py compiled both its private sandbox module and the real library module cleanly (21.0 s and 16.0 s respectively), with no errors or warnings. Repair validation is recorded below. autoImplicit is explicitly false; universe u and every variable are bound. The delivered file contains only the named theorem's sorry. No global build or direct git command was run, and no shared source was written.

## Dependency modules

No new dependency modules are needed; the one retained repair is an existing-declaration attachment under §1(B).

`def-weil-compactifications-refinements`: its current module Compactification.Refinement defines OverRefinement, while the recorded Refinement and category declarations actually live in WeilConjectures.Compactification.RefinementCategory. Rebind to that existing module and its exact declaration, whose fields are hom, i_hom and hom_g, and whose morphism is automatically proper. This is the node's exact compactification category, without the extra Cartesian condition of OverRefinement. Only lean changes.

The maintainer performs the independent second reading, as required by the dispatcher brief. No worker-independent second reading is claimed here.

## Repair of return d3438d3454a7

H2/H12: inlined every finiteLevelCompactSupport use as its exact sfIntrinsicCompactSupport body, including the explicit finite_coefficientExtensionRing witness, and removed the abbreviation module's direct import and prop-finite-compact-support-constructibility from stmt_deps. The comparison still uses the same sfIntrinsicCompactSupportComparison definition from the same module; its ownership citation is now def-sf-intrinsic-compact-support-realization in place of cor-exc-base-change-open-immersion-general. Thus no mathematical clause changes.

H2/H13: removed the sandbox def-weil-finite-tor-amplitude.json replacement entirely. The delivery leaves the live NW finiteTorConstructibleEtale record intact for its landed consumers. The precise interval predicate used here remains HasProEtaleTorAmplitude, now directly cited through its owning def-weil-proetale-tor-amplitude node. The unrelated FiniteTorAmplitude direct import has been removed.

Kept the explicitly approved lean-only def-weil-compactifications-refinements repair to WeilConjectures.Compactification.RefinementCategory. The advisory redundant existential α is retained to preserve the independently approved comparison clause exactly; its equality still fixes the canonical value. Every former finiteLevelCompactSupport application has only been unfolded, so its type and construction are definitionally unchanged.

Repair self-check: the item differs from current main only in lean and added definition-node stmt_deps; the retained compactification dependency differs only in lean. There is no delivered finite-Tor dependency replacement. The recorded theorem signature matches the file verbatim, every source line is at most 100 characters, autoImplicit is false, and exactly the one named theorem has a sorry proof. A direct scompile.py run of the inlined repair passed both sandbox (15.2 s) and library (9.9 s), with no warnings. The final module directly imports the recorded Tor predicate owning module CoefficientProEtaleTorAmplitude, which publicly retains HasProEtaleTorAmplitude.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
