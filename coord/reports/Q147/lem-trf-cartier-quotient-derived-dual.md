## Worker report

The module `Sheaf.Algebra.Homology.CartierQuotientDerivedDual` states
`ModuleCat.cartier_quotient_derived_dual`, with one postponed theorem and no new
definitions. The item node changes only in `lean`.

Source read: `literature/stacks-project/dualizing.tex`, lines 2404–2431,
Tag 0BZH, lemma-compute-for-effective-Cartier-algebraic, especially the reduction
to RHom(A,R) and its two-term dual resolution; lines 2235–2248, Tag 0A71,
lemma-RHom-ext. The source imposes no Noetherian condition in this lemma.

Hypothesis and conclusion correspondence:

- The commutative ring S is `(S : Type u) [CommRing S]`.
- Its actual ideal is `(I : Ideal S)`, so its inclusion into S is fixed, not
  an arbitrarily chosen map of abstract modules.
- Finite generation and projectivity are `[Module.Finite S I]` and
  `[Module.Projective S I]`; these are the hypotheses in the node, rather than
  a stronger global freeness assumption.
- Rank-one freeness at every prime is `hlocal : ∀ (p : Ideal S) [p.IsPrime],
  Nonempty (LocalizedModule p.primeCompl I ≃ₗ[Localization.AtPrime p]
  Localization.AtPrime p)`. No global basis or compatible choice is required.
- B is the actual quotient `S ⧸ I`; the ring map is `Ideal.Quotient.mk I`.
- Ordinary scalar extension uses Mathlib's standard left-module convention,
  `(S ⧸ I) ⊗[S] I`. The node's `I ⊗[S] (S ⧸ I)` is the same scalar extension
  under canonical tensor symmetry `x ⊗ b ↦ b ⊗ x`; its right-factor quotient
  action is exactly the left-factor quotient action used here. This changes
  neither the module nor the assertion up to canonical B-linear identification.
- The ordinary B-linear dual N is literally
  `Module.Dual (S ⧸ I) ((S ⧸ I) ⊗[S] I)`, bundled by `ModuleCat.of`.
  It is not a derived Hom, an S-linear dual, or an arbitrary inverse line.
- The two `HasDerivedCategory` binders choose the ordinary unbounded derived
  categories of modules. `wS` and `wB` are independent morphism universes;
  no equality of localization universe choices is imposed.
- `DerivedCategory.singleFunctor ... 0` places S and N in degree zero.
- The left side is the recorded `ModuleCat.derivedCoinduction` along the
  quotient map, evaluated on S[0]. It carries exactly the coinduction B-action
  `(b • h)(b') = h(b'b)` of the dependency, not an invented action.
- The conclusion is `Nonempty (left ≅ right⟦(-1 : ℤ)⟧)` in D(B),
  so this is the full derived-category isomorphism requested. It asserts only
  existence, without extra naturality or a preferred normalization.
- There is no Noetherian, proper-ideal, nontrivial-ring, or nonempty-spectrum
  hypothesis. Every variable and universe is explicit (`autoImplicit false`).

Dependency declarations inspected and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor` (the statement uses these).
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction` for def-trf-derived-coinduction;
  `ModuleCat.derivedCoinductionAdjunction_spec` for the proof dependency.
  The real K-injective construction, model comparisons, adjunction, evaluation
  counit and theorem signature/docstrings were read in full.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective` for
  def-weil-pbc-projective-module.
- `Sheaf.RingTheory.LineModuleDuality`: `Module.line_module_duality`.
- `Sheaf.Algebra.Homology.DerivedHomProjectiveResolution`:
  `CategoryTheory.derivedHom_projectiveResolution`. This legacy interface uses
  one-point-site module sheaves; its comparison with ordinary modules is proof
  infrastructure, not a change of the present statement's ordinary Mod_S/Mod_B.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex` (upstream module, not its retired twin).
- `Sheaf.CategoryTheory.DerivedDegreeZeroNormalization`:
  `DerivedCategory.existsUnique_iso_single_homology_zero`.

All recorded proof dependency modules are imported privately unless already
publicly needed by the statement. The docstring records all five proof steps,
including the sign in the resolution, the balanced tensor formulas, the
quotient-lift check of B-linearity, and degree-zero reconstruction after shifting.

Edge cases checked mathematically before writing: I=S gives B=0 and both derived
objects vanish; S=0 has no primes, the local condition is vacuous and the module
category is zero, so the conclusion still holds; I=0 with S nonzero cannot satisfy
the rank-one localization hypothesis (equivalently scalar endomorphism duality
would force S=0); for S=Z and I=(2), the right side is Z/2 in degree 1, confirming
the negative shift. Nonprincipal invertible ideals remain allowed, as do
non-Noetherian rings. No node fault or statement correction was needed.

Searches actually run with `msearch.py Q147 lem-trf-cartier-quotient-derived-dual`:

- leanfinder: `Derived dual of a quotient by an invertible ideal is the dual
  conormal module in cohomological degree one`: eight hits, ordinary cotangent
  cohomology, Picard-group duality, and dual quotient lemmas; no derived dual.
- loogle: `"DerivedCategory", "Ideal", "dual"`: zero hits.
- grep: `derivedCoinduction|cartier.*[Dd]ual|[Dd]ual.*[Cc]artier`: zero hits.
- leansearch: `For a quotient ring by an invertible ideal derived coinduction
  of the ring is the dual conormal module in degree one`: eight hits, quotient
  and cotangent definitions, Picard invertibility and local cohomology; no match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `cartier.*[Dd]ual|[Dd]ual.*[Cc]artier|derivedCoinduction|lem-trf-cartier-quotient-derived-dual`
  found the existing coinduction framework and polynomial-duality consumers,
  but no theorem for this Cartier quotient dual. Searching the item id in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json` found no declaration.

Validation: the prescribed server single-file compile and deliver2 dry run are
run before delivery; their results are recorded below.

## Second reading by Q147

This is the dispatcher's single-worker workflow; no separate agent was started.
I reread the item and the completed signature to check the correspondence above.
In particular the dual is taken over B, coinduction is the specified functor,
the conclusion is an isomorphism in D(B), and the shift is -1 rather than +1.
Finite projective hypotheses and all prime localizations remain explicit. The
left-factor tensor convention is explained above, including its B-action under
symmetry; it introduces no hypothesis. The zero-ring and unit-ideal cases were
checked against the source proof. No signature mismatch was found on this pass.
The maintainer's independent review remains the separate review of this delivery.

Validation results: `scompile.py` passed both sandbox and library module checks
(8.4 s and 2.1 s), without warnings or errors. `deliver2.py --no-push` printed
`OK (dry run): commit ebed7b54295 passes the preflight and compiles; nothing pushed`.
A source/JSON check confirmed only `lean` changed, the stored signature is verbatim,
and all Lean lines are at most 100 characters.
