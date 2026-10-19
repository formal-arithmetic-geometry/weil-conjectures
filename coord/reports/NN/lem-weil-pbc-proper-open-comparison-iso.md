## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOpenComparisonIso` states
`AlgebraicGeometry.Etale.isIso_properOpenComparison`, with `sorry` as its only proof.
It asserts invertibility of the exact map already constructed by
`AlgebraicGeometry.Etale.properOpenComparison`; it introduces no new map or definition.

Read the entire item node, its statement dependency and the full declaration and docstring
of `properOpenComparison` in `Sheaf.AlgebraicGeometry.ProperOpenComparison`, including the
construction of `properOpenIdentification`. Read the blueprint source file
`sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-proper-open-comparison-iso.md`, order 1482.
The source's assertion agrees with the node. The proof docstring follows the node's expanded
five-step proof, including the precise restricted map `θ⁻¹`, the empty fibre argument,
proper base change, exact stalk/cohomology comparison, and conservativity for module sheaves.

Hypothesis and conclusion correspondence:

- “For every datum in the comparison-map construction” expands to exactly the binders of
  the recorded definition: `{T₁ T₂ X : Scheme.{u}}`, `f : T₁ ⟶ T₂`, `[IsProper f]`,
  `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂`, `[IsOpenImmersion j₁]`, `[IsOpenImmersion j₂]`, and
  `h : j₁ ≫ f = j₂`. Thus both open immersions, properness, and the commuting triangle
  are retained. The symbol `f` renders the node's morphism `u`.
- Finite commutative coefficients are `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`,
  identical to the dependency's coefficient convention.
- The arbitrary bounded-below étale module complex is
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  No constructibility, finiteness of individual sheaves, or extra bound is assumed.
- “The specified map α is an isomorphism” is exactly
  `IsIso (properOpenComparison Λ f j₁ j₂ h K)`. Its source is `j₂! K` and its target
  is `Ru_* j₁! K`, because those are the domain and codomain of that dependency.
  It refers to the actual counit mate of the inverse of the specified composite
  identification, not an arbitrary morphism between these objects.

Statement dependency used:
`Sheaf.AlgebraicGeometry.ProperOpenComparison`, declaration
`AlgebraicGeometry.Etale.properOpenComparison` (with its specified
`properOpenIdentification`). This module is imported publicly.
All recorded proof-dependency modules are imported without `public`, with duplicates
removed. These include extension by zero and its adjunction/exactness in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`; stalks in its
`FiniteComparison`; `Sheaf.AlgebraicGeometry.OpenImmersionSquare`;
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`;
`Sheaf.AlgebraicGeometry.GeometricFiberFinite`;
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`;
`Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`;
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`; and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Mathlib proof leaves are imported from `CategoryTheory.Sites.Point.Basic`,
`CategoryTheory.Sites.Point.Skyscraper`, `Algebra.Homology.ShortComplex.ShortExact`,
and `Algebra.Homology.DerivedCategory.Plus`.
The proof-only nodes `lem-weil-pbc-proper-open-section` and
`lem-weil-pbc-proper-open-identification` have no recorded modules; therefore no
imports for these unstated proofs are invented. Their canonical geometry and
identification constructions are already exposed by the statement dependency.

Edge cases checked before writing: empty `X` and empty geometric fibres require no
nonemptiness assumptions; both sides then vanish where appropriate. Identity `f`
and identity open immersions are allowed by the binders. The zero complex, zero
coefficient ring, and all characteristics are retained. Arbitrary (possibly
unbounded above) bounded-below complexes are permitted. Nothing forces the open
image to exhaust either ambient scheme, or the ambient schemes to be separated,
Noetherian or nonempty. The universe `u` and coefficient/module universe `u+1`
are explicitly bound and exactly match the existing construction.

Searches made (2026-10-15):

- `msearch.py leanfinder`: “For a proper morphism fixing an open subscheme the canonical
  comparison from extension by zero to derived pushforward is an isomorphism”.
  Eight hits: Zariski `Scheme.Modules.restrictFunctorAdjCounitIso`, generic
  sheaf-pushforward composition and sheaf-of-modules pushforward isomorphisms.
  None states invertibility of the specified étale proper/open comparison.
- `msearch.py loogle`: `CategoryTheory.IsIso, AlgebraicGeometry.Etale.properOpenComparison`.
  No hits; the project's comparison is not in the remote Mathlib search index.
- `msearch.py grep`: `properOpenComparison|proper.open.comparison|extensionByZero`.
  Zero Mathlib hits.
- `msearch.py leansearch`: “proper pushforward extension by zero etale derived comparison
  isomorphism”. Service unavailable (Internal Server Error); no verdict inferred.
- `rg` on project sources for `properOpenComparison|properOpenSection` finds the recorded
  dependency and its constructions, not this theorem. `rg` of the upstream source for
  `properOpenComparison|proper.open.comparison` finds `LowerShriekCoherence` comments.
  Read its `refinementOpenImmersionLowerShriekComparison` and
  `isIso_refinementOpenImmersionLowerShriekComparison`: these use a compactification
  refinement with a Cartesian square, and a different unit/base-change comparison.
  Its arbitrary-refinement isomorphism is constructed via a dense refinement, and its
  restriction identification is defined from the inverse of that comparison. These
  are not the node's specified restriction composite and its counit mate, so they
  cannot be recorded as an exact existing statement.
- Required upstream grep for `lem-weil-pbc-proper-open-comparison-iso` has no hits.
  Searches for `isIso_properOpenComparison` in Mathlib, upstream, project Lean, and
  `dag/lean_names_upstream.json` have no hits; the declaration name is new.

No statement correction, dependency repair, or new node is needed. No statement dispute.
The module has explicit universes and binders and no proof other than the requested `sorry`.
Validation: `scompile.py NN lem-weil-pbc-proper-open-comparison-iso` compiled both the
sandbox module and its library-path check cleanly (3.0 s and 3.3 s), without warnings.


## Second reading by NN

Independently read the complete sandbox node and module, the statement-dependency
node def-weil-pbc-proper-open-comparison and its complete recorded module
Sheaf.AlgebraicGeometry.ProperOpenComparison. Read both blueprint source places
(order 1482 and order 1475), the unit introduction, the scheme-conventions source,
and the derived-categories source. The item source is the blueprint, not a Stacks
statement; additionally read etale-cohomology.tex at Tags 03S4, 03S5, 0F70, and
0DDF to check the source facts and their hypotheses. These facts impose no
Noetherian, base-field, separated-scheme, or characteristic restriction here.
Finite commutative coefficients make all underlying module cohomology torsion.
The unit's separated finite-type morphism convention is already satisfied by
properness of f; it does not impose an additional condition on either open.

Object/hypothesis/conclusion checklist, expanded from “every datum” via the
statement dependency (all verdicts PASS):

- Schemes T₁, T₂ and X: `{T₁ T₂ X : Scheme.{u}}`. These are arbitrary schemes,
  without a field, base scheme, nonemptiness or Noetherian structure.
- The morphism u : T₁ → T₂: `(f : T₁ ⟶ T₂)`. Renaming u to f has no effect.
- Properness of u: `[IsProper f]`, using the actual scheme-morphism predicate.
- The two open embeddings of the same X: `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)` and
  `[IsOpenImmersion j₁] [IsOpenImmersion j₂]`. Neither is assumed dense or
  quasi-compact; both use the recorded comparison's exact objects.
- The commuting triangle: `(h : j₁ ≫ f = j₂)`, in the correct composition order.
- Finite commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is exactly the dependency's finite commutative coefficient convention,
  with no invertibility or nontriviality assumption.
- Arbitrary K in D⁺(X_et,Λ):
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  These are ordinary small étale module sheaves, not pro-étale or Zariski modules.
  Bounded below refers to cohomology, as in the source; no upper bound,
  constructibility or finite-generation condition is added.
- The specified α, with source j₂!K and target Rf_*j₁!K:
  `properOpenComparison Λ f j₁ j₂ h K`. Opened its definition and checked its
  source and target and its body: it maps the inverse of
  `properOpenIdentification` by j₂! and then applies the descended counit.
  That identification is precisely r followed by Rp_*(e), then c, using the
  canonical exchange, canonical extension-zero base change and the component
  restriction. Also read clopenSectionDirectImage's characterization: its
  existential isomorphism is constrained by the restriction equation, so its
  choice here is not an arbitrary isomorphism or hollow data.
- Sole conclusion, invertibility of that very α for every datum:
  `IsIso (properOpenComparison Λ f j₁ j₂ h K)`. The schemes, maps, coefficients
  and K are all universally bound, and no replacement map is quantified over.

Edge cases: empty X, empty ambient schemes when the morphisms exist, and empty
geometric fibres are included; no Nonempty instance occurs. Zero complexes and
the zero coefficient ring are included. Identity maps and arbitrary common
opens are included. All characteristics are included, including torsion at the
residue characteristic (proper base change only needs torsion here). There is
no natural-number parameter or index family whose zero/empty case could be
lost. The explicit universe u is arbitrary; site and coefficient/module sizes
match the recorded dependency's u/u+1 convention, with no new universe equation.
Finite rings fit this coefficient universe without excluding a mathematical
finite ring. Every variable and universe in the signature is bound by eye.

Independent duplicate searches used different wording from the worker:

- msearch.py leanfinder: “extension by zero along open immersions commutes with
  proper direct image for a morphism identical on the open”. Eight results,
  all ordinary open-immersion section formulas or Zariski module restriction
  formulas; none concerns this specified derived étale comparison.
- msearch.py loogle: `CategoryTheory.IsIso, CategoryTheory.Adjunction.counit`.
  Twelve generic adjunction/equivalence results. None states this theorem.
- msearch.py grep: `proper.*shriek|shriek.*proper|properOpen`: no Mathlib hits.
- Direct rg of Mathlib's AlgebraicGeometry and CategoryTheory directories with
  `proper.*[Ss]hriek|[Ss]hriek.*proper|properOpen|extensionByZero`: no hits.
  Direct rg of project lean/Sheaf and upstream WeilConjectures for properOpen,
  proper/open comparison and extension/proper alternatives located the
  recorded comparison and upstream LowerShriekCoherence. Opened the latter's
  `refinementOpenImmersionLowerShriekComparison` and its isIso instance:
  they require compactification refinements and a Cartesian square and define
  a unit/base-change comparison, not the specified counit mate of the
  r/Rp_*(e)/c composite. Thus they do not supply the exact statement.
  Exact-name search in Mathlib, project Lean and dag/lean_names_upstream.json
  found no pre-existing isIso_properOpenComparison declaration.

No new nodes or dependency modules are present. No statement_change is present
or needed. No H3/H4/H5/H6 mismatch was found, and no Lean or node repair was
made. The theorem docstring includes the correct source and blueprint id and
all five proof steps, including θ⁻¹ on restriction, empty-fibre base change,
proper base change, exact cohomology stalks, and module-linear conservativity.
The only theorem proof is the requested sorry; there are no local definitions,
notation or instances. Statement and proof imports follow the node's plan.

Validation: scompile.py NN lem-weil-pbc-proper-open-comparison-iso with the
absolute sandbox file compiled the sandbox and library-path probes cleanly
(3.0 s and 3.2 s), without warnings. A text check confirmed lean.statement is
verbatim the theorem signature, and every Lean line has at most 100 characters.
Second reading changed only this report, recording the independent audit.
