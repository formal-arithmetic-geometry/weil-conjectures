## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit` states
`AlgebraicGeometry.Scheme.proEtaleClassicalSheavesUnit`, with `sorry` as its entire proof.
It states both clauses of det-pe-classical-sheaves-unit without changing the node.
The previous worker left only dispatcher markers; this delivery supplies the missing
module, node copy, and report.

Hypothesis and clause correspondence:

- “Let X be a scheme” is `(X : Scheme.{u})`, for the explicitly declared universe `u`.
  There is no finiteness, separation, nonemptiness, or characteristic assumption.
- “For every sheaf of sets F on X_et” is
  `∀ F : Sheaf X.smallEtaleTopology (Type (u + 1))`.
  The coefficient universe is exactly that of the recorded comparison adjunction.
- The actual comparison unit eta_F is
  `((proEtaleSiteComparison X).unit.app F)`. Its invertibility is `IsIso` of this
  morphism, not merely the existence of an unrelated isomorphism between its objects.
  The adjunction signature gives its source F and target nu_* nu^* F.
- “Consequently nu^* is fully faithful” is expressed by the node's explicit equivalent
  formulation: the second conjunct quantifies over all `F F'` of the same sheaf category
  and asserts `Function.Bijective` of the map on morphisms.
- The map `phi ↦ nu^* phi` is the `.map φ` of
  `Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
  (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)`, exactly the left functor
  in the recorded `proEtaleSiteComparison`. Its domain binder is `φ : F ⟶ F'`;
  the codomain is the Hom set between their inverse images, inferred by Lean.

Dependency declarations read and used:

- Statement dependency def-weil-pbc-site-comparison-morphism:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`. Its full signature and docstring
  specify the canonical Kan-extension/sheafification adjunction, with restriction as
  direct image. This module is publicly imported.
- Proof dependency lem-cbc-comparison-pullback-sections:
  `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`,
  `AlgebraicGeometry.proEtaleComparisonPullbackSections`. Its signature includes
  the section equivalences, naturality, bijectivity at etale objects, and the actual
  unit normalization. This module is imported for the later proof.
- Proof dependency lem-weil-pbc-sets-etale-inverse-image-restriction:
  `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`,
  `AlgebraicGeometry.etaleSetInverseImageRestriction`. Its natural isomorphism to
  localization restriction and unit equation were read. It is imported for the proof.

The theorem docstring records all three proof steps: identify the unit sectionwise
using these two tools, assemble the inverse component bijections by naturality, and
use the adjunction and postcomposition with the invertible unit to prove Hom bijectivity.
No definitions or other DAG statements are introduced. No dependency repair is needed.

Sources checked: the current main-20261015 blueprint's
`sec-proetale-coefficients/sk-thm-pe-classical-sheaves/` statement and proof files for
`sk-thm-pe-classical-sheaves-unit`; Stacks `proetale.tex`,
`lemma-fully-faithful` (Tag 099T), which states unit invertibility for every sheaf.

Edge cases checked before writing: the empty scheme is admitted, with no extra
hypothesis; arbitrary (including non-quasi-compact and non-quasi-separated) schemes
are admitted; no ring or abelian structure on F is assumed. Sheaves with empty section
sets and the terminal sheaf remain in the quantification, as do identity morphisms
and all pairs of sheaves. The proof uses a section formula explicitly valid for empty
covers, and bijections on empty sets cause no restriction. The arbitrary universe `u`
and the fixed larger site/sets universe agree with the dependency interface.

Searches for an existing exact statement (msearch.py, Q15, this item):

- LeanFinder: “The unit from an etale sheaf of sets to the direct image of its proetale
  inverse image is an isomorphism”. Eight hits concern condensed locally constant
  sheaves, module pullback, equivalences of sites, or dense-subsite counits; none gives
  this comparison unit for set-valued sheaves.
- Loogle: `CategoryTheory.Adjunction.unit, CategoryTheory.Functor.FullyFaithful`.
  Four hits include `Adjunction.fullyFaithfulLOfIsIsoUnit` and restriction-adjunction
  formulas. These supply the generic categorical implication, not the needed unit theorem.
- LeanSearch: “The inverse image from the small etale topos to the small proetale topos
  is fully faithful and its adjunction unit is invertible”. Eight generic adjunction,
  equivalence, or localization results; none establishes this site's unit invertibility.
- Mathlib grep through msearch.py: `pro[Ee]tale|comparisonAdjunction` in
  `AlgebraicGeometry/Sites`. Ten hits in ElladicCohomology and Proetale, giving sites
  and other constructions, with no exact theorem.
- Project source rg: `fullyFaithful|[Ii]sIso.*[Uu]nit|unit.*[Ii]sIso` under
  `WeilConjectures/SixFunctors/ProEtale` and the side project's ProEtale modules.
  Read the complete upstream `Comparison/FullyFaithful.lean` and `Comparison/Defs.lean`:
  `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit` assumes `[Abelian A]`
  and `[IsGrothendieckAbelian A]`, so cannot be specialized to sets. The side
  `ProEtaleSiteComparisonFiniteLevel` theorem likewise concerns module coefficients;
  `ProEtaleComparisonStalk` concerns stalk comparison, not unit invertibility.
- Source grep for `det-pe-classical-sheaves-unit` in upstream WeilConjectures: no hits.
- rg for `proEtaleComparisonUnit|proEtaleComparison_unit|proEtaleSiteComparison.*[Ff]aith|
  classicalSheavesUnit` in upstream-name inventory, Mathlib, upstream WeilConjectures,
  and side Sheaf: no hits. No existing declaration states both clauses for sets.

Validation: scompile.py compiled this delivered file cleanly, checking its sandbox
and library-relative forms (2.9 s and 3.2 s respectively). Every variable and universe
is explicitly bound. The only postponed proof is the named theorem above.
No STATEMENT-DISPUTED finding and no statement correction.

## Second reading by Q15

I reread the node `det-pe-classical-sheaves-unit.json`, its source place, the
recorded dependency declarations, and `ProEtaleClassicalSheavesUnit.lean`.
The node's statement decomposes as follows.

- The object introduced is an arbitrary scheme `X`; the Lean binder is
  `(X : Scheme.{u})`, with an explicitly bound universe and no additional
  assumptions.
- The first universal object is an arbitrary sheaf of sets `F` on the small
  étale site, rendered as `F : Sheaf X.smallEtaleTopology (Type (u + 1))`.
- The first conclusion clause is that the canonical comparison unit
  `eta_F : F ⟶ nu_* nu^* F` is an isomorphism.  Lean renders this exactly as
  `IsIso ((proEtaleSiteComparison X).unit.app F)`.  The recorded dependency
  defines this adjunction with inverse image
  `Functor.sheafPullbackConstruction.sheafPullback (toProEt X) ...` and direct
  image `(toProEt X).sheafPushforwardContinuous ...`, so the unit is the node's
  `nu_X` unit rather than an unrelated map.
- The consequence quantifies over arbitrary `F F'` in the same sheaf category.
  Lean uses `∀ F F' : Sheaf X.smallEtaleTopology (Type (u + 1))`.
- The second conclusion clause is bijectivity of the map on morphisms.  Lean's
  `Function.Bijective (fun φ : F ⟶ F' ↦ ...map φ)` uses precisely the inverse
  image functor from the comparison adjunction, so this is
  `phi ↦ nu_X^* phi` with the node's quantifier order and no extra condition.

The source (Stacks Tag 099T, `lemma-fully-faithful`) assumes only that `X` is a
scheme and states unit invertibility for every étale sheaf; the adjacent source
paragraph gives the adjunction and full-faithfulness consequence.  The Lean
statement adds no Noetherian, separated, quasi-compact, characteristic, ring,
or nonemptiness hypothesis, and does not restrict the sheaf coefficients beyond
sets.

Edge cases checked: `X` may be empty; `u` is arbitrary; empty section sets,
terminal sheaves, identity morphisms, and arbitrary pairs of sheaves remain in
the quantifiers.  There is no index set, integer `n`, characteristic, or zero
object in this statement, hence those cases impose no hidden restriction.

Searches were repeated with LeanSearch (`proetale etale comparison pullback
fully faithful on sheaves of sets`), Loogle (`CategoryTheory.Adjunction.unit,
CategoryTheory.Functor.FullyFaithful`), LeanFinder (`Etale sheaves embed fully
faithfully in proetale sheaves of sets via inverse image`), and
repository/Mathlib grep for `proEtaleSiteComparison`,
`fullyFaithful`, `comparisonAdjunction`, and the item id.  The hits were generic
adjunction/site results or module-coefficient results; none states this
set-valued comparison unit and its Hom-bijection consequence.  The existing
dependency modules `ProEtaleSiteComparison`, `ProEtaleComparisonPullbackSections`,
and `EtaleSetInverseImageRestriction` were opened and their signatures match the
objects used by the statement.

One metadata mismatch was found: `lean.statement` flattened the signature's
whitespace rather than retaining it verbatim. I replaced it with the exact
multiline signature from the Lean file. No mathematical or Lean change was needed.
The searches also found a record for
`Scheme.proEtaleComparisonUnitSets_isIso` in
`lem-weil-pbc-proetale-comparison-unit-sets`. I read its recorded module through
`scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`:
the current resolved source does not contain that declaration (it contains the
affine section-formula theorems). That candidate therefore supplies no usable
existing declaration for this item. The upstream full-faithfulness theorem
requires an abelian coefficient category and does not cover sets.
The module
compiled with `scompile.py` in both sandbox and library-relative checks; its only
postponed proof is the named theorem's `sorry`.
