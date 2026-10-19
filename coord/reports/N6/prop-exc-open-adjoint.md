## Worker report

Attach the existing declaration
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`
in `WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek`
(lines 64–72 of the read-only source). No module is written and no proof is postponed.
Only the item's `lean` field changes. The previous attachment already identified this
same declaration, but lacked the complete stage-2 record. This delivery completes it.

Read the node and its three statement dependencies, their recorded signatures and
source docstrings, and the full current upstream module through `scompile.py --source`.
Read the original blueprint `prop-exc-open-adjoint.md` on the server (the literature
files are absent from the local shared checkout). Its assertion and proof agree with
the DAG. This is an existing-declaration attachment, not a new derived operation.

Hypothesis and clause matching:

- The finite commutative coefficient ring is `(A : Type u) [CommRing A] [Finite A]`.
  Specialize the upstream coefficient-category parameter to
  `ModuleCat.{u + 1} (ULift.{u + 1, u} A)`. The category is abelian, Grothendieck,
  symmetric monoidal, closed, monoidal preadditive, and has functorial flat resolutions
  by existing instances. These are properties of this coefficient category, not added
  hypotheses on A or on a complex. The wrapper compilation checked their inference.
  The universe lift changes only the presentation of the coefficient ring and allows
  the module universe required by the small pro-etale site.
- The schemes and open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`. No finite-type, separatedness, nonemptiness, characteristic,
  or invertibility assumption is introduced.
- The small sites are exactly `Scheme.ProEt.topology U` and
  `Scheme.ProEt.topology X`, used by the upstream functors.
- Extension by zero is `ProEtale.openImmersionLowerShriek` with the above module
  coefficient category. Its construction is presheaf left Kan extension along the
  localization followed by sheafification. For an open immersion the factorization
  indexing set is empty or a singleton, giving the node's zero-or-original-section
  prescription.
- Inverse image is `ProEtale.upperStar` with the same coefficient category.
  `ProEtale.upperStarIsoOpenImmersionRestriction` identifies it canonically with
  restriction along the open localization. This is inverse image, not direct image.
- `D((j)_!open[A]) ⊣ D((j)^*[A])` is the actual adjunction data on the unbounded
  `DerivedCategory` categories. `D(-)` is `Functor.mapDerivedCategory`, applying
  the exact functor termwise and descending through quasi-isomorphisms. This is the
  unbounded declaration, not its separate `...Plus` bounded-below sibling.
- Neither functor's domain is a constructible or finite-Tor subcategory; no hypotheses
  on objects occur. Thus the final sentence is rendered by the scope of the adjunction.
- The rings `A_{E,n}` are examples, not an additional coefficient restriction. The
  recorded `Padic.coefficientExtensionRing` and
  `Padic.finite_coefficientExtensionRing` give a finite commutative ring for `n ≥ 1`,
  so the same specialization includes them.

Dependency interfaces read:

- `def-weil-extension-by-zero` records
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` in
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`. Its body is literally
  the upstream `openImmersionLowerShriek` between the inverse and forward canonical
  `sfIntrinsicModuleEquivalence`s. Hence the attachment uses the same extension by
  zero in the fixed-scalar presentation. The equivalence is the published
  `finiteCoefficientIntrinsicRealization.asEquivalence`, extending scalar actions
  through the constant-sheaf unit, not an arbitrary identification. Its source and
  `finiteCoefficientIntrinsicRealization_exact` in
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` were read.
- `def-weil-finite-torsion-constructibility` records
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` in
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`. Its bounded-constructibility
  predicate is not an assumption of this theorem. Its quotient ring supplies the
  mentioned examples; no global finite-field datum or l ≠ p is needed here.
- `def-weil-scheme-morphism-properties` is explicitly a convention node. Its open
  immersion pointer means Mathlib's `AlgebraicGeometry.IsOpenImmersion`.

The upstream proof is exactly the node's route: the sheaf adjunction is exact on both
sides; applying it to complexes and localizing yields
`Adjunction.mapDerivedCategoryAdjunction`. The implementation uses the generic total
left/right derived machinery and then exactness to identify it with these termwise
functors. `ModuleCat.hasFunctorialFlatResolution` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` supplies
its resolution requirement without imposing a Tor condition on objects.

Edge cases checked: empty U, empty X, identity and arbitrary open immersions,
zero coefficient ring, and unbounded complexes. The signatures impose no nonempty,
nontrivial, bounded, constructible, or Tor-amplitude assumptions excluding these cases.
The small site retains different object and morphism universes; no equality of them
is imposed. Independent sizes may be placed in a common maximum universe.

Searches actually run on 2026-10-16:

- `msearch.py ... leanfinder "right adjoint open immersion extension by zero inverse
  image ordinary derived category pro-etale"`: eight Mathlib hits, principally
  ordinary Zariski `Scheme.Modules.restrictAdjunction`; none is this assertion.
- `msearch.py ... loogle "derivedOpenImmersionLowerShriekUpperStarAdjunction,
  Adjunction, DerivedCategory"`: zero hits; Loogle reported the upstream identifier
  unknown to its Mathlib index.
- `msearch.py ... leansearch "extension by zero is left adjoint to inverse image on
  unbounded derived categories of proetale module sheaves"`: service unavailable
  (HTTP internal server error), not a negative search result.
- `msearch.py ... grep "derivedOpenImmersionLowerShriekUpperStarAdjunction|openImmersionLowerShriekUpperStarAdjunction"
  WeilConjectures/SixFunctors`: zero hits (this wrapper searches Mathlib, not upstream).
- `msearch.py ... grep "extensionByZero|lowerShriek|LowerShriek" CategoryTheory`:
  zero Mathlib hits.
- Direct `rg` in upstream for the node id found the exact declaration's blueprint
  docstring at line 64. Name searches found the declaration, its bounded-below
  sibling, and callers. Direct Mathlib `rg` found only general derived-adjunction
  machinery. Direct `rg` in `lean/Sheaf` found no second statement of this exact
  unbounded pro-etale adjunction; it did locate the canonical intrinsic transport
  definition discussed above.

Validation: `scompile.py N6 prop-exc-open-adjoint scratchpad/ExistingChecks.lean`
passed both file checks without errors or warnings. The probe checks the full generic
signature and its finite-ring specialization. `#print axioms` returned exactly
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
No statement correction, new node, dependency repair, or disputed statement is needed.
The independent second reader remains responsible for review and actual delivery.

## Second reading by N6

I independently opened the sandbox node, its source blueprint, the containing unit
and chapter, all three statement-dependency records, and the declarations below.
The blueprint was read directly on the project server because its local literature
copy is absent. This source is a blueprint Markdown node, not a Stacks lemma with
an additional ambient-hypothesis section. Its statement and two proof paragraphs
agree verbatim with the DAG. The containing closed-immersion unit has finite-type
and constructibility hypotheses for its own proposition, but the present auxiliary
node explicitly asserts the open adjunction on the entire ordinary categories.
Those unit hypotheses are not hypotheses of this node.

My object/hypothesis/conclusion checklist, made from the node before comparison:

1. A finite commutative ring A: specialize the upstream category parameter (also
   named A there) to `ModuleCat.{u + 1} (ULift.{u + 1, u} A)` for
   `(A : Type u) [CommRing A] [Finite A]`. The printed full signature requires an
   abelian Grothendieck coefficient category, symmetric closed monoidal structure,
   monoidal preadditivity and functorial flat resolutions. The finite-ring probe
   supplies all these by instance inference. These introduce no extra ring or
   complex hypothesis. Verdict: matches.
2. Schemes U, X and an open immersion j: the source context is
   `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`. I opened the convention
   node and its `def-weil-open-immersion` pointer; Mathlib's `IsOpenImmersion`
   means the stated open-subscheme identification. There is no base field,
   Noetherian, separated, quasi-compact, or finite-type binder. Verdict: matches.
3. The small pro-etale sites: both functors have sheaf categories over exactly
   `Scheme.ProEt.topology U` and `Scheme.ProEt.topology X`, not the etale or
   Zariski sites. Verdict: matches.
4. Constant A-module sheaves and the specified extension by zero: I opened
   `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and its comparison
   import, not just the similarly named upstream functor. With
   `E_T = sfIntrinsicModuleEquivalence T A`, the recorded dependency literally is
   `E_U.inverse ⋙ ProEtale.openImmersionLowerShriek (ModuleCat _ ) j ⋙ E_X.functor`.
   The middle functor is precisely the functor in the attached adjunction.
   `finiteCoefficientIntrinsicRealization` extends scalars along the canonical
   constant-sheaf unit by module sheafification; `E_T` is its equivalence, not an
   arbitrary identification. Thus the attachment uses the fixed-scalar
   presentation of the same constant-ring modules and extension-by-zero functor.
   The upstream construction is localization left Kan extension followed by
   sheafification; uniqueness of factorization through j gives the prescribed
   original-module/zero alternatives. Verdict: matches through this specified
   canonical equivalence; no private replacement notion.
5. Inverse image as the right adjoint: `D((j)^*[A])` expands to
   `(ProEtale.upperStar A j).mapDerivedCategory`.
   I read `upperStarIsoOpenImmersionRestriction` and the construction of
   `openImmersionLowerShriekUpperStarAdjunction`: this upper star is canonically
   restriction along the open localization. In the intrinsic presentation the
   right functor is restriction with the constant scalar action transported by
   the same E_X and E_U; extension of constant actions to local scalar sections
   commutes with this restriction. Verdict: inverse image, with the correct
   variance, and not direct image or an arbitrary right adjoint.
6. The adjunction on the entire ordinary derived categories: the declaration is
   `noncomputable def ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction :`
   followed by `D((j)_!open[A]) ⊣ D((j)^*[A])`. Both `D` expressions are termwise
   `mapDerivedCategory` on unbounded derived categories. I checked the body uses
   `mapDerivedCategoryAdjunction`; the separate `...Plus` declaration is not the
   selected declaration. Adjunction supplies natural Hom bijections, unit,
   counit and triangle identities. Verdict: every conclusion clause matches.
7. No constructibility or finite-Tor restriction: neither side is a full
   subcategory and no object-dependent assumption occurs. The upstream flat
   resolution instance is a property of the coefficient category, not a finite
   Tor condition on any object. Verdict: matches the node's final sentence.
8. The examples A_{E,n}: the dependency records
   `intrinsicFiniteTorsionConstructible`, whose coefficient ring is the actual
   `Padic.coefficientExtensionRing l E n`. I opened that predicate, the quotient
   ring definition, and `Padic.finite_coefficientExtensionRing`: for positive n
   this is a finite commutative ring, hence an instance of checklist item 1.
   Constructibility itself is not an assumption here. Verdict: included, with
   no restriction to just these examples and no extra characteristic condition.

Edge cases: the signatures allow empty U and empty X, the identity immersion,
an arbitrary open immersion, the zero ring, zero complexes and complexes
unbounded in both directions. There is no index set or cohomological-degree
binder to restrict; n is only in the coefficient examples, where the source
requires n >= 1. The zero-ring specialization also covers the formula at n = 0.
The site object universe and morphism universe remain distinct. The coefficient
category has the required morphism universe u+1, achieved by ULift of the ring;
this is not an equality imposed on site universes. Larger ambient choices can
be made in a common maximum universe. Every variable in the attached signature
is bound by its source section context, confirmed by `#check @...`.

Independent duplicate searches on 2026-10-16 used different search terms from
the worker's:

- LeanFinder: `exact left adjoint localization of unbounded chain complexes
  sheaves along an open inclusion`; eight hits about sheaf adjunctions,
  sheafification/localization and abelian localization, none this pro-etale
  unbounded adjunction.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Sheaf`; twelve hits about
  sheafification and sheaf composition, not this statement.
- Mathlib grep through msearch: `restrictAdjunction|extension.?by.?zero|openImmersion.*Adjunction`
  in AlgebraicGeometry; five hits for ordinary scheme-module restriction, not
  this statement. Direct Mathlib rg for extension by zero, open-immersion
  adjunctions and left Kan adjunctions likewise found only generic machinery.
- Direct rg in WeilConjectures for localization/restriction and derived open
  adjunctions found the exact selected declaration and its distinct bounded-below
  sibling. I opened its current server source through `scompile.py --source`
  and its sheaf-level construction, rather than relying on its name or audit.
- Direct rg in `lean/Sheaf` for the intrinsic extension, coefficient equivalence
  and derived open adjunction found the dependency modules and etale/bounded-below
  callers, but no alternative statement of this unbounded pro-etale adjunction.
- LeanSearch: `exact extension by zero functor left adjoint restriction on derived
  categories sheaves`; HTTP Internal Server Error, recorded as unavailable, not
  as evidence of absence.

No new definition node or dependency module is delivered, so H12/H13 introduce
no additional nodes to review. No node statement is corrected and there is no
`statement_change` or citer audit to amend. The existing source declaration has
real adjunction data, and is not a hollow definition. No new proof is written.
Its docstring identifies this blueprint node and explains exactness, the
sheaf-level adjunction and derived descent, consistent with both proof steps.
The stored `lean.statement` is verbatim the two signature lines in that source.

Validation independently rerun:
`scompile.py N6 prop-exc-open-adjoint scratchpad/ExistingChecks.lean` passed
both isolated file checks without errors or warnings. It printed the full
generic signature and the finite-ring specialization, with all instances
inferred. `#print axioms` of the attached upstream declaration returned only
`propext`, `Classical.choice`, `Quot.sound`.

No mathematical or signature mismatch was found; I retained the node's Lean
attachment and added this independent reading only. For precision, the axiom
claim above concerns the attached fixed-scalar upstream declaration itself.
The published intrinsic comparison's exact-equivalence theorem is still a
stage-2 theorem with a postponed proof; the report does not assert that this
comparison has already been proved without sorry.
