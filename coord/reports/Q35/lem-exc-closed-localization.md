## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization` states
`AlgebraicGeometry.ProEtale.proEtale_closed_localization`, with `sorry` as its whole
proof. It introduces no definitions, new nodes, or dependency replacements. The
natural-language statement, dependency lists, and proof are unchanged.

Hypotheses and clauses, matched with the Lean:

- Schemes `X` and `Z` are `{X Z : Scheme.{u}}`; the closed immersion is
  `(i : Z ⟶ X) [IsClosedImmersion i]`.
- The weakly etale morphism `W → X` is an arbitrary `(W : X.ProEt)`; its underlying
  scheme, map, and weakly etale proof are `W.left`, `W.hom`, and `W.prop`.
  This includes every weakly etale morphism between schemes of the size convention.
- The cartesian square is the chosen `pullback i W.hom`, with
  `v_Z = pullback.fst i W.hom` and `i_W = pullback.snd i W.hom`.
  Every cartesian square of the stated form is canonically isomorphic to this one;
  choosing the product does not add a mathematical hypothesis.
- Constant commutative coefficients are `(Λ : Type (u + 1)) [CommRing Λ]`.
  Module sheaves are `Sheaf (Scheme.ProEt.topology _) (ModuleCat.{u + 1} Λ)`,
  the existing fixed-coefficient encoding used by the restriction-injectives node.
  There is no finiteness, invertibility, constructibility, or boundedness condition.
- Restriction to `W` is `localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop`.
  Restriction along `v_Z` is the same recorded upstream construction at the first
  projection; its weakly etale instance follows from weakly etale base change.
- Commutation with underived closed direct image is the natural isomorphism `alpha`,
  from `lowerStar i ⋙ restriction W` to `restriction v_Z ⋙ lowerStar i_W`.
  The coefficient category is written explicitly at each occurrence of these functors.
  The first conjunct fixes its component on every sheaf `G` and every object `T`
  to `G.obj.map` of the opposite of the canonical
  `MorphismProperty.Over.pullbackMapComparison`. Thus `alpha` is the actual
  fibre-product restriction identification, including its scalar action and maps.
- Agreement of the two inverse-image composites is the natural isomorphism `beta`,
  from `upperStar i ⋙ restriction v_Z` to `restriction W ⋙ upperStar i_W`.
  Localization restriction is canonically inverse image for weakly etale maps by
  `upperStarIsoLocalizationRestriction`. The inverse images `upperStar` are the
  already defined module-valued Kan extension followed by sheafification.
- Unit compatibility is the second conjunct: for every `F`, restrict the unit at
  `i`, apply `alpha` at `i^* F`, and push forward `beta` at `F`; this equals the unit
  at `i_W` on the restriction of `F`.
- Counit compatibility is the third conjunct: for every `G`, apply `i_W^*` to
  `alpha.inv`, then apply `beta.inv` at `i_* G`, then restrict the counit at `i`;
  this equals the counit at `i_W` on the restriction of `G`.
  All four unit/counit occurrences are those of the existing
  `upperStarLowerStarAdjunction`. These equations identify `beta` with the adjoint
  of the normalized direct-image identification, so no arbitrary comparison or
  arbitrary adjunction is substituted.

Dependency declarations read and used:

- The recorded statement dependency is
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`, imported publicly.
  Its signatures and docstrings, and the reexported original operations and canonical
  adjunction modules, were read. Its fixed-scalar `upperStar` is explicitly the
  operation transported into finite-coefficient modules by `finiteCoefficientPullback`.
  This theorem uses that existing fixed-scalar encoding directly, without restricting
  the coefficients to finite rings or constructing a replacement coefficient category.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` is publicly reexported by that
  dependency: `Scheme.proEtaleBaseChange`, `Scheme.proEtaleSheafInverseImage`, and
  `Scheme.proEtaleSheafAdjunction` give the base-change, Kan-extension/sheafification,
  and adjunction constructions. For `ModuleCat Λ`, these are definitionally the
  upstream `lowerStar`, `upperStar`, and `upperStarLowerStarAdjunction` used here.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `ProEtale.localizationRestriction`, `ProEtale.localizationRestrictionLowerStarAdjunction`,
  and `ProEtale.upperStarIsoLocalizationRestriction`. Their complete signatures and
  docstrings were read. The module reexports
  `MorphismProperty.Over.pullbackMapComparison`, whose construction and signature were read.
- The proof dependency `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives` was read
  in full, including `proEtale_restriction_injectives` and its slice, exactness,
  injectivity, and derived-evaluation clauses. Its module import was tested and removed:
  it imports the legacy `ProEtale.UpperLowerStar.Defs`, which conflicts with the
  finite-coefficient operations required by the statement dependency. Both the local
  compiler and server confirmation reported the duplicate scoped notation
  `AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. Following the launcher's duplicate-import
  repair instruction, the theorem imports only the finite-coefficient side needed
  for its signature. Its proof docstring retains this proof dependency and its slice
  argument. No declaration from that incompatible module is redeclared.

Edge cases checked before writing: empty `W`, empty `Z`, and the empty ambient scheme
are not excluded; the zero ring and zero module are allowed; identity localization
and identity closed immersion are allowed; no geometric points, nonemptiness, or
positive characteristic/invertibility conditions occur. All integer or derived
conditions are absent because this is an underived statement. The site retains
object universe `u+1` and morphism universe `u`, with coefficient modules of size
`u+1`; neither site universe is forced equal to the other.

Searches performed:

- `msearch.py ... leanfinder`, query “restriction to weakly etale localization commutes
  with closed immersion direct image inverse image unit counit”: eight results;
  scheme-module open-immersion restriction and unrelated geometry, no full match.
- `msearch.py ... loogle`, query `CategoryTheory.Adjunction, NatIso, IsPullback`:
  no results, with `unknown identifier 'NatIso'`.
- `msearch.py ... leansearch`, query “pro etale sheaf restriction closed immersion
  direct image base change adjunction”: unavailable, Internal Server Error.
- `msearch.py ... grep`, pattern
  `localizationRestriction|closed.*baseChange|baseChange.*closed` in `CategoryTheory`:
  one unrelated precoverage/hypercover result.
- `rg` in Mathlib, upstream `WeilConjectures`, the upstream name inventory, and
  `lean/Sheaf` for `closedLocalization`, `closed_localization`, `ClosedLocalization`,
  and the exact node id: no full matching theorem. General closed ring localizations
  and unrelated open-closed modules were inspected and excluded.
- `rg` for `localizationRestriction` found upstream
  `ProEtale.BaseChange.WeaklyEtale`. Its full source was read: it provides canonical
  direct-image base change and its mate with the *localization* adjunctions, but does
  not state both closed inverse-image/unit/counit clauses of this node. Hence there
  is no exact existing declaration to record. Its site-level comparison is reused
  directly instead of defining another base-change map.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
  confirmed the current published interface agrees with the read-only local source.
- The original blueprint node and unit were read from the available literature copy
  under `work-bp/sheaf`; the node's three reviewed proof steps were read from its JSON.

No mathematical node fault or `STATEMENT-DISPUTED` finding.

Validation: `scompile.py Q35 lem-exc-closed-localization` compiled the final file
successfully both as a sandbox module (9.9 seconds) and under its library module
name (4.4 seconds), with no warnings or errors. The JSON signature is verbatim,
only the node's `lean` field changes, and every Lean line is at most 100 characters.

## Second reading by Q35

I read the sandbox theorem independently against the shared DAG node, its three
proof steps, and the blueprint source at order 1846. The source file is available
in `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/` under
`sec-smooth-purity/sk-prop-sf-open-closed-triangle/lem-exc-closed-localization.md`.
I also read the unit `_section.md`, the recorded operations and inverse-image node
statements and declarations, the restriction-injectives declaration, and the
supporting Stacks sources. In `proetale.tex`, `section-morphism` (Tag 09A5) starts
with an arbitrary morphism of schemes and defines the site morphism by base change.
The extra quasi-compact/quasi-separated hypotheses belong to the following etale
comparison lemma, which this item does not use. The closed-immersion section adds
no ambient field or Noetherian hypothesis. In `sites-modules.tex`,
`lemma-adjoint-push-pull-modules` uses the ordinary inverse/direct-image adjunction
and the action restricted along its coefficient unit. The finite-type k-scheme
assumptions of the target triangle do not occur in this auxiliary node's own
statement or its base-change argument.

The list of objects, hypotheses, and conclusion clauses, matched item by item:

1. Ambient and closed schemes X and Z: `{X Z : Scheme.{u}}`. Verdict: exact,
   with arbitrary schemes in the established size convention.
2. Closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]`. Verdict: exact;
   this is not an open immersion, a proper-map substitute, or a chosen closed subset.
3. Weakly etale v: W → X: `(W : X.ProEt)`, with scheme `W.left`, map `W.hom`,
   and certificate `W.prop`. Verdict: exact. This bundles arbitrary weakly etale
   morphisms, without an etale, affine, quasi-compact, or monomorphism condition.
4. Cartesian square: `pullback i W.hom`, with `pullback.fst i W.hom : Z_W ⟶ Z`
   and `pullback.snd i W.hom : Z_W ⟶ W.left`. Verdict: exact. Every other
   cartesian square with these maps is canonically isomorphic to this one.
   The weakly etale certificate on the first projection is obtained by base change;
   it is not an extra hypothesis. The square passed to the comparison is correctly
   flipped: its bottom arrow is W → X and its right arrow is Z → X.
5. Coefficients and sheaves: `(Λ : Type (u + 1)) [CommRing Λ]` and
   `Sheaf (Scheme.ProEt.topology _) (ModuleCat.{u + 1} Λ)`. Verdict: the
   constant-coefficient module sheaves specified in proof step 2 and in the
   restriction-injectives node. The theorem has no `[Finite Λ]`, topology, field,
   torsion, characteristic, or invertibility assumption. The operations dependency
   retains its arbitrary identified-coefficient interface and its constant
   specialization; the word `FiniteCoefficient` in its current module path does
   not impose the hypotheses of its separate realization declarations here.
6. Restriction functors: `localizationRestriction (ModuleCat.{u + 1} Λ)` at
   `W.hom` and `pullback.fst i W.hom`. Verdict: the existing restriction by
   composition on site objects, not arbitrary functors. The read declaration
   `upperStarIsoLocalizationRestriction` identifies these with inverse image by
   the specified adjunction to `lowerStar` for weakly etale maps.
7. Restriction commutes with underived closed direct image: the first existential
   `alpha` has type `lowerStar i ⋙ restriction v ≅ restriction v_Z ⋙ lowerStar i_W`,
   with the coefficient category explicit throughout. Verdict: all sheaves are
   quantified, and this is the underived operation. The first conjunct specifies
   its component on every `G` and every `T : W.left.ProEt` as `G.obj.map` of the
   opposite of `MorphismProperty.Over.pullbackMapComparison`. I read that
   construction: its component is the fibre-product lift from the local product
   to the global product. Contravariance therefore gives exactly the stated
   direct-image map. Its projections, coefficient action, and naturality agree
   with proof step 1; the existential is not an arbitrary isomorphism.
8. The two composites of inverse images agree: the second existential `beta` has
   type `upperStar i ⋙ restriction v_Z ≅ restriction v ⋙ upperStar i_W`.
   Verdict: exact direction and domains. I read `upperStar` and
   `upperStarLowerStarAdjunction` in the finite-coefficient framework, and
   `Scheme.proEtaleSheafInverseImage` and `Scheme.proEtaleSheafAdjunction` in the
   recorded inverse-image module. They use the same base-change functor, Kan
   extension, sheafification, and constructed adjunction. For `ModuleCat Λ` the
   module-valued construction keeps the fixed scalar action. No replacement
   adjunction or private coefficient-category copy is introduced.
9. Unit compatibility, for every ambient F: the second conjunct first restricts
   `unit_i F`, then applies `alpha` at `i^* F`, then applies `i_W*` to `beta F`.
   Its result equals `unit_i_W (restriction v F)`. Verdict: the whole square
   commutes, including its actual unit; no isomorphism-only weakening.
10. Counit compatibility, for every closed G: the third conjunct first applies
    `i_W^*` to `alpha.inv G`, then `beta.inv` at `i_* G`, then restricts
    `counit_i G`. Its result equals `counit_i_W (restriction v_Z G)`.
    Verdict: the whole square commutes with the actual counit. The inverses occur
    in the correct direction. Together with the normalized alpha, these equations
    fix the inverse-image comparison by adjunction.
11. Quantifiers: i, W, and Λ precede the two comparisons; each comparison is one
    natural isomorphism valid for all sheaves and all test objects. Verdict: exact;
    there is no separate choice of comparison for each sheaf or test scheme.

Dependency and delivery audit: the only delivery module belongs to this item;
there are no new definition nodes, dependency replacement modules, or
`statement_change` to audit under H12/H13/step 4c. The original operations module
is publicly reexported through the recorded finite-coefficient direct-image
module. The proof-only restriction-injectives import is omitted for the duplicate
legacy/finite scoped notation collision already documented in the Worker report;
I inspected that module's imports and full theorem. Its slice identification is
retained in the proof plan, and none of its declarations is privately duplicated.
The statement itself needs only the already imported canonical restriction and
inverse/direct-image constructions.

Edge cases: empty W, empty Z, empty X, zero coefficient ring, zero module sheaves,
identity localization, and identity closed immersion are all permitted. The
comparison is functorial on the entire site, including the empty object. There is
no numerical degree or indexing family in this underived lemma, so n = 0 and an
empty external index set add no omitted case. Characteristics are unrestricted.
The site keeps object universe u+1 and morphism universe u; coefficient-module
morphisms live in u+1. No equality of site universes or additional smallness
binder is imposed. All variables and the sole universe `u` are explicitly bound.

Independent searches, using different words from the Worker report:

- `msearch.py ... leanfinder`, query `Beck Chevalley equivalence sheaves cartesian
  square localization adjunction mate`: eight hits. The relevant candidates were
  the general sheaf-pullback adjunction and its abstract comparison isomorphism,
  sheaf composition transformations, and the module pullback adjunction. None
  states this closed-localization comparison with both closed unit/counit equations.
- `msearch.py ... loogle`, query `CategoryTheory.Adjunction, CategoryTheory.NatIso`:
  zero hits, unknown identifier `CategoryTheory.NatIso`; this is an unavailable
  pattern, not evidence of nonexistence.
- `msearch.py ... leansearch`, query `Base change for sheaves along localization
  respects inverse image direct image adjunction unit counit`: unavailable,
  Internal Server Error.
- `msearch.py ... grep`, pattern
  `BeckChevalley|beckChevalley|localizationRestrictionBaseChangeMap`: zero hits
  in its Mathlib search. Direct `rg` searches in Mathlib's category theory,
  upstream `WeilConjectures`, and project `lean/Sheaf` used `mateEquiv`,
  `localizationRestriction`, `closed.*localiz`, `localiz.*closed`,
  `baseChange.*[Uu]nit`, and `baseChange.*[Cc]ounit`. I also checked the upstream
  declaration inventory for the proposed name and closed-localization variants.
  Generic mates and ring localizations are different statements.
- I opened and read upstream `ProEtale/BaseChange/WeaklyEtale.lean` in full.
  `isIso_localizationRestrictionBaseChangeMap_of_isPullback` supplies the direct
  image part; `mateEquiv_localizationRestrictionBaseChangeMap` concerns the
  localization adjunctions in the other direction. Neither gives the two closed
  inverse-image/unit/counit clauses of this item. Thus there is no exact existing
  declaration to attach. The actual shared site comparison is reused in the
  theorem, rather than defined again.

H3 verdict: no mismatch found and no mathematical repair needed. H4/H5/H6/H8/H9:
no duplicate notion, no definitions or hollow data, one theorem with whole proof
`sorry`, source/blueprint docstrings and all three proof steps present, public
statement imports, no private/local notation or instance, and lines at most 100
characters. I left the correct Lean and node unchanged and added this independent
reading only. A mechanical check confirmed that `lean.statement` equals the
signature verbatim, and that the sandbox node differs from the shared node only
in `lean`. The required final compile and delivery dry run are recorded below.

Validation completed: `scompile.py Q35 lem-exc-closed-localization
lean/Sheaf/AlgebraicGeometry/ProEtaleClosedLocalization.lean` passed for both the
sandbox and library module names (23.9 s and 25.1 s), without warnings or errors.
`deliver2.py Q35 lem-exc-closed-localization --no-push` printed
`OK (dry run): commit 2b925414a5 passes the preflight and compiles; nothing pushed`.
The dry run staged exactly the item module, item node, and Q35 report.
