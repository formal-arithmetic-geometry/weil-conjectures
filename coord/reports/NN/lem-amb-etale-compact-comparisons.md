## Worker report

The node is delivered as a mixed record, as permitted by stage-2's existing-declaration
rule and its mixed-record checker: one missing normalization theorem in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`, together with the existing
upstream coherent comparison and composition declarations in `lean.declarations`.
The new theorem has only `sorry` as proof. There are no definitions, additional nodes,
dependency repairs, or statement corrections.

### Hypotheses and clauses

- Finite commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  All the reused comparison and composition declarations use these same coefficients.
- Ordinary small etale module sheaves and bounded-below complexes:
  `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  These are the coefficient categories of `def-weil-pbc-derived-categories`, not
  pro-etale, condensed, or ringed-space module categories.
- Noetherian X and Y: `[IsNoetherian X] [IsNoetherian Y]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this exactly with the
  node's finite affine cover by Noetherian spectra, including the empty scheme.
- A separated finite-type morphism: `(f : X ⟶ Y) [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]`. Chosen compactifications are
  `{c d : Compactification f}`; they in particular witness compactifiability.
- Restriction of the unbounded candidate to D+: existing
  `rightDerivedLowerShriekOfCompactificationPlusCompatibility` identifies the
  restriction with `rightDerivedLowerShriekOfCompactificationPlus`; it is the
  same `Dj_!` followed by `Rr_*`, with no new candidate definition.
- The *specified* proper-refinement comparison: `(r : c.Refinement d)` is arbitrary.
  `etaleCompactSupport_refinementComparison_eq` states that the component of the
  existing natural refinement isomorphism is exactly
  `R(d.g)_*.map (properOpenComparison Λ r.hom c.i d.i r.i_hom K)`, followed by
  the inverse of the formalism's `pfComp' r.hom d.g c.g r.hom_g`.
  `pfComp'` points from the composite-morphism pushforward to the iterated
  pushforward; its inverse therefore has precisely the node's required direction.
  The module `LowerShriekFormalismComparison`, re-exported by `LowerShriekComposition`,
  identifies this inverse with the injective-representative composition identification.
  Equality at every K identifies the natural transformation without assuming
  naturality as an extra hypothesis.
- Natural coherent isomorphisms, identities and composites of refinements:
  `rightDerivedLowerShriekOfCompactificationPlusRefinementIso` has a natural
  isomorphism as its type. Its `_id` is `Iso.refl`, and `_comp` says the map for
  `r.comp s` equals the comparison for s followed by that for r (contravariance).
- Independence of common refinement:
  `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso` identifies
  the canonical isomorphism c to d with `A_r` followed by `A_s.symm`, for EVERY
  common refinement e and arbitrary r:e→c and s:e→d. No Cartesian/density
  condition on these refinements is imposed. This is the node's A_s⁻¹ A_r.
- Identity and cocycle for the resulting candidate identifications: the existing
  `rightDerivedLowerShriekOfCompactificationPlusIso_refl` and `_trans` state
  exactly C_cc = id and C_cd followed by C_db = C_cb.
- The notation Rf_! uses existing `rightDerivedLowerShriekPlus`, the functor of
  `HasCompactification.compactification f`; the independent comparisons identify
  every other candidate with it. The independence node is added to stmt_deps,
  since its recorded `RefinementIso` occurs in the new normalization theorem.
- For composable compactifiable separated finite-type f and g of Noetherian
  schemes, `rightDerivedLowerShriekPlusCompIso Λ f g` has type
  `rightDerivedLowerShriekPlus ... f ⋙ rightDerivedLowerShriekPlus ... g ≅
   rightDerivedLowerShriekPlus ... (f ≫ g)`.
  The required `HasCompactification (f ≫ g)` is available by Nagata over the
  Noetherian (hence qcqs) target; it is not an extra mathematical hypothesis.
  Its quasi-compactness hypotheses follow from finite type.
- Independence from compactification choices: `_hom_eq` computes this map for
  EVERY `Compactification.Triangle f g`, conjugating the model map by the
  canonical comparisons for its three compactifications. It is not a bare
  existence of an arbitrary natural isomorphism.
- Associativity for three such morphisms: `_assoc` equates the two composites,
  including the functor associator and transport along `Category.assoc f g h`.
  All its compactifiability instances follow over the Noetherian targets by
  Nagata, and quasi-compactness follows from finite type. The declared theorem
  applies to X,Y,S,T Noetherian without any additional geometric hypotheses.

### Dependencies and source declarations read

Read each original statement dependency's complete node, recorded signature and docstring:

- `Sheaf.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` and the recorded
  `DerivedCategoryModule`, `DerivedCategory.Plus`, and `Bounded` encoding.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`; its defining
  compactification clause uses `WeilConjectures.Compactification.Defs`,
  `AlgebraicGeometry.Compactification` and `HasCompactification`. The new statement
  uses those general definitions and does not impose a field hypothesis.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, and the
  bounded-below candidate, restriction compatibility, and chosen candidate.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`:
  `AlgebraicGeometry.Etale.properOpenComparison`, with its actual
  `properOpenSection`, `properOpenIdentification` and descended counit formula.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`:
  the full refinement and independent-cocycle family recorded above; the current
  published source was also read with `scompile.py --source`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  the full canonical bounded-below composition family, its triangle normalization,
  and associativity. Also read `LowerShriekFormalismComparison` to check the
  normalization of the direct-image composition identification.

All stated proof-dependency modules are imported, directly or via these public
imports. Unstated proof lemmas are left to stage 3; none is a missing definition
needed to type this statement. The theorem docstring carries all five proof steps,
including equalization of parallel refinements, the explicit compatible-model
construction, interchange, tower choice independence, and pasting associativity.

### Edge cases

The empty scheme, zero ring, zero complex, degree zero, arbitrary lower bound,
and arbitrary residue characteristics are allowed. Finite coefficients need no
invertibility hypothesis. Arbitrary refinements, including non-dense ones and
ones whose square over X is not Cartesian, are included. Identity refinements
are covered by `_id`; identity morphisms are allowed by the existing composition
API. Threefold composition includes both parenthesizations and their equality
transport. The coefficient/site universe is the established `u + 1` convention;
no independent smaller site or coefficient universe is imposed.

### Searches and verification

- `msearch.py ... leanfinder` query: "For finite ring coefficients the bounded
  below etale compact support functors have canonical compactification comparisons
  and associative composition isomorphisms". Eight hits, including affine-limit
  and condensed constructions, none the requested statement.
- `msearch.py ... loogle '"rightDerivedLowerShriek"'`: zero hits.
- `msearch.py ... grep 'LowerShriek|[Cc]ompactification' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in upstream `WeilConjectures` found `LowerShriekCoherence` and
  `LowerShriekComposition`. Reading their complete relevant declarations found
  all comparison/composition coherence clauses, but no equation relating the
  separately recorded `properOpenComparison` to that API. The module only adds
  this missing normalization; existing constructions are reused.
- `rg` in project `lean/Sheaf` found `EtaleShriekQcqsComposition`, whose theorem
  gives only `Nonempty` of an isomorphism and therefore does not state the
  canonical coherent package. The independence node already records the exact
  upstream independent-cocycle family, which is reused rather than copied.
- Upstream grep of the item ID found no implementation. Searches for the new
  declaration name in Mathlib/upstream/project names found no collision.
- `scompile.py NN lem-amb-etale-compact-comparisons` compiled the delivered module
  cleanly (sandbox and library forms), with no errors or warnings.

No STATEMENT-DISPUTED issue was found. No original node statement was changed.

## Second reading by NN

I independently read the complete node, its five proof steps, the blueprint source,
Stacks more-etale.tex (the section preceding 0F7I and the proofs of 0F7I, 0F7J,
0F7K), the five statement-dependency nodes, and the signatures and constructions
in their recorded modules. No statement correction or dependency repair is needed.
There are no new nodes or sibling dependency modules in this delivery.

### Object, hypothesis and conclusion checklist

1. Finite commutative ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   Verdict: exact; neither a field nor invertibility of its characteristic is assumed.
2. Ordinary small etale module categories and D+: `Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)` and `DerivedCategory.Plus`. Opened DerivedCategories and
   the upstream coefficient encoding; these are the dependency's recorded categories,
   not the pro-etale or ringed-space encoding. Verdict: exact.
3. Schemes X,Y with finite affine Noetherian covers: `[IsNoetherian X]`
   and `[IsNoetherian Y]`. Read Mathlib Noetherian.lean, including the class
   (locally Noetherian plus compact) and the finite affine open-cover equivalence.
   These express exactly the stipulated convention. Verdict: exact.
4. Compactifiable separated finite-type f: `(f : X ⟶ Y) [IsSeparated f]
   [LocallyOfFiniteType f] [QuasiCompact f]`, with arbitrary
   `{c d : Compactification f}`. Opened Compactification.Defs: the data are an
   ambient scheme, proper g, open immersion i, and f = i followed by g.
   Such c,d witness compactifiability; finite type is locally finite type plus
   quasi-compactness. The imported over-field theorem adds no field binder here.
   Verdict: exact.
5. Restrict the unbounded chosen candidate to D+: the recorded existing
   `rightDerivedLowerShriekOfCompactificationPlusCompatibility` is an isomorphism
   from the Plus candidate followed by inclusion to inclusion followed by the
   unbounded candidate. Read both candidate bodies: degreewise derived open
   extension followed by total right derived proper pushforward. Verdict: exact.
6. The specified proper-refinement comparisons: arbitrary `(r : c.Refinement d)`
   and arbitrary `(K : DerivedCategory.Plus ...)` in the new theorem.
   Its right side is R(d.g)_* of `properOpenComparison Λ r.hom c.i d.i r.i_hom K`,
   followed by `(pfComp' r.hom d.g c.g r.hom_g).inv` at the extension of K.
   Read ProperOpenComparison's actual data: theta is open-restriction exchange,
   extension-zero base change, and clopen-component restriction; alpha is
   extension of theta inverse followed by the descended counit. Read
   `derivedPlusFormalism_pfComp'_inv`: this is precisely the canonical derived
   direct-image composition identification in the required direction.
   The left side is the existing refinement natural isomorphism's component.
   Thus componentwise equality for every K supplies naturality and invertibility
   of the specified pushed-forward maps. Verdict: exact, including non-Cartesian
   and non-dense refinements; no arbitrary replacement map is introduced.
7. Identities and composites of refinements: the recorded existing
   `rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id` is Iso.refl;
   `_comp` equates the comparison for r.comp s with the comparison for s followed
   by that for r. Read the surrounding section: only finite commutative
   coefficients and QuasiCompact f are required. Verdict: exact contravariance.
8. Common-refinement independence: `_PlusIso_eq_refinementIso` quantifies over
   arbitrary c,d,e and r:e→c, s:e→d, and equates the canonical c→d isomorphism
   with A_r followed by inverse A_s. `_PlusIso_refl` and `_PlusIso_trans` give
   identity and cocycle. Opened their signatures and the dense-refinement
   construction; no Cartesian restriction survives in the recorded arbitrary
   refinement theorem. Verdict: every clause present.
9. Canonical notation Rf_!: existing `rightDerivedLowerShriekPlus` is the candidate
   of `HasCompactification.compactification f`; the independent PlusIso family
   identifies any candidate with it. Verdict: uses the existing construction.
10. Composable f:X→Y and g:Y→S of Noetherian schemes: existing
    `rightDerivedLowerShriekPlusCompIso Λ f g` is a natural isomorphism from
    Rf_! followed by Rg_! to R(f followed by g)_!. Its instances require
    compactifications of f,g,fg and quasi-compactness of fg. Finite type supplies
    quasi-compactness, and Nagata over the Noetherian (hence qcqs) target
    supplies a compactification of fg. Opened NagataCompactification's hypotheses.
    These requirements do not add mathematical assumptions. Verdict: exact.
11. Independence of composition from compactifications: `_CompIso_hom_eq`
    quantifies over every `Compactification.Triangle f g` and computes the map
    by conjugating its model map with the three canonical PlusIso comparisons.
    This states choice independence, beyond mere Nonempty of an isomorphism.
    Verdict: exact; read the complete equation and its parameter instances.
12. Associativity for three morphisms: `_CompIso_assoc` equates the two whiskered
    composition maps, with the functor associator and equality transport for
    Category.assoc. All seven compactification instances exist by the same
    Noetherian-target Nagata argument, for both parenthesizations. Verdict: exact.

### Edge cases and conventions

Empty schemes and their finite empty affine covers are admitted by IsNoetherian;
no Nonempty scheme or density hypothesis appears. The zero coefficient ring and
zero complex are allowed. D+ means an arbitrary cohomological lower bound, not
nonnegative complexes; degree zero and shifts are included. There is no index
set restriction, no excluded residue characteristic, and no prime-to-characteristic
condition. Identity refinements and identity scheme maps are included. Universe u
is explicitly declared, schemes have universe u, and the coefficient category has
the established u+1 size convention; no extra universe equality was added.

The only new declaration is a named theorem with whole proof `sorry`; there is
no definition with postponed data. Its source/blueprint docstring contains the
five proof steps, including equalizing parallel refinements and the two pasting
arguments. The signature has no unbound variable, hidden let, local notation,
private definition, or new instance. The node's lean.statement agrees verbatim
with the multiline source signature. The mixed record deliberately records the
existing coherence/composition declarations as well as the new equation.

### Independent searches, findings and changes

- LeanFinder: "Proper refinements of compactifications induce coherent natural
  isomorphisms on bounded below etale module derived categories": eight hits
  about homotopy/localization and condensed modules, no exact match.
- Loogle: `"properOpenComparison"`: zero hits.
- LeanSearch: "Derived etale compact support is independent of compactification
  with coherent composition": service unavailable (Internal Server Error).
- Independently searched Mathlib, upstream WeilConjectures, and project lean/Sheaf
  for properOpenComparison, refinementComparison_eq, compact-support comparison,
  and compactification coherence. The existing upstream coherence, formalism,
  and composition family supplies the reused clauses. The project's
  ProperOpenComparison defines the specified alpha. No existing theorem equates
  that separately defined alpha with the arbitrary-refinement candidate iso.
  In particular the upstream formalism comparison equation concerns its own
  exchange comparison, so it does not eliminate the new normalization theorem.

No mathematical mismatch was found; no Lean or node change was made. The change
from this second reading is this independently checked report and search log.
The authorized scompile.py wrapper compiled the delivered module in sandbox and
library forms cleanly (3.3 and 3.6 seconds), without errors or warnings.
