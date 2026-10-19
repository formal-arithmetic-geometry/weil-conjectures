## Worker report

Final implementation after the second reading: the item is stated by
`AlgebraicGeometry.ProEtale.properOpenComparison_site_normalization` in
`Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`. Every theorem proof
is `sorry`; definitions and the coefficient finiteness instance have existing data.
There is no statement correction and there are no new DAG nodes.

The original worker supplied the comparison pullback presentation, the compatible
canonical mate, and a formerly unstated proper/open dependency. During the second
reading Q24's proper/open module landed. The duplicate dependency was removed and
the final item uses that landed module unchanged. The detailed independent reading
and exact changes are recorded below.

The final coefficient parameters are prime `l`, a finite-dimensional field extension
`E` of `Padic l`, and `n : Nat`; the ring is the recorded
`Padic.coefficientExtensionRing l E (n + 1)`. This parametrizes all positive levels.
The named instance `properOpenNormalizationCoefficientFinite` applies the existing
`Padic.finite_coefficientExtensionRing` theorem at `n + 1`; it supplies no extra
hypothesis. Schemes `X`, `T₁`, `T₂` have the node's `IsNoetherian` binders; `f` is
proper, `j₁`, `j₂` are open immersions, and `h : j₁ ≫ f = j₂`. The input is an
arbitrary bounded-below etale module complex. There is no characteristic,
constructibility, nonemptiness or nonzero-object restriction.

The final equation uses the following exact dependency declarations:

- `Padic.coefficientExtensionRing`, from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`, and its finite-ring theorem from
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- Mathlib's `IsNoetherian`, `IsProper`, and `IsOpenImmersion` from the recorded
  Noetherian, proper-morphism and open-immersion modules.
- `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat Λ))` and the
  corresponding `Sheaf (Scheme.ProEt.topology T)` presentation of the two sites.
- `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`, in the supplied
  `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`: the exact termwise lift
  of the existing `comparisonUpperStar`.
- `AlgebraicGeometry.ProEtale.properOpenSiteExtensionIso`, in the now-landed
  `Sheaf.Paper.ProEtaleProperOpenComparison`: the termwise lift of the canonical
  adjoint `openImmersionLowerShriekComparisonUpperStarIso` of
  `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`, in the supplied
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: exactly the existing
  right-derived base-change of the underived canonical mate. The supplied
  `fixedComparisonDirectImageMatePlus_counit` specifies the node's normalization,
  and `isIso_fixedComparisonDirectImageMatePlus` states qcqs invertibility.
- `AlgebraicGeometry.Etale.properOpenComparison`, in
  `Sheaf.AlgebraicGeometry.ProperOpenComparison`: the specified etale alpha.
- `(AlgebraicGeometry.ProEtale.properOpenProEtaleIsoPlus ...).hom`, in Q24's landed
  `Sheaf.Paper.ProEtaleProperOpenComparison`: the named pro-etale alpha. That module
  also states the required identity and composition laws and constructs its ambient
  unbounded presentation. It is imported without modification.

The equality reads e_j2 then alpha_p equals A_T2(alpha_e), then b at j1_et! L, then
Ru_proet(e_j1). Both sides have source A_T2(j2_et! L) and target
Ru_proet(j1_proet!(A_X L)) in bounded-below pro-etale derived modules on T2.

Initial searches used LeanFinder (canonical proper/open compatibility), Loogle
(`mapDerivedCategoryPlusNatIso` and `conjugateEquiv`), and Mathlib/project grep for
proper/open comparison and the canonical open mate; none provided the complete named
map equality. LeanSearch was unavailable (Internal Server Error). The second reader's
fresh queries and source inspections are recorded below and in `searches.jsonl`.
The empty scheme/open and zero complexes are allowed; `n = 0` means coefficient
level 1. Coefficients and module values have the established universe `u + 1` over
`Scheme.{u}`, without equating site object and morphism universes.

## Dependency modules

`def-sf-comparison-derived-pullback`: its recorded functor lands in module sheaves
over the continuous-function coefficient ring, whereas the item's recorded open
comparison and direct-image mate use the fixed-ring sheaf presentation.
`ComparisonDerivedPullbackFixed` publicly retains the old module and provides the
same exact termwise comparison as `siteComparisonDerivedPullbackPlus` in fixed-ring
module sheaves. This is section 1(B); there is no new inverse image or coefficient
identification. The old unbounded/intrinsic interfaces remain publicly available.

`lem-weil-pbc-comparison-direct-image-canonical-mate`: the recorded module reaches
`ComparisonPullbackCoherence` and the side framework's
`FiniteCoefficient.UpperLowerStar.Defs`. Its lower-star notation parser conflicts
with the upstream fixed-ring operations required by the etale arrow and canonical
open comparison (`environment already contains AlgebraicGeometry.ProEtale.term(_)_*[_]`).
The section 1(B) module `FixedComparisonDirectImageMate` imports the compatible
upstream operations. Its data is exactly the old
`rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange ...)`,
with the canonical termwise pullback comparison. Its two postponed theorems state
qcqs invertibility and the full counit-mate equation using the actual derived
adjunctions. This preserves the named map. The second reader expanded its proof
plan to all six DAG steps.

The originally supplied `lem-weil-pbc-proper-open-comparison-proetale` module and
node delta are no longer delivered: Q24's landed declaration is now used. Final
payload: three modules, the item node, two dependency node lean-field repairs, and
this report. There are three named sorry-only theorem proofs, no hollow definitions,
and no change to the item's mathematical statement or dependency edges.

## Second reading by Q18

I independently read the item and both supplied dependency nodes, the newly landed proper/open dependency, and all three
final sandbox modules, the declarations actually used from the shared library and upstream,
and the primary blueprint source at order 1484. The read-only literature copy is
`/home/ubuntu/work-bp/sheaf/literature/`: I opened the complete proper/open pro-etale
blueprint node, Stacks `proetale.tex` section-comparison (099R),
lemma-relative-comparison, and lemma-jshriek-comparison (09AF), and
`more-etale.tex` lemma-shriek-proper-and-open and its composition lemma. The blueprint
constructs the pro-etale arrow by transporting the specified etale arrow; 09AF fixes
the open comparison by the identity on restriction functors. There is no ambient
characteristic restriction in these sources. This is a statement reading; the three
postponed theorem proofs remain `sorry`.

The object's/hypothesis's/conclusion's checklist, with its Lean rendering and verdict:

1. Prime ell, finite field extension E/Q_ell, a uniformizer, and a positive level:
   `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`, and `Padic.coefficientExtensionRing l E (n + 1)`.
   PASS. I read `CoefficientExtension` and `CoefficientExtensionFinite`: this is the
   recorded quotient of the recorded integer ring by the power of the ideal generated
   by its recorded uniformizer. The underlying ideal is the power of the maximal
   ideal, independent of the choice of generating uniformizer. No new coefficient
   object is introduced. `n : Nat` parametrizes exactly the positive levels: level 1
   occurs at `n = 0`. The finite instance applies the existing finiteness theorem at
   `n + 1`, without adding a finiteness hypothesis.
2. Three Noetherian schemes: `{T₁ T₂ X : Scheme.{u}}` and the three
   `[IsNoetherian ...]` binders. PASS. I checked Mathlib's class extends precisely
   `IsLocallyNoetherian` and `CompactSpace`; it is the node's meaning of Noetherian.
3. A proper map T1 -> T2: `(f : T₁ ⟶ T₂) [IsProper f]`. PASS; this is the
   recorded Mathlib morphism property, not a separated or finite-type substitute.
4. Open immersions with common source and their equation: `j₁`, `j₂`, both
   `[IsOpenImmersion ...]`, and `h : j₁ ≫ f = j₂`. PASS; Lean's composition order
   expresses precisely u composed with j1 equals j2. No cartesian, dense-open,
   connectedness, base-field or constructibility hypothesis has been inserted.
5. Constant-coefficient module sheaves on the two small sites and bounded-below L:
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} ...)` and `DerivedCategory.Plus`.
   PASS. The comparison's target uses `Sheaf (Scheme.ProEt.topology T) ...`.
   I opened `DerivedCategories`, the fixed-ring upstream operations, and the finite
   coefficient module realization. This is the constant-ring presentation used in
   the node's specified open and direct-image interfaces, with arbitrary module
   sheaves, not only finite or locally constant sheaves.
6. A_T, the exact derived comparison: `siteComparisonDerivedPullbackPlus T Λ`.
   PASS after reading its actual definition: it is exactly
   `(comparisonUpperStar (ModuleCat Λ) T).mapDerivedCategoryPlus`. It uses the
   inclusion of the etale site in the pro-etale site and the existing exact descent,
   not a chosen functor or an arbitrary coefficient identification.
7. The specified e_j: `(properOpenSiteExtensionIso Λ j).hom.app L`. PASS.
   I opened upstream `openImmersionLowerShriekComparisonUpperStarIso`: it is the
   conjugate of the identity between the two restriction composites. The helper
   applies that isomorphism termwise with the exact-derived composition isomorphisms.
   Its direction is A_T j_et! -> j_proet! A_X as required by 09AF and the node.
8. The specified b_u: `(fixedComparisonDirectImageMatePlus Λ f).app ...`. PASS.
   Its real data is `rightDerivedFunctorPlusBaseChange` of the existing underived
   mate `lowerStarComparisonUpperStarBaseChange`, not the upstream comparison
   selected from `Nonempty`. The supplied counit theorem uses the actual two
   derived adjunctions and precisely states a, p(b), then epsilon_p equals
   A_U(epsilon_e). By the adjunction bijection this uniquely characterizes the
   transpose of a inverse followed by A_U(epsilon_e), exactly the node's q.
9. The specified etale alpha: `Etale.properOpenComparison Λ f j₁ j₂ h L`. PASS.
   I opened its declaration: it applies j2! to the inverse of the named theta and
   follows with the descended extension/restriction counit. No endpoint isomorphism
   has been substituted for that arrow.
10. The canonical pro-etale alpha: `(properOpenProEtaleIsoPlus Λ f j₁ j₂ h L).hom`.
    PASS. Its body is the inverse e_j2, A_T2(alpha_et), b_u at j1_et! L, and
    Ru_proet(e_j1), in that order, as the blueprint's first and last paragraphs
    prescribe. Every piece has actual data. The dependency constructs an actual `Iso`
    from those specified factors,
    so its hom is precisely the canonical arrow.
11. The sole conclusion: `e_j2.hom.app L ≫ (properOpenProEtaleIsoPlus ...).hom =`
    `A_T2.map (Etale.properOpenComparison ...) ≫ b_u.app (j1_et! L) ≫`
    `Ru_proet.map (e_j1.hom.app L)`. PASS. Both sides start at A_T2(j2_et! L)
    and end at Ru_proet(j1_proet!(A_X L)) in the same `DerivedCategory.Plus`
    on T2. Lean reverses the written functional composition order correctly.
    There is no extra existential, weaker endpoint assertion or added clause.

Dependency-module reading (no new definition nodes are present):

- `ComparisonDerivedPullbackFixed`: PASS against
  `def-sf-comparison-derived-pullback`. Its fixed-ring bounded-below interface has
  the same termwise construction as the node. It publicly retains the old module
  and therefore its unbounded derived comparison and intrinsic coefficient
  realization, rather than deleting the original interface. The general ring
  construction specializes to every finite discrete coefficient in the node.
- `FixedComparisonDirectImageMate`: PASS against
  `lem-weil-pbc-comparison-direct-image-canonical-mate`, including naturality,
  finite commutative coefficients, qcqs maps, named invertibility and the explicit
  counit identity. I compared the old module and `ComparisonPullbackCoherence`:
  the latter reaches `FiniteCoefficient.UpperLowerStar.Defs`, whose lower-star
  syntax conflicts with the compatible upstream fixed-ring operations used here.
  The repair retains exactly the old mate's data under a usable import boundary
  and adds the node's explicit counit statement. The pullback comparison is the
  inverse of the canonical upstream `comparisonUpperStarCompUpperStarIso`, with
  exact-derived composition identifications; its orientation agrees with a_u.
- Newly landed dependency `Sheaf.Paper.ProEtaleProperOpenComparison`: PASS against
  the existing blueprint node, including every clause. During the dry run this
  dependency acquired Q24's reviewed Lean record. I opened the actual complete
  module and found that `properOpenSiteExtensionIso` and `properOpenProEtaleIsoPlus`
  construct precisely the open comparison and transported arrow this item needs.
  I removed our duplicate `ProperOpenComparisonProEtale.lean` and its dependency
  node copy, and replaced the item's references with these landed declarations.
  Its arrow is defined for every finite commutative coefficient ring; the
  composition and identity laws assume the Noetherian ambient schemes of the
  source. `_comp` compares alpha_(r then s) with alpha_s followed by Rs_*(alpha_r)
  and the iterated-to-composite direct-image identification. `_id` follows the
  arrow by the canonical R(id)_* identification and asserts the identity. The
  unbounded presentation is also present. No dependency record is overwritten.

Edge cases: empty schemes and empty opens are allowed (there is no nonemptiness
binder); arbitrary zero complexes and arbitrary integer lower bounds are allowed;
level 1 is present; coefficient level zero is outside the positive-level item;
no condition that ell is invertible on a scheme occurs. Generic fixed-coefficient
helpers also accept the zero ring. There is no index family to restrict. Scheme
universes are the existing `Scheme.{u}` universes, with coefficient/module universe
`u + 1` as in the recorded sites and operations; no equality of site object and
morphism universes is imposed. The finite extension is in that coefficient universe,
and no separate universe below the schemes is quantified over as a test category.

Independent duplicate searches, using different wording from the first reader:

- `msearch.py leanfinder`: "inverse image from etale to pro etale conjugates the
  proper open comparison by extension by zero and derived direct image comparisons";
  eight hits (scheme-module restriction compositions, standard etale and condensed
  functors), none for the named derived proper/open equality.
- `msearch.py loogle`: `"rightDerivedFunctorPlusBaseChange"`; zero indexed Mathlib hits.
- `msearch.py grep`: `jshriek.*comparison|comparison.*jshriek|proper.*open.*comparison|open.*proper.*comparison`;
  zero Mathlib hits. These are actual new entries in `searches.jsonl`.
- Independent `rg` over upstream `WeilConjectures`, shared `lean/WeilConjectures`,
  shared `lean/Sheaf`, and `dag/lean_names_upstream.json` found the existing etale
  alpha, its composition/identity laws, and the previously recorded comparison
  constructions, which I opened. No existing declaration gives the item's
  pro-etale named-map equality. The upstream compact-support comparison explicitly
  chooses a direct-image isomorphism from `Nonempty`; it cannot replace the
  counit-normalized arrow required here. The final sandbox module declaration names
  do not collide with those search results.

Mismatches and changes: I found no mathematical statement mismatch in the item or
its supplied dependencies, and preserved the mathematical statement. The late-arriving
Q24 dependency was
reused as described above, removing a duplicate module and node delta. The existing
positive-level finiteness instance was moved to the item, renamed and documented
with its owning blueprint. The item now names the landed isomorphism's hom and open
comparison. This is definitionally the same four-factor arrow and e_j. The
canonical-mate invertibility docstring condensed the node's six proof steps too
far for H8: I expanded it to include affine restriction, the fixed-stage continuity
hypotheses, injective computations, and verification of the named map on sections.
I also removed one stray leading space in the item's docstring. The second reading
adds this independent clause-by-clause report and fresh searches.
The item has no `statement_change`, and none is necessary. Every declaration has
its owning source/blueprint docstring; each postponed theorem has its own proof
plan. Definitions contain constructed data, and all theorem proofs are `sorry`.

Final validation after reusing Q24's landed dependency: the prescribed `scompile.py`
compiled all three delivered modules separately, including their sandbox/library
checks and the landed dependency overlay, and exited 0 with no warnings or errors.
The node signatures match their files verbatim; all Lean lines are at most 100
characters. Only the item's `lean` and the two dependency nodes' `lean` fields are
changed. The final dry run and delivery are performed after this report update.
