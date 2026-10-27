## Worker report

The delivery states `CategoryTheory.RegularRoosKoszul.regular_roos_koszul_unit` in
`Sheaf.SixFunctors.RegularRoosKoszulUnit`. Its sole postponed theorem has proof `sorry`;
all helper definitions contain real data. No statement correction or dependency module is
needed. The H2 repair adds a definition node for two existing helper definitions. The current Q40 stage-1 split is retained verbatim: it supplies the
reviewed proof plan, rather than preventing this distinct stage-2 statement delivery.
The independent return at immutable head 0f6fb78e1f9f requests the H2 repair below.

Hypothesis and clause matching:

- The site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`. The explicit
  universes `c`, `v`, `r`, `w` implement def-weil-size-convention; the chosen module and
  coefficient universe `max c v r` contains the small site. Object and morphism universes
  are independent. Ring/module sheafification instances on the site and its slices are
  the usual available instances at this size, not mathematical restrictions on the site.
- `R : Sheaf J CommRingCat.{max c v r}` is exactly the commutative ring sheaf. The public
  abbreviations `ring` and `Modules` unfold to its underlying ring sheaf and the recorded
  `ringedSiteModules`, not copied module or derived structures.
- `t : (SheafOfModules.unit (ring R)).sections` is the global section, and
  `_hreg : Mono (globalSectionMultiplication R t)` is injectivity of multiplication on it.
- `P : DerivedCategory (Modules R)`, `Q : CochainComplex (Modules R) ℤ`,
  `e : DerivedCategory.Q.obj Q ≅ P` and `_hQ : IsKFlatIndependentCoefficients Q` express an
  arbitrary unbounded derived object and any K-flat representative of that same object.
  No termwise-flat or boundedness assumption is added.
- `principalQuotient`, `principalKoszul`, `reductionTensorTower`, `koszulTensorTower`,
  `koszulTensorTowerComparison` and `koszulStrictAugmentation` are the existing canonical
  positive-power quotient/Koszul constructions and their actual transitions. Index `n`
  means exponent `n+1`. Their tensor order (Koszul factor, then Q) is the dependency's
  canonical symmetric model of the source's tensor order.
- `koszulRlim R` is the already recorded total right derived strict limit, with universal
  comparison `limitComparison`. In particular it is not the underived product-cone
  construction, which would need exactness of products. `koszulCompletion` is the existing
  strict Koszul total limit and `quotientLimit` applies the same functor to the quotient
  tower.
- `constantUnit` localizes the ordinary constant/limit adjunction unit and follows the
  right-derived comparison. This is the representative formula for the specified derived
  constant-tower unit (with the exact-constant factorization), as characterized by the
  normalized adjunction in lem-coef-derived-tower-counit-projections. `augmentedUnit`
  follows it by the derived image of the actual strict augmentation. `koszulUnit` and
  `quotientUnit` precompose by `e.inv`. No arbitrary map or nonnormalized adjunction is
  supplied as a hypothesis. Choosing the total right-derived pair is allowed because its
  universal property determines it up to the uniquely normalized comparison.
- `cP : koszulCompletion R Q t ≅ quotientLimit R Q t` is an isomorphism in the derived
  category itself. `cP.hom = comparison R Q t` specifies that its actual forward map is
  the image of the strict quotient chain comparison. The next equality is precisely
  `c_P κ_P = comp_P` (Lean writes composition from left to right).
- The four entries of `List.TFAE` are, in order, precisely (i), (ii), (iii), (iv).
  Entry (i) quantifies `p` and `δ`, uses `IsDerivedLimitTriangle` for the actual quotient
  transition maps, and requires `p ≫ Pi.π _ n = e.inv ≫ Q.map (koszulRepresentativeQuotient
  R Q t n)` for every n. Thus it asserts an existential distinguished Roos triangle with
  the actual quotient components, not a chosen or unit-normalized comparison to its fibre.
- Entry (ii) quantifies over every object W and every compatible section f on the slice
  `Over W`. Evaluation at its terminal object `Over.mk (𝟙 W)` identifies these sections
  bijectively with `O(W)`. Membership in the principal ideal is expressed as existence of
  y whose image under actual multiplication by t equals that value of f. Because t is
  monic, its image ideal sheaf is isomorphic to O, so this is precisely `(t)O(W)`, including
  sheaf-image rather than merely presheaf-image membership. The vanishing is `IsZero` of
  the recorded `derivedInternalHomOfUniverses` from the actual sheafified sectionwise
  localization, concentrated in degree zero, to the actual derived slice restriction of P.
- Entries (iii) and (iv) are `IsIso` of the specifically constructed `koszulUnit` and
  `quotientUnit`. No existential substitute unit appears.
- Representative independence is the following universal clause over Q', e', and its
  K-flatness: there exist isomorphisms hV and hU carrying both actual units to those for
  Q' and commuting with the two quotient comparisons. Together with the TFAE for every
  representative, this makes all four conditions independent of the choice.
- Naturality is the final clause, for every map f of representative complexes. `tensorTowerMap`
  is actual whiskering of the existing tensor bifunctor, `koszulMap` and `quotientMap`
  apply total derived inverse limit to those maps, and the three equations state the
  comparison square and the naturalities of the two units. The construction thus descends
  naturally through representatives. The theorem imposes no exactness of products,
  Noetherian condition, finite-quotient condition, or bound. Its derived product instance
  is in the conclusion.

Dependencies used, after reading their full source signatures and docstrings:

- def-weil-size-convention is metatheoretic (its recorded convention has no declaration).
- Sheaf.CategoryTheory.SiteCoveringAxioms: `Precoverage.IsSiteForCoverings`, its retained
  Mathlib `GrothendieckTopology` and `Sheaf` presentation of the site/sheaf component.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `DerivedCategory.Q`.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients` and the canonical tensor instances.
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (the recorded availability
  of the chosen representative; imported publicly as a listed statement dependency).
- Mathlib.Algebra.Homology.BifunctorShift: `CochainComplex.mapBifunctor` and the actual
  total tensor bifunctor used by the strict tower constructors and their maps.
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients` supplies the actual total right
  derived limit and its comparison, K-injective computation, and derived products.
- Sheaf.CategoryTheory.DerivedTowerCounitProjections:
  `derived_tower_counit_projections`, fixing the normalized derived unit/counit and projections.
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit:
  `IsDerivedLimit` and its more precise recorded `IsDerivedLimitTriangle`.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  `derivedInternalHomOfUniverses`, on each slice with explicit universes.
- Sheaf.Paper.DerivedCompleteKoszulReconstruction:
  `koszulRlim`, `koszulCompletion` are statement data recorded by
  def-sf-koszul-total-derived-limit; `derivedComplete_koszul_reconstruction` is used only
  as a proof dependency.
- Sheaf.Paper.WeilCompletedTensorReflector publicly retains the general
  Sheaf.CategoryTheory.RingedKoszulCompletionReflector interface and its
  `ringedKoszulCompletionReflector`; the scheme-only `wfCompletionReflector` specialization
  is not substituted for that general theorem. This is a plain proof import.
- Sheaf.CategoryTheory.InjectiveTowerRoosShifts: `injectiveTowerRoosShifts`, a plain proof
  import fixing the actual product of limit projections, as required by reviewed Step 4.
- Added existing statement dependency def-pur-principal-koszul-quotient-towers:
  Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers, the actual constructions named above.
- Added existing statement dependency def-weil-pbc-ringed-derived-restriction:
  Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral, `ringedDerivedRestrictionGeneral`. The helper `restriction` only binds the existing
  derived-category instance across the two definitionally equal slice-ring presentations;
  its data is exactly that existing functor.
- Added existing statement dependency def-weil-pbc-ringed-section-localization:
  Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses,
  `ringedSectionLocalizationOfUniverses`. These are the published generalized interfaces.
- def-sf-koszul-total-derived-limit records the existing `koszulRlim` and
  `koszulCompletion` definitions used literally by the statement. The reconstruction
  theorem is retained in proof_deps and removed from the saved packet's stmt_deps.

Sources checked directly: literature/stacks-project/algebraization.tex,
lemma-derived-completion (Tag 099B) and lemma-derived-completion-koszul (Tag 0A0E).
The docstring follows all five current reviewed proof steps, including the corrected
Step 4 use of the normalized injective-tower Roos projections.

Edge cases checked mathematically before writing:

- If t is a unit, both derived limits vanish and the four conditions require P to vanish;
  the prescribed quotient first components and unit maps have exactly that behavior.
- For t=0, regularity forces the ring sheaf to be zero, hence its module category is zero.
  The statement does not exclude the zero ring or an empty site.
- P=0 is permitted, as are unbounded complexes and the first positive power n=0.
- For O=Z, t=p and P=Q, the quotient tower and Koszul completion vanish while P does not;
  all four completeness conditions are false. This tests against a vacuous unit condition.
- On sites with nonexact countable products, only products in the derived category occur;
  no termwise product or Roos cone is silently identified with the total limit.

Searches performed (all via the prescribed wrapper unless explicitly `rg`):

- LeanFinder: "On a small ringed site regular principal quotient Roos completeness is
  equivalent to the canonical Koszul completion unit being an isomorphism". Eight hits,
  led by `AdicCompletion.of_bijective_iff`, `isAdicComplete_iff`, BDeRhamPlus and solid
  condensed-module statements. Their types concern ordinary adic completion or solidification,
  not this general ringed-site derived-limit criterion; none is an exact match.
- Loogle: `"Koszul", "complete"`. No hits.
- Mathlib grep: `Koszul.*complet|complet.*Koszul|Roos|derived.*complet`. No hits.
- LeanSearch: "For a regular global ring-sheaf element, a quotient Roos distinguished
  triangle is equivalent to the canonical Koszul derived-completion unit being an
  isomorphism". Eight hits, including mapping-cone triangles,
  `DerivedCategory.mem_distTriang_iff`, `DerivedCategory.triangleOfSES`, and
  `SheafOfModules.unit`; none states the requested equivalence and normalization.
- `rg` in both lean/WeilConjectures and lean/Sheaf for the item ID, regular Roos/Koszul
  completion and canonical-unit patterns. The principal towers and generic reconstruction
  are reused. `RegularQuotientCompletionUnit.lean` was read in full: it assumes exact
  countable products, so its theorem is not this item's statement. The ringed reflector's
  general source was also read rather than using the recorded scheme specialization.
- `rg` for `RegularRoosKoszul|regular_roos_koszul_unit` in Mathlib, WeilConjectures, Sheaf
  and dag/lean_names_upstream.json returned no collision before the module was written.

No STATEMENT-DISPUTED issue remains. All modifications are in the assigned sandbox.

## New nodes

`def-sf-koszul-total-derived-limit` records, with `existing: true`,
`CategoryTheory.koszulRlim` and `CategoryTheory.koszulCompletion` in
`Sheaf.Paper.DerivedCompleteKoszulReconstruction`. Its source is Stacks Tags 0941
and 0A0E, read directly in sites-cohomology.tex and algebraization.tex. The first
is the chosen total right-derived strict inverse limit; the second applies it to
the localized degreewise strict principal Koszul tensor tower. Both use the exact
existing definitions, with no new module or duplicate construction. No regularity,
K-flatness, boundedness or exact-product assumption is needed to define either.
LeanSearch found the generic totalRightDerived API, sheaf limit instances and
ordinary AdicCompletion. LeanFinder found Tor and ordinary adic tensor completion;
neither gives these specialized definitions. Mathlib grep found only a generic
pointwise right-derived colimit lemma. Direct rg of WeilConjectures found no match;
Sheaf rg found the two exact definitions above and specialized scheme/constant
coefficient constructions. DAG searches found their listing under the reconstruction
theorem, but no separate definition node. blueprint_refs.py search returned no match;
its ancestor query returned fix-prop-coherence. Exact wrapper search results are
preserved in the new node's mathlib_searches.

## Repair self-check

H2 from independent immutable head 0f6fb78e1f9f is repaired: the item's stmt_deps
cites def-sf-koszul-total-derived-limit in place of
lem-pur-derived-complete-koszul-reconstruction, while proof_deps retains that theorem.
The genuine strict-tower theorem statement dependency remains: limitComparison uses
its choose_spec. The main Lean source and its theorem signature are unchanged.
The saved node differs from current shared main only in lean and stmt_deps; the
reviewed proof and mathematical statement remain verbatim. deliver2.py's initial
dry run of the retained packet passed at 856ff6005ba before this metadata repair.
The new definition node matches the two source definitions clause by clause:
site/ring/module category use ringedSiteModules; derived tower categories and Q use
DerivedCategory; strict towers use koszulTowerComplex and koszulTensorTower;
the total derived limit is Classical.choose of
ringedStrictTowerHomotopyLimitIndependentCoefficients; completion is its .obj on
DerivedCategory.Q.obj of that strict tower. The choice is normalized by its
right-derived comparison, rather than the reconstruction theorem's conclusion.
Zero rings, empty sites, arbitrary complexes, t=0, invertible t and first exponent
n+1=1 are admitted by both definitions. All other clauses retain the maintainer's
independent passing review supplied in the return. No independent worker was
started, as the dispatcher explicitly prohibits other agents.

Validation after repair: scompile.py compiled the sandbox and library module cleanly
(23.2 s and 29.9 s). The main theorem signature and the existing definition signature
match their Lean records verbatim. The item differs from current shared main only
in lean and added stmt_deps; no base statement dependency was removed.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
