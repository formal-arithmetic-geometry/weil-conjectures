## Worker report

The module `Sheaf.Paper.DerivedLocalClassEdgeComparison` states
`AlgebraicGeometry.ProEtale.derivedLocalClassEdgeComparison`. Its only theorem proof
is `sorry`. Its fourteen other declarations contain real constructions (including
two Prop-valued law predicates), with no arbitrary choice of edge, comparison map,
or comparison isomorphism. The node changes only in `lean`; no statement correction,
new DAG node, or dependency-node repair is needed.

Source checked directly: `literature/stacks-project/sites-cohomology.tex`,
`lemma-sheafification-cohomology` (0BKV), lines 4348ff, including its injective
cycle/kernel/image proof; and `lemma-unbounded-describe-higher-direct-images`
(0D6I), lines 4434ff. The specified comparison was read in
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`: it is precisely
`boundedBelowComparisonGlobalSections`, constructed using the derived unit and
canonical Leray identification. The theorem docstring records all eight proof
steps of the node, including the representative computation of this very unit.

### Hypothesis and clause correspondence

* The fixed finite datum is the binder `P : WeilConjectures.PurityFiniteSetting.{u}`.
  Its `Coefficient` is the established universe lift of its quotient ring
  `Ring = O_E/(varpi_E^n)`. The field, distinct primes, finite extension, and positive
  level are its existing data. No coefficient ring is supplied as arbitrary new data.
* The arbitrary scheme is `(T : Scheme.{u})`. There is no finite-type, smoothness,
  nonempty, or scheme-over-k restriction added to T.
* The two choices of site are the first two conjuncts of the theorem:
  `DerivedLocalClassEdgeLaws T.smallEtaleTopology P.Coefficient` and
  `DerivedLocalClassEdgeLaws (Scheme.ProEt.topology T) P.Coefficient`.
  Thus both etale and pro-etale are included. These use ordinary
  `Sheaf J (ModuleCat.{u+1} P.Coefficient)` and its ordinary `DerivedCategory`.
  These are fixed-ring module sheaves, canonically equivalent to modules over the
  coefficient ring sheaves in the dependencies, not completed or constructible
  categories. The recorded pro-etale module realization supplies this equivalence.
* Every V (and V' for naturality) ranges over
  `DerivedCategory.Plus (Sheaf J (ModuleCat ...))`. This is cohomological boundedness
  below, not a condition of termwise boundedness on an arbitrary representative.
  Every r ranges over `ℤ`, without a nonnegative-degree restriction.
* The presheaf W ↦ H^r(W,V) is `derivedLocalCohomologyPresheaf J Λ V r`:
  derive the underlying-presheaf functor and take presheaf cohomology.
  `localClassObjectCohomologyIso` is the actual canonical isomorphism at every
  W with cohomology of right-derived literal evaluation. It is constructed from
  `rightDerivedFunctorCompMapDerivedCategoryIso` for exact evaluation and
  `mapDerivedCategoryHomologyFunctorIso`. Thus this is genuinely the specified
  derived-section presheaf, including its restriction maps.
* The canonical cohomology sheaf is always `DerivedCategory.homologyFunctor`.
  `derivedLocalClassSheafification` is the map from the associated sheaf of that
  presheaf to the cohomology sheaf, constructed using the exact-sheafification
  cohomology iso and the derived sheafification counit. The first conjunct inside
  `DerivedLocalClassEdgeLaws` states `IsIso` of this specified map for every V,r.
* The actual local-class presheaf arrow is
  `derivedLocalClassPresheafMap = toSheafify ≫ derivedLocalClassSheafification.hom`.
  The global arrow is `derivedGlobalLocalClassEdge`: transpose cohomology of the
  derived constant-sheaf counit across the ordinary constant-sheaf/sections
  adjunction. These definitions fix their normalization. On an injective model,
  the derived counits are the ordinary counits, so they send a cycle to its
  cohomology-sheaf quotient class, exactly as 0BKV does.
* The second conjunct inside `DerivedLocalClassEdgeLaws` identifies the global
  arrow with the component of that presheaf map at every terminal object W.
  `localClassTerminalCohomologyIso` is the canonical identification of the source
  with the presheaf evaluated there; `Sheaf.ΓNatIsoSheafSections` identifies the
  target with sections there. This expresses precisely the final-object definition
  of e_V^r, without silently identifying independently implemented section functors.
* The third conjunct inside `DerivedLocalClassEdgeLaws` is
  `H^r(RΓ(f)) ≫ e_V' = e_V ≫ Γ(H^r(f))` for every `f : V ⟶ V'`.
  The full subcategory's morphisms are all ambient derived morphisms; no chain-map
  representative, injectivity, or quasi-isomorphism hypothesis is imposed on f.
* The fourth conjunct inside `DerivedLocalClassEdgeLaws` is the shift equation:
  `e_(V[1])^r ≫ Γ(shift_H) = shift_RΓ ≫ e_V^(r+1)`.
  `localClassCohomologyShift` uses the canonical derived-functor `commShiftIso 1`
  and the actual cochain homology shift iso with `1+r=r+1`, not an arbitrary iso.
* The third main conjunct is `DerivedLocalClassSiteLaws P T`. Its first conjunct
  quantifies over every etale D+ object V and integer r. It states both
  `IsIso (localClassSiteComparison P T V r)` and the required square
  `c_V^r ≫ e_(nu*V)^r = e_V^r ≫ localClassSectionPullback P T V r`.
  Equality of these module morphisms is exactly the displayed equality for every x.
* `localClassSiteComparison` is explicitly homology of
  `(boundedBelowComparisonGlobalSections T P.Coefficient).app V`.
  It therefore retains the comparison unit specified by the node and its dependency;
  it is not a newly chosen iso between the groups.
* `localClassSectionPullback` is Γ applied to the ordinary module comparison unit,
  followed by `comparisonLowerStarCompGlobalSectionsIso`, followed by Γ applied to
  `comparisonUpperStar.mapDerivedCategoryHomologyFunctorIso r`. Its last factor
  is exactly H^r(nu*V) = nu*H^r(V) in the orientation used in the square.
  The fixed-ring ModuleCat comparison retains the same constant coefficients and
  their scalar actions, so this is section pullback with the required coefficient
  identification.
* The second conjunct inside `DerivedLocalClassSiteLaws` is naturality of c for
  every derived `f : V ⟶ V'`. The third is its cochain-shift equation using
  `localClassPlusCohomologyShift`. This helper includes the genuine shift iso for
  the full-subcategory inclusion `DerivedCategory.Plus.ι`; it does not assume that
  the chosen D+ shift and ambient shift coincide definitionally. Naturality and
  shift laws for the two edges and c make the already asserted comparison square
  compatible with both operations. No concentration, constructibility, finite Tor
  amplitude, or edge-map invertibility is assumed.

### Dependencies actually used

* `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.Coefficient`, and
  `.coefficientCommRing` (full structures and docstrings read).
* `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its fixed-ring
  `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding, together with Mathlib
  `DerivedCategory`, `DerivedCategory.Plus`, and `homologyFunctor`.
* `def-weil-pbc-proetale-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `FiniteCoefficientModules`,
  `finiteCoefficientRingSheaf`, `finiteCoefficientRealization` and its recorded
  equivalence; the fixed-ring sheaf encoding is the source of that realization.
* `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`, and the underlying
  `ProEtale.comparisonUpperStar`, `.comparisonLowerStar`, `.comparisonAdjunction`
  in `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
* `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` (and its category of morphisms).
* `def-weil-derived-cohomology-sheaves`: the node's usable **mathlib_match**,
  `DerivedCategory.homologyFunctor`, with `homologyFunctorFactors` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. Its current `lean`
  record names `sfModelCohomology`, an unrelated common-stage realization; this
  delivery uses the already recorded exact generic Mathlib match instead. There
  is no missing notion and no duplicate cohomology-sheaf definition.
* `sk-prop-sf-comparison`:
  `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`,
  `ProEtale.boundedBelowComparisonGlobalSections` and `.boundedBelowComparison`.
  The full definition of the former and signature/docstring of the latter were read.

The module also imports the stated proof plan: the ringed-site Grothendieck
abelian node, the compatible slice-section model, K-injective derived Hom,
and right-adjoint injective preservation. The bounded-below comparison module
already publicly imports the exact-functor, derived-adjunction, injective-resolution,
right-derived-plus, and Leray modules for the other proof dependencies. Exact
sheafification, objectwise presheaf homology, and enough injectives are Mathlib inputs.

### Universes and edge cases

The actual site object universe remains u+1 and its morphism universe u, while
coefficients and module elements live in u+1. The presheaf derived category uses the
standard localization in u+2 (`localClassPresheavesHasDerivedCategory`); this is
technical localization data, has no sorry, and imposes no equality of site universes.
Every universe and variable is explicitly bound. There is no local notation,
private definition, or file-local instance hiding in the statement.

Checked mathematically before writing: V=0; the empty scheme; an ordinary sheaf F
in degree zero (e^0 is the sections identity under the canonical isos, e^r for
r>0 has zero target); positive and negative shifts of F, including r=-1; and a
complex with several nonzero cohomology sheaves. The equations require neither
injectivity nor surjectivity of an edge. All derived morphisms, including zero,
identity and arbitrary noninvertible morphisms, occur. No counterexample or
statement dispute was found.

### Searches

* `msearch.py ... leanfinder`, query:
  "For a bounded below complex of sheaves of modules the sheafification of derived
  section cohomology is the cohomology sheaf naturally in morphisms and shifts".
  Results: `Sheaf.cohomologyPresheaf`, `.H`, `.cohomologyPresheafFunctor`, ordinary
  sheaf abelian/Grothendieck instances, and a HomComplex shifted-Hom lemma. None
  states the integer-degree derived local-class edge or the comparison square.
* `msearch.py ... loogle`, query `"homologyComparison"`.
  Results: twelve `ShortComplex.leftRightHomologyComparison` and associated data
  lemmas. These compare left/right homology, not the required edge map.
* `msearch.py ... grep`, query `homologyComparison|homology.*comparison` in
  `Algebra/Homology/ShortComplex`. Results: eleven left/right-homology comparison
  references; no local-class edge.
* `msearch.py ... leansearch`, query:
  "The sheafification of hypercohomology is the cohomology sheaf and the local
  class map commutes with derived morphisms and shifts".
  Results: `plusPlusSheaf`, `plusPlusAdjunction`, module sheafification,
  `sheafifyLift`, `sheafifyComposeIso`, `isColimitSheafifyCocone`, and
  `GrothendieckTopology.toSheafify`; none states this derived comparison theorem.
* `rg` on Mathlib's homology APIs found the canonical exact-functor cohomology
  isomorphisms; project searches found
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`,
  `Functor.rightDerivedFunctorCompMapDerivedCategoryIso`, and the prescribed
  bounded-below site comparison. These are used, not copied.
* `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `localClass`, local-class edges,
  sheafification/homology, and the item id found no existing declaration of this
  statement. The topological ringed-space variants and ordinary-sheaf presheaf
  results do not cover arbitrary derived module sheaves on these two small sites.
  A final exact-name search for the new principal helper names also found no clash.

Validation: the complete theorem and all definitions compiled cleanly with
`scompile.py` in sandbox and library-module modes (28.8 s and 25.5 s respectively)
before the final explicit proof-plan imports. The final compile and delivery
preflight are recorded below after they run.

## Second reading by Q58

Worker self-audit against the open node and full source file; the dispatch brief
assigns the independent review to the maintainer and explicitly forbids starting
other agents. The mapping above was checked against every sentence and display of
the unchanged node. The draft's shift comparison initially omitted the canonical
D+ inclusion shift iso; it was repaired with `localClassPlusCohomologyShift`.
The presheaf was also given an explicit `localClassObjectCohomologyIso` so that its
values are visibly the specified derived sections at every site object. The site
comparison remains the homology of the existing derived-unit comparison throughout.
No hypothesis, degree case, or clause was dropped. No new nodes or dependency
modules are included.

Final explicit proof-plan-import compile: clean sandbox compile (8.2 s) and clean
library-module compile (9.8 s), through the prescribed `scompile.py` wrapper, with
no warnings or errors. One sorry remains, on the item theorem only. JSON comparison
against the read-only node confirms that only its `lean` field changes; all Lean
lines satisfy the 100-character limit.

Delivery dry run: `deliver2.py Q58 lem-pur-derived-local-class-edge-comparison
--no-push` printed `OK (dry run): commit 985eba2980d passes the preflight and
compiles; nothing pushed`.
