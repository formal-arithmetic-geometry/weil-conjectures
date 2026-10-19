## Worker report

Item: lem-weil-pbc-comparison-pullback. The original natural statement, dependencies,
and proof are unchanged. The delivery supplies
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`, main declaration
`AlgebraicGeometry.ProEtale.comparison_pullback_coherent`.
There is one postponed theorem, with the node's four-step natural-language proof
in its docstring. Every definition has actual data; no additional theorem is postponed.

### Hypotheses and clauses

- Schemes and arbitrary scheme morphisms: the definitions and each coherence clause
  quantify over `Scheme.{u}` and `f : X ⟶ Y`, with no geometric property assumed.
  In the composition clause, `f : X ⟶ Y` and `g : Y ⟶ Z` are both arbitrary.
- The displayed natural isomorphism is the actual definition
  `comparisonCoefficientPullbackIso D f`:
  `etaleComparisonPullback D f ⋙ comparisonCoefficientPullback D X ≅
  comparisonCoefficientPullback D Y ⋙ proEtaleComparisonPullback D f`.
  Lean functor composition reads left to right, giving exactly
  `ν_X^* f_Et^{-1} ≅ f_Proet^{-1} ν_Y^*` in the node's convention.
  A natural isomorphism includes naturality, an inverse and both inverse laws.
- The comparison is normalized, not an arbitrary isomorphism: its definition applies
  `conjugateIsoEquiv` to the two composite adjunctions and to the existing
  `lowerStarCompComparisonLowerStarIso f D`. This restriction comparison evaluates
  at an etale `W/Y` on the same sections over `W ×[Y] X`, including restriction maps.
  Conjugation gives the node's unit/Hom-bijection normalization.
- Identity maps: the first conjunct of `ComparisonPullbackCoherent D` equates the
  component of the comparison at `𝟙 X` followed by `proEtaleComparisonId` with
  comparison pullback applied to `etaleComparisonId`. This is the identity equation
  after the canonical inverse-image identity identifications, for every sheaf `F`.
- Composites: the second conjunct equates the path through `c_f`, pullback of `c_g`,
  and the etale composition comparison with `c_(f ≫ g)` followed by the pro-etale
  composition comparison. The comparison isomorphisms are the conjugates of the
  existing `MorphismProperty.Over.pullbackComp` associativity maps.
- Chosen cartesian identification: the third conjunct quantifies over
  `sq : ChosenCartesianSquare g' f' f g`, retaining `isoPullback`, `hom_fst`,
  `hom_snd` and `sq.w`. It equates exactly the two paths in proof step 4.
  `etaleComparisonSquare` and `proEtaleComparisonSquare` are the specified
  `k_(f',g)^{-1}`, equality transport by `sq.w.symm`, `k_(g',f)` composites.
  This is the formula of `Etale.squareUpperStarIso`; with abelian coefficients,
  the same adjunctions and the same pullback-composition maps are used. An alpha
  preserving both projections is unique, so the formula does not need to inspect
  the representation of `sq.isoPullback` beyond the supplied square equality.
- Coefficients: the main theorem asserts the conjunction of this entire proposition
  for `Type (u + 1)`, `AddCommGrpCat.{u + 1}`, and every
  `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]` with `ModuleCat.{u + 1} Λ`.
  This retains all three coefficient settings in the source/proof, including
  noncommutative finite rings. The auxiliary coefficient-category assumptions
  (colimits and sheafification) are discharged in the theorem, not hypotheses on it.

### Dependency declarations and interface choices

All four statement-dependency records and their source declarations/docstrings were read.

- `def-weil-pbc-cartesian-square`: module
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, declaration
  `AlgebraicGeometry.ChosenCartesianSquare`, directly imported and quantified over.
- `def-weil-pbc-inverse-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declarations
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction`.
  The set-capable `etaleComparisonPullback` and `etaleComparisonAdjunction` are
  abbreviations for the identical existing Kan-extension/sheafification construction.
  The new interface is necessary because the recorded `upperStar` adjunction requires
  abelian coefficients and cannot be instantiated with sets. No site is duplicated.
- `def-weil-pbc-site-comparison-morphism`: module
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, declarations
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`,
  `preservesFiniteLimits_proEtaleSiteComparison`, `proEtaleSiteComparisonModules`.
  Directly imported. `comparisonCoefficientAdjunction` is the same constructed
  adjunction for sets and the same `ProEtale.comparisonAdjunction` for modules/Ab.
- `def-weil-proetale-inverse-image`: recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`, declarations
  `AlgebraicGeometry.Scheme.proEtaleRingModelUnit`, `proEtaleRingModuleInverseImage`,
  and its imported `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` were read.
  For the coefficients of this theorem, its `proEtaleSheafInverseImage` and
  `proEtaleSheafAdjunction` are exactly the same Kan-extension construction used here.
  Importing the ring module together with `Comparison.LowerStar` fails because
  the two `UpperLowerStar.Defs` reorganizations both declare the same constants.
  Following the explicit duplicate-import repair instruction, this module imports
  only the upstream `Comparison.LowerStar` side, which supplies the same base-change
  inverse-image and adjunction construction transitively. There is no new ring inverse
  image, coefficient transport or site model in this delivery.

Proof interfaces are reached by the imports: `Etale.isContinuous_overPullback`,
`ProEt.isContinuous_overPullback`, `Scheme.toProEt`, `Adjunction.comp`,
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
`Functor.sheafPushforwardContinuousId'`, `sheafPushforwardContinuousComp'`,
`MorphismProperty.Over.pullbackId`, `pullbackComp`, `conjugateIsoEquiv`,
`unit_conjugateEquiv_symm`, and the existing direct-image functors. The square module
imports the project's specified inverse-image square interface. No proof-dependency
import is omitted except the conflicting reorganized pro-etale ring-module import
explained above; its relevant canonical construction is already available upstream.

The auxiliary declarations all belong to this node's single comparison notion and are
listed in `lean.declarations`. They extend the existing constructed interfaces to sets,
rather than introducing a new independent notion or an arbitrary map. In particular
no general coefficient-category coherence theorem, stronger than the node, is asserted.

### Searches and source reading

- Read the full blueprint source
  `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-comparison-pullback.md`,
  the DAG's updated four-step proof, and the dependency modules. Read the published
  etale `Defs` through `scompile.py --source` to check the current composition interface.
- `msearch.py ... leanfinder "The inverse image from the etale to the proetale site
  commutes with scheme pullback compatibly with identities composition and cartesian
  squares"`: eight hits for scheme modules, over-sites and existence of site pullbacks;
  none is this full statement.
- `msearch.py ... loogle '"conjugateIsoEquiv"'`: found `conjugateIsoEquiv` and its
  hom/inverse formulas in `Mathlib.CategoryTheory.Adjunction.Mates`; used here.
- `msearch.py ... grep 'sheafPullback.*(Comp|Id)|sheafPushforward.*(Comp|Id)'
  CategoryTheory/Sites`: found the existing continuous pushforward identity and
  composition comparisons in `Sites/Continuous.lean`; used here.
- `msearch.py ... leansearch "Inverse image comparison from etale to proetale
  sheaves commutes with pullback and is coherent under composition"`: service
  unavailable (Internal Server Error); no search verdict inferred from this failure.
- `rg` on both project source roots and `lean/Sheaf` for comparison/pullback names,
  and for the node id upstream, found
  `ProEtale.comparisonUpperStarCompUpperStarIso` in `Comparison/LowerStarAcyclic.lean`
  and the derived comparison in `BaseChange/SmoothBaseChange.lean`.
  Read their signatures/docstrings and construction: the former supplies the inverse
  of the displayed isomorphism only for Grothendieck abelian coefficients, with no
  identity/composition/square equations; the latter is derived and not this statement.
- Read `Comparison/LowerStar.lean` in full through the comparison construction:
  its `toProEtCompOverPullbackIso` and `lowerStarCompComparisonLowerStarIso` give the
  exact canonical input, already general in the coefficient category for restriction.
- `rg` of every new helper/main declaration name across Mathlib, upstream
  `WeilConjectures` and `lean/Sheaf`: no collision.

### Edge cases and validation

Checked identity arrows explicitly, arbitrary pairs including identity factors,
empty schemes/sites, zero abelian sheaves, the zero ring and arbitrary finite rings,
and arbitrary chosen Cartesian presentations. No nonempty, nonzero, separated,
qcqs, characteristic, or etale-morphism hypothesis is added. There is no index-set
restriction. The site object universe remains `u + 1` and its morphism universe `u`;
coefficients have Hom universe `u + 1`, so sets and all recorded sheaf interfaces fit
without an equality between site universes. The independent object universe `v`
of the helper coefficient category is explicitly bound. All universes and variables
are explicit, and there are no local notations or private declarations.

`scompile.py NE lem-weil-pbc-comparison-pullback <module>` compiled the final module
successfully both as a sandbox file (3.7 seconds) and with its intended library name
(3.8 seconds), without errors or warnings. The earlier duplicate import was repaired
by choosing the upstream side; the continuity inference issue was repaired by giving
the existing etale continuity instance its explicit topology type and the constructed
adjunction its explicit return type. No source tree or live Lean file was edited.

## Second reading by NE

I independently read the node and its four proof steps, the blueprint source at
`sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-comparison-pullback.md`,
Stacks `proetale.tex` at `lemma-morphism-big-small` (especially (2)) and the
comparison inclusion preceding `lemma-describe-pullback-from-etale`. The former
allows an arbitrary scheme morphism in a sufficiently large big site; the latter
uses suitably compatible choices of sites. Neither adds properness, qcqs,
Noetherianity, characteristic or nonemptiness assumptions. The existing small
sites and the common larger coefficient universe implement those choices.

Object/hypothesis/conclusion checklist, matched against the Lean:

1. Schemes U,V and arbitrary u:U→V: `{X Y : Scheme.{u}} (f : X ⟶ Y)`
   in `comparisonCoefficientPullbackIso`. Verdict: exact, with no geometric
   typeclass on f. The coherence proposition universally quantifies schemes
   and arrows, rather than fixing one arrow before asserting coherence.
2. Etale and pro-etale inverse images: `etaleComparisonPullback D f` and
   `proEtaleComparisonPullback D f` use `MorphismProperty.Over.pullback`
   for `Etale` and `WeaklyEtale` and the existing topologies. I opened the
   recorded etale `upperStar`/adjunction and the pro-etale dependency modules
   `ProEtaleInverseImage` and `ProEtaleRingInverseImage`: the underlying
   Kan-extension/sheafification expressions agree. Verdict: the actual
   inverse images, not arbitrary adjoints or maps. The ringed extension-of-
   scalars interface is not needed for fixed ModuleCat coefficients here.
3. Comparison morphism ν: `comparisonCoefficientPullback D X` uses
   `Scheme.toProEt X`. I read `proEtaleSiteComparison`, its left-exactness
   statement, `proEtaleSiteComparisonModules`, and upstream
   `comparisonUpperStar`/`comparisonAdjunction`. The constructed expressions
   agree, and sets, Ab and finite fixed-ring modules are retained. Verdict:
   exact coefficient and site objects; no condensed coefficients substituted.
4. Natural isomorphism ν_U^* u_Et^{-1} ≅ u_Proet^{-1} ν_V^*:
   `comparisonCoefficientPullbackIso` has exactly these composite functors
   (Lean composition reads left to right). Its data is conjugation of
   `lowerStarCompComparisonLowerStarIso`, not a postponed existence choice.
   I read that restriction comparison in the current source returned by
   `scompile.py --source WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar`.
   Its components come from `toProEtCompOverPullbackIso`, with identity
   fibre-product components. I checked `conjugateIsoEquiv` in Mathlib Mates:
   the inner symmetry and final symmetry produce L1→L2 from δ:R2→R1,
   as required by the node's unit/Hom normalization. Verdict: exact.
5. Identity compatibility: first conjunct of `ComparisonPullbackCoherent`
   equates c_id followed by the pro-etale identity identification with ν^*
   of the etale identity identification, for every F. I compared the
   identity constructions with upstream `upperStarId`: they use the same
   conjugation of `pullbackId`. Verdict: exact identity normalization.
6. Composite compatibility: second conjunct first applies ν_X^* to
   `etaleComparisonComp D f g`, then c_f and f_Proet^{-1}(c_g); its other
   side applies c_(f≫g) followed by `proEtaleComparisonComp D f g`.
   I opened both existing `upperStarComp` constructions: the same conjugate
   of `sheafPushforwardContinuousComp'` and `pullbackComp` is used here.
   Verdict: the canonical composition equation with the correct direction.
7. Specified Cartesian identification: third conjunct quantifies over
   `sq : ChosenCartesianSquare g' f' f g` and F on Y_Et. I read the
   dependency structure, including `isoPullback`, `hom_fst`, `hom_snd`, and
   the inherited `sq.w`, and `Etale.squareUpperStarIso`. The delivered
   square maps are k_(f',g) inverse, transport by `sq.w.symm`, then k_(g',f).
   The two sides of the conjunct are precisely the two paths in proof step 4.
   Ignoring the representation of `isoPullback` loses no choice: its two
   projection equations determine it uniquely by the pullback property.
   Verdict: the specified square comparison, not an arbitrary replacement.
8. Coefficients: `comparison_pullback_coherent` asserts all of the above
   for `Type (u+1)`, `AddCommGrpCat.{u+1}`, and every finite ring Λ in
   `Type (u+1)` with `ModuleCat.{u+1} Λ`. No commutativity is imposed.
   Helper-category colimit/sheafification assumptions are discharged at
   these specializations. Verdict: all coefficient settings of the node's
   proof, with no additional hypotheses on the main theorem.

Edge cases: empty schemes are allowed by all binders; the zero sheaf and
zero ring are allowed; identity arrows and identity factors in composites
are explicitly covered. No index set, integer degree or characteristic is
restricted (n=0 is inapplicable). `u` and `v` are explicitly bound. The small
site retains object universe u+1 and morphism universe u; coefficient Hom
universe u+1 is the shared size convention, not an equation between the two
site universes. There is no unbound variable, local notation or private copy
of a site. General helper abbreviations only expose the same construction
for nonabelian set coefficients; their identity and composition data likewise
extend the existing construction rather than selecting another notion.

Independent searches used different wording from the worker:

- `msearch.py NE lem-weil-pbc-comparison-pullback leanfinder
  'Naturality of the etale proetale inverse image comparison under identity
  and composition of scheme maps'`: eight hits, about scheme maps and etale
  morphisms, none the comparison coherence statement.
- `msearch.py ... loogle '"sheafPushforwardContinuousComp"'`: nine hits in
  Mathlib Continuous, including the canonical primed composition comparison
  used here. I read its definition and the identity variant.
- `rg` in Mathlib CategoryTheory, upstream WeilConjectures and project
  `lean/Sheaf` for `comparison.*(Comp|Id|Coher)`, `toProEt.*pullback` and
  `pullback.*toProEt`: the pertinent existing comparison is
  `comparisonUpperStarCompUpperStarIso` in LowerStarAcyclic. Its declaration
  gives the reverse isomorphism for abelian/Grothendieck coefficients, not
  sets or the three coherence equations; I opened its body. Monoidality
  and derived comparison results also do not state these equations. Thus
  the complete item has no exact existing declaration.

No new definition nodes or dependency modules occur in this delivery, and
there is no statement_change to audit. I found no mathematical or signature
mismatch and left the Lean and node unchanged. The sole sorry is the named
main theorem; its docstring follows all four node proof steps and identifies
restriction, composition of adjunctions, conjugation, and the square/Hom
calculation. Definitions contain actual data. Each declaration has its
source and blueprint docstring. The node's `lean.statement` matches the
main signature verbatim.

Validation: the prescribed `scompile.py NE lem-weil-pbc-comparison-pullback`
compiled the delivered file both in its sandbox (3.7 seconds) and at its
intended module name (3.8 seconds), with no errors or warnings. The second
reading changed only this report by adding the independent audit.
