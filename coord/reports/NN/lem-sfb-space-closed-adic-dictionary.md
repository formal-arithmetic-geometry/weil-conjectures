## Worker report

Item: lem-sfb-space-closed-adic-dictionary. Group: NN. Stage 2 only: all theorem
proofs are `sorry`; every definition has real data. The statement is unchanged.
The two modules are Sheaf.AlgebraicGeometry.SpaceClosedAdicDictionary and
Sheaf.AlgebraicGeometry.SpaceThickeningCoherentSystems. The latter belongs to the
new definition node def-sfb-space-thickening-coherent-systems.

The module states the dictionary in three declarations: closedAdicDictionary,
closedAdicDictionary_properSupport, and closedAdicDictionary_thickenings.
All auxiliary declarations are listed in their owning node's lean.declarations.

Hypothesis and clause correspondence:

- A scheme S and algebraic spaces over S: explicit universe u, `{S : Scheme.{u}}`
  and `{X Z : AlgebraicSpace S}`. The existing small-etale module category
  `X.Modules` is used throughout, with its original coefficient universe. No
  site/coefficient universe equality or new site has been imposed.
- Locally Noetherian, quasi-compact, quasi-separated X: `hln` quantifies over
  every object of X.EtaleSite with the recorded IsLocallyNoetherian scheme
  predicate; `hqc : CompactSpace (Point X.obj.obj)` and
  `hqs : IsAbsolutelyQuasiSeparated X` are exactly the topology and absolute
  diagonal/affine-test conventions of the adic-system dependency.
- Closed immersion i: `hi : IsRepresentableWith (fun _ _ p =>
  IsClosedImmersion p.left) i.hom.hom` is the scheme-test definition, for all
  scheme base changes, not a hypothesis on an arbitrary monomorphism.
- Its quasi-coherent ideal K: `K : QuasiCoherentIdeal X` and `hK` make its actual
  inclusion a limiting kernel fork of `moduleStructureMap i`. This says K is
  the ideal cutting out i. No arbitrary annihilating ideal has been substituted.
- The ideal J is an arbitrary `QuasiCoherentIdeal X`. There is no completeness,
  nilpotence or finite-generation assumption on J.
- Z is Noetherian: the first three conjuncts assert exactly hln, compactness,
  and absolute quasi-separatedness for Z, rather than presupposing them.
- Coherent modules on Z and coherent modules on X killed by K:
  `ClosedAdicCoherent` abbreviates site IsQuasicoherent together with the
  recorded RingedSpace.IsCoherent on every `schemeRestriction`.
  `ClosedAdicKilled K 1` adds `AdicPowerKills K 1`. The displayed equivalence E
  has its forward functor naturally isomorphic, after the full-subcategory
  inclusion, to the recorded `moduleDirectImage i`.
- J O_Z: the existential L is a quasi-coherent ideal with an epi factorization
  of the existing `idealTensorMap i J` through its monic inclusion. This is
  precisely the image ideal and determines the ideal as a subobject.
- Every positive exponent: the index n : Nat represents the exponent n+1 in
  the existing AdicQuotientModel; thus exponent one is included and zero is not
  erroneously required. The natural isomorphism beta compares the two actual
  quotient-diagram functors on the full category of coherent Q.
- Canonical quotient map: beta satisfies the equation with
  `(adicQuotientModel J).projection` and the direct image of the L-quotient
  projection. This specifies the induced quotient map, rather than choosing
  an unnormalized abstract isomorphism.
- Naturality in Q and compatibility with ALL quotient transitions:
  beta is a natural isomorphism of functors into the full diagram category
  `(Natᵒᵖ ⥤ X.Modules)`. Its components are diagram isomorphisms, so both
  morphism naturality and every ordered transition square are retained.
- The adic equivalence: `(IsCoherentAdicSystem L).FullSubcategory` is
  definitionally CoherentAdicSystem Z L with the Noetherian witnesses supplied
  by the first conjuncts. `ClosedAdicKilledSystems J K` is the full
  subcategory of IsCoherentAdicSystem J with ALL terms killed by K. The
  equivalence's forward functor agrees up to natural isomorphism with
  `closedAdicPushDiagram i`, which is the existing whiskering functor for
  moduleDirectImage i and acts on all component arrows.
- Commutation with completion is exactly the same beta: its source is
  completion after pushforward and its target is pushforward of completion,
  including all quotient maps and transitions. This is completion as a diagram,
  as the node's proof explicitly specifies, not an additional inverse-limit claim.
- Relative setup: in the two relative declarations X and Z are spaces over
  Spec A, and p is their structural map to `schemeSpace (Over.mk (identity _))`.
  Giving a morphism from an algebraic space to Spec A is precisely giving
  this base structure. This uses the same relative form as the recorded
  CoherentAdicHasProperSupport dependency. It does not require a map from
  Spec A to the earlier auxiliary scheme S or any factorization through S.
  A : Type u has only CommRing A, including the zero ring.
- Separated and finite type: explicit `hsep : MapIsSeparated p` and
  `hft : MapIsFiniteType p` in both relative declarations. The proper-support
  assertion supplies the corresponding facts on i composed with p, rather
  than adding them as hypotheses.
- Proper support for coherent modules: the first conjunct of
  closedAdicDictionary_properSupport uses the EXISTING
  `CoherentAdicHasProperSupport` on constant diagrams. Unfolding it gives
  exactly a closed proper carrier and a finite-type quasi-coherent module
  whose specified direct image is the coherent module in question.
- Proper support for systems: its second conjunct applies that SAME predicate
  to F.obj and `closedAdicPushDiagram i` of F.obj. By definition this tests
  level one. Both clauses are iff, so they preserve AND reflect proper support.
- J = I O_X: hJ identifies its ideal of sections on every affine etale chart
  with the image of I under the actual structural ring map from A. The map
  is `(Scheme.ΓSpecIso (.of A)).inv` followed by the chart map's appTop.
  Checking affine etale charts is enough for equality of quasi-coherent
  ideal sheaves; requiring a global-sections image on nonaffine charts would
  have been incorrect, and is deliberately not done.
- X_n = X times_A Spec(A/I^n): `closedAdicBase I n` is the literal quotient
  spectrum for exponent n+1; `closedAdicBaseMap` is Spec of Ideal.Quotient.mk.
  hb is the actual sheaf pullback square for Y n, with its two projections i
  and b. Quantifying over these chosen pullback squares covers every model
  of the fibre product, with no extra representability or chart hypothesis.
- Coherent modules on X_n versus modules killed by J^n: the first thickening
  conjunct gives the equivalence for EVERY n, and its ambient natural
  isomorphism identifies its forward functor with moduleDirectImage (i n).
- Specified adjacent tensor restrictions: the new category's objects retain
  `restriction n : (moduleTensorPullback (j n)).obj (term (n+1)) ≅ term n`.
  j has the equation `j n ≫ i (n+1) = i n`; these are the canonical adjacent
  inclusions, determined by the fibre products and monicity of the i's.
- Objects AND arrows: E is a category equivalence, and each rho n is a natural
  isomorphism of the evaluation/pushforward functor with evaluation of E.
  This specifies the image on component maps, not just an object bijection.
- Actual transitions: closedAdicRestrictionTransition is built from the
  recorded adjunction UNIT, direct image of the specified restriction,
  and the right-adjoint mate of the tensor-normalized composition iso.
  The displayed rho equation identifies this with E's adjacent transition.
  The natural-number diagram determines all longer transitions by composition.
- Tensor restriction of M equals completion: R is the restriction-system
  functor, alpha identifies EACH term naturally with the specified tensor
  pullback i_n^* M, and sigma is a natural DIAGRAM isomorphism with the actual
  completion. The last equation sends the adjunction unit, via alpha and rho
  and sigma, to the EXISTING quotient projection of M. Thus it retains the
  unit/quotient normalization, arbitrary module maps, and all transitions.

Dependency interfaces read and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Spec, Spec.map;
  Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace,
  IsRepresentableWith, EtaleSite, structureSheaf, Modules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and the
  slice instances for Mathlib's SheafOfModules.IsQuasicoherent.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  ModuleDirectImageModel, moduleDirectImage, moduleTensorPullback,
  moduleTensorAdjunction. Its full projection/limit signature and its
  definition of tensor pullback were read, not just their names.
- Sheaf.AlgebraicGeometry.CoherentFiniteType and
  WeilConjectures.AlgebraicGeometry.Coherent: the publicly exposed
  RingedSpace.IsCoherent, with finite type and finite-type kernels, NOT
  merely IsQuasiCoherentFiniteType.
- Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem: adicPowerSections,
  AdicPowerKills, AdicQuotientModel (all fields), adicQuotientModel,
  IsCoherentAdicSystem, CoherentAdicSystem, coherentAdicCompletionDiagram,
  CoherentAdicHasProperSupport.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsSeparated,
  MapIsFiniteType, MapIsProper; SpaceProperQuotFunctor.ProperQuotient's
  properSupport field, which is the closed-carrier convention used above.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback,
  etale_fibreProduct_isScheme. Pullback is a sheaf pullback, as in that module.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal:
  QuasiCoherentIdeal and idealTensorMap;
  AlgebraicSpaceModuleStructureMap: moduleStructureMap;
  SpaceFlatDirectImageBaseChange: moduleTensorComposition with its unique
  local-tensor normalization; AlgebraicSpaceSchemeRestriction: schemeRestriction.
  The additional landed definition dependencies record these exact interfaces.
- def-weil-size-convention is a metatheoretic convention: explicit universe u
  supplies the pinned space/site/section sizes; no dummy Lean declaration exists.

The already stated proof dependencies are imported plainly, including the
closed-coherent, etale pushforward/restriction, Zariski/etale comparison,
affine tilde/Gamma, closed-ideal correspondence, affine finite-type and
ideal-product theorems, chart property test and tensor realization modules.
The currently unstated proof-only nodes
lem-sfb-space-closed-immersion-quasi-coherent-modules,
lem-sfb-space-noetherian-coherent-acc,
lem-sfb-space-noetherian-coherent-support, and
lem-sfb-space-module-proper-carrier-support have no module to import yet.
Their mathematical uses are described in the theorem docstrings; no statement
from them is assumed as a replacement hypothesis.

Sources opened: spaces-cohomology.tex lemma-i-star-equivalence (08AM),
spaces-more-morphisms.tex lemma-existence-tricky first paragraph (08BC),
and remark-reformulate-existence-theorem (08BF). The natural-language proof
is carried step by step in the declaration docstrings. The formal-effectivity
assumptions of 08BF (A Noetherian and complete) are not imposed on its purely
closed-immersion dictionary, which does not need them.

Edge cases checked mathematically before and during the second reading:
Z empty; i identity; K zero and the unit ideal; J zero and the unit ideal;
I zero and the unit ideal; A the zero ring; n=0 means the required first
positive level, not an excluded first level; nonreduced closed immersions
such as k[t]/(t^2); a point of A^1 has proper support while O_(A^1) does not;
nonaffine etale tests, for which ideal products require local membership
rather than just finite sums of global sections. The hK universal property
and epi factorization of L remain meaningful on the empty and zero cases.

Searches for an existing dictionary:

- msearch leanfinder: 'Closed immersion pushforward equivalence coherent
  modules annihilated by ideal, coherent adic systems and infinitesimal
  thickenings': 8 hits, including scheme overEquivIdealSheafData, open
  immersion module pushforward and local cohomology. None states the space
  dictionary or its quotient/system normalizations.
- msearch loogle: 'SheafOfModules, CategoryTheory.Equivalence': 6 hits, general
  site-equivalence pushforward, restriction-to-opens and affine tildeEquiv.
  None is a closed algebraic-space adic dictionary.
- msearch grep: 'CoherentAdic|closed.*equivalence|adic.*[Ee]quiv': 25 broad
  radical/p-adic hits, no matching statement. A focused grep for
  'CoherentAdic|RestrictionSystem|Thickening.*System' in AlgebraicGeometry
  returned 0 hits.
- msearch leansearch: 'Category of coherent modules on infinitesimal
  thickenings with specified adjacent tensor pullback isomorphisms and
  compatible component morphisms': 8 hits for ambient module categories,
  scheme module pseudofunctor and pullback composition; no space system category.
- rg on lean/WeilConjectures and lean/Sheaf for closed adic dictionaries and
  the node id found no exact statement. The focused thickening-system search
  found WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem and
  ThickeningSystemPushforward: their signatures quantify over SCHEMES and
  use Scheme.Modules.tensorPullback, hence cannot define this space category.
- DAG searches for adjacent tensor restrictions found the item, its consumer
  and unrelated arithmetic interpolation. blueprint_refs searches for
  'coherent systems' and 'tensor restriction' returned 0 blueprint nodes.

No statement dispute or correction is needed. The withdrawn CompactObject
example module now contains no declarations; its node is an existing upstream
attachment. Module-mode headers and the current stage-2 conventions were used.

## New nodes

`def-sfb-space-thickening-coherent-systems` defines the category of coherent
modules with SPECIFIED adjacent tensor-pullback isomorphisms on a tower of
algebraic spaces, together with compatible component maps, component identities,
component composition and evaluation. Source: 08BF, conditions (1) and (2).
Its coherent abbreviation uses the recorded predicates rather than redefining
scheme coherence. The scheme node def-weil-pbc-coherent-thickening-system is
not usable because these are algebraic spaces with small-etale module functors.
The existing def-sfb-space-coherent-adic-system instead has all terms on ONE
space and quotient conditions; it has no varying sites or specified tensor
restriction isomorphisms. The three recorded search kinds plus project/DAG
searches found no existing definition. Its category-law obligations are named
sorry theorems with complete elementary proof docstrings; its data are concrete.
The inherited blueprint ancestor command returns no node (the item's own
blueprint.from.node is null); the new node retains that ancestor and extends
its complete inherited via chain, naming its precise 08BF application.

## Second reading by NN

The dispatcher explicitly forbids starting other agents. This section records a
separate in-thread rereading with BOTH JSON statements and BOTH module files
open; it does not claim to be an independent second worker. The maintainer's
independent review follows delivery.

I checked each hln/hqc/hqs binder against the node's Noetherian convention,
the kernel universal property against 'ideal K of i', and the image
factorization against J O_Z. I read beta as a natural isomorphism INTO the
whole diagram category and checked its projection equation, rather than
mistaking pointwise isomorphisms for transition compatibility. I unfolded
ClosedAdicKilledSystems to verify that every term is killed by K, and checked
that the full-subcategory arrows are all natural transformations. I checked
proper support through the existing first-term predicate for both a constant
module diagram and an actual adic system; the iff in each clause gives both
directions. I checked that no extra map Spec A -> S is assumed in either
relative assertion: these objects have the base Spec A given by the structural
morphism, exactly as in the source and adic-system definition.

I checked the new category's Hom comm equation, component identities,
component compositions, and evaluation. Its coherence uses the finite-type
KERNEL condition via RingedSpace.IsCoherent, not only finite presentation or
finite type. The tower's j equation and actual pullback squares determine the
canonical inclusions, including identity and empty thickenings. I checked
rho's domain/codomain and its transition equation against the ADJUNCTION UNIT
and specified restriction isomorphism. I checked alpha's direction (its inverse
occurs after the unit) and sigma's direction (system pushforward to completion),
so the last equation is literally the quotient projection. Naturality of
rho, alpha and sigma handles all arrows.

Corrections during this rereading: the equation J=I O_X was restricted to
affine etale charts (global image ideals on nonaffine charts would be too
strong); the relative statements were put directly over Spec A rather than
assuming a map Spec A -> S; proper support was expressed using the EXISTING
CoherentAdicHasProperSupport predicate and stated explicitly for systems as
well as modules; and the missing algebraic-space tensor-restriction category
was assigned its own definition node. These are choices of exact rendering,
not changes to the natural-language statement. All theorem proofs remain
sorry. No private data, arbitrary comparison, or additional mathematical
assumption is used.

Validation: scompile.py compiled each delivered module separately in dependency
order, including the sibling overlay, without errors or warnings. The required
deliver2.py --no-push finished with `OK (dry run)` at 5f8a4f71470: maintainer
preflight and all per-file compiles passed. The delivered packet contains two
Lean files, the item record, the new definition-node record, and this report.
