## Worker report

This delivery states `AlgebraicGeometry.Scheme.Modules.exists_affineCohomologyEtaleModuleRealization`
in `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization`. It leaves theorem proofs as
`sorry`; all maps and inverse maps used in definitions have actual data or are selected by a
specified uniqueness/bijectivity property. The source is the local Stacks text,
`etale-cohomology.tex`, `lemma-higher-direct-images`, Tag 03Q8 (lines 7515ff), together with the
recorded simultaneous Tag 03P2 comparison. No mathematical statement correction is made.

Hypothesis and clause correspondence:

- Schemes and the given morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Quasi-compact and separated: `[QuasiCompact f] [IsSeparated f]`. There is no global
  compactness or separatedness assumption on S or X.
- The two quasi-coherent modules: `(G : X.Modules) [G.IsQuasicoherent]` and
  `(E : S.Modules) [E.IsQuasicoherent]`.
- Degree: `(q : ℕ)` includes degree zero.
- Every affine etale base object: `V : S.Etale` with `[IsAffine V.left]`. The raw comparison
  uses `pullback V.hom f`, the canonical interchange of factors in the node's fibre product;
  its map to X is `pullback.snd`, and its map to V is `pullback.fst`.
- The coefficient `G_V` is `affineRealizationCoefficient`, literally tensor pullback along
  that map to X. The tensor-pullback comparison helper supplies the required instance.
- The supplied bijections are `e V`, an additive equivalence from the recorded
  `RingedSpace.moduleCohomology` to tensor sections of E. `e_linear` states exactly linearity
  over base sections, with the source scalar pulled back by `pullback.fst.appTop`.
- `e_natural` quantifies over every arrow between affine etale objects, not just open
  immersions. `affineRealizationRestriction` is `moduleCohomologyFMap` adjoint to the
  normalized tensor-composition coefficient map; the target is the recorded
  `etaleTensorSectionsRestriction E h`.
- The common coefficient universe is `AddCommGrpCat.{u+1}` throughout, and every coefficient
  lift is the existing `liftedCoherentEtaleSheaf`. All scalar sections have the same
  `ULift.{u+1}`. No equality of independent site/coefficient universes is assumed.
- The left side is `affineRealizationHigherImage`, literally degree q homology of the
  abelian derived functor `R+((f)_*[AddCommGrpCat.{u+1}])`, the definition of
  `Etale.rightDerivedLowerStarPlus`, applied to G's lifted sheaf in degree zero.
  The right side is E's lifted associated sheaf. `Φ` is an isomorphism of those actual
  abelian sheaves.
- A module sheaf over the lifted etale structure ring is expressed by its sectionwise
  `Module (ULift Γ(V.left,⊤))` structures, the first conjunct (semilinear restriction),
  and the third conjunct (linearity of Φ). These are exactly the data and equations of
  the recorded sheaf-of-modules definition, without constructing a second category.
- The second conjunct fixes the source action on all local cohomology classes by the
  actual `coherentEtaleMap` of multiplication by `pullback.fst.appTop a`. Thus the action
  is induced by local multiplication, independently of Φ. The class maps are locally
  surjective by the associated-presheaf construction, so this condition fixes the
  sheaf action. It is not merely an arbitrary action transported through Φ.
- The fourth conjunct is the requested affine formula for every x. Its c is
  `affineRealizationAffineComparison`, the inverse of the uniquely normalized
  simultaneous comparison, specialized using the existing separated-over-affine
  equivalence. `affineRealizationClass` is defined with the actual raw class map and
  inverse of the actual raw evaluation, rather than an unspecified comparison witness.
- The fifth conjunct is the formula for every raw derived-Hom class z. It uses
  `Etale.abelianHigherDirectImageClass` and `affineRealizationRawEvaluation`. The latter
  applies `rawRestrictedCohomologyComparison` followed by the canonical derived/Ext and
  tensor-restriction identifications. This pins the same class normalization, including
  the sign, rather than choosing a witness to the existence-only comparison theorem.
- The first three conjuncts quantify over every etale object, with no affineness
  hypothesis. They therefore include the required non-affine scalar compatibility.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.Separated`: `QuasiCompact`,
  `IsSeparated`, their base-change instances, and `HasAffineProperty.iff_of_isAffine`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: fibre products use the
  recorded `Limits.pullback` convention, with the factor order displayed above.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` and the publicly imported
  upstream tensor modules: `tensorPullback`, `exists_tensorPullbackAdjunction`,
  `tensorSectionsComp`, `tensorSectionsUnit`.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`: `etaleTensorSectionsSheaf`;
  `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`:
  `etaleTensorSectionsRestriction` and its normalized composition convention.
- `Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison`: `liftedCoherentEtaleSheaf`,
  `coherentEtaleMap`; `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`:
  `exists_qcoherentCohomologyComparisonPullback`; its canonical family is supplied by
  `exists_unique_qcoherentNormalizedComparison` in `.QcoherentNormalizedComparison`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`;
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`: `moduleCohomologyFMap`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `.Derived.UpperLowerStarCoherence`: `rightDerivedLowerStarPlus`;
  `.Derived.LowerShriek`: `rightDerivedGlobalSections`,
  `cohomology`.
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`:
  `abelianHigherDirectImageRawPresheaf`, with its exact derived-Hom source;
  `.AbelianHigherDirectImageClassCompatibility`: the actual `abelianHigherDirectImageClass`.
- `WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`:
  `rawRestrictedCohomologyComparison`; `.RawRestrictedCohomologyComparisonIsIso`:
  `isIso_rawRestrictedCohomologyComparison`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`, already used by the actual raw constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is the transparent
  Mathlib `SheafOfModules` specialization; its sectionwise module data are expanded in
  the conclusion. No second module-sheaf definition is introduced.
- `pqf-def-coherent`'s finite-type repair is not used to strengthen quasi-coherence:
  the node here asks only for Mathlib's `IsQuasicoherent`.

Edge cases checked: q=0 (the canonical integer-generator evaluation and section units
fix the degree-zero comparison); zero coefficients and zero rings; the empty scheme and
empty affine etale object; identity arrows and all other arrows in the affine subsite;
non-affine etale objects; and an arbitrary base S that need not be qcqs. No nonempty,
field, properness, smoothness, torsion, or finiteness assumption was added.

Searches performed, with actual outcomes:

- `msearch.py ... leansearch` with “Compatible affine etale coherent cohomology
  isomorphisms realize an abelian higher direct image as a module sheaf with canonical
  scalar action”: eight results, including module-sheafification scalar compatibility,
  but no affine realization with the two class normalizations.
- `msearch.py ... leanfinder` with the same query: eight results, including `Sheaf.H`,
  `Sheaf.cohomologyPresheaf` and abelian module-sheaf categories; no exact statement.
- `msearch.py ... loogle` with `CategoryTheory.Sheaf.H, AlgebraicGeometry.Etale.lowerStar`:
  zero hits; the service reported the project-specific lowerStar name unknown.
- `msearch.py ... grep` with `affine.*[Cc]ohomology|[Hh]igher[Dd]irect[Ii]mage.*[Mm]odule`:
  zero hits in Mathlib.
- `rg`/`grep` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  by the item id and by affine cohomology, lifted coherent coefficients, raw evaluation,
  and the proposed new declaration names: existing construction tools found, no duplicate
  affine realization or public canonical restriction/derived-presentation bridge.

## Returned-delivery repair

The saved packet first passed the prescribed dry run as commit 3f81ae465fc. A
point-by-point self-check against the return at f860f10ce33d nevertheless confirmed
that it still contained the returned ownership defects, so that packet was repaired.
The current shared sources and node records were read without Git commands or edits.

H13: the three rebound dependency copies were removed from the packet. Consequently
`def-weil-pbc-etale-cohomology`, `def-sc-etale-qcoherent-module`, and
`lem-weil-pbc-module-pullback-quasi-coherent` retain their live records byte for byte:
respectively `Etale.cohomology`, `etaleTensorSectionsSheaf`, and
`isQuasicoherent_pullback`. Their consumers retain exactly the same declarations.
The three helper modules remain, now owned by distinct new definition nodes listed
below. Tensor-pullback quasi-coherence is supported by the explicit natural
isomorphism `tensorOrdinaryPullbackIso`, obtained from the specified adjunctions
by `leftAdjointUniq`; the existing ordinary quasi-coherence theorem is still used
in its proof plan. No original declaration is withdrawn or copied.

Mechanical statement dependencies: the realization now cites the new definition
owner `def-weil-pbc-abelian-higher-image-class` for the actual class map, replacing
the added theorem-node citation `lem-sbc-abelian-higher-direct-image-class-compatibility`.
The added `lem-sbc-raw-restricted-cohomology-comparison-is-iso` citation is removed
from the item's statement dependencies and retained in the coherent class helper
node, where bijectivity of the explicit raw evaluation is required to define its
inverse. The genuine dependency
`lem-weil-pbc-module-pullback-quasi-coherent` remains, together with the new tensor
comparison owner supplying the instance for tensor pullback.

H2: the item now explicitly cites `def-pbc-canonical-coherent-etale-comparison`
for `liftedCoherentEtaleSheaf` and `coherentEtaleMap`,
`def-sc-ringed-space-module-cohomology` for `RingedSpace.moduleCohomology`, and
`lem-weil-pbc-qcoherent-normalized-comparison-exists` for the uniquely normalized
comparison selected in `affineRealizationComparison`. Its actual tensor-section
restriction is owned by the new definition node
`def-weil-pbc-etale-tensor-sections-restriction`, reusing the upstream declaration
unchanged. No theorem is substituted for the definition of a map.

The item theorem's signature and its mathematical statement are unchanged. No
statement correction or disputed mathematical clause is needed.

## Second reading by NN

A separate reading pass in this dispatcher-started worker, without launching another
agent as instructed, compared the node's hypotheses and every conclusion clause with
the signatures above. The affine maps retain their full linearity and naturality;
the derived image is computed in abelian sheaves; the action is normalized independently
of Φ on all local cohomology classes; and both affine class formulas are present.
The factor order of the fibre product was checked against the upstream raw comparison,
and both projections were checked accordingly. The ordinary-pullback quasi-coherence
record is preserved, and the new tensor-comparison definition node owns the required
tensor-pullback instance. The
coefficient and Ext/derived transports retain the literal ULift and the actual raw
maps. The source action is not defined through Φ. The original node statement is
unchanged. Compilation and delivery checks are recorded below after completion.

## New nodes

`def-weil-pbc-coherent-higher-image-classes` packages the canonical constructions used
by the realization: the actual tensor-pulled coefficient, actual abelian higher image,
actual raw evaluation with the canonical coefficient and Ext/derived transports, and
its inverse followed by the canonical raw class. It imposes no geometric hypotheses
on f or V. Its source is Stacks Tag 03Q8. The source and target groups are the existing
ones; the new definition merely supplies their missing explicit class map with its
normalization. Keeping these constructions in their own file also makes their
compilation independent of elaborating the realization theorem. LeanSearch and
LeanFinder returned eight general cohomology/Ext results each, but no such transported
coherent class map. Mathlib grep returned zero hits. Searches of DAG nodes, upstream
Lean and Sheaf Lean found no existing declaration of these particular constructions;
the raw evaluation and raw class declarations are reused. The blueprint search found
no unit for this helper, and its ancestor is the item's proper-image finiteness unit.
All raw search outputs are retained in the new node's mathlib_searches.

The second reading also checked this node: its coefficient, universe, factor order,
actual raw map, and inverse are the same constructions used in the realization. No
new existence-only choice is introduced by the split.

`def-weil-pbc-derived-ext-evaluation` supplies the generic derived evaluation used
by the cohomology-presentation transport, in `Sheaf.CategoryTheory.DerivedExtEvaluation`
as `CategoryTheory.derivedExtEvaluation`. It applies the represented Ext morphism to
the degree-zero section, using the existing right-derived degree-zero and shift
comparisons, followed by the canonical single-complex localization identification.
Its source is Stacks, Cohomology on Sites, equations defining derived
sections, together with the derived-category construction. The node keeps the category and
localization universes independent; Ext and
the target groups use the stated common universe u+1. Specializing
to the recorded etale site fixes only its actual existing universe parameters.
LeanSearch and LeanFinder found the individual Ext, derived-zero, and exact-functor
operations, but no evaluation composite of this signature. Mathlib grep found
unrelated evaluation declarations; DAG, upstream, and Sheaf searches found no
existing node or declaration for this composite. The raw results are in the node.
The second reading checked its order of zero, morphism, and shift comparisons
against the explicit implementation. Its data contain no postponed proof.

`def-weil-pbc-coherent-etale-restriction` owns
`Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso`: the unique restriction
isomorphism characterized on every section by inverse tensor composition. Its
hypotheses are exactly an etale morphism and a quasi-coherent module with
quasi-coherent tensor pullback; the latter instance is supplied separately.
The sources are Stacks 03DR, 03DU and 03Q8. This notion differs from the associated
sheaf itself and leaves that sheaf's record unchanged. Its two declarations are
the normalized existence-and-uniqueness theorem and the uniquely selected map.

`def-weil-pbc-etale-cohomology-presentation` owns
`Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation`: evaluation at the integer
generator identifies Ext cohomology with derived-global-sections cohomology. The
map is explicit; additivity and bijectivity are named postponed theorems; the
inverse is determined by that bijectivity. The sources are Stacks 03FD and 01FT.
This is a presentation comparison, distinct from the retained cohomology definition.

`def-weil-pbc-tensor-pullback-ordinary-comparison` owns
`Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`. Its new main definition
`tensorOrdinaryPullbackIso` compares the specified tensor and ordinary pullback
adjunctions by `Adjunction.leftAdjointUniq`. Its helper
`isQuasicoherent_tensorPullback` transports the existing ordinary-pullback
quasi-coherence instance along that isomorphism. This retains every scheme morphism
and every quasi-coherent coefficient, including zero modules and empty schemes;
Stacks Modules 01BG is its source. No data are selected from mere existence of an
unspecified isomorphism.

`def-weil-pbc-abelian-higher-image-class` records `existing: true` on
`WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility`,
`AlgebraicGeometry.Etale.abelianHigherDirectImageClass`. Its signature was read in
full at lines 119ff: exact inverse-image single comparison, derived adjunction,
zeroth homology, shift comparison, and the sheafification-unit identity generator
are the literal construction in the source. It needs no geometric finiteness
hypothesis. The source is Stacks 03Q8. The compatibility theorem was not used as
a replacement for this definition, and its live record is unchanged.

`def-weil-pbc-etale-tensor-sections-restriction` records `existing: true` on
`WeilConjectures.AlgebraicGeometry.EtaleTensorSections`,
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction`. Its signature
and body at lines 62ff were read: the unit, normalized composition and over-category
triangle are precisely the usual pullback restriction, for every module and every
etale arrow. Its source is Stacks 03DR. No quasi-coherence hypothesis is added.
The functoriality theorem node remains unchanged.

For each of these five nodes, LeanSearch and LeanFinder queries about canonical
etale cohomology evaluation, coherent tensor restriction and higher-image classes
returned eight general Ext/cohomology primitives, not the project comparison
composites. Mathlib grep of the exact five helper names returned zero hits.
Project source grep found the two exact existing map definitions reused above;
no existing public definitions of the three other comparisons were found. DAG
record ownership was inspected by exact final declaration name, and blueprint
searches for cohomology presentation, coherent restriction, higher direct image
class and tensor sections restriction each returned zero blueprint units. Several
proofs locally use `leftAdjointUniq` for tensor pullback, but no public definition
or node owns that comparison. The raw service outcomes and local search summaries
are stored in each new node's `mathlib_searches`. Each source and section formula
was also checked against the helper declarations during this second reading.

## Validation

The original dry run passed mechanically but did not resolve the independent
review's ownership faults. The repaired packet preserves all three original live
dependency records and gives every new module exactly one new owner. All six
files compiled cleanly through `scompile.py` against the published live build,
including each private import and library module (3.9–24.5 seconds per module).
There were no errors or warnings. The repaired dry run and final delivery perform
their required server checks.

The repaired dry run's first preflight found 19 record-format faults: combined
bracket citations were not parsed as individual node citations, the local main
comparison signature included the `noncomputable` modifier, and the two exact
upstream bindings needed `branch: slopmaster2`. All were repaired without changing
any Lean term. The two theorem-node statement dependencies warned about by
preflight are retained as explicitly requested by the independent review: ordinary
quasi-coherence supplies the transport instance, and the normalized comparison
existence-and-uniqueness supplies the uniquely determined choice. These are actual
requirements of the definitions used in the item signature.
