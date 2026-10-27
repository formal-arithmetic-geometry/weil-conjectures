## Worker report

The delivery states `SheafOfModules.OpenTotalTensorCoefficient.interchange_exists` in
`Sheaf.Algebra.Homology.OpenTotalTensorCoefficientInterchange`. Its only theorem proof is
`sorry`. Three definition modules introduce the missing comparison-data, normalization,
and strict-coherence packages; they contain real constructions and structures, no
postponed data. No existing statement or definition is changed. The item's original
statement and proof remain verbatim; its statement dependencies gain the three definitions.

Hypotheses and notation, clause by clause (all names below are in
`SheafOfModules.OpenTotalTensorCoefficient` unless qualified):

* The small site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
  The coefficient universe is `max c v r`, containing the independent site-object
  and morphism universes. `R : Sheaf J CommRingCat.{max c v r}` renders B, and `V : C`
  is the localized object. The `HasSheafify` and `WEqualsLocallyBijective` instances
  on J and J.over V are the standard small-site sheafification interfaces, available
  in this universe. They do not impose flatness or a geometric restriction.
* The localized site and ring are `J.over V`, `R.over V`; `slice R V A` is the
  existing `LocalizedStrictTensor.sliceAlgebras` value. `extension` and `restriction`
  apply the recorded `localizedSystemExtension` and `localizedSystemRestriction`
  degreewise. Thus j_! is the actual direct-sum presheaf followed by module
  sheafification, and j* retains its actual section modules.
* Unital coefficient algebra sheaves are `Under R`. `AlgebraTowers R` is the
  existing `ℕᵒᵖ ⥤ Under R`, with level n representing the paper's n+1.
  Functor identity and composition laws encode every q_(m,n), including m=n.
  Maps of these functors are arbitrary unital algebra-tower maps.
* `Complex A` abbreviates the recorded module-sheaf category's `CochainComplex ... ℤ`.
  `total R P Q` is the existing `P ⊗ Q`, the signed direct-sum total tensor;
  `totalSection` uses its actual `CochainComplex.ιMapBifunctor` insertion and the
  existing sheafified pure tensor. There is no boundedness condition and no product
  totalization. The differential sign is the Mathlib cochain tensor sign (-1)^p.
* `change A.hom` is `CategoryTheory.CochainPullback.extend A.hom`, the actual
  scalar-extension functor applied termwise; `forget A.hom` is its recorded
  `restrictComplex`, actual scalar restriction. The API writes the scalar first:
  `extensionTmul a M W s x` represents the paper's x tensor s. No signed interchange
  is involved because coefficients have degree zero.
* `extendedTotal R V Q F` and `sliceTotal R V Q F` render G and G_V.
  `source R V A Q F` is G tensor_B A; `intermediate` is T_A; `sliceTarget` is S_A;
  `target` is j_(A!) S_A. Q_A and F_A are the displayed `change` objects in these
  definitions. These are A-linear complexes before restriction of scalars.
* `Comparisons.gamma` has exactly the ordinary total-tensor projection isomorphism
  type over every coefficient sheaf. `GammaNormalization.gamma_forward` fixes the
  map on the original homogeneous extension-presheaf generators;
  `gamma_inverse` fixes its inverse. The existing generator uniqueness and adjunction
  characterization imply this inverse is precisely the open-unit transpose, rather
  than an arbitrary inverse to some unrelated isomorphism.
* `Comparisons.linear` is the A-linear r_(L,A), with its forward and reverse
  generator formulas in `LinearNormalization.linear_normalized` and `linear_inverse`.
  The coefficient is evaluated at (W,f) by the actual slice functor, so j*a is a.
  Actual scalar restriction is used throughout the strict families; the recorded
  identity-on-extension-summands comparison identifies it with j_(B!) after
  restriction on the slice. No arbitrary identification replaces scalar restriction.
* `Comparisons.baseBalanced` is the existing normalized `CochainPullback.epsilon`;
  `sliceBalanced` is epsilon followed by tensoring with
  `Comparisons.restrictionCoefficient`. `RestrictionNormalization.normalized` fixes
  that identification on tensor sections. This is the restriction/scalar comparison
  needed to identify j*F tensor A_V with j*(F tensor A), as the accepted proof says.
  Epsilon's existing normalization places a in the first factor and 1 in the second;
  its inverse multiplies the two scalar entries.
* `Comparisons.left` is gamma_A composed with Tot(r_Q tensor 1) and b^X.
  `Comparisons.right` is j_(A!)(b^V) composed with r_(G_V,A) and change(gamma_B).
  `StrictCoherence.equation` is their equality as A-linear chain maps for every A,Q,F,
  hence simultaneously for all levels of any specified tower.
* `sourceSection` and `targetSection` use the original extension summands followed
  by sheafification, not hypothetical representatives of arbitrary sheaf sections.
  `StrictCoherence.generator` is the exact common forward value with coefficient a,1;
  `generator_inverse` fixes the inverse with two independent coefficients a,b and
  their product ab. `GammaNormalization`, `LinearNormalization` and these formulas
  retain each p,q insertion. Every comparison and its inverse is an actual complex
  isomorphism, so differential commutation is part of the type, with precisely the
  signed total differential already defined by the dependency.
* `StrictFamily` contains literal identity/composition equations.
  `StrictCoherence.source_transition` applies the algebra map to the source coefficient;
  `target_transition` applies it to both independent target coefficients.
  These generator formulas determine the canonical maps by the tensor,
  direct-sum and sheafification universal properties; the existential strict families
  cannot choose unrelated transitions. `left_strict` and `right_strict` give every
  transition square before localization. `strictIso` packages these into natural
  isomorphisms, so their inverse squares are included by naturality of the inverse.
  Precomposition by any algebra tower gives exactly the required strict B-module towers.
* `StrictCoherence.tower_equation` explicitly asserts equality of these strict-tower
  maps. `transpose` constructs complexes of actual module towers degree by degree;
  `localizeTower` uses `HasDerivedCategory.standard` and `DerivedCategory.Q` for the
  abelian category `ℕᵒᵖ ⥤ Modules R`. `localized_equation` asserts equality after this
  localization, in D(strict towers), without replacing it by levelwise derived categories.
* `StrictCoherence.natural` is the square for arbitrary chain maps u and v, with
  the actual `sourceMap` and `targetMap`. Strictness is quantified over every unital
  coefficient-algebra map, so it includes every component and square of a tower map.
  No flatness, boundedness, completeness, surjectivity, adic, or quotient assumption
  appears in the theorem. All comparison data are existential conclusions,
  normalized on their actual generators, not new hypotheses of the theorem.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`: `CategoryTheory.Precoverage.IsSiteForCoverings`;
  the site is used here through the associated `GrothendieckTopology`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`; site/ring localization uses
  `GrothendieckTopology.over` and `Sheaf.over` from Mathlib's Sites.Over.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExtension`, `localizedSystemRestriction`, their
  additive instances, `localizedSystemAdjunction`, and `localizedSystemExact`.
* `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence`; the equivalent inverse-system interface here is a functor
  on ℕᵒᵖ, as the recorded dependency explicitly permits.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used through the existing `LocalizedStrictTensor.Modules` abbreviation.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the corresponding additive structure and
  coproduct-preservation instances, used by the existing total tensor instance.
* `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and its chain maps;
  `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `ιMapBifunctor` (the tensor uses this construction).
* `Sheaf.CategoryTheory.RingedSliceTensorGenerators`:
  `SheafOfModules.exists_ringedSliceTensorGenerators`, its uniqueness, inverse
  generator and open-unit transpose clauses; `ringedSliceExtensionSection`.
* `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`:
  `SheafOfModules.ringedOpen_totalTensor_kFlat` and the total-tensor presentation.
  As its accepted DAG proof specifies, only the totalization shape is used here;
  its unnormalized comparison is not substituted for the generator-normalized gamma.
* `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; and
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.
  The existing `LocalizedStrictTensor.extensionSection` is their actual unit on
  a direct-sum summand, as used by the generator-normalized dependency.
* `Sheaf.CategoryTheory.SliceTensorGeneratorCoherence`:
  `SheafOfModules.SliceTensorGenerator.coherence_exists`, `Coherence`, its linear,
  restriction and strict-coefficient generator normalizations. Existing
  `LocalizedStrictTensor.sliceAlgebras`, `AlgebraTowers`, `Modules`, `pure`, and
  `extensionSection` are reused, not reimplemented.
* `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`; its public
  coefficient-arrows interface supplies `extend`, `epsilon`, `restrictComplex`,
  and `extensionTmul` used by the delivered constructions.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` through the existing coefficient interface.

The source places were read in the local Stacks sources: sites-modules.tex,
lemma-j-shriek-and-tensor (0E8I), and sites-cohomology.tex, the same label (0GL1).
The strict coefficient calculation is the DAG's expressly labeled agent refinement,
not a claim that the short Stacks lemmas themselves state tower coherence.

Edge cases checked before finalizing: zero Q or F; an empty extension-index set
(no arrow W to V); the zero coefficient ring (unital maps remain correctly typed);
identity/constant coefficient towers; arbitrary non-surjective coefficient maps;
non-flat Z to Z/2 change; negative p or q; unbounded complexes, where all inserts
remain in direct sums. No characteristic, invertibility or finiteness restriction
enters the code. Site object and Hom universes remain independent; the explicit
universe parameters on strictIso/transpose/localizeTower repair a universe inference
failure without identifying universes or changing the mathematical statement.

Searches: the sandbox searches.jsonl records msearch.py searches for the statement
using LeanFinder, Loogle, LeanSearch and Mathlib grep. The initial query
“Extension by zero total tensor product cochain complexes coefficient change strict
 tower interchange” returned tensor insertions and generic HomologicalComplex tensor
interfaces, not this statement. Loogle `SheafOfModules, CochainComplex.mapBifunctor`
returned zero hits. Mathlib grep `coefficient.*interchange|totalTensor.*coefficient|
extensionByZero` returned zero. The later data query returned ModuleCat scalar-extension
objects/maps, sheaf module presentation generators and tensor insertion; the coherence
query returned generic monoidal coherence and natural transformations. No exact match.
`rg` of lean/WeilConjectures and lean/Sheaf for OpenTotalTensorCoefficient and
coefficientInterchange found no existing declaration; searching the item id in
WeilConjectures found none. DAG searches and tools/blueprint_refs.py searches for
“open total tensor” and “coefficient coherence” found no matching definition node.
The nearby normalized slice generators and scalar-unit augmentation statements
are reused through their owning declarations and do not state the present equation.

Validation: all four modules were checked separately, in dependency order, with
scompile.py and its unmodified default per-file limits. The split2 compile completed
successfully with no Lean error and no non-sorry warning. The only postponed theorem
is interchange_exists. The prescribed deliver2.py dry run and delivery are recorded
in the corresponding sandbox logs.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.

## New nodes

`def-sf-open-total-tensor-coefficient-data` owns
`OpenTotalTensorCoefficientData`: the actual source/intermediate/target complexes,
original homogeneous generators and the type of ordinary and coefficient-linear
comparison data, including the existing balanced epsilon maps. It packages the
notion used in the assigned node's displayed formulas; it defines no alternative
sheaf tensor, extension, scalar extension or complex category. Its source is the
0E8I/0GL1 coefficient refinement recorded in the assigned node. The three search
kinds and repository/DAG searches are recorded in mathlib_searches; none gives
this combined data notion.

`def-sf-open-total-tensor-coefficient-normalization` owns
`OpenTotalTensorCoefficientNormalization`: normalization predicates on the actual
presheaf generators, the two displayed composites, strict coefficient families and
their isomorphisms, the actual transpose to complexes of towers, standard derived
tower localization, and maps in the two input complexes. It depends on the data
node and the recorded scalar-restriction, tower and derived-category definitions.
The maps are genuine constructions from these definitions. The source is the same
agent refinement; the searches found generic coherence and tensor constructions,
not this normalized comparison package.

`def-sf-open-total-tensor-coefficient-coherence` owns
`OpenTotalTensorCoefficientCoherence`: the precise predicate/data structure for
interchange, its homogeneous forward/inverse values, canonical strict transitions,
complex naturality, strict-tower equality and derived-tower equality. It is a
structure defining the notion, not a proof of its existence. The assigned theorem
asserts its nonemptiness with the normalization predicates. Its source is exactly
the assigned node's strict coefficient refinement of 0E8I and 0GL1. The same three
search kinds and the DAG/repository checks found no existing definition of this
specific notion. All three new nodes point to prop-sf-pf-coherence through the
assigned item's original blueprint ancestry, and are cited from the item.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
