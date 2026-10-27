## Worker report

The module `Sheaf.Paper.SfExactPullbackQuotientAugmentationSquare` states
`AlgebraicGeometry.Scheme.SfExactPullbackQuotient.quotient_augmentation_square`.
Its proof is `sorry`. The other declarations are transparent constructions of
levelwise application, the localized quotient augmentation, its two pullbacks,
and the resolution comparison; the two instance structures use Mathlib's
pointwise preservation instances. No definition contains postponed data.

This repairs the independent return on immutable head `43bc37ad024a`.
The initial saved-packet dry run passed as commit `69daf7c2eac`, but that
mechanical pass did not repair the ownership finding. The accepted Lean statement
and all its helper definitions are retained verbatim. The item's statement, proof,
and proof_deps remain unchanged. Its stmt_deps now cites
`def-cbc-strict-quotient-pullback-data` for the seven transparent definitions,
instead of citing `lem-cbc-strict-quotient-pullback-computation` as their owner.
The latter is retained in proof_deps only. The other previously added landed
statement dependency is `def-pur-tower-derived-localization-comparisons`.

Hypothesis and clause correspondence:

1. The schemes and morphism are `{X Y : Scheme.{u}} (g : Y ⟶ X)`, without
   Noetherian, dimension, immersion or coefficient-map invertibility hypotheses.
   `A : Type (u + 1)` and `d : AdicCoefficientDatum A` are the existing datum,
   including its Noetherian, finite, perfect positive-quotient conditions.
   `pbcAdicCompletion T d` is the actual limit of its quotient sheaves.
   `completedModulePullback g d` uses the projection-defined coefficient map and
   scalar extension, exactly the G of the node. It is not an arbitrary functor.
2. `F` has the existing additive, finite-limit-preservation and
   finite-colimit-preservation classes, and `m : completedModulePullback g d ≅ F`
   is specified. `pbcModules`, `pbcTowers`, `DerivedCategory`, and
   `DerivedCategory.Q` give the module categories, strict inverse sequences and
   unbounded derived localizations. Index `n : ℕ` denotes positive exponent n+1.
3. `L`, `ε`, `Lt`, `τ` are arbitrary specified derived pairs; `_hL` and `_hLt`
   are precisely their universal left-derived properties. `_hε` specifies
   computation on K-flat flat-term representatives and `_hτ` specifies the same
   for objectwise K-flat flat-term strict complexes. The former reuses
   `CbcStrictKFlatRepresentative`; the latter uses the recorded independent
   coefficient K-flat predicate and `SheafOfModules.IsFlatOnSite` explicitly.
   Its site objects have universe u+1, morphisms u, and coefficients/modules u+1.
4. Exact descents are `F.mapDerivedCategory` and
   `(exactTowerFunctor d F).mapDerivedCategory`; their `mapDerivedCategoryFactors`
   are the node's xi and Xi. `e` and `E` are the specified natural isomorphisms.
   `_he` and `_hE` render each of the two assumed counit equations on EVERY
   complex. `NatIso.mapHomologicalComplex m` and its levelwise version are Q(m).
5. `b : Functor.ConstantTowerDerivedComparison L Lt` is the specified
   constant-tower comparison. `_hb` uses the published
   `Functor.IsConstantTowerRepresentativeNormalized` on every K-flat flat-term
   representative, including the invertible counit and its inverse formula.
   The exact comparison c is the inverse of the published
   `CategoryTheory.UnboundedExactTower.constantInterchange F`. Its definition
   is exact localization of the identity-component ordinary comparison, with
   the canonical composition identifications. No comparison is assumed or chosen.
   The first conjunct states `b_K ≫ E_(Delta K) = Delta(e_K) ≫ c_K` for EVERY K.
6. `cbcStrictReduction d X` is the existing strict quotient complex R(P), with
   its actual transitions; `cbcStrictAugmentation d X P.complex` is its existing
   x tensor 1 augmentation (the coefficient-first presentation writes 1 tensor x).
   `quotientAugmentation d K P i` localizes it and includes the representative
   identification `i : Q(P) ≅ K`, the inverse `Delta(i)`, and the canonical exact
   constant/localization factor. Thus its target is precisely Q(R(P)), the
   node's chosen K_bullet. The identity representative i is allowed.
7. `pulledAugmentation` is b_K followed by Lt(a_K), and `exactAugmentation` is
   c_K followed by the exact tower descent applied to a_K. The second conjunct
   is the final square `beta_K ≫ E_Kbullet = Delta(e_K) ≫ beta^F_K`, as an
   equality IN THE DERIVED STRICT-TOWER CATEGORY. No evaluation or homology
   functor occurs in this equation.
8. The existential δ identifies its hom with τ at the constant representative.
   `cbcStrictPulledAugmentation d g Lt P (δ P)` is consequently exactly w_P,
   namely δ inverse followed by Lt(Q(a_P)). The subsequent equation identifies
   w_P, after the specified ordinary counit and representative source transport,
   with `pulledAugmentation`. It is the node's actual-augmentation identification,
   not an additional unrelated map.
9. For EVERY strict resolving arrow r, χ has hom `resolutionComparison`, i.e.
   Lt(Qr) inverse followed by τ_H. The resolving arrow's own quasi-isomorphism
   proof is installed only inside that real definition. The computation equation
   `w_P ≫ chi_r ≫ Q(G(r)) = Q(G(a_P))` identifies the actual resolved augmentation.
   The following equation compares it under chi_r inverse followed by chi_s,
   explicitly expressing independence of strict resolutions. In particular this
   never inverts τ_R(P) or asks for a lift of a_P to a resolving complex.
10. The isomorphisms ρ have their hom fixed to the existing reduction-tower
    complex counit. For arbitrary P, P', i and i', the LAST conjunct compares
    both augmented maps by the canonical isomorphism
    `ρ_P.symm ≪≫ reduction.mapIso (i ≪≫ i'.symm) ≪≫ ρ_P'`.
    This states independence of ALL chosen representatives, including those
    related only in the derived category. It asserts it for both the actual
    and exact augmentations. The earlier strict-tower square therefore agrees
    under the same canonical identifications.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.AdicCoefficientDatum` and its supporting published modules:
  `AdicCoefficientDatum`, `completedReductionTower`,
  `completedReductionTowerComplexCounit`, `completedReductionComplexTowerFunctor`.
  `pbcAdicCompletion`, `pbcModules`, `pbcTowers` in the published
  `Sheaf.Paper.BoundedConstructibleTower` are abbreviations for that actual
  completed ring, `ringedSiteModules`, and the strict functor category.
- Recorded module `Sheaf.Paper.PbcQbarCompletedPullback` is imported. Its public
  upstream `Sheaf.Paper.CompletedTowerPullback` supplies the ambient declarations
  used here: `completedCoefficientMap`, `completedModulePullback`,
  `completedTowerModulePullback`, `completedReductionModuleUnit`,
  `completedTowerConstant`, `completedDerivedConstant`. The Qbar restriction
  itself is not substituted for the ambient functor.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (through the published `pbcModules` abbreviation); Mathlib
  `DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`;
  `Mathlib.CategoryTheory.Functor.OfSequence`: strict `ℕᵒᵖ` indexing convention.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`;
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies
  the exact derived composition/isomorphism comparisons used by the published c.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`. The latter is exactness of tensoring.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `CategoryTheory.Functor.leftDerived_from_resolvingClass`; universality is
  rendered by the existing `Functor.IsLeftDerivedFunctor` class on Q.
- `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization`:
  `Functor.ConstantTowerDerivedComparison`, `Functor.IsConstantTowerRepresentativeNormalized`,
  `Functor.constantTowerDerivedSourceCounit`, and the generic comparison uniqueness
  theorem `RingedToposMorphism.existsUnique_derivedConstantTowerComparison` for
  the proof. The definitions used in the signature allow independent site universes;
  its small-site specialized theorem is not imposed as an extra assumption.
- New definition owner `def-cbc-strict-quotient-pullback-data`, recorded as
  existing in module `Sheaf.Paper.StrictQuotientPullbackComputation`:
  `CbcStrictKFlatRepresentative`, `CbcStrictQuotientResolution`,
  `cbcStrictReduction`, `cbcStrictDelta`, `cbcStrictAugmentation`, `cbcStrictPull`,
  `cbcStrictPulledAugmentation`. The theorem `strictQuotientPullbackComputation`
  in that same module is used for the proof only. The module's public import
  remains necessary to expose the existing definition declarations.
- Added landed definition node `def-pur-tower-derived-localization-comparisons`,
  module `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare`:
  `CategoryTheory.UnboundedExactTower.constantInterchange`.
- The stated proof dependencies `QuasiIsoSaturatedTriangulated` and
  `DiagramKFlatReplacements` are plain imports. Localization's universal property
  is Mathlib's existing API. The proof dependency
  `lem-cbc-strict-coefficient-augmentation-homotopicality` has no Lean attachment
  in the read clone and is consequently not imported; no object in the signature
  requires a new declaration for it.

Edge cases checked before and while drafting: K=0; unbounded K; K not intrinsically
complete; g=id with the identity exact comparison; I=0; I=A; the zero ring;
nonflat quotient levels such as Z_l/l^n; r=s; equal representatives; identity and
arbitrary representative identifications i. None is excluded. Coefficients use
the existing datum universe u+1, without forcing the site's object and morphism
universes equal. δ and χ are outputs characterized by actual counits, not extra
hypotheses that assume the desired square. The definitions introduce no arbitrary
map, `Nonempty` choice, or unnamed postponed proof.

Searches made:

- msearch.py / leanfinder, query `counit normalized derived pullback constant tower
  quotient augmentation comparison square`: 8 results, including
  `CategoryTheory.Adjunction.derived'_counit`, `derived_counit`,
  `MorphismProperty.Over.mapPullbackAdj_counit_app`, and simplicial augmentation
  constructions. None states the normalized quotient-tower square.
- msearch.py / loogle, query `CategoryTheory.Functor.mapDerivedCategoryFactors,
  CategoryTheory.NatTrans.naturality`: 0 hits.
- msearch.py / grep, query `quotient.*augmentation|constant.*tower|derived.*constant`
  under Mathlib/CategoryTheory: 0 hits.
- msearch.py / leansearch, query `exact derived functor comparison constant towers
  quotient augmentation counit normalization`: 8 results, including
  `Functor.totalLeftDerivedCounit`, `Adjunction.derivedε`,
  `Functor.mapDerivedCategoryFactorsh_hom_app`, and general adjunction functoriality.
  None is the item.
- rg on the named project Lean roots for the item id, constant-tower normalization
  and strict-quotient pullback names found `ConstantTowerNormalization`,
  `StrictQuotientPullbackComputation`, and the parent
  `SfExactPullbackCounitNormalization`. The parent fixes a special exact functor
  from an invertible coefficient map and canonical universal pairs, whereas this
  item allows arbitrary F,m and arbitrary specified universal pairs. It does not
  already state the present theorem.
- Broader rg for `compConstIso ℕᵒᵖ` found the generic published
  `UnboundedExactTower.constantInterchange`. Its full signature and definition
  were read. The initial separate construction of c was removed in favor of
  its inverse. The new statement reuses its existing definition node. The generic
  construction `cbcRealizationConst` is also the same exact localization in a
  more specialized interface; no new copy of either is delivered.

No statement correction or disputed mathematical claim is needed. The return's
ownership defect is repaired by the new definition-node record below, using the
return's explicit existing:true option. No existing definition is duplicated.
The theorem proof remains `sorry` as required for stage 2. Compilation and the
prescribed dry-run preflight are run through the launcher wrappers.


## New nodes

`def-cbc-strict-quotient-pullback-data` owns seven already published definitions
through `existing: true` in `Sheaf.Paper.StrictQuotientPullbackComputation`.
There is no new Lean module or new mathematical construction. The self-contained
node defines precisely the K-flat flat-term data, constant and quotient strict
complexes, their actual augmentation, strict quasi-isomorphic resolution data,
levelwise ordinary pullback, and the transported augmentation for any supplied δ.
Its source is the item's retained localization normalization Steps 4-5, with
Stacks 06XN (dual) as the resolving-class context. I opened both blueprint source
passages and the Stacks lemma, and read the live module using
`scompile.py --source Sheaf.Paper.StrictQuotientPullbackComputation`.

The exact source correspondences are:

- The coefficient datum and B_T are the same `AdicCoefficientDatum` and
  `pbcAdicCompletion` used throughout the item. `CbcStrictKFlatRepresentative`
  (lines 33-39) has exactly complex, independent-coefficient K-flat proof and
  flat-term proof fields, with no extra chosen K or identification.
- `cbcStrictReduction` (line 43) aliases the existing
  `completedReductionComplexTowerFunctor`; `cbcStrictDelta` (line 47) is the
  cochain extension of `completedTowerConstant`. Their transitions are respectively
  the actual quotient transitions and identities. Natural-number index n means
  exponent n+1, covering every positive exponent.
- `cbcStrictAugmentation` (lines 52-57) is literally the cochain extension of
  `completedReductionModuleUnit`, whose coefficient-first formula is 1 tensor x.
  It is the same scalar-extension map as x tensor 1 in the node's notation.
- `CbcStrictQuotientResolution` (lines 77-88) has exactly complex H, arrow r,
  its quasi-isomorphism proof, and levelwise K-flat and flat-term proofs.
  It contains no augmentation lift and no quotient-flatness condition.
- `cbcStrictPull` (line 64) applies the actual
  `completedTowerModulePullback` degreewise, including maps.
- `cbcStrictPulledAugmentation` (lines 102-107) has exactly the supplied functor
  LF, P and δ, and is `δ.inv ≫ LF.map (Q.map a_P)`. It does not use the module's
  τ binder or an existence theorem. Thus the new node does not assert an
  invertible counit, resolution existence, or the comparison-square conclusion.

I searched dag/nodes for these declaration names and definition owners: none.
`blueprint_refs.py search 'strict quotient'` returned three different nodes:
finite-reduction reconstruction, intrinsic-to-tower completeness, and a Koszul
quotient-limit lemma; none owns this data. `blueprint_refs.py ancestor` returned
`prop-sf-localization-all-stages`. The new node uses that ancestor and prepends
this item to the inherited via chain. Mathlib searches, recorded in searches.jsonl
and in the node, were:

- LeanSearch: `K-flat flat-term representative strict quotient resolution quotient
  augmentation pulled back through a counit` — eight general pullback, quotient,
  or resolution hits; no exact definition.
- LeanFinder: `strict quotient complex augmentation constant tower K-flat
  representative resolution data` — eight left/projective/injective resolution
  hits; no exact definition.
- grep: `CbcStrictKFlatRepresentative|CbcStrictQuotientResolution|cbcStrictAugmentation`
  — zero Mathlib hits. Direct rg of WeilConjectures returned none; rg of Sheaf
  found the existing definitions in StrictQuotientPullbackComputation and consumers
  in SfCompletedAugmentationAdjunct. These are reused with existing:true.

## Second reading by NN

This is the dispatcher's required self-check, performed without starting another
agent. I reopened the saved theorem, the item node, the new definition node and
the current live definition source after editing the packet. The substantive
correspondence remains the ten clauses in the Worker report above: arbitrary
schemes g and datum, additive exact F and m, specified universal pairs with the
K-flat computations, both counit equations, normalized b, c from exact localization,
both strict-tower squares for all unbounded K, actual augmentation formula, every
strict resolution comparison and arbitrary representative independence. The Lean
file has not changed since the substantively accepted returned head.

The one required correction is now concrete: all seven declarations named in the
return occur in the new definition node's lean.declarations, the item cites that
node in stmt_deps, and the theorem node occurs in proof_deps only. The owning node
records the exact existing declaration and its module, and introduces no duplicate
definition. All of its cited notions have existing definition nodes. Its definitions
are real data even though the unrelated computation theorem in the same source
module still has sorry. The χ cocycle and repeated resolutionComparison/flat-term
presentations mentioned in the return were advisory and are retained.

I checked again that the zero complex, unbounded complexes, I=0, the zero ring,
g=id, nonflat quotients, and incomplete K acquire no extra restriction through
the new ownership node. The node defines resolution data rather than asserting
that every quotient level is flat; δ is supplied data for defining a composite,
while its existence and counit characterization remain conclusions of the item.


Validation: the prescribed scompile.py run compiled the unchanged item in sandbox
and library modes cleanly (30.6 s and 22.1 s). The revised deliver2.py --no-push
run passed server preflight and compilation as commit `100d5c64899`. The field
comparison against the current read clone found only lean and stmt_deps changed;
there are exactly two added statement dependencies and none removed from the
base. The theorem signature record is verbatim, and all Lean lines are at most
100 characters. The new definition node's statement citations equal its stmt_deps.
