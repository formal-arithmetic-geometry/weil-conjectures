## Worker report

Repair of returned head `114da1ab2089`. The module is
`lean/Sheaf/SixFunctors/EtaleOpenTensor.lean`, namespace
`AlgebraicGeometry.Etale`. The mathematical node statement is unchanged. Its
`stmt_deps` additionally cites the already landed
`lem-pur-etale-sum-flat-kflat` and `lem-coef-etale-hom-thick-locus`, whose
canonical realization and normalized scalar tensor comparison are reused.
There are no new nodes or dependency-record replacements.

Hypothesis-by-hypothesis correspondence:

* The commutative rings and their homomorphism are
  `{A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)`.
* Schemes and the open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`.
* `DerivedCategoryModule A U` and `DerivedCategoryModule A X` are the published
  ordinary unbounded constant-coefficient étale derived categories.
  `derivedExtension` and `derivedRestriction` abbreviate the exact functors
  `D((j)_!open[ModuleCat A])` and `D((j)^*[ModuleCat A])`.
  `scalarExtension φ T` is the published derived coefficient extension.
* All `P,T` are universally quantified in the appropriate full derived
  categories. There is no boundedness, constructibility, finite generation or
  coefficient-flatness hypothesis. Every universe and variable is bound;
  `autoImplicit` is false.

Clause-by-clause correspondence, using the fields of
`EtaleOpenTensorComparisons φ j`:

1. `gamma_isIso` asserts invertibility of `canonicalGamma j P T`, the exact
   published `derivedOpenImmersionLowerShriekProjectionMap` component.
   `canonicalGammaExact` transports this same map along the published
   `leftDerivedUpperStarIsoMapDerivedCategory` for formulas written with exact
   restriction. Its defining map is not independent projection data.
2. `canonicalGammaZero` defines the ordinary map by the inverse `homEquiv` of
   `openImmersionLowerShriekUpperStarAdjunction`, applied to
   `tensorRightUpperStarIso.hom.app P`. This is the specified adjunct of the
   open unit followed by the restriction/tensor comparison. `ordinary_tensor`
   asserts invertibility of this map itself, not existence of an unrelated
   isomorphism between its endpoints.
3. `flat_preserved` uses `etaleFlat`, which is exactly the recorded
   `SheafOfModules.IsFlatOnSite` after the published constant-ring module
   realization. `kflat_preserved` uses `etaleKFlat`, exactly the recorded
   `CochainComplex.IsKFlatIndependentCoefficients` after the corresponding
   degreewise realization. Neither is replaced by the categorical flat or
   morphism-property K-flat predicate.
4. `openRestrictScalarsIso` is the sectionwise coefficient-restriction
   identification, transported from `openImmersionRestriction` to `upperStar`.
   Its exact derived descent is `openDerivedRestrictScalarsIso`.
   `openScalarExtensionZero` constructs ordinary `q⁰` by uniqueness of left
   adjoints to these fixed functors; `openScalarRestrictionZero` constructs
   ordinary `r⁰` by the sectionwise direct-image/scalar adjunctions.
5. `openScalarExtension φ j` constructs natural derived `q` for each ring map
   using `Adjunction.leftAdjointUniq` on the fixed derived open and scalar
   adjunctions. `openScalarRestrictionMap φ j` is the mate of the actual
   coefficient-restriction identification. The named theorem
   `openScalarRestrictionMap_isIso` asserts its invertibility;
   `openScalarRestriction` uses `asIso` on this fixed map. Thus `q,r` are
   definitions, not arbitrary families or fields chosen under `Nonempty`.
6. `OpenScalarExtensionNormalization` and
   `OpenScalarRestrictionNormalization` give explicit equations on every
   K-flat cochain representative `P`. They compare the actual `q.hom.app (Q P)`
   or `r.hom.app (Q P)` with `Q.map` of the degreewise canonical `q⁰` or `r⁰`,
   using `scalarExtensionRepresentative` and the exact open
   `mapDerivedCategoryFactors` maps. The fields `q_normalized`, `r_normalized`
   assert these equations for the fixed comparisons; `q_unique`, `r_unique`
   assert that any natural isomorphism satisfying the respective equation is
   equal to the fixed one. This is a K-flat characterization rather than a
   uniqueness assertion about unrestricted endpoint isomorphisms.
7. `q_restricts` is the restriction identity after the canonical inverse open
   units: `j* q` followed by the inverse B-unit equals `r⁻¹` followed by scalar
   extension of the inverse A-unit. `counit` is precisely the displayed node
   equality `q ; j!(r) ; ε_B = F_X(ε_A)` at `j* T`.
8. `tensor_associative` compares the two actual composites out of
   `j!((P ⊗ᴸ j*T₁) ⊗ᴸ j*T₂)`: first rebracket, use the canonical restriction
   tensorator, then project once; or project with `T₂`, project with `T₁`, then
   rebracket on X. It uses `derivedTensorAssociator` and
   `openExactRestrictionTensor`, not an associator/inverse tautology.
9. `successive_scalar` quantifies every commutative ring C and map `ψ : B →+* C`.
   It equates `F_ψ(q_φ) ; q_ψ ; j!(scalarComp_U)` with
   `scalarComp_X ; q_(ψ.comp φ)`. The composition maps are the published
   `ProEtale.pbcFixedScalarExtensionComp` for the composite ring homomorphism.
   Both paths mention the fixed q and have the same actual endpoints.
10. `mixed_tensor_scalar` is the mixed projection/coefficient square. One path
    applies `γ_B`, `q⁻¹ ⊗ 1`, then the canonical scalar tensor comparison on X.
    The other applies `j!` to `1 ⊗ r⁻¹` followed by the canonical scalar tensor
    comparison on U, then `q⁻¹` and `F_X(γ_A)`. The comparison
    `etaleHomTensorComparison` is the landed natural, uniquely K-flat-normalized
    scalar tensor isomorphism. This is an equality between the tensor/scalar
    paths themselves, not just naturality in an unrelated morphism.
11. The open derived adjunction used throughout is
    `derivedOpenImmersionLowerShriekUpperStarAdjunction`, the published
    degreewise-derived open sheaf adjunction. The normalization equations
    explicitly use its exact functors' cochain localization factors.

Dependency declarations and locations:

* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`.
* `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`.
* `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `derivedTensor`, `derivedTensorAssociator`; and
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionMap`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`:
  `Scheme.etaleSumFlatModuleRealization`,
  `Scheme.etaleSumFlatComplexRealization`. These are the already recorded
  constant-ring coordinate transports for the two preceding predicates.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  the recorded general interface `SheafOfModules.DerivedChangeOfRingsCochainModel`;
  its constant-coefficient interface used here is
  `AlgebraicGeometry.Etale.scalarExtension` and
  `AlgebraicGeometry.Etale.scalarExtensionRepresentative`, both from
  `Sheaf.Paper.EtaleDerivedScalarTensor`. Ordinary scalar extension is
  `ProEtale.etaleSheafExtendScalars` with its fixed adjunction.
* `Sheaf.SixFunctors.EtaleHomThickLocus`:
  `AlgebraicGeometry.Etale.etaleHomTensorComparison`, with its published
  uniquely normalized tensor model. The scalar tower uses
  `AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp`, imported through
  this existing coefficient framework.
* Mathlib's `Adjunction.leftAdjointUniq`, `mateEquiv` and
  `Functor.mapHomologicalComplexCompIso`, together with the published
  `Functor.mapDerivedCategorySquareIso` from
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
  implement the canonical adjunction and localization transports, without
  introducing another coefficient action.

Sources checked: the node's Stacks references 0GL1, 0E8I, 06YY, 03EL, 03DI,
0E8J; the ordinary and unbounded derived `lemma-j-shriek-and-tensor` source
passages in `sites-modules.tex` and `sites-cohomology.tex`; and the current
blueprint `sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.proof.md`,
whose coefficient/projection discussion fixes tensor, counit and successive
coefficient compatibilities. The main theorem docstring gives the generator,
K-flat descent and coherence argument, including the total-complex signs.
The mate-invertibility theorem has its own source and proof docstring. These
are the only two postponed theorem proofs. Every definition has actual data;
the inverse mate uses its named invertibility theorem, which determines the
inverse uniquely.

Edge-case reading (mathematical checks, not executable proofs): identity and
empty open immersions use the same open adjunction and its units; the zero
extension/zero tensor case imposes no nonemptiness requirement. The zero ring,
zero complexes, identity ring map, and scalar towers containing identities are
included. Arbitrary nonflat coefficient maps are allowed: only model complexes
in the characterization have a K-flat premise, not the theorem's P or T. The
coherence laws use total derived tensor and apply to unbounded complexes.
No statement dispute or source correction was needed.

Searches performed in the retained packet and this repair:

* `msearch.py NV lem-coef-etale-open-tensor leanfinder` with query
  `Extension by zero along an open immersion commutes with derived tensor and
  scalar extension with canonical natural comparisons and counit compatibility`:
  eight unrelated Zariski restriction/direct-image declarations, no exact
  complete assertion.
* `msearch.py ... loogle` with query
  `CategoryTheory.Adjunction.leftAdjointUniq, CategoryTheory.mateEquiv`:
  zero indexed hits; direct source reading located the needed Mathlib APIs.
* `msearch.py ... grep` with query
  `openScalarExtension|openScalarRestriction` in `CategoryTheory`: zero hits.
* `rg` in Mathlib, upstream `WeilConjectures/` and project `lean/Sheaf` for
  `openImmersionLowerShriek`, `IsFlatOnSite`,
  `IsKFlatIndependentCoefficients`, coefficient comparisons, derived
  associators, `etaleSumFlatModuleRealization` and
  `etaleHomTensorComparison`: found the existing canonical interfaces listed
  above. The projection theorem alone does not state the full node, especially
  its coefficient normalizations and three compatibility laws.

## Second reading by NV

Independent maintainer reading, 2026-10-18, of immutable delivery
01f55574bfcb48391f4ed501bfc8658cf46fce5d. This replaces the delivered
self-check with an independent reading; the Worker report above is retained.
No Lean declaration, node statement, dependency record or project clone was changed.

I read packet.md, the item JSON, all nine statement-dependency JSON records,
the delivered Lean module and its docstrings, and the dependency declarations
in the read-only NV clone. I followed check-brief2.md and the stage-2 brief,
including delivery-errors H. Source passages read: the named master blueprint
thm-coef-finite-hom paragraph beginning “Extension by zero commutes with
coefficient tensor”; sites-modules.tex lemma-extension-by-zero (03DI),
lemma-extension-by-zero-exact (03DJ), lemma-tensor-product-pullback (03EL),
lemma-j-shriek-and-tensor (0E8I), lemma-restriction-flat (0E8J);
sites-cohomology.tex lemma-j-shriek-and-tensor (0GL1),
lemma-pullback-K-flat and lemma-derived-base-change (06YY).

Hypotheses and conclusions checked against the file:

1. The theorem binds arbitrary commutative A,B and their ring homomorphism,
   arbitrary schemes U,X and an open immersion j. It has no quasi-compactness,
   finite-type, Noetherian, coefficient-flatness, boundedness or constructibility
   hypothesis. The u+1 coefficient/module universe is precisely that of the
   recorded DerivedCategoryModule dependency; autoImplicit is false. It is not
   an extra identification of distinct ringed-site universes.
2. derivedRestriction and derivedExtension are abbreviations for the existing
   exact open functors on the ordinary unbounded small-etale module derived
   categories. derivedTensor is the existing K-flat-derived total tensor.
   canonicalGamma uses the published projection map: its definition is the
   adjunct of the unit tensored with identity and the restriction tensorator.
   canonicalGammaExact transports that same map from Lj* to exact j*.
   gamma_isIso covers every P,T. canonicalGammaZero is the inverse homEquiv
   applied to tensorRightUpperStarIso; that iso already includes the open unit.
   ordinary_tensor asserts invertibility of this very ordinary map.
3. etaleFlat and etaleKFlat abbreviate the recorded exact-tensor and
   acyclic-total-tensor predicates through etaleSumFlatModuleRealization and
   etaleSumFlatComplexRealization. Their definitions use the existing
   constant-module equivalence and canonical ring transport. flat_preserved
   and kflat_preserved state preservation with no finite-type premise from
   the stronger sum-extension theorem being imposed on j.
4. openScalarExtensionZero and openScalarExtension are fixed by uniqueness of
   left adjoints to the actual restriction/scalar functors. The derived r is
   the mate of openDerivedRestrictScalarsIso, with its invertibility stated in
   the named sorry-only theorem. openScalarRestrictionZero is the ordinary
   canonical left-adjoint comparison. q_normalized and r_normalized compare
   these maps with the degreewise ordinary maps on every K-flat representative,
   using the actual scalar counit and exact localization factors. q_unique and
   r_unique retain those normalizations. These are real constructions, not
   arbitrary endpoint isomorphisms or unconstrained Nonempty choices.
5. q_restricts has the correct orientation: j*(q) followed by the inverse
   B-open unit equals r inverse followed by F of the inverse A-open unit.
   counit is exactly q at j*T, then j! of r_T, then the B-counit, equal to
   F_X of the A-counit. Both maps are B-linear by their category. The existing
   derived open adjunction is mapDerivedCategoryAdjunction of the ordinary
   adjunction, with its degreewise unit normalization; it is not a free choice.
6. tensor_associative compares rebracketing/restriction tensorator/single
   projection with two projections and rebracketing. successive_scalar compares
   F_psi(q_phi), q_psi and j!(scalarComp_U) with scalarComp_X and q_(psi phi).
   mixed_tensor_scalar compares gamma_B, q inverse tensor identity and the
   normalized scalar tensor comparison with j! of the r inverse/tensor
   comparison, q inverse and F(gamma_A). All are equalities of the intended
   composites, not naturality tautologies. etaleHomTensorComparison is fixed
   by naturality and its flat-term K-flat counit equation. The tower comparison
   pbcFixedScalarExtensionComp is the canonical comparison of fixed adjoints.
7. Despite their ProEtale namespace, etaleSheafExtendScalars and its adjunction
   explicitly use X.smallEtaleTopology; scalarExtension and the tower comparison
   are specialized to that same topology. No pro-etale site is substituted.

The main proof docstring covers site localization/open units, the ordinary
adjunct, exactness and flatness, direct-sum totalization/K-flat preservation,
degreewise derived adjunction, K-flat computation, coefficient normalization,
the restriction and counit generator calculations, triple-tensor signs,
scalar towers and the mixed square. The mate-invertibility theorem has its own
source and argument. Only these two theorem bodies contain sorry; definitions
contain actual data. Every delivered declaration has source/blueprint
documentation and is listed in lean.declarations. The recorded main statement
is verbatim equal to the file signature; no line exceeds 100 characters.

Edge cases checked mathematically: empty U and empty X, identity open,
non-quasi-compact open, zero sheaves/complexes and zero rings, identity scalar
maps and identity-containing towers, nonflat Z -> Z/2, and unbounded complexes.
The direct-sum tensor and degree-zero coefficient factors produce the stated
signs without boundedness. None of these cases is excluded by an implicit
instance or by a theorem premise.

I independently searched Mathlib, upstream WeilConjectures and project Sheaf
sources for canonicalGammaZero, openScalarExtension, openScalarRestriction,
EtaleOpenTensorComparisons, open/coefficient scalar comparisons, and the
published projection interfaces. The projection and tensor constructions exist
and are reused; no existing declaration found states the full normalized
coefficient/counit/coherence assertion. The worker's three recorded search
modes were also read. No missing helper or universe repair is needed. The two
added statement dependencies are landed interfaces, permitted by the brief.
No statement_change or citer audit is necessary because the statement is unchanged.

Route pivot: the item statement/proof dependencies have empty intersection with
origin/newtargets-dag:coord/route-pivot-dropped.txt. The requested item repair
note does not exist at that ref. The delivery uses ordinary derived categories,
K-flat resolutions and adjunctions; it introduces no dropped enhancement,
rectification, coherent-section or operadic machinery.

Compiler reproduction: prescribed scompile.py NV lem-coef-etale-open-tensor
snapshot/lean/Sheaf/SixFunctors/EtaleOpenTensor.lean exited 0. Its sandbox probe
completed in 7.7 s and library confirmation in 8.8 s, with no diagnostics.
The installed wrapper now uses nt_srv_compile.py --wire-confirm (server-side
private overlay); this is the actual workflow observed, rather than a claim of
local compilation. No global build, direct SSH command, delivery/merge action,
live Lean write or repository mutation was performed.

Finding: H11, delivered Second reading explicitly said it was a self-check.
This complete replacement report supplies the independent clause-by-clause
reading. The mathematics and Lean require no change. Verdict: FIX, report only.
