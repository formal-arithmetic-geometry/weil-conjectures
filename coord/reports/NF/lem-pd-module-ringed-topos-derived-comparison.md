## Worker report

This delivery states lem-pd-module-ringed-topos-derived-comparison in
Sheaf.Paper.ModuleRingedToposDerivedComparison, namespace
AlgebraicGeometry.ProEtale.ModuleRingedComparison. All theorem proofs are sorry;
definitions contain actual categorical constructions. The theorem list in lean
is intentional: the long node is stated in separate named clauses, with the
paper-setting delta clause as the primary declaration. It is not a claim that
the primary delta equation alone states the entire node.

Hypotheses and objects:

- The primary theorem binds ell and p, Fact ell.Prime, a field k : Type u,
  CharP k p, 0 < p, and p != ell. X,Y are objects of Over (Spec k), with
  LocallyOfFiniteType, QuasiCompact and IsSeparated structure maps; f is a
  morphism in that over-category and the actual scheme map is f.left.
- Lambda is the existing Sheaf (coherentTopology Profinite) Ab with MonObj and
  IsCommMonObj. The comparison constructions are valid for arbitrary schemes;
  the primary declaration retains the paper's base-field setting explicitly.
- The site is Scheme.ProEt.topology T. Objects have universe u+1, morphisms u,
  and modules and section rings have universe u+1. No equality between the
  site's object and morphism universes is imposed. The existing comparison
  module supplies its relative smallness instance.
- ring is sectionRingSheaf of condensedRingObj Lambda T. equivalence is exactly
  sectionModuleEquivalence, not a new implementation. modules is Mathlib's
  SheafOfModules over the forgetful image of that ring.
- HasDerivedCategory at size u+1 is bound explicitly for the section-module
  categories. This is the standard choice-of-localization interface, not an
  additional mathematical restriction or a chosen second Abelian structure.

Clause-by-clause rendering:

1. Additivity, exactness, preservation and reflection of flat objects are the
   first three clauses of ordinary_exact_flat_kflat. Flatness is exactFunctor
   (tensorRight M), and the section side is SheafOfModules.IsFlatOnSite.
2. Its fourth clause uses the actual recorded IsKFlatModuleObject and
   CochainComplex.IsKFlatIndependentCoefficients. It includes both directions.
   Their test sides differ; the proof plan explicitly uses signed symmetry.
3. ordinaryTensorComparison and ordinaryUnitComparison are specified by unique local pure-tensor and scalar-section formulas. The
   existing internal_section_tensor_comparison supplies those same maps; the
   small uniqueness interfaces avoid expanding its much larger existential
   statement in each construction. ordinary_monoidal states naturality,
   associativity, the left and right unit laws and symmetry for these maps.
4. totalComparison_existsUnique fixes the chain isomorphism on every summand
   p+q=n. It uses the existing signed direct-sum total, not a product total.
5. derivedFunctor is the termwise functor localized by mapDerivedCategory;
   derivedFunctor_isEquivalence and derivedEquivalence give D(E). tensor is its
   conjugate K-flat tensor model. tensorComparison_existsUnique specifies its
   actual comparison by the equivalence unit. tensor_representatives identifies
   it with the ringed derived tensor: q is uniquely normalized on termwise E images,
   becomes invertible when either factor is K-flat, and the unit is the regular
   section-ring module in degree zero. Thus tensor is not an arbitrary tensor
   or an extra assumption on a tensor supplied by a consumer.
6. coefficientMap directly reuses InternalModuleOperations.coefficientMap, the uniquely
   normalized actual adjunct condensed coefficient map as a section-ring map. pushforward is Mathlib's module pushforward for this
   ring map and the actual pro-etale base-change site functor. pullback directly reuses InternalModuleOperations.upperStar, the sheafified
   tensor-formula inverse image followed by extension of scalars. pullComparison reuses InternalModuleOperations.upperComparison, fixed by the
   adjunction mate equation; pushComparison reuses lowerComparison, which fixes every section.
7. derivedPullComparison uses the actual internal upperStar.leftDerivedFunctor
   and its canonical exact-functor comparison. derivedPushComparison uses the
   actual lowerStar.rightDerivedFunctor and the canonical derived-composition
   comparisons. derived_homEquiv is equality of the specified derived Hom
   bijections. Evaluating this equation at identities gives both the specified
   unit and counit, rather than just isomorphic adjoint functors.
8. pushforwardComposition reuses InternalModuleOperations.lowerComp, fixed on sections
   by ProEtale.lowerStarComp, the actual geometric fibre-product pasting map.
   pullbackComposition is its mate under the specified ordinary adjunctions;
   derivedPullbackComposition localizes that exact map. composition_comparison
   equates it with the existing internal leftDerivedUpperStarComp under D(E).
9. internalDelta is upperStar.leftDerivedTensorComparison: the actual localized
   oplax mate. The underived mate is fixed by the local pure-tensor direct-image
   pairing. tensorPullComparison is independently specified by its unique ordinary
   ringed pure-tensor representative square, using qTensor, the localization factors and
   the underlying mapBifunctorComparison of its oplax tensor map. This is the
   defining component of mapHomologicalComplexδNatTrans. The representative normalization in
   ringedTopoiCanonicalDerivedTensorPullback therefore identifies this with
   the dependency's canonical ringed comparison. delta_comparison is equality
   of these specified transformations. The primary paper-setting theorem is
   this exact equation for the specified field, schemes and k-morphism.
   internalDelta_isIso states the invertibility already asserted by identification
   with the canonical ringed tensor isomorphism, with its flat-resolution proof
   plan. internalMu is the inverse actual delta, and mu_comparison explicitly
   states its equality with inverse canonical ringed delta.
10. internalProjection is the actual derived adjoint transpose of counit after
    internalDelta. projection calls the existing derivedProjectionFormulaMate
    used by the ringed projection interface. projection_comparison equates
    these actual arrows under the already specified comparisons. This equation
    applies in particular to proper f; it asserts no invertibility of projection.
11. extension and openAdjunction reuse the landed sectionwise extension and specified
    open adjunction of InternalModuleOperations. extensionComparison reuses its
    uniquely mate-normalized openComparison, and
    derivedExtensionComparison localizes it. derivedExtension and
    derivedOpenAdjunction are levelwise exact localization. internalOpenAdjunction
    is the actual existing derived open adjunction, with right adjoint expressed
    as L j*. open_homEquiv identifies the Hom bijections, hence units and counits.
12. internalOpenProjection is explicitly the adjoint transpose of the open unit
    followed by inverse actual delta. openProjection is the ringed version using
    inverse tensorPullComparison. openProjection_comparison equates the arrows,
    so this includes precisely the actual mu used by adjoint-of-unit projection.

Dependency declarations read and used (module; declaration):

- Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport;
  InternalModuleOperations.coefficientMap, lowerStar, upperStar, adjunction,
  lowerComparison, upperComparison, extension, openAdjunction, openComparison,
  lowerComp and upperComp. These are the landed ordinary operations reused directly.
- WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate;
  CategoryTheory.Functor.mapDerivedCategorySquareIso: canonical localization
  of the ordinary pullback and open-extension comparison squares.

- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible;
  AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField: field setting.
- Sheaf.Topology.ProfiniteCondensedRing; Profinite.CondensedRing: arbitrary
  condensed-ring convention, an object of the existing monoid category.
  Its public ContinuousCoefficientCommRing import retains continuous examples.
- Mathlib.AlgebraicGeometry.Sites.Proetale; Scheme.ProEt and its topology.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic;
  condensedRingObj, coefficientRing, condensedPullbackHom, condensedPushforwardHom.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence;
  InternalAbelianSheafModule.sectionRingSheaf, sectionModuleEquivalence.
- WeilConjectures.CategoryTheory.ModuleObjects.Monoidal; Mod.monoidalCategory.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom;
  CondensedRing.derivedTensor and the specified internal derived tensor.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs;
  CondensedRing.upperStar, lowerStar, upperStarLowerStarAdjunction.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar;
  CondensedRing.derivedUpperStarLowerStarAdjunction,
  leftDerivedUpperStarIsoMapDerivedCategory, leftDerivedUpperStarComp.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses;
  SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback: independent site universes and
  unique flat-term K-flat representative normalization.
- Sheaf.Paper.ProjectionMateExact; SheafOfModules.ringedProjectionMateExact;
  its imported Sheaf.Paper.ProjectionFormulaArrows supplies
  CategoryTheory.derivedProjectionFormulaMate. The generic uncurried mate
  avoids imposing the equal site/Hom universes of the older corner interface.
- Sheaf.Algebra.Homology.KFlatModuleObject;
  AlgebraicGeometry.ProEtale.IsKFlatModuleObject.
- Sheaf.Algebra.Homology.KFlat; CochainComplex.IsKFlatIndependentCoefficients.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs;
  CondensedRing.openImmersionLowerShriek,
  openImmersionLowerShriekUpperStarAdjunction.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek;
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction.
- Proof dependency lem-pe-internal-section-tensor-comparison;
  Sheaf.CategoryTheory.InternalSectionTensorComparison,
  InternalAbelianSheafModule.internal_section_tensor_comparison. This supplies
  the existing normalized ordinary tensor/unit maps and acyclic/flat/K-flat
  comparison; it is not restated as a second independent tensor construction.

The section-equivalence source missing from the older local checkout was read
with scompile.py --source, as authorized; framework sources were read in the
shared lean/WeilConjectures tree. Source passages of Stacks 00YV, 03EK, 03EL,
03D7, 03DI, 03DJ, 07A4, 0G7E, 07A6 and 0B56 ground the construction and proof plans.

Edge cases checked: the empty scheme, the zero condensed ring, zero modules and
complexes, arbitrary unbounded complexes and their infinite direct sums, identity
and composite morphisms, identity/empty open immersions, and nonproper morphisms
for the projection mate. No division by ell or by the characteristic is used;
there is no accidental nonzero-ring, boundedness, flat-coefficient or properness
hypothesis. A projection arrow is not asserted invertible. Regular-unit and
pure-tensor normalizations rule out replacing a canonical arrow by a scalar twist.
All test complexes in K-flatness range over the full recorded module category.

Searches for the item: msearch leanfinder for internal abelian sheaf/module
comparison with derived tensor and ringed topoi returned generic module adjunction
and sheaf equivalence hits; leansearch for the same comparison returned generic
monoidal and sheaf-module results. A loogle query containing Monoidal as a bare
identifier was invalid (not evidence of absence). msearch grep for
sectionModuleEquivalence|internal_section_tensor_comparison in Mathlib returned
zero hits. rg in WeilConjectures and lean/Sheaf found the existing ordinary
comparison, but no complete derived push/pull/actual-delta/projection comparison.
The exact item id was also searched upstream. Additional searches for the new
construction are recorded verbatim in its mathlib_searches.

The clarification of the independently specified ringed derived adjunction and the resulting dependency repair are recorded below under Statement corrected. No STATEMENT-DISPUTED issue remains.

Compilation uses only the prescribed scompile.py wrapper, each file separately
in dependency order within its private overlay and the default 60-second limit.
The four-module packet had compiled cleanly through scompile.py before this return;
only the expected postponed theorem proofs remain. The resumed dry run exposed a 60-second
derived-helper timeout. The repair reuses the landed ordinary operations and the
generic mapDerivedCategorySquareIso, fixes the categories of localization
functors explicitly, and names sectionLocalizationComparison, localizedTotalComparison and
totalPullComparison so large localization
instance arguments are not repeatedly inferred. The representative equations use
HomologicalComplex.tensorObj and the underlying mapBifunctorComparison directly;
these are the same signed tensor and oplax total map, without repeatedly
synthesizing the full monoidal category of cochain complexes. Compact finite-limit,
finite-colimit and adjoint instances reuse the existing ordinary comparison theorem
and adjunction. Explicit high-priority zero-map preservation instances are the
existing additive-functor instances; they prevent a search through the expanded
pullback composite. totalTensor_obj records the defining equality of functor-level
and object-level totals, and the component maps use its equality transports.
The literal normalization formulas are named TensorRepresentativeCondition and
TensorPullRepresentativeCondition, so their uniqueness statements and choice
selectors do not repeat the full formula in each declaration.
The main equations name CondensedRing.derivedTensor explicitly, including its
object and first-variable map operations, instead of asking Lean to infer the
entire derived monoidal structure at each notation. These are the same existing
tensor and whiskering maps. internalDelta_isIso records the invertibility clause
so inv uses that named fact directly. All temporary diagnostics are removed.

## New nodes

def-pd-section-derived-tensor-data owns Sheaf.Paper.SectionDerivedTensorData, the localized
section equivalence, derived functor models and normalized conjugate tensor data.
It uses the same ordinary comparisons, signed totals and localization maps
already described below. The former larger helper module exceeded the 60-second
limit; its tensor-data portion is isolated here, with separate ownership, while
SectionDerivedRealization imports it for the representative normalization and
functor-comparison constructions. No construction is duplicated or replaced.
The additional LeanFinder query returned generic HomologicalComplex tensor
declarations; blueprint_refs.py found zero matching construction nodes.

def-pd-proetale-section-module-functors owns the additional normalized tensor
interfaces in Sheaf.Paper.ProEtaleSectionModuleFunctors. Its primary declaration
ordinaryTensorComparison selects the unique local-pure-tensor comparison supplied
by internal_section_tensor_comparison. Its other constructions give the normalized
internal and ringed direct-image relative tensor pairings, their inverse-image
adjunction mates, regular-unit selector and signed direct-sum total selector.
The current-source recheck found the landed
lem-sfb-internal-module-operations-transport (2026-10-18). Its
Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport already supplies the
actual adjunct coefficient map, tensor-formula inverse image, direct image,
ordinary comparisons, open extension and geometric compositors. The delivery now
reuses these exact declarations by transparent aliases; the saved packet's separate
constructions of these notions were removed. Its ordinary data now come through def-pd-section-module-operations-data; the comparison theorem is a proof dependency of the main item.
The original recorded searches are retained as historical results, and the current
source discovery and precise distinction are appended to mathlib_searches.
Sources: Stacks 03EK, 03EL, 03D7, 03DI and 03DJ. Every existence choice determines
its maps uniquely by local formulas; definitions contain actual categorical data.

def-pd-section-derived-realization owns Sheaf.Paper.SectionDerivedRealization.
It imports the localized equivalence, exact derived pullback, K-injective direct
image and equivalence-unit tensor data, then defines the unique representative square,
the independently derived ordinary ringed adjunction, and localized open extension and
composition. Sources are Stacks 00YV, 03DJ, 06YU, 07A4 and 07A6. The saved
LeanSearch and LeanFinder results contain generic module/section constructions;
Mathlib grep has no hit, and current DAG/blueprint searches find no such node.
Project grep finds the ordinary equivalence used here. Each helper theorem is included in the statement and declaration list of its
owning construction node: tensor data in def-pd-section-derived-tensor-data,
representative normalization and functor comparisons in def-pd-section-derived-realization. An earlier attempt repaired this saved module
with its own owner record; the present resumed dry run retained that record. Current compilation also
required exact sequential colimits for the localized open adjunction and, after F1, the independently derived ringed adjunction. The named
section_hasExactSequentialColimits supplies this by the exact equivalence.
section_hasFunctorialFlatResolutions transports the existing internal flat
resolution functor through the exact tensor equivalence; the existing
internal_section_tensor_comparison gives flatness preservation, without a
dependency on this consumer's later comparison theorem.
The internal_hasGradedTensor, section_hasGradedTensor,
internal_hasCochainTotal and section_hasCochainTotal statements give the countable
coproduct prerequisites of the already specified signed totals. Their proofs
are postponed, and their existence assertions are included in the tensor-data
node's statement. The internal/section goodTensorLeft, goodTensorRight and quadrupleTensorExt
instances similarly specialize the existing graded tensor coproduct comparison
predicates: the universal properties follow because tensor distributes over
these countable sums, as explicitly included in the construction node. These specialize existing Mathlib predicates and introduce no new
tensor data. The small functor aliases are marked implicit_reducible to avoid repeatedly
unfolding large localization instance arguments during type comparison.
comparisonSource returns the source of the actual published
comparison isomorphism; internalDerivedPullback and internalDerivedPushforward
therefore retain exactly the existing total derived functors while avoiding
repeated inference of their large instance arguments. Functor arguments of the
comparison compositions are written explicitly for the same reason.

## Second reading by NF

This repair-session reading compares the node texts with all five final modules.
The tables identify the declarations checked, their exact roles, the mismatches
found, and their repairs. The dispatcher prohibits starting another agent; the
maintainer performs the independent delivery review. This section supplies the
actual clause checks that were missing from the returned report.

### Main comparison node: hypotheses and objects

| Node hypothesis or object | Lean checked | Finding |
| --- | --- | --- |
| Prime ell | `ℓ : ℕ`, `[Fact ℓ.Prime]` in the primary theorem | Exact. |
| Field of characteristic p positive and different from ell | `(k : Type u) [Field k] [CharP k p]`, `_hp : 0 < p`, `_hne : p ≠ ℓ` | Both characteristic conditions retained. |
| Separated finite-type k-schemes | `X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on each structure map | Finite type is local finite type plus quasi-compactness. |
| k-morphism f | `f : X ⟶ Y` in that over-category; all component operations use `f.left` | Base compatibility is structural. |
| Arbitrary commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ] [IsCommMonObj Λ]` | No discrete, nonzero, flat, or finiteness restriction. |
| Small pro-etale site relative to module sheaves | `Scheme.ProEt.topology T`, site objects at u+1, arrows at u, section rings and modules at u+1 | No equation u+1=u. |
| Pulled-back coefficient ring and its section-ring realization | `condensedRingObj Λ T`, `ring Λ T`, `modules Λ T` in SectionModuleOperationsData | Transparent use of the existing section-ring construction. |
| Fixed equivalence preserving underlying abelian sheaf | `equivalence Λ T := sectionModuleEquivalence ...` | No new equivalence is chosen. |
| Existing internal and section relative tensors | `Mod.monoidalCategory`, existing `SheafOfModules` tensor | No replacement relative tensor. |
| Existing total derived operations | `internalDerivedPullback`, `internalDerivedPushforward`, `derivedPullback`, `derivedPushforward` | Published internal functors; exact-localized ringed pullback and K-injective ringed direct image. |
| All unbounded complexes and standard localization choice | `CochainComplex ... ℤ`, `[∀ X, HasDerivedCategory.{u+1} (modules Λ X)]` | No boundedness assumption; the latter selects the usual localization. |

### Main comparison node: every conclusion

| Node conclusion | Lean checked | Finding or repair |
| --- | --- | --- |
| E is additive and exact | First two conjuncts of `ordinary_exact_flat_kflat` | Exact predicates, not only left exactness. |
| E preserves and reflects flat modules | Third conjunct, `exactFunctor _ _ (tensorRight M) ↔ SheafOfModules.IsFlatOnSite ...` | Both directions, same relative coefficient rings. |
| E preserves and reflects K-flat complexes | Fourth conjunct, `IsKFlatModuleObject ... P ↔ CochainComplex.IsKFlatIndependentCoefficients ...` | Full acyclic test categories; signed symmetry connects their opposite test-side conventions. |
| E is symmetric monoidal | `ordinary_monoidal`: naturality, associator, left unitor, right unitor, braiding equations | All five clauses use the normalized tensor and regular-unit maps. |
| Total tensor complexes are identified | `totalComparison_existsUnique`, its coproduct-inclusion equation for every p+q=n, `totalComparison` | Signed direct-sum total, including infinite degrees. |
| Induced D(E) is an equivalence | `derivedFunctor`, `derivedFunctor_isEquivalence`, `derivedEquivalence` | Localizes E itself; inverse, unit and counit descend. |
| Derived tensor and its unit are identified | `tensorComparison`, `TensorRepresentativeCondition`, `tensor_representatives`, `qTensor` | Normalization uses E on total complexes and the internal localization tensor map; either K-flat factor makes q invertible; unit is the regular module in degree zero. |
| Underived pullback is tensor-formula inverse image | `pullback := InternalModuleOperations.upperStar` | Existing forget/presheaf scalar-extension/sheafification composite, not a transported arbitrary functor. |
| Underived pushforward is the actual module direct image | `pushforward := InternalModuleOperations.lowerStar` with `coefficientMap` | Underlying site base-change evaluation and scalar restriction fixed. |
| Derived pullback and pushforward comparisons | `derivedPullComparison`, `derivedPushComparison` | Actual exact localization and canonical right-derived composition/natural-isomorphism comparisons. |
| Specified derived adjunction, unit and counit agree | `derived_homEquiv`, equality for every M,N,q | F1 repaired: `derivedAdjunction` is `(adjunction Λ f).derivedAdjunction` changed only on its left by `leftDerivedFunctorIsoMapDerivedCategory`. It never mentions D(E) or the internal adjunction in its defining term. The Hom equality remains a theorem; identities recover unit and counit. |
| Pullback composition comparisons agree | `derivedPullbackComposition`, `composition_comparison` | Localization of the geometric ordinary compositor, compared with `leftDerivedUpperStarComp`. |
| Actual oplax delta equals canonical ringed delta | `internalDelta`, `TensorPullRepresentativeCondition`, `tensorPullComparison`, `delta_comparison`; primary theorem specializes the same equation to the field setting | Actual `upperStar.leftDerivedTensorComparison`; the other endpoint is independently fixed on representatives by the ordinary mate and q. |
| Actual lax mu is carried to inverse delta | `internalDelta_isIso`, `internalMu`, `mu_comparison` | Uses the inverse of that actual delta, with no freely chosen tensor isomorphism. |
| Actual proper projection is the precise ringed alpha | `internalProjection`, `projection`, `projection_comparison` | Both are counit-after-delta adjoint transposes; F1 repair makes the ringed transpose use its independent canonical ringed adjunction. Valid for every f, hence every proper f; no invertibility assertion. |
| Open extension by zero agrees levelwise and after localization | `extension`, `ordinaryExtensionComparison`, `derivedExtension`, `derivedExtensionComparison` | Existing extension; comparison fixed by its ordinary adjunction mate, then localized. |
| Open adjunction, unit and counit agree | `internalOpenAdjunction`, `derivedOpenAdjunction`, `open_homEquiv` | Ringed adjunction localizes its ordinary version; the internal one uses its published adjunction and exact-pullback identification. Hom equality gives both specified units/counits. |
| Actual mu in adjoint-of-unit open projection agrees | `internalOpenProjection`, `openProjection`, `openProjection_comparison` | Both transpose unit tensor identity followed by inverse actual delta. Equation compares those particular maps. |

### New definition nodes: every construction clause

`def-pd-section-module-operations-data`, module SectionModuleOperationsData:

| Node clause | Lean checked | Finding |
| --- | --- | --- |
| Ring, internal/section categories, fixed E | `ring`, `internalModules`, `modules`, `equivalence` | Transparent aliases, retaining universe indices. |
| Actual adjunct coefficient map | `coefficientMap` | Existing unique section-normalized selector. |
| Ringed direct and inverse images and specified adjunction | `pushforward`, `pullback`, `adjunction` | Transparent existing definitions, no assertion of a comparison theorem in their types. |
| Identity-on-sections direct comparison and mate-normalized inverse comparison | `pushComparison`, `pullComparison` | Existing uniquely characterized selectors. |
| Open extension, adjunction and normalized comparison | `extension`, `openAdjunction`, `ordinaryExtensionComparison` | Existing left adjoint and fixed mate comparison. |
| Geometric direct compositor and inverse-image mate | `pushforwardComposition`, `pullbackComposition` | Existing fibre-product pasting and its mate. |
| Internal relative pure tensor | `internalPureTensor` | Alias of `comparison_internalTmul`, the sheaf tensor followed by balancing projection. |
| Section-module pure tensor | `sectionPureTensor` | Alias of `comparison_sectionTmul`, balanced section tensor followed by sheafification. |
| No duplicate notion or arbitrary choice | All 17 declarations are abbreviations | F2 repair moves the saved aliases to their own owner and adds aliases for the existing open comparison and two pure tensors. Original constructions are reused, not copied. |

`def-pd-proetale-section-module-functors`, module ProEtaleSectionModuleFunctors:

| Node clause | Lean checked | Finding |
| --- | --- | --- |
| Ordinary operations supplied by a definition | Public import SectionModuleOperationsData and its aliases | F2 repaired: the node cites def-pd-section-module-operations-data, not the two comparison theorem nodes. |
| Pure-tensor direct-image lax structures and regular unit | `InternalPushNormalized`, `PushNormalized`, their unique-existence theorems and `internalPushLax`, `pushLax` | Normalize every local pure tensor; unitor forces regular-unit coefficient map. |
| Inverse-image oplax structures are adjunction mates | `internalPullOplax`, `pullOplax` | Actual adjunction-mate constructors. |
| Strong structures from invertible scalar-extension tensor/unit formulas | Both delta/eta IsIso lemmas and `internalPullMonoidal`, `pullMonoidal` | Same oplax data; inverses multiply scalar factors. |
| Internal pullback preserves flat objects | `internalPull_preservesFlat` | Existing PreservesFlat predicate, no added flatness hypothesis. |
| Unique local tensor and scalar-unit comparisons | `ordinaryTensorComparison_existsUnique`, `ordinaryTensorComparison`, `ordinaryUnitComparison_existsUnique`, `ordinaryUnitComparison` | Same data formerly expressed using theorem-module pure-tensor constructors, now transparent aliases from their definition owner. |
| Signed direct-sum total comparison | `totalComparison_existsUnique`, `totalComparison` | Each summand and each total degree specified. |
| Additivity, exact pullback/open extension, preservation of homology | Named additive, finite-limit, finite-colimit and homology instances | Included construction prerequisites. The two existing comparison theorems are imported without public and supply proofs, not statement data. |

`def-pd-section-derived-tensor-data`, module SectionDerivedTensorData:

| Node clause | Lean checked | Finding |
| --- | --- | --- |
| Termwise E descends to D(E) | `derivedFunctor`, `derivedFunctor_isEquivalence`, `derivedEquivalence` | Actual localization functor. |
| Ringed pullback is exact localization; direct image uses K-injectives | `derivedPullback`, `section_hasKInjectiveResolutions`, `derivedPushforward` | No second functor chosen. |
| Internal derived operations retained | `comparisonSource`, `internalDerivedPullback`, `internalDerivedPushforward`, `internalDerivedExtension` | comparisonSource returns its input iso's actual source. |
| Functorial flat resolutions transfer | `section_hasFunctorialFlatResolutions` | Existing resolution property, not new resolution data from arbitrary existence. |
| Conjugate derived tensor and unit | `tensor`, `tensorUnit` | Explicit conjugation of the published internal K-flat tensor and image of its unit. |
| Equivalence-unit normalization | `tensorComparison_existsUnique`, `tensorComparison` | Full formula on every pair of derived objects. |
| Countable graded tensors and cochain totals | Both hasGradedTensor and hasCochainTotal families | Full integer grading, no bounded subcategory. |
| Triple/quadruple comparison universal properties | Both goodTensorLeft, goodTensorRight, quadrupleTensorExt families | Existing predicates specialized to the same tensor/sum construction. |
| Functor-level signed total agrees with object total | `totalTensor`, `totalTensor_obj` | Same `mapBifunctor`, not a product-total alternative. |
| Localization factors and localized ordinary total comparison | `sectionLocalizationComparison`, `localizedTotalComparison` | Existing factor iso, ordinary total map, and the named object equality transport. |

`def-pd-section-derived-realization`, module SectionDerivedRealization:

| Node clause | Lean checked | Finding or repair |
| --- | --- | --- |
| q fixed on termwise E-images, K-flat invertibility, regular unit | `TensorRepresentativeCondition`, `tensor_representatives`, `qTensor` | Full three-conjunct predicate, every image complex and either K-flat factor. |
| Canonical ringed tensor-pullback representative square | `totalPullComparison`, `TensorPullRepresentativeCondition`, `tensorPullComparison_existsUnique`, `tensorPullComparison` | Actual ordinary oplax map, signed total, q and exact localization factors all appear in the square. |
| Internal total derived operations compared canonically | `derivedPullComparison`, `derivedPushComparison` | Localized ordinary comparison and canonical derived-composition isomorphisms. |
| Ringed adjunction derived independently of internal transport | `derivedAdjunction` | F1: old node sentence 'Transport the specified internal derived adjunction along these comparisons' replaced by derivation of the ordinary ringed adjunction. `conjugatePullIso`/`conjugatePushIso` remain functor comparison isomorphisms; they no longer define this adjunction. |
| Exact sequential colimits | `section_hasExactSequentialColimits` | Same stated property; moved before derivedAdjunction to supply its construction prerequisite. |
| Localized ordinary open extension/comparison/adjunction | `extensionComparison`, `derivedExtension`, `derivedExtensionComparison`, `derivedOpenAdjunction` | Existing extension comparison alias and exact localization. |
| Internal open adjunction with right adjoint Lj* | `internalOpenAdjunction` | Published internal open adjunction with canonical exact-left-derived comparison. |
| Localized geometric pullback compositor | `derivedPullbackComposition` | Same ordinary compositor followed by canonical localization composition iso. |
| Independent site universes and unbounded complexes | Explicit universes and all `DerivedCategory`/integer-cochain binders | No restriction added. |

Edge-case recheck: the zero condensed ring and zero modules make every normalized
formula the unique zero map; empty schemes and empty open immersions remain
admissible. Identity maps and identity opens use the specified adjunctions and
pasting maps. Infinite unbounded totals remain coproducts. Nonproper f are
allowed for the projection arrow, and no projection-invertibility claim was added.
The independent adjunction construction uses the ordinary ringed adjunction even
when f is the identity; its compatibility is a theorem about specified data.
All declarations retain source/blueprint docstrings; every postponed theorem is
listed in its owning node and has a natural-language proof. The new definition
module has no theorem or sorry and no data chosen from arbitrary mere existence.

### Returned findings repaired

F1: replaced derivedAdjunction by exactly the independently derived ringed
adjunction requested by the reviewer; retained derived_homEquiv as a theorem;
projection continues to call derivedProjectionFormulaMate with that adjunction.
Corrected the new realization node sentence and clarified the main node's
canonical adjunction endpoint with the source/citer record below.

F2: SectionModuleOperationsData now owns the saved ordinary transparent aliases,
the open comparison alias and the pure-tensor aliases. Both the main item and
def-pd-proetale-section-module-functors cite its definition node. The main item's
proof_deps now include lem-sfb-internal-module-operations-transport and
lem-pe-internal-section-tensor-comparison; its first proof step records their
actual uses. Their modules are non-public proof imports of the consumer.
The former owner's lean.declarations list no longer claims the moved aliases.
Definition nodes retain empty proof and proof_deps as the new-node contract requires.

F3: replaced the former general author re-reading paragraph with the hypothesis
and conclusion matches above, including every clause of all four definition
nodes and both explicit mismatches and repairs. No second worker is invented.

## New nodes (repair addition)

def-pd-section-module-operations-data owns
Sheaf.Paper.SectionModuleOperationsData. The node records only the existing
section-ring operations, specified ordinary adjunctions and comparison selectors,
geometric composition maps, and two pure-tensor constructors. Its module moves
the delivery's transparent operation aliases out of the larger normalization
module and adds transparent aliases for the existing open comparison and pure
tensors. The original project constructions stay the definitions used everywhere.
Sources: Stacks 00YV, 03D6, 03D7, 03DI, 03DJ, 03EK and 0GMW. New LeanSearch,
LeanFinder, Mathlib grep, source/DAG grep and blueprint_refs.py searches are
recorded in the node, with their actual results: only generic Mathlib hits,
existing helper constructions in the two theorem modules, and no definition-only
DAG interface. This is the F2 repair requested in the return, not a new operation.

## Statement corrected

The original main-node statement is reproduced verbatim in
statement_change.old_statement. Its ambiguous 'including the specified derived
adjunction' did not explicitly distinguish the independent ordinary-ringed-derived
adjunction from transport of the internal adjunction. The returned realization
node and definition used transport, making the Hom comparison tautological and
providing the wrong specified projection endpoint. The clarified statement names
the canonical derived ordinary ringed adjunction and the separate definition-data
node; the intended mathematical hypotheses and conclusions are retained.
Source: literature/stacks-project/sites-cohomology.tex, Tag 07A6,
lemma-adjoint (derive the ringed module adjunction), and Tag 0B56,
equation-projection-formula-map (its precise counit-adjoint projection).
The first proof step now names the two existing ordinary comparison theorems
used in its proof, and proof_deps includes those nodes and the new definition.
The source record, original statement/dependencies/proof, and full citer audit
are in statement_change; no citer is edited.

- det-prop-p1-adjunction-rational-triangle: Holds: the canonical adjunction, projection and composition comparisons used for the projective-line triangle are preserved.
- det-thm-sf-pf-adic-projection: Holds: its proper projection and shift transport use the independently canonical ringed adjunction and the same identified counit and tensor map.
- lem-pd-condensed-open-exceptional-projection-formula: Holds: the exact open adjunction, its unit and actual inverse delta remain identified.
- lem-pd-condensed-proper-projection-formula: Holds: its actual counit-adjoint proper projection now explicitly uses the independent canonical ringed derived adjunction.
- lem-sfb-projection-section-normalization: Holds: its projection/composition normalization uses precisely the canonical ringed adjunction now made explicit.
- nt-target-poincare-isiso: Holds: the proper and open adjoint transposes in Step 2 are unchanged and use the canonical ringed operations.

The auxiliary realization node is new in this packet, so its incorrect transport
sentence is corrected directly. None of these nodes is the blueprint unit's own
statement, and no blueprint unit or target statement is modified.

## Validation of the repaired packet

All compilation uses the prescribed scompile.py wrapper and the unchanged
60-second per-file limit. The initial retained-packet dry run reported the
mechanical theorem-statement-dependency defect in F2; the definition interface
and moved declaration ownership address it. The prescribed five-module scompile.py run passed with exit code 0 and no compiler
errors or unexpected warnings. Published-name timings were 4.9, 20.5, 14.2, 20.2
and 18.1 seconds for SectionModuleOperationsData, ProEtaleSectionModuleFunctors,
SectionDerivedTensorData, SectionDerivedRealization and
ModuleRingedToposDerivedComparison, respectively. All are below 60 seconds.
The primary signature of each node matches its module verbatim, declaration
ownership is updated, all Lean lines are at most 100 characters, definition-node
citations equal stmt_deps, and the main proof_deps equals the union of step uses.
