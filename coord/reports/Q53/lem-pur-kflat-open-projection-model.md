## Worker report

This delivery states lem-pur-kflat-open-projection-model in
Sheaf.Paper.PurKFlatOpenProjectionModel. The theorem is
AlgebraicGeometry.Etale.KFlatOpenProjection.computes_coefficient_projection.
The new definition node def-pur-kflat-open-model-maps supplies the actual cochain
adjunct and the canonical localization comparison composites. Existing tensor
models are reused from def-pur-etale-kflat-support-data.
The single theorem proof is sorry. The mathematical statement is unchanged. stmt_deps gains the existing
def-pur-etale-kflat-support-data and the new definition node.

### Hypotheses and objects

- The schemes are U,P : Scheme.{u}, j : U ⟶ P, with [IsOpenImmersion j].
- The unital finite commutative coefficient rings are A,B : Type (u+1),
  [CommRing A], [CommRing B], [Finite A], [Finite B], and φ : A →+* B.
  There is no Nontrivial assumption and no flatness assumption on φ.
- The categories are DerivedCategoryModule A/B P/U, literally the ordinary
  unbounded derived categories of ModuleCat-valued sheaves on smallEtaleTopology.
  Localization ell is DerivedCategory.Q. Complexes are integer cochains.
- T_W is scalarExtension φ W; Res_W is Sheaf.derivedRestrictScalars.
  Geometric derived pullback and pushforward are the published L(upperStar ...)
  and R(lowerStar ...), with derivedUpperStarLowerStarAdjunction.
- L is an arbitrary object of DerivedCategoryModule A P.
  boundedDomain φ j L is exactly the conjunction of the five assertions that
  L, Rj_*j^*L, T_P L, T_P Rj_*j^*L, and Rj_*j^*T_P L are bounded below.
  Each assertion is ∃ n : ℤ, X.IsGE n; its bound is independent of the other four.
- I represents L via eI : DerivedCategory.Q.obj I ≅ L. Q and J are arbitrary
  A-linear cochains. hQ is the standard categorical K-flat predicate
  (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q; _hflat states flatness of
  each Q.X n via ObjectProperty.flat. These are the ordinary constant-coefficient
  presentations of the dependency notions, also used by the published FlatModel API.
- b : Q ⟶ (CochainComplex.singleFunctor _ 0).obj (scalarCoefficientSheaf φ P)
  with [QuasiIso b] is exactly the augmented K-flat coefficient resolution.
  The coefficient sheaf is the actual restricted B-unit sheaf.
- N is Q ⊗ I, the existing signed direct-sum total tensor of integer cochains.
  a : Q ⊗ I ⟶ J and [QuasiIso a] specify precisely its A-linear replacement.
  I and J need no strict B-actions and neither is assumed K-flat or K-injective.
- The two IsIso hypotheses are specifically lowerStar.rightDerivedFunctorUnitQ
  at the termwise pullbacks of I and J. Thus they are the canonical comparison
  maps of etaleDerivedChainTranspose, rather than arbitrary isomorphisms.

### Each construction and conclusion

openComplex j I is literally the termwise composite j_*j^*I; the same helper
at J defines C'. ordinaryMap is the Hom-equivalence adjunct of the ordinary
pullback tensor comparison, tensor of the actual cochain counit, its inverse
comparison, and termwise j^*a, in that order. tensorAdjunct writes this universal
formula once; it is specialized to the canonical ordinary cochain adjunction.

pullbackRepresentativeIso uses leftDerivedUpperStarIsoMapDerivedCategory and
mapDerivedCategoryFactors, retaining the localization factors. The helper
directImageIdentification uses the given invertible canonical comparison and
then derived j^*eI, exactly the identification ell C = Rj_*j^*L.

The theorem asserts the representative isomorphisms exist and, for every one,
requires equality to its displayed canonical formula. These are constrained
existentials, not arbitrary input maps or choices used to define data.
modelScalarIdentification is e_N and equals the already published
KFlatSupportComparison.tensorModel φ Q b hQ I L eI. That definition uses
localized signed symmetry, QObjTensorQObjIsoOfKFlatRight, augmentation,
eI, the general/site tensor identification and normalized scalarTensorIso.
modelTensorIdentification is this same e_N followed by scalarTensorIso.
Both replacement identifications are the inverse of this very ell(a)
followed by their respective model identification, so e_J is fixed exactly.

projectionSourceIdentification applies that same tensorModel at C with
directImageIdentification, then scalarTensorIso. scalarSourceIdentification
is sigma, by the inverse scalarTensorIso at Rj_*j^*L.
projectionTargetIdentification is alpha_J, followed under Rj_* by the inverse
pullbackRepresentativeIso, j^* of replacementTensorIdentification, and the
canonical leftDerivedUpperStarTensorIso. Thus it is pinned before scalar change.

scalarTargetNormalization is the target comparison through e_J, followed by the
canonical inverse-image/restriction isomorphism. The theorem first asserts that
scalarRestrictionDirectImageMap is invertible on the specified target. It then
asserts a unique isomorphism tau whose composite with this very comparison is
scalarTargetNormalization. This characterizes exactly the prescribed tau, using
the inverse of the canonical comparison; tau is neither an unconstrained input
nor chosen by an existence theorem to define any data.

coefficientProjection is scalarMate at j^*L followed by Rj_* of the inverse of
scalarPullbackIso. This is exactly beta with target written Rj_*j^*T_P L.
The second equation in the unique-tau clause is ell(v) ≫ tau.hom =
sigma.hom ≫ Res(beta), i.e. the node equation in Lean composition order.

The following conjunct states the full equality with
rightDerivedLowerStarProjectionMap before scalar conversion. The next conjunct
states its derived transpose as leftDerivedUpperStarTensorComparison followed
by the derived counit tensored with the coefficient identity. Thus neither the
projection-formula identification nor its precise counit formula is omitted.
The last conjunct is the naturality square for coefficientProjection for every
k : L ⟶ L' with both objects in the stated bounded-below domain. Together with
the universal representative equations, this gives the asserted naturality with
these representing identifications; it adds no claim of invertibility of beta.

### Dependency declarations used

- def-weil-pbc-scheme-conventions: this is a convention-only node. Its recorded
  leaf meanings are Mathlib Scheme and IsOpenImmersion.
- def-weil-pbc-derived-categories: WeilConjectures.AlgebraicGeometry.DerivedCategories
  reexports DerivedCategoryModule and the ordinary categories; no torsion predicate
  or constructibility condition is imposed here.
- lem-pur-sheaf-ring-derived-coefficient-adjunction:
  Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction,
  SheafOfModules.sheafRingDerivedCoefficientAdjunction, imported for the normalized
  general coefficient adjunction and its ordinary specialization scalarExtension.
- lem-pc-kflat-resolution:
  Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
  CochainComplex.exists_isKFlatResolutionIndependentCoefficients. The existing
  ordinary constant-coefficient API CochainComplex.exists_quasiIso_flat_kFlat
  and DerivedCategory.QObjTensorQObjIsoOfKFlatRight are used for the same notions.
- def-pc-tensor-complex-sheaves: Mathlib.Algebra.Homology.BifunctorShift,
  CochainComplex.mapBifunctor / HomologicalComplex.mapBifunctor, underlying ⊗
  on integer cochains, with differential sign (-1)^p and direct-sum totalization.
- lem-sp-etale-derived-chain-transpose:
  Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose,
  AlgebraicGeometry.Etale.etaleDerivedChainTranspose; its specific
  rightDerivedFunctorUnitQ comparisons and canonical adjunction are used.
- lem-pur-cochain-pullback-tensor-coherence:
  Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence,
  CategoryTheory.CochainPullback.cochainPullbackTensorCoherence.
  The ordinary constant-coefficient cochain comparison is the published
  Functor.mapCochainComplexMonoidal, induced by the identical degreewise
  ordinary pullback tensor comparison and full direct-sum totalization.
- lem-weil-pbc-kflat-fixed-tensor-triangulated:
  Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated,
  SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated. The statement
  uses the published ordinary specialization QObjTensorQObjIsoOfKFlatRight,
  which computes with an arbitrary second cochain variable without boundedness.
- lem-pur-derived-change-of-rings:
  Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings reexports the general
  coefficient construction. The already published small-etale normalized
  specialization is Sheaf.Paper.EtaleDerivedScalarTensor: scalarExtension,
  scalarCoefficientSheaf, scalarCoefficient, scalarTensorIso. No second scalar
  extension or tensor product is defined.
- lem-sbc-canonical-restrict-scalars-functor-comparisons:
  Sheaf.Paper.EtaleUnboundedRestrictionComparison,
  scalarRestrictionPullbackIso and scalarRestrictionDirectImageMap.
- lem-pur-etale-scalar-mate-projection:
  Sheaf.Paper.PurEtaleScalarMateProjection, scalarMate, scalarPullbackIso,
  scalarMate_restrict_eq_projection.
- def-kun-projection-formula-map:
  WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection,
  rightDerivedLowerStarProjectionMap, with the actual counit/tensor transpose.

The five further recorded proof-dependency modules are imported privately by
the theorem module. No dependency module is needed. The new model-map module
reuses KFlatSupportComparison.tensorAdjunct instead of copying that formula.
The existing support-data node's sourceThirdModel and targetThirdModel require
K-injective pullbacks; this item only assumes the weaker canonical-comparison
IsIso conditions, so those two constructors cannot directly serve here.

### Sources and edge cases

Read the complete 0FPI canonical counit square and its proof, the 07A4
representative construction, and 06YS in literature/stacks-project/sites-cohomology.tex.
The node proof gives the additional tensor/scalar specialization; the Stacks
counit lemma is not misrepresented as the whole projection formula.

Checked j=id, empty U, zero L, the zero coefficient ring, φ=id, and nonflat
Z/4 → Z/2. The counit is canonical even for the empty open. Zero rings are
allowed. Nonflat scalar change is handled by hQ, not by a flatness assumption
on φ. Arbitrary unbounded I,J are allowed subject precisely to the displayed
canonical-comparison and bounded-derived-object assumptions. The augmentation
need not be termwise epi. No injective-preservation assumption is used. There
is no STATEMENT-DISPUTED flag and no source-based correction.

### Searches

- msearch.py leanfinder, query: Localization of an open immersion cochain tensor
  adjunction map from a K flat coefficient resolution computes the derived
  projection formula morphism. Eight hits: ordinary scheme restriction counit,
  Proj localizations, cm5b, Tor, and ordinary projective resolutions. No match.
- msearch.py loogle, query CategoryTheory.Adjunction, DerivedCategory: zero hits.
- msearch.py grep, query projectionFormula|projection_formula|derived.*counit:
  three hits, all totalLeftDerivedCounit in Mathlib's LeftDerived.lean; no match.
- msearch.py leansearch, query: Computing a derived projection formula morphism
  from a K flat cochain coefficient resolution and a canonical chain adjunction
  transpose. Eight hits, all ordinary projective-resolution/left-derived APIs;
  none states this specified comparison.
- rg searches in lean/WeilConjectures and lean/Sheaf for the node id,
  kflatOpen, kFlatOpen, and cochain/projection combinations found no existing
  statement. The generic CochainComplex ProjectionMap and étale derived
  LowerStarProjection APIs were read and reused as ingredients, not duplicated.

### Prior dispatcher rejection

The node has no lean record or released repair note. Its NM PASS is a stage-1
proof split (the NM report explicitly says no Lean was written or compiled).
This is a first stage-2 statement delivery, rather than a second stage-1 split.
The prescribed deliver2.py wrapper is used for preflight and delivery.

### Validation

Both modules compile separately with scompile.py without errors or warnings.
The final deliver2.py --no-push passed preflight and all per-file compiles
(OK dry run, commit 73107afbeb7). Only the theorem has sorry.
Dependency traversal confirms no added path back to this item.

## New nodes

- def-pur-kflat-open-model-maps defines the actual total cochain adjunct v and
  canonical representative comparison composites for arbitrary scheme morphisms.
  Source: Stacks 07A4 and 0FPI, in sites-cohomology.tex. It reuses the published
  generic tensorAdjunct and exact-pullback/derived comparison APIs. No theorem or
  new tensor product is asserted. It applies to the arbitrary complexes with
  invertible canonical comparison required here, including non-K-injective ones.
  blueprint_refs.py search 'K-flat open tensor' found zero nodes; ancestor is None.
  DAG and Lean rg searches found support-data's generic adjunct and its
  K-injective support-sequence comparisons, reused where applicable. The actual
  cochain adjunct constructor and arbitrary-comparison composite were missing.
  msearch leansearch/leanfinder with 'Canonical open cochain tensor adjunct and
  augmented K flat fixed factor tensor representative isomorphism' gave eight
  hits each (augmentTruncate, module flat kernels, tensor summands/unitors).
  msearch grep 'kFlat.*tensor|tensor.*kFlat|tensorAdjunct' gave zero Mathlib hits.
  Loogle 'CategoryTheory.Adjunction, CategoryTheory.Iso' gave twelve generic
  adjunction-transport/yoneda hits. None supplies these canonical cochain maps.

### Elaboration and statement representation

All auxiliary isomorphisms in the theorem have explicit canonical equality
clauses. Writing them as independent specialized definitions caused expensive
proof-instance conversions; the equivalent existential equations compile within
the fixed limit. Nothing is chosen by this theorem to supply definition data.
There is no let, hidden have, arbitrary comparison hypothesis or extra K-flatness
assumption on I or J. The tensor notation in derived targets is the existing
site derivedTensor, and coefficient normalization is the existing tensorModel.
The single sorry belongs to the DAG theorem, with the full six-step proof docstring.

The human dispatcher prohibits spawning agents and supplies independent maintainer
review; no independent second-reader report is claimed by this worker.

The earlier dry runs caught overlong module-documentation lines. Both were
wrapped; the final dry run passes without warnings.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
