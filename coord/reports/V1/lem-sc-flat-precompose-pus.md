## Worker report

The theorem `AlgebraicGeometry.flat_precompose_pus` binds the cartesian qcqs affine square, both right adjunctions, and invertibility of the canonical base-change map. Its left composite is `schemeGlobalDerivedHom_pullback_comparison` followed by postcomposition with `dualityEquationBaseChangeMap` and the scalar square isomorphism. Its right composite is `schemeGlobalHomAdjunctionIso`, the global pullback comparison, inverse base-change Hom, and the inverse adjunction iso. Every hypothesis and factor is present in the Lean signature; no arbitrary comparison morphism is quantified.

`GlobalHomPullbackComparison.lean` defines `schemeGlobalDerivedHom_pullback_comparison`, `schemeGlobalScalarRestrictionCompIso`, and `schemeGlobalScalarSquareIso`. It uses `schemeDerivedTensorHomEquiv` at both schemes, the canonical tensor comparison, pullback/direct-image adjunction, and Leray. `GlobalHomAdjunctionIso.lean` replaces all four former arbitrary `Classical.choose (scheme_derivedInternalHom_adjunction _)` terms by the pinned family. Its comparison theorem is documented as the fixed-data form of `exists_derivedDirectImage_internalHom_comparison`.

## Dependency modules

The dependency `lem-pc-global-hom-adjunction` is delivered through `GlobalHomAdjunctionIso.lean`. `CanonicalDerivedTensorHom.lean` imports `DerivedInternalHom`, `CanonicalPullbackTensorComparison`, and the upstream sheaf `MonoidalClosed` module. It defines `IsCanonicalDerivedTensorHom`, with the naturality equation and K-flat/K-injective representative clause, then the named existence and uniqueness theorem sorries and `schemeDerivedTensorHomEquiv`. The two global Hom modules import this module and use its declaration.

## New nodes

`def-pc-canonical-derived-tensor-hom-bijection` adds the pinned canonical tensor/internal-Hom family. `def-pc-global-hom-pullback-comparison` remains the explicit global pullback comparison definition and imports the pinned family. The family is characterized by naturality and representative evaluation using the total-complex Hom-tensor model and pullback tensor model map; its existence and uniqueness are named theorem statements. This prevents independent choices at the schemes appearing in the global Hom comparisons.

Edge cases checked include zero complexes and morphisms, arbitrary unbounded complexes, and empty schemes; no finiteness, flatness, perfectness, boundedness, or Noetherian assumptions were added. Searches (`leansearch`, `loogle`, `grep`, and `rg`) found no existing pinned family in Mathlib or the project.

## Second reading by V1

I read the item's node, its three proof steps, the source's surrounding base-change
construction and final compatibility diagram in duality.tex, lemma-more-base-change
(Tag 0AA8), and lemma-iso-global-hom (Tag 0B6I). I also read cohomology.tex,
lemma-internal-hom (08DJ), including its representative construction. The final
compatibility is the categorical identity used in the proper/perfect argument:
properness, perfectness of the generator, flatness and finiteness are used there
for invertibility, whereas this node assumes invertibility of beta directly.
They are not additional hypotheses of this compatibility identity.

Objects, hypotheses and conclusions checked individually:

- The schemes X,Y,Y' and cartesian X' are `{X Y Y' : Scheme.{uMain}}` and
  `pullback f g`; its projections are `pullback.fst f g` and `pullback.snd f g`.
  Verdict: the chosen universal fibre product of def-pc-fibre-product, with the
  correct horizontal/vertical maps, not an arbitrary commutative square.
- All schemes are qcqs. The three input schemes have `CompactSpace` and
  `QuasiSeparatedSpace`. The fourth inherits them by base change: g is affine
  because Y,Y' are affine, and f is qcqs between qcqs schemes. The instance passed
  explicitly for X' is `quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)`.
  Verdict: matches; qcqs properties of the morphisms follow from these schemes.
- Y=Spec(A), Y'=Spec(A') are `[IsAffine Y] [IsAffine Y']`. A and A' are their
  rings of global functions, used by `schemeGlobalScalarRestriction g`.
  Verdict: equivalent affine encoding, including the zero ring/empty affine scheme.
- f and g are `(f : X ⟶ Y) (g : Y' ⟶ Y)`; a and a' are functors between the
  shared `schemeDerivedQCohCategory` categories, with `adjf` and `adjf'` for the
  lifted `schemeDerivedDirectImage` functors. Verdict: the specified right
  adjoints, without an arbitrary Hom isomorphism input.
- The canonical beta is `schemeDerivedBaseChangeMap f (pullback.snd f g) g
  (pullback.fst f g) pullback.condition`. `hβ` requires its invertibility for
  every E in D_QCoh(X). Verdict: precisely the transformation-level assumption.
- M and K are `(M : schemeDerivedQCohCategory X)` and
  `(K : schemeDerivedQCohCategory Y)`. Verdict: arbitrary unbounded quasi-coherent
  derived objects; no perfectness or boundedness restriction.
- c is `(dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom`.
  I opened its definition: it uses pullback of a(unit), inverse conjugate of beta,
  and the pullback counit. Verdict: the exact dependency map, not a replacement.
- Global Hom is the dependency's `schemeGlobalDerivedHom`, i.e. derived global
  sections of the recorded `derivedInternalHom`. Verdict: global Hom with the
  correct module scalars, not sheaf Hom or an underlying Hom set.
- The first composite uses `schemeGlobalDerivedHom_pullback_comparison` for g_X,
  then `schemeGlobalDerivedHom.map` in the second entry with c. The outer
  `schemeGlobalScalarRestriction f` and `schemeGlobalScalarSquareIso` identify
  its A-action and final target. Verdict: the transpose of exactly the first
  A'-linear map in the node.
- The second composite uses `(schemeGlobalHomAdjunctionIso f a adjf M K).hom`,
  the same pullback comparison for g, `schemeGlobalDerivedHom.map` in the first
  entry with `(inv (schemeDerivedBaseChangeMap ... M.obj)).op`, then the inverse
  Hom adjunction iso for f'. Verdict: all four factors, in the required order;
  contravariance explains the inverse beta direction.
- The conclusion is equality of these A-linear transposes. The node's maps out
  of E tensor_A^L A' are specified as the extensions of precisely these maps.
  Extension/restriction adjunction gives a bijection of morphisms, so this
  encoding is equivalent to equality in D(A'); it is not an assertion obtained
  by merely forgetting A'-linearity. Verdict: neither weakened nor strengthened.

Dependency and definition review:

I opened the recorded declarations of schemeDerivedCategory (including the
quasi-coherent full subcategory), schemeDerivedDirectImage, derivedPullback,
schemeGlobalDerivedHom, dualityEquationBaseChangeMap and schemeDerivedBaseChangeMap.
Their signatures and carriers agree with the objects above. I also read
DerivedInternalHomAdjunction, DerivedInternalHom, HomComplex, HomTensorTotal,
CanonicalPullbackTensorComparison and the upstream sheaf tensorHomEquiv, and
checked every delivered module and both new node records.

`lem-pc-global-hom-adjunction` previously supplied only `Nonempty` of an
isomorphism. Its actual declaration is not usable for naming the counit-induced
map in a compatibility equation: its signature does not constrain which
isomorphism is selected. The dependency module supplies that fixed map, an
invertibility/naturality theorem, and its iso. Its Leray comparison is pinned by
identity on underived sections and compatibility with derived units. Its
pullback adjunction is the same choice used by the base-change dependency, and
its tensor comparison satisfies the existing canonical representative predicate.
I read its evaluation-mate equation against the already landed
exists_derivedDirectImage_internalHom_comparison: it is the fixed-data form,
not a competing definition of derived internal Hom.

`def-pc-global-hom-pullback-comparison` is the evaluation mate after canonical
pullback tensor identification, followed by global sections and Leray. Its
scalar composition/square isos use the actual restrictScalarsComp' comparison.
This matches its source and node; there is no arbitrary comparison parameter.

The earlier `def-pc-canonical-derived-tensor-hom-bijection` module did NOT say
what its new node claimed. Its supposed representative condition was merely
`φflat = φflat ∧ φ = φ ∧ hP = hP`, independent of e. Naturality alone allows,
for example, the negative of the intended bijection and cannot justify the
uniqueness theorem. I replaced the entire vacuous clause with componentwise
uncurrying on every total-tensor summand and the localization equation
`e(Qφ ; j⁻¹) = μ ; Qψ ; (Qη)⁻¹`. Here j is exactly Localization.fac for the
recorded derivedInternalHom model, η is the existing functorial K-injective
replacement, μ is the existing pullbackTensorModelMap, and ψ is fixed on every
summand by the existing Hom-complex projections and sheaf tensorHomEquiv.
The scheme resolution helpers only supply the known Grothendieck instance to
existing constructions. They introduce no second resolution or internal Hom.
I made the new node self-contained with this equation and its dependencies,
and added the missing module/declaration source docstrings and the existence
and uniqueness proof descriptions. All new node field requirements were read;
its chapter, unit, ancestor/via, created and lean_audit records were retained.
The main item and the global comparison composites were not rewritten.

Edge cases: zero M/K and zero maps are included; no Nonempty hypothesis is used.
Empty schemes (including empty affine bases/zero global rings) are allowed.
Complexes are indexed by all integers, including degree zero and negative degrees;
no boundedness hypothesis excludes them. No field or characteristic hypothesis
occurs. uMain/wMain and uCD/wCD are explicitly bound and polymorphic; the
HasDerivedCategory assumptions supply the shared localization model, not
Noetherian, finite-dimensional or other geometric assumptions. There is no
index-family restriction. The K-flat condition in the new characterization
is on the first resolution representative only, not extra hypotheses on the item's M/K.

Independent searches: LeanFinder query "canonical derived tensor internal Hom
evaluation on complexes" returned eight generic hits (tensorHom of complexes,
ModuleCat evaluation, etc.), none the pinned scheme family. Loogle query
`"derivedInternalHom"` returned zero hits. LeanSearch query "canonical tensor Hom
adjunction in derived category of sheaves" returned HTTP Internal Server Error;
I record this as unavailable, not a negative search. I searched by rg for tensor/Hom,
evaluation and the exact declared names in Mathlib, WeilConjectures and lean/Sheaf,
and for canonical tensor/Hom in dag/nodes. The existing scheme adjunction is
existential with a naturality clause only; it does not pin its family on the
representative evaluation, so cannot replace the new characterization. The
existing generic direct-image comparison similarly existentially chooses its
adjunction/tensor data. No exact existing item theorem or usable pinned family
was found. The two existing notions are reused through their real declarations.

No hollow data definition remains: chosen data come from named existence
statements, and representative helpers use existing constructions. Every theorem
proof remains sorry. No item statement correction was made and no citer changed.

Validation: all four delivery modules compiled together locally in dependency
order, exit code 0, with no errors or warnings (54.9 seconds). All signatures
were regenerated verbatim from the files using the project's declaration reader;
all universes/binders and the 100-character line limit were checked.

The prior return was also read. The representative condition now quantifies over
an arbitrary L, as requested there. The fixed functorial I(M) and its actual
localization factorization avoid choosing an arbitrary isomorphism for a
K-injective target. The condition for this fixed resolution determines the same
family as the condition for every K-injective representative: compare any such
representative to the functorial resolution and use naturality. The obsolete
"Earlier second reading" section was removed.

For the dependency module, the following individual declarations were checked.
`schemeGlobalScalarRestriction` is the existing exact restrictScalars functor
lifted to derived categories. `exists_schemeGlobalSectionsDirectImageIso` states
identity on sections and derived-unit compatibility, fixing the Leray map.
`schemeGlobalSectionsDirectImageIso` selects that pinned derived iso.
`schemeHomPullbackAdjunction` selects the same adjunction as beta's definition.
`exists_schemeHomTensorPullbackIso` states invertibility of the already pinned
pullback tensor comparison, with its representative predicate.
`schemeHomTensorPullbackIso` selects that characterized tensor iso.
`exists_schemeHomDirectImageComparison` fixes the comparison by its equation
against every test morphism, using the shared adjunction, tensor iso and tensor-Hom
family. `schemeGlobalHomDirectImageMap` applies derived global sections and the
inverse Leray map to that comparison. `schemeGlobalHomAdjunctionMap` follows it
by Hom of the right-adjoint counit. `schemeGlobalHomAdjunctionMap_isIso` asserts
invertibility and naturality, with the source's coherator/global-sections proof.
`schemeGlobalHomAdjunctionIso` forms asIso using that theorem. No declaration
uses an arbitrary additional hypothesis or an independently chosen Hom iso.

I removed the now-unused imports of GlobalHomAdjunction and
DerivedInternalHomAdjunction from the dependency module, importing its actual
global-Hom and qcqs-direct-image dependencies explicitly instead.

The required delivery dry run printed OK: all four modules passed the server
compile and the full stage-2 preflight; no warning other than sorry was emitted.
The initially reported preflight metadata faults were repaired (standalone
citations and an explicit unavailable-search status).
