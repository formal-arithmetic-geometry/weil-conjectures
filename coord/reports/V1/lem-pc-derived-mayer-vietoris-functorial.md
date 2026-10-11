## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` states two theorems,
`AlgebraicGeometry.schemeDerived_mayerVietoris_naturality` and
`AlgebraicGeometry.schemeDerived_mayerVietoris_directImage`, for clauses (1) and (2).
Both proofs are `sorry`; no new definition or axiom is introduced. The file compiles
cleanly on the server. No statement correction or new/dependency node is delivered.

Source read: Stacks Project, Lemma 20.33.2, Tag 08BV
(https://stacks.math.columbia.edu/tag/08BV), especially its K-injective construction
and degreewise short exact sequence. The local Stacks source directory is absent on
this machine, so this source was read online. The node's three proof steps are
reproduced in the declaration docstrings, including comparison with a K-injective
replacement of h_*I' and naturality of the short-exact-sequence boundary. The QCoh
and qcqs restrictions are those of this DAG node, rather than extra restrictions
on the ringed-space lemma.

Hypotheses and clauses:

- W is the `X : Scheme.{u}` of the naturality theorem, with `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`. Its cover is `U V : X.Opens`, with `hU`, `hV` stating
  compactness of the underlying subsets, and `hcover : U ⊔ V = ⊤`. These are precisely
  quasi-compact opens covering the qcqs scheme.
- Open inclusions are the existing `U.ι`, `V.ι`, `(U ⊓ V).ι`. Restriction is the
  existing `(schemeOpenRestriction X T).mapDerivedCategory`. Derived direct image
  is the existing `schemeDerivedDirectImage T.ι`.
- Membership E,F in D_QCoh is `schemeDerivedQCohProperty X E` and the analogous
  hypothesis for F. All derived objects are in `schemeDerivedCategory X`, the
  ambient category of O_X-module complexes; the full subcategory is full, so its
  morphisms are exactly `φ : E ⟶ F` under these membership hypotheses.
- The first map in each `Triangle.mk` is
  `biprod.lift (adjU.unit.app E) (adjV.unit.app E)`; the second is the biproduct
  descent of `schemeDerivedOpenDirectImageRestriction` and the negative of the
  V restriction. Thus the maps are the pair of units and the difference of
  restrictions, with the sign as in the node.
- The triangle's third term is the intersection direct image, and its boundary
  is `δ E : RjUV_*(E|UV) ⟶ E⟦(1 : ℤ)⟧`. The adjunctions and boundary family are
  existentially chosen together, following the existential interface of
  `schemeDerived_mayerVietoris_triangle`. The K-injective/short-exact construction
  in the node describes how to obtain these choices; it is reproduced in the
  proof docstring, and is not an additional assumption on E.
- For every E,F in D_QCoh and every φ, the conclusion provides a morphism `m`
  between the displayed distinguished triangles. Its three components are fixed
  by `m.hom₁ = φ`, the biproduct of the two restricted/direct-imaged maps, and the
  intersection restricted/direct-imaged map. `TriangleMorphism.comm₃` is exactly
  `δ E ≫ φ⟦1⟧' = RjUV_*(φ|UV) ≫ δ F`; its other two fields give the other squares.
- In the second theorem W' is X and W is Y. Both have compactness and
  quasi-separatedness instances. The binder `h : X ⟶ Y` has `[QuasiCompact h]`
  and `[QuasiSeparated h]`. U,V are compact opens in Y with the same cover equation.
  Their inverse images are literally `h ⁻¹ᵁ U` and `h ⁻¹ᵁ V`, with `hU'` and `hV'`
  giving the compactness assumed by the node. Their cover follows from hcover.
- `HasDerivedCategory.{w}` binders specify the shared localization for each
  category. In the direct-image theorem the open-category binders are families
  over opens, to ensure that the syntactically different intersection opens
  `h ⁻¹ᵁ (U ⊓ V)` and `(h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)` use the same localization. This is
  derived-category infrastructure, not a geometric hypothesis or a different
  carrier. No custom Abelian instance is installed.
- The target and source boundary families in clause (2) are chosen before E,
  and each satisfies the explicit shifted naturality equation on all D_QCoh
  morphisms. Then E is universally quantified with its QCoh hypothesis.
- The conclusion explicitly includes QCoh of `(schemeDerivedDirectImage h).obj E`,
  distinguishedness of both MV triangles, and distinguishedness of the source
  triangle after `(schemeDerivedDirectImage h).mapTriangle`.
- For each of U,V,UV, `aU`/`bU` (and their V/UV counterparts) have exactly the
  composition-comparison signatures of `derivedDirectImageComposition`, and
  `rU` (etc.) has the open-restriction comparison signature of
  `schemeDerivedDirectImage_openRestriction`. They are natural functor
  isomorphisms, not unconstrained object maps. Equations for `cU.hom`, `cV.hom`,
  and `cUV.hom` require the term isomorphisms to be the composite of these
  comparisons, transported along `morphismRestrict_ι`. Thus both isomorphisms
  in the node's displayed chain of comparisons occur explicitly.
- The resulting triangle isomorphism e has `e.hom.hom₁ = 𝟙 (Rh_*E)`;
  `e.hom.hom₂` is the lift of `Rh_*(biprod.fst) ≫ cU.hom` and
  `Rh_*(biprod.snd) ≫ cV.hom`, incorporating the finite-biproduct comparison;
  `e.hom.hom₃ = cUV.hom`. Its `comm₃` includes the shift comparison of Rh_* and
  gives exactly compatibility of Rh_*(δ') with δ. The shift and triangulated
  structures come from the existing right-derived-functor instances.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`;
  `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict_ι` and open inclusions.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`; these fix the ambient and QCoh carriers.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`:
  `schemeDerived_mayerVietoris_triangle`; the exact three terms and two maps are reused.
- Its imported `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `schemeOpenRestriction`, `schemeDerivedOpenDirectImageRestriction`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`:
  `DerivedCategory.triangleOfSESδ`, `triangleOfSES`, `triangleOfSES_distinguished`,
  `triangleOfSESδ_naturality`, and `triangleOfSES.map`, read for the resolution-level
  proof construction; no second boundary definition is introduced.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`;
  `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`: `kInjective_of_restrict_open`;
  `Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`:
  `injective_restriction_surjective`. These three recorded statements are the
  resolution construction, restriction, and exactness inputs in the docstrings.
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`:
  `schemeDerivedDirectImage_preserves_QCoh`; its exact conclusion is included.
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`:
  `derivedDirectImageComposition`; its isomorphism types are used for aT,bT.
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`:
  `schemeDerivedDirectImage_openRestriction`; its natural isomorphism type is
  reused for rT through the shared restriction abbreviation.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`:
  the existing `CommShift ℤ` and `IsTriangulated` instances on `rightDerivedFunctor`.
  This is the recorded source module of lem-pc-right-derived-functor-triangulated.

Edge cases checked before writing: the empty scheme and empty open, either open
being the whole scheme, repeated opens U=V, and empty intersection remain permitted.
The difference sign in the second map is retained even for U=V. Zero objects,
zero morphisms and identity morphisms are admitted; identities give the expected
boundary equation. No cohomological boundedness, field, characteristic, or
nonempty-space assumption is added. Universes u,w are explicitly declared; all
objects, opens, morphisms and variables are explicitly bound with autoImplicit off.

Searches performed:

- msearch LeanFinder: `functorial Mayer Vietoris distinguished triangle derived
  direct image schemes`: eight hits, all generic site MayerVietorisSquare facts;
  none states the scheme derived triangle naturality.
- msearch Loogle: `Triangle, Functor.mapTriangle`: no hit, unknown identifier Triangle.
- msearch LeanSearch: `Mayer Vietoris triangle naturality derived category`:
  unavailable, HTTP Internal Server Error; not recorded as a negative search.
- msearch grep: `MayerVietoris|mayerVietoris`, AlgebraicGeometry: no hits.
- rg in source WeilConjectures for the item id and MayerVietoris: only the adic
  pro-etale MayerVietoris module and related imports, with different carriers.
- rg in project Lean for derivedMayer/mayerVietoris/MayerVietoris: the existing
  triangle theorem and the derived Hom Mayer--Vietoris material, neither of which
  states either functoriality clause. Read their definitions rather than copying them.
- Read Mathlib's `DerivedCategory/ShortExact.lean`: generic SES naturality is
  already available, but not this scheme/direct-image specialization.

No counterexample or mathematical statement fault was found. The use of existential
compatible comparison witnesses follows the dependency declarations, which state
existence of the canonical natural comparisons rather than naming a chosen one.
The independent second reader should in particular check this choice-based
presentation against the node's canonical-comparison wording.


## Second reading by V1

I read the node, both theorem signatures, and the recorded dependency declarations
independently of the worker. The node has no statement correction. This delivery has
no new definition node and no dependency module, so H12/H13 introduce no additional
objects to review. The mathematical statement and DAG dependencies stay as on the base.

Source reading: the local literature checkout lacks the Stacks `.tex` files. I read
Stacks' upstream `cohomology.tex` and `perfect.tex`, saving read-only source material
in the sandbox scratchpad, and checked the published tags as well:
[08BV](https://stacks.math.columbia.edu/tag/08BV),
[0D5T](https://stacks.math.columbia.edu/tag/0D5T),
[08FE](https://stacks.math.columbia.edu/tag/08FE), and
[0DJ9](https://stacks.math.columbia.edu/tag/0DJ9).
In the TeX these are `lemma-exact-sequence-j-star`,
`lemma-derived-pushforward-composition`, `lemma-restrict-direct-image-open`,
and the induction step of `lemma-single-complex-base-change`.
08BV assumes a ringed space and a two-open cover, with no boundedness or
nonemptiness condition. It chooses K-injective representatives with injective
terms and attaches the SES boundary to their direct-image sequence. The schemes,
QCoh membership, and qcqs assumptions here are precisely the node's specialization.
0D5T and 08FE assume arbitrary ringed-space morphisms; neither adds a finiteness
condition to the comparison. 0DJ9 uses the resulting relative triangles in a
qcqs induction. Its base-change hypotheses belong to the application, not to
this functoriality lemma.

The node's object/hypothesis/conclusion list, with its Lean rendering and verdict:

1. W is a qcqs scheme. The first theorem has `X : Scheme.{u}`,
   `[CompactSpace X]`, `[QuasiSeparatedSpace X]`. Correct: quasi-compactness here
   is compactness without Hausdorffness. No field, Noetherian, separated, or
   finite-dimensional hypothesis has been inserted.
2. U,V are quasi-compact opens covering W. `U V : X.Opens`,
   `hU : IsCompact (U : Set X)`, `hV`, and `hcover : U ⊔ V = ⊤` express exactly
   these conditions. The immersions are `U.ι`, `V.ι`, `(U ⊓ V).ι`. Correct.
3. E,F are in D_QCoh(O_W), with every derived morphism φ:E→F admitted.
   `schemeDerivedCategory X` and `schemeDerivedQCohProperty X E/F` use the
   dependency's actual sheaf-of-modules localization and cohomology property.
   `φ : E ⟶ F` has precisely the full subcategory's morphisms. Correct.
4. MV has E as first term, the biproduct of the U,V derived direct images as
   second term, the intersection direct image as third term, and a map into
   E[1]. The displayed `Triangle.mk`, the types of `δ`, and the
   `distTriang (schemeDerivedCategory X)` membership express these terms and
   distinguishedness. The maps are `biprod.lift` of the units and `biprod.desc`
   of restriction from U minus restriction from V. Correct, including the sign.
   QCoh of the local direct-image terms is the existing triangle dependency's
   conclusion; the ambient category is the same full-subcategory carrier.
5. The construction chooses representatives with injective terms, restricts
   K-injectives, and attaches the natural SES boundary. These are construction
   steps, not extra hypotheses on E. The theorem existentially chooses the
   adjunctions and boundary family, as does the recorded triangle dependency,
   then requires distinguishedness and naturality. Its proof docstring gives
   all the resolution/exactness steps and cites the appropriate nodes. Correct
   with the dependency's choice-based interface; no second boundary is defined.
6. Clause (1) specifies all three components of the triangle morphism.
   `m.hom₁ = φ`, `m.hom₂ = biprod.map (...) (...)`, and the `m.hom₃` equation
   specify exactly the triple in the node. `TriangleMorphism.comm₃` is the
   boundary equation `δ E ≫ φ⟦1⟧' = RjUV_*(φ|UV) ≫ δ F`; comm₁ and comm₂
   supply the other squares. Correct. The boundary family is chosen before
   quantifying E,F,φ, so this is simultaneous naturality.
7. Clause (2) introduces h:W'→W with qcqs source and target, h qcqs, and
   quasi-compact inverse-image opens. In the second theorem W'=X, W=Y,
   `h : X ⟶ Y`, the four compactness/quasi-separatedness space instances,
   `[QuasiCompact h]`, `[QuasiSeparated h]`, `hU`, `hV`, `hcover`, `hU'`, `hV'`
   are exactly those assumptions. `h ⁻¹ᵁ U/V` are literally the inverse-image
   opens. Their covering condition follows by inverse image from hcover and is
   not imposed as an extra hypothesis. Correct.
8. E' ranges over all of D_QCoh(O_W'), and Rh_*E' belongs to D_QCoh(O_W).
   `∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E → ...`
   and `schemeDerivedQCohProperty Y ((schemeDerivedDirectImage h).obj E)`
   express both statements. Correct; membership of the image is a conclusion.
9. The source MV triangle, its Rh_* image, and the target MV triangle are
   distinguished. The three explicit `distTriang` conjuncts express each of
   these with the same source and target boundary families. Correct.
10. For each T=U,V,U∩V there is the two-step natural comparison from
    Rh_*RjT'_* to RjT_*RhT'_* and then to RjT_* restriction of Rh_*.
    The `aT` and `bT` functor isomorphism types are those of
    `derivedDirectImageComposition`. `rT` has exactly the open-restriction
    theorem's type, with `schemeOpenRestriction` unfolding to its explicit
    `overFunctor ⋙ overEquiv` term. The equations for `cT.hom` compose
    `aT.symm`, transport by `morphismRestrict_ι`, `bT`, and `RjT_*(rT.inv)`.
    The inverse-image-intersection and intersection-of-inverse-images opens
    agree definitionally. Correct after the quantifier repair below.
11. The component isomorphisms and the identity of Rh_*E' form a triangle
    isomorphism including the boundary. `e`, `e.hom.hom₁ = 𝟙 (...)`,
    `e.hom.hom₂ = biprod.lift (Rh_*(biprod.fst) ≫ cU.hom)
    (Rh_*(biprod.snd) ≫ cV.hom)`, and `e.hom.hom₃ = cUV.hom`
    fix precisely these components. `e.hom.comm₃` includes Rh_*'s canonical
    shift comparison and gives compatibility with Rh_*(δ') and δ. Correct.
12. Universes and category infrastructure: u,w are explicitly declared;
    `HasDerivedCategory.{w}` supplies the chosen localization of each module
    category. The second theorem supplies it as a family over opens, keeping
    definitional equal inverse-image opens on the same instance. These are
    infrastructure choices, not boundedness or geometric hypotheses. A common
    universe accommodates arbitrary schemes by enlargement; no small-index or
    low-universe test-algebra restriction occurs. No variable is auto-implicit.

Mismatch found and repaired: the nine comparison functor isomorphisms
`aU,bU,rU,aV,bV,rV,aUV,bUV,rUV` were existentially quantified *after* the
universally quantified object E. Although each witness was a natural functor
isomorphism, the old statement allowed a different such witness for each E.
The node's functorial comparisons must work uniformly for every E. I moved
those nine binders to the outer existential before E, leaving `cU,cV,cUV,e`
objectwise. Their component equations now evaluate one fixed set of natural
comparisons at every object. This also makes the component comparisons natural:
all expressions are components of the same composites of natural isomorphisms.
The dependency records provide the comparisons existentially, rather than a
named normalized choice; this theorem likewise chooses compatible comparisons
jointly, with the prescribed compositions and all three triangle squares.
It does not claim compatibility for arbitrary independently chosen isomorphisms.
I added a docstring sentence explaining the quantifier order and updated the
record's date/note. The primary signature is unchanged and was compared exactly
with `tools/stage2_delivery.py signature`; both declarations remain listed.

I opened all statement dependency declarations, including Scheme/Hom in pinned
Mathlib, DerivedCategory/QCoh, SchemeDerivedDirectImage and its ringed-space
right-derived construction, the existing MV triangle and shared restriction
maps, generic `triangleOfSESδ` and its naturality/map declarations, the small-site
functorial K-injective theorem, open K-injective restriction, injective section
surjectivity, QCoh preservation, and both comparison modules. I also read the
upstream right-derived triangulated instances. No declaration with merely a
similar name was substituted for a dependency; in particular restriction uses
`schemeOpenRestriction`, not a new pullback or a private carrier.

Edge cases: the empty scheme is allowed, with both opens empty; an empty member
of a nonempty cover forces the other to be top and is allowed. Disjoint opens,
empty intersection, U=V=top, and either open equal to top are allowed. The
negative V restriction remains even for repeated opens. The zero complex, zero
morphism, identities, and shifts in every integer degree are admitted. There
is no parameter n requiring n>0, no characteristic or field parameter, no
nonempty index set, and no boundedness assumption.

Independent H4 searches (different wording from the worker):

- LeanFinder through msearch: `naturality boundary morphism open cover derived
  category pushforward` returned eight generic gluing/MayerVietorisSquare hits,
  with no scheme-derived functoriality statement.
- Loogle through msearch: `"triangleOfSES"` returned the existing generic
  SES triangle, boundary, distinguishedness, and triangle-map declarations.
  I opened their implementation. They are the correct generic input, not this
  open-cover/direct-image specialization.
- LeanSearch through msearch: `open cover derived direct image triangle
  functoriality` was unavailable (Internal Server Error); this is not evidence
  of absence. LeanFinder and Loogle searches succeeded.
- rg across project Lean, upstream WeilConjectures, and pinned Mathlib homology
  and category theory for Mayer--Vietoris and SES-boundary naturality found
  generic SES facts and site sheaf-cohomology sequences, the project's existing
  MV triangle and derived Hom exactness, and upstream adic/pro-etale material.
  I opened `derived_hom_mayer_vietoris`, the extension-by-zero MV triangle, and
  the adic MayerVietoris declarations. They have different conclusions or
  coefficient categories; none realizes either clause of this item. The
  primary/secondary names are not declared elsewhere in these sources.

H5/H6/H8/H9: the delivery adds no definition, abbreviation, instance, axiom,
private copy, local notation, or proof. Both theorem proofs remain `by sorry`.
Both docstrings name the source and exact blueprint id and give the node's
three proof steps (the first step is expanded into construction and morphism
naturality). All imports contribute used structures/terms; line lengths stay
within 100 characters. The repaired module compiled cleanly through scompile,
with no errors or warnings. The delivery dry run and final push are performed
by deliver2 after this reading.
