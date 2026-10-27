## Worker report

The module `Sheaf.CategoryTheory.InternalModuleInverseImageComparison` states
`CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison`.
It also supplies the canonical-structure and normalization helpers needed to express
all clauses of this node. The only postponed proofs are the named theorems
`directLax_existsUnique`, `inverseBraided_existsUnique`, and
`internalModuleInverseImageComparison`. Each has this node's blueprint tag, its
source, and its complete corresponding proof in the docstring. All definitions
have real data. Both structure choices use existence AND uniqueness; the tensor
maps are determined by the universal pairings, and the inverse strong structure
is determined by its actual oplax mate. No object is chosen from bare Nonempty.

NJ's reviewed stage-1 split is retained verbatim. The earlier worker's message
about a superseded split does not obstruct this stage-2 statement: the current
node is split and reviewed, but has no Lean record. No second split is attempted.

Hypotheses and input objects, individually:

* The two sites are `C : Type uC`, `[Category.{vC} C]`, `J : GrothendieckTopology C`
  and the independently sized `D`, `K`. The bounds
  `[UnivLE.{max uC vC, u}]`, `[UnivLE.{max uD vD, u}]` express precisely that the
  sites are small in the common coefficient universe. No universe equality is
  imposed. As in the recorded site convention, the sheaf categories use Mathlib's
  Grothendieck-topology presentation of the sites.
* Abelian sheafification and monoidality of local equivalences are exactly
  `[HasSheafify J AddCommGrpCat.{u}]`, `[(J.W (A := AddCommGrpCat.{u})).IsMonoidal]`,
  and their K counterparts. `Sheaf.monoidalCategory` and `Sheaf.braidedCategory`
  are registered globally, using the existing localized tensor. This is the
  same monoidal structure returned by `sfbSheafTensorStructure`; no tensor is
  redefined.
* The geometric morphism is
  `f : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u))`, with its specified
  adjunction and left-exact inverse. It is not restricted to site-induced maps.
* `A : AbelianInverseImagePresentation f.inverse` and
  `B : AbelianInverseImagePresentation f.direct` render the specified induced
  finite-product lifts on algebraic operations. Their fields fix the underlying
  sheaf functors naturally and transport addition and zero on every generalized
  section. Additive inverses follow from those operations.
* `adj : A.functor ⊣ B.functor` and `unit_eq` specify the induced lifted
  adjunction, including the underlying set-unit normalization of the recorded
  Mathlib `Adjunction.mapCommGrp` construction. They are the presentation of
  the chosen induced adjunction in the node, not an arbitrary new adjunction
  assumption. The lifted adjunction exists by the node's recorded
  `lem-weil-pbc-adjunction-lifts-abelian-group-objects` (Mathlib mapCommGrp).
  The unit compatibility is essential to forbid twisting that adjunction while
  keeping the set-level identifications fixed.
* `R : Sheaf J AddCommGrpCat.{u}`, `[MonObj R]`, `[IsCommMonObj R]` is the
  commutative tensor-ring object. With the constructed braided inverse lift,
  scoped `Functor.monObjObj` gives its transported ring `A.functor.obj R` and
  its commutative-monoid instance.
* `RI` and
  `I : SheafOfModules.AlgebraicInverseImageOfUniverses f.inverse
    (InternalAbelianSheafModule.sectionRingSheaf J R) RI`
  use the dependency's RECORDED interface for the finite-product algebraic
  inverse image. The assertion applies to every presentation of that same
  inverse image, including the identity presentation. There is no assumed
  comparison of I with mapMod.

Conclusions, individually:

* `tensorSection` is the actual universal bilinear pairing on sections: the
  existing inclusion tensorator applied to `x ⊗ₜ[ℤ] y`. `integerOne` uses the
  existing inclusion unit applied to `ULift.up 1`. In particular these are
  the generators for the sheafified tensor and sheafified integer unit.
* `TensorNormalization J K L A q` requires preservation of the graph of that
  pairing for every test sheaf T and every pair of arrows a,b from T. Taking T
  to be the product of the operand sheaves and a,b its projections gives exactly
  `mu p = L(p) lambda^{-1}`. Its second conjunct, tested on the terminal sheaf,
  is the integer-1 normalization. The quantification over T avoids the false
  assertion that every section of a tensor sheaf is globally a pure tensor.
* `directLax_existsUnique` and `directLax` specify the canonical right lax
  structure by exactly that normalization. `inverseOplax` is literally
  `adj.leftAdjointOplaxMonoidal` with that right lax structure. The main theorem's
  first equality identifies the constructed strong structure's oplax part with
  that mate. Thus a different strong monoidal structure cannot be substituted.
* `inverseBraided_existsUnique` proves existence and uniqueness of the inverse
  strong structure, including the pairing and unit normalization. Its proof
  is the reviewed node's steps 2 and 3: SET-adjunction injectivity first proves
  `d L(p) = p lambda` and `d0 L(1) = 1 lambda_*`; the bilinear and integer universal
  properties construct and identify the two-sided inverses. Invertibility is
  a conclusion, not an added assumption. The main theorem's second conjunct
  states the pairing/unit normalization for the chosen structure explicitly.
* `ComparisonStatement` gives `σ : sectionRingSheaf K (A.functor.obj R) ≅ RI`.
  Its displayed equality on every object V and every section r says σ is the
  canonical underlying inverse-image comparison. Being a ring-sheaf isomorphism,
  it intertwines addition, zero, multiplication and one. The equality fixes both
  directions of the isomorphism and makes it identity under those identifications.
* The natural isomorphism θ has source
  `A.functor.mapMod R ⋙ (sectionModuleEquivalence K (A.functor.obj R)).functor`
  and target
  `(sectionModuleEquivalence J R).functor ⋙ I.modules ⋙ restrictScalars σ.hom`
  (with the existing ring-sheaf forgetful functor applied to σ.hom).
  Thus θ is precisely σ-semilinear, and naturality includes every module map.
  Its displayed section equality fixes its underlying comparison to be identity.
  Module morphisms are additive and linear; by the recorded
  `Functor.act_mapMod_obj`, the source action is exactly
  `Functor.LaxMonoidal.μ A.functor R M.X ≫ A.functor.map (Mod.act M.X)`.
  The I.moduleSMul graph condition is exactly the inverse finite-product image
  of the original sectionwise action. Hence this expresses the stated action
  identification, not just an unspecified equivalence of module categories.
* `underlyingULift` is the canonical same-universe ULift insertion, obtained from
  `sheafCompose_map` and `uliftFunctorTrivial.inv`. It is needed only because the
  RECORDED AlgebraicInverseImageOfUniverses interface lifts underlying sets even
  when the coefficient and module universes agree. Every displayed normalization
  retains this insertion explicitly; no identification of ULift with its input
  is assumed definitionally.
* `ComplexComparison _ _ θ` produces preservation of zero maps for the two
  actual comparison functors (a consequence, not a hypothesis), their termwise
  natural isomorphism via `NatIso.mapHomologicalComplex`, the component formula
  in every integer degree, and the equation at EVERY differential P.d i j.
  Under the displayed underlying comparisons these differentials are L(d), by
  the naturality of A.underlying and I.moduleUnderlying. P ranges over all
  `CochainComplex` objects, so there is no boundedness restriction.
* The last part of `ComplexComparison` supplies an isomorphism between the
  complex functors followed by `DerivedCategory.Q`, and requires its component
  to be Q.map of the very termwise chain comparison. This is an isomorphism in
  the derived category, natural in P, not merely a per-degree cohomology
  isomorphism. `HasDerivedCategory.standard` constructs the localization in
  the ambient size convention. It asserts no preservation of arbitrary
  quasi-isomorphisms by an unproved derived functor.
* There are no K-flatness, termwise-flatness, enough-points, or resolution
  hypotheses. The only local instances inside definitions are explicit
  specializations of existing size, sheaf-composition and sheaf-abelian APIs;
  no file-local instance or notation leaks into the public statement.

Dependency declarations used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its recorded convention uses
  Mathlib `GrothendieckTopology` and `Sheaf` for sheaf categories. It is already
  imported through the geometric-morphism/abelian-presentation interfaces.
* `def-weil-size-convention` is metatheoretic; its recorded Lean convention is
  rendered by the explicit universes, UnivLE bounds, and standard localization.
* `Sheaf.CategoryTheory.SheafTensor` and `.SheafTensorStructure`:
  `sfbSheafTensor_properties`, `sfbSheafTensorStructure`; the concrete localized
  structure is `CategoryTheory.Sheaf.monoidalCategory`.
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` with its full adjunction and leftExact fields.
* `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` records the
  broad transport node; the smaller public dependency `.ModuleObjects.MapMod`
  (already imported by the section equivalence) supplies exactly
  `Functor.mapMod`, `Functor.monObjObj`, `Functor.modObjObj`,
  `Functor.act_mapMod_obj` and `Functor.mapMod_comp_forget` used here. This avoids
  an unrelated projection-formula import.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf` and `sectionModuleEquivalence`.
  The actual definitions/signatures and their construction were read; the
  latter's forward functor preserves the underlying abelian sheaf identically.
* `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`:
  `SheafOfModules.AlgebraicInverseImageOfUniverses`, all ring graph fields,
  modules, moduleUnderlying, and moduleSMul. Its public import also supplies
  the older specialized presentation, which is not substituted for the record.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
* Added the already landed definition `def-trf-abelian-inverse-image-presentation`
  to stmt_deps: `Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation`,
  `CategoryTheory.AbelianInverseImagePresentation`. This names the existing
  interface for the node's finite-product abelian lifts; it is not a new node.
* Proof APIs: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`SheafOfModules.tensor_bilinear_universal`); Mathlib `.Monoidal.Functor`
  (`Adjunction.leftAdjointOplaxMonoidal`, `laxMonoidalEquivOplaxMonoidal`);
  `.Monoidal.CommGrp_` (`Adjunction.mapCommGrp`, `Functor.mapCommGrp`);
  `.Adjunction.Limits` (`Adjunction.rightAdjoint_preservesLimits`);
  `.Sites.Sheafification` (`presheafToSheaf`, `sheafificationAdjunction`).

Source reading: local Stacks sites-modules.tex lemma-pullback-module (03D2),
section-tensor-product (03EK), lemma-tensor-product-pullback (03EL); sites.tex
proposition-functoriality-algebraic-structures-topoi (00YV); the current blueprint's
`lem-sfb-module-mapmod-pullback-kflat.proof.md`; and the reviewed six-step DAG proof.
The exact recorded declaration signatures and docstrings were read in the live
source. `scompile.py --source Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
confirmed the current server copy agrees.

Edge cases checked mathematically before and during writing:

* Identity geometric morphism: the mate and normalized structures reduce to
  the ordinary identity structure; σ and θ are the identity comparisons.
* Zero ring, zero modules and zero tensor inputs: the quantifiers allow them;
  ring-one and action normalization impose the expected trivial operations,
  without a nonzero-ring hypothesis.
* Empty/degenerate site: every formula is about sheaf maps or all sections,
  allowing terminal sheaf categories and vacuous section indices. Uniqueness
  is still categorical uniqueness. No chosen point or site object is required.
* An arbitrary, non-site-induced geometric morphism is included by f.
* Complexes unbounded in either direction, and degrees 0 and negative integers,
  are included by the unrestricted CochainComplex and integer indices.
* Independent object/morphism universes are retained. The compiler initially
  tried default skeleton universes in the ULift and abelianity APIs; the final
  definition explicitly specializes the existing limit-preservation and
  essentially-small-site transport APIs at coefficient universe u. The bound
  is unchanged, and no new universe equation or hypothesis was introduced.

Searches (all through the prescribed wrapper or read-only source searches):

* msearch leanfinder: "The internal module inverse image under a geometric
  morphism agrees with the sectionwise module inverse image under the section
  module equivalence" — 8 hits, e.g. ModuleCat.Tilde.res_apply,
  Scheme.Modules.inv_app, SheafOfModules.unitHomEquiv_symm_comp, pullbackObjFreeIso;
  no internal/sectionwise inverse-image comparison.
* msearch loogle: `"mapMod", "SheafOfModules"` — 0 hits.
* msearch leansearch: "Inverse image of internal modules in tensor abelian
  sheaves agrees with sectionwise module inverse image for a geometric morphism"
  — 8 hits about module sections and site pullback/free sheaves; no exact match.
* msearch grep: `sectionModuleEquivalence|internal.*module.*inverse|inverse.*internal.*module`
  — no exact theorem. Mathlib has the sectionwise pullback and tensor APIs but
  not the present internal comparison.
* msearch grep: `tensorLiftNormalization|canonicalInverseBraided|internalModuleInverseImageComparison`
  — 0 hits, checking proposed helper/main names.
* rg in lean/WeilConjectures and lean/Sheaf for sectionModuleEquivalence,
  internalModuleInverse, inverseImageComparison, mate/tensor and inverse/pullback
  filenames found the recorded equivalence, InternalSectionScalarAdjunction,
  SectionRingLaxPushforwardCoherence and site-induced tensor interfaces. None
  compares arbitrary geometric inverse image with internal mapMod as this node
  requires. In particular the direct-image and scalar-extension comparisons
  are different statements, and are not restated here.
* grep -rn of the item id in lean/WeilConjectures, and rg of the item id in both
  library roots, found no existing declaration for this node.

Validation: scompile.py compiled BOTH the sandbox module and its actual library
module name against the live published build, with no errors or non-sorry warnings
(4.8 s and 4.6 s respectively on the successful run). No global build was run.
The delivery dry run and delivery are run after recording this report.

No statement correction, dependency module, new node, or STATEMENT-DISPUTED issue.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
