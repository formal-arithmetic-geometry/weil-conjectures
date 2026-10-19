## Worker report

Stage 2 statement of `lem-coef-rational-bidual-triangle-compatibility`, in
`Sheaf.CategoryTheory.CoefficientBidualTriangles`. The namespace is
`CategoryTheory.CoefficientBidualTriangles`. The primary theorem is `compatibility`;
`restriction` and `scalarCompatibility` state the remaining clauses. Every theorem
has a whole-body `sorry`; all definitions have data. No node statement, proof,
dependency list, stage-1 split or reviewed record is changed.

The previous worker's stale-assignment diagnosis conflated stages: Q108's ledger
entry at 2026-10-17 13:53 merged the stage-1 split. The current item has no `lean`
record. This delivery adds its stage-2 statement and does not split it again.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ringed site is `{C : Type c} [Category.{v} C]`, `J : GrothendieckTopology C`,
  and `O : Sheaf J CommRingCat.{max c v r}`. The module universe contains the site
  objects and arrows independently. `HasSheafify` and `WEqualsLocallyBijective`
  are the standard sheaf-category infrastructure in that universe, not extra
  geometric restrictions. In particular object universe t+1 and arrow universe t
  are allowed.
- `Modules J O` is only an abbreviation for the dependency's `ringedSiteModules`,
  hence Mathlib's `SheafOfModules` with its existing abelian instance. `D J O` is
  `DerivedCategory (Modules J O)` under `HasDerivedCategory.{w}`. The choice of
  morphism universe is explicit. `Complex` includes all integer cochain complexes.
- `dual` fixes the second argument of the recorded
  `derivedInternalHomOfUniverses` at `ringedSiteDualityUnit J O`, which is O[0].
  `bidual` is `dual.rightOp` followed by `dual` on both objects and arrows.
- `M : RingedSiteDualityModel J O` specifies the dependency's canonical closed
  tensor-Hom presentation, including its K-flat representative normalization and
  Koszul symmetry; such a presentation exists by `ringedSiteDualityMaps_exists`.
  This is not an arbitrary map or an extra duality assumption. `bidualMap` uses
  exactly `ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit J O)`.
  Its naturality field is the dependency's `ringedSiteBidual_naturality`.
- The signed shift is not left unspecified. `targetResolution` is the fixed
  coefficient K-injective replacement already used by derived Hom. `modelMap`
  uses the inverse actual `coefficientHomResolutionIso` for Hom(T(E),O), followed
  by the contravariant Hom action of the actual comparison for Hom(E,O).
  `signedHomShift` selects its uniquely normalized first witness s from
  `SignedDoubleHomCone.comparison`, and `signedModelShift` constructs chi
  as minus T(s_E,1)^(-1) followed by s_(T(E),-1). That
  theorem fixes chi by its section formula (-1)^(p+t), including the leading minus
  in -s_(T(E),-1) T(s_(E,1))^(-1). Its product projections determine this map
  uniquely, so this is not data chosen from an unspecified existence statement.
  The representative equality in `compatibility` transports exactly this chi
  across `modelMap` and `DerivedCategory.Q.commShiftIso`.
- `compatibility` produces coherent integer `Functor.CommShift` structure for
  this bidual, asserts its `IsTriangulated`, and asserts
  `NatTrans.CommShift (bidualMap J O M) ℤ`. The latter includes every signed shift
  equation, with zero, positive and negative shifts. `canonicalCommShift` selects
  the structure fixed by the preceding representative normalization: Q is
  essentially surjective, so this normalization determines its components.
- For each `T : Triangle (D J O)` with `T ∈ distTriang _`, the theorem supplies
  `f : T ⟶ bidual.mapTriangle.obj T` whose three components are exactly d at
  `T.obj₁`, `T.obj₂`, `T.obj₃`. A triangle morphism includes all three squares;
  its `comm₃` is the connecting-map square. Exactness ensures that its target
  triangle is distinguished, rather than merely a triangle with unrelated arrows.
- The first closure clause is the equivalence of `IsIso (d.app (V⟦n⟧))` and
  `IsIso (d.app V)` for every integer n. The last clause separately states all
  three pairs (1,2), (1,3), (2,3) in any distinguished triangle.
- The slice in `restriction` is literally `J.over U`, with coefficient `O.over U`
  and its own chosen derived morphism universe w'. The functor F factors the
  dependency's actual `ringedSiteDualityRestrictionComplex J O U` through Q;
  that functor is `SheafOfModules.overFunctor` followed by the canonical transport
  identifying restriction of the coefficient ring with the forgotten restricted
  commutative ring. Thus an unrelated exact functor is not substituted.
- `restriction` supplies the tensor/Hom/unit comparisons in the existing
  duality-map interface. The evaluation square identifies the Hom comparison with
  the tensor-Hom comparison. Its formula for beta is the iterated Hom comparison,
  including both occurrences of the coefficient-unit isomorphism. It asserts
  `NatTrans.CommShift beta.hom ℤ` for the same normalized base and slice bidual
  shifts, and `F.map d ≫ beta = d_U`. Naturality supplies the first two triangle
  squares; the final displayed equation explicitly states equality on the
  connecting arrow after restriction, the two shift comparisons, and beta[1].
- A commutative central coefficient ring is `(A : Type a) [CommRing A]` with
  `rho : ∀ U : Cᵒᵖ, A →+* O.obj.obj U` and `hnat` saying rho commutes with every
  restriction. These are exactly a compatible action on the commutative ring
  sheaf; the independent universe a allows larger acting rings as well.
  `coefficientLinear_existsUnique` states the unique induced linear structure on
  module-sheaf morphisms, with scalar action specified on every section.
  `coefficientLinear` takes data only from this uniqueness theorem, as allowed by
  AGENTS §5. `scalarCompatibility` installs precisely that structure; it does not
  assume that the derived dual or bidual is already linear.
- The full triangulated subcategory is
  `T : ObjectProperty (D J O)` with `[T.IsTriangulated]`. No closure under arbitrary
  isomorphisms is added. `hT` is precisely preservation of T by `dual`.
  `subBidual` uses `ObjectProperty.lift` and applies hT twice; `subBidualMap`
  wraps the same canonical components in the full subcategory. The assumed
  A-linear shift by one is the node's A-linear shift; its inverse and powers
  account for all integer shifts. `subBidual_linear` derives additivity and
  linearity from the sectionwise action, before scalar extension.
- The scalar parameter is arbitrary `s : A`. The category is exactly
  `ScalarLocalization A T.FullSubcategory s`, without an idempotent completion.
  The zero/shift/additive-shift/triangulation instance binders, `hshift`, `hQ`, and
  `hdist` specify exactly the structures provided by
  `ScalarLocalization.exists_triangulated_scalarLocalization`: the induced
  shift, Q's identity comparison, and distinguished triangles precisely the
  isomorphic Q-images of original distinguished triangles. They are the encoding
  of the prescribed raw localized triangulation, not new mathematical hypotheses.
- `scalarCompatibility` constructs F and d on this fixed category. Its object and
  pure-tensor arrow equations specify the extension of the actual `subBidual`;
  its d-component equation specifies d tensor 1; its shift-component equation
  specifies the original normalized shift comparison tensor 1. ScalarLocalization
  uses scalar-first tensor order, canonically symmetric to the node's Hom-first
  order. HEq only handles object wrappers/shift identifications; it does not weaken
  a map equation. These formulas determine the maps on all tensors by additivity.
  F is exact, d commutes with integer shifts, and every localized distinguished
  triangle has its componentwise d triangle morphism. The last clauses assert
  shift equivalence and all three two-out-of-three implications in that category,
  including triangles with fraction arrows.
- There is no assertion that arbitrary d components are invertible, and no
  perfectness, flatness, boundedness, finite generation, nonzero s or characteristic
  assumption on the derived objects is imposed.

Dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its shift/triangle structures.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its representative construction.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`:
  `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`, `Triangle`.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`: `RingedSiteDualityModel`,
  `ringedSiteBidual`, `ringedSiteBidual_naturality`, `ringedSiteDualityUnitComplex`,
  `ringedSiteDualityUnit`, `ringedSiteDualityRestrictionComplex`, and the
  `ringedSiteDualityMaps_restriction` comparison interface.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`:
  `ringedInternalHom_restriction`, `ringedInternalHom_exact` explain the exactness
  and restriction comparisons; its old single-universe derived Hom is not silently
  substituted for the recorded independent-universe derived Hom.
- `Mathlib.CategoryTheory.Sites.Over` and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `GrothendieckTopology.over`, `Sheaf.over`, `SheafOfModules.overFunctor`.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`:
  `NatTrans.mapTriangle`, `NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂`,
  `NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃`, and
  `NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃`, used by the proof plan.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`,
  `ScalarLocalization.localization`, `ScalarLocalization.map`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `ScalarLocalization.exists_triangulated_scalarLocalization`.
- `Sheaf.Algebra.Homology.SignedDoubleHomCone`: `SignedDoubleHomCone.doubleDual`,
  `SignedDoubleHomCone.comparison`, including the exact signed cone identities.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `WeilConjectures.coefficientHomResolution` and `coefficientHomResolutionIso`.
  This is reused through the public import of the duality-map dependency.
- The available proof-dependency modules are imported without public: K-flat
  resolutions, Hom-complex global homotopy, K-injective Hom, quasi-isomorphism
  invariance, exact localized module adjunction, Hom-tensor currying, derived tensor
  descent and K-injective resolutions. There is no new dependency module.

Edge cases checked against the formulas: zero complex and zero coefficient ring;
unbounded complexes; characteristic two (all signs reduce correctly); the object
O[0]; a non-reflexive infinite-dimensional vector space (closure statements do not
assert its biduality map invertible); n=0, n=1 and n=-1; s=1, s=0 and nilpotent s
(the localized category can be zero); the zero full triangulated subcategory;
slices with arbitrary U; independent object/arrow/coefficient/morphism universes.
The sectionwise central action commutes with addition and multiplication even for
large acting-ring universe a.

Searches (2026-10-17):

- `msearch.py leanfinder`, query "coefficient biduality natural transformation
  compatible with shifts and distinguished triangles scalar localization": eight
  hits on generic shift/localization tools; no coefficient biduality theorem.
- `msearch.py leansearch`, query "biduality natural transformation commutes shifts
  distinguished triangles": eight hits, including NatTrans.CommShift and generic
  triangulated adjunctions; no theorem about the specified coefficient evaluation.
- `msearch.py loogle`, query "CategoryTheory.NatTrans.CommShift,
  CategoryTheory.Functor.CommShift": twelve hits on the generic shift structures.
  These are reused; they do not identify the actual signed biduality components.
- `msearch.py grep`, regex "bidual|doubleDual|double.dual", CategoryTheory:
  zero Mathlib hits. Regex "biduality|doubleDual|double.dual", Algebra/Homology:
  zero Mathlib hits.
- `rg` in upstream WeilConjectures and project lean/Sheaf for bidual/double-dual
  shift/triangle compatibility: the project's existing SignedDoubleHomCone
  calculation is the relevant hit and is reused. No complete theorem found.
  The requested upstream search for this item's blueprint id returned no hits.
- Name search for CoefficientBidualTriangles, canonicalCommShift,
  coefficientLinear_existsUnique and signedModelShift in Mathlib, upstream,
  the upstream declaration-name index and lean/Sheaf returned no collisions.

Sources opened: Stacks sites-cohomology.tex at lemma-RHom-triangulated,
lemma-internal-hom-evaluate and lemma-restriction-RHom-to-U; the current blueprint's
lem-coef-rational-retract-evaluation proof; the item and all twelve statement
dependencies including their recorded Lean declarations and docstrings.

No new DAG nodes, dependency repairs, statement correction or disputed statement.
Validation uses scompile.py only, then deliver2.py --no-push and deliver2.py.

## Second reading by Q58

Independent maintainer second reading, 2026-10-17. The following review replaces
the original disclaimer; the Worker report above is preserved.


1. `{C : Type c} [Category.{v} C]`, J, and commutative O encode precisely the
   small ringed site. Module/sheaf values lie in max c v r. Objects and arrows
   are not forced into equal universes. HasSheafify and WEqualsLocallyBijective
   supply the standard small-site abelian infrastructure. HasDerivedCategory w
   selects a localization morphism universe, not boundedness or finiteness.
2. Modules is the recorded ringedSiteModules abbreviation, D is the actual
   unbounded DerivedCategory, and Complex is integer-indexed CochainComplex.
   dual fixes the second variable of derivedInternalHomOfUniverses at the
   recorded coefficient unit O[0]; bidual is dual.rightOp followed by dual.
3. bidualMap uses ringedSiteBidual and its naturality theorem directly.
   I read the definition: it transposes the braiding followed by evaluation.
   RingedSiteDualityModel is not an arbitrary duality assumption: its models
   field pins uncurrying on K-flat representatives and symmetry_model pins the
   Koszul sign. ringedSiteDualityMaps_exists supplies such presentations for
   arbitrary inputs. The conditional ordinary-O[0] normalization is not
   incorrectly applied to arbitrary complexes in this delivery.
4. targetResolution and modelMap use the existing fixed K-injective resolution
   and actual Localization.fac comparisons. The two comparison directions in
   modelMap agree with contravariance of Hom in its first variable.
5. signedHomShift chooses the first witness of SignedDoubleHomCone.comparison.
   That witness is determined by all product projections, with sign (-1)^(m*q).
   signedModelShift is minus the contravariant image of the inverse comparison
   followed by the comparison at T(E), -1. Thus it fixes chi, including its
   leading minus, rather than allowing an unrelated exact shift structure.
6. compatibility asserts a coherent integer CommShift, exactness, and
   NatTrans.CommShift for the actual bidualMap. Its representative equality
   specifies the degree-one comparison across Q and modelMap. I checked the
   sign calculation: p+t+p(t+1) and (p+1)t differ by 2p. The dependency's cone
   equation uses the actual triangle mor3=-pi. Integer coherence extends this
   degree-one normalization to zero and negative shifts. canonicalCommShift
   selects this normalized structure; essential surjectivity of Q and shift
   coherence determine its components, meeting the no-hollow-definition rule.
7. The triangle conjunct supplies a Triangle morphism whose three components
   are exactly d at the three vertices. Triangle.comm3 is the connecting square;
   IsTriangulated ensures the image triangle is distinguished. The final
   conjuncts give shift equivalence for every integer and all three distinct
   pairs in two-out-of-three. No universal invertibility is asserted.
8. restriction uses exactly J.over U, O.over U, and the independent slice
   derived universe w'. Its factorization is through the existing termwise
   ringedSiteDualityRestrictionComplex, itself overFunctor with the canonical
   coefficient equality transport. It does not substitute a different site.
   The Hom comparison is evaluation-compatible, beta is explicitly the
   iterated Hom comparison with both coefficient transports, beta commutes
   with the same normalized shifts, and F.map d followed by beta equals d_U.
   Its final displayed equality has the correct composition order for the
   restricted connecting arrow. Naturality supplies the other two squares.
9. A : Type a, CommRing A, rho, and hnat encode a compatible central action on
   the commutative coefficient sheaf. coefficientLinear_existsUnique specifies
   every scalar multiple sectionwise; all other Linear fields are laws.
   Consequently coefficientLinear chooses uniquely characterized data, not
   an unconstrained structure. subBidual_linear derives additivity and
   linearity; it does not assume linearity of the double-dual functor.
10. T is the full ObjectProperty subcategory with its inherited triangulation.
    Mathlib's IsTriangulated does not demand closure under all isomorphisms.
    hT states exactly preservation by dual, and applying it twice constructs
    subBidual. subBidualMap wraps the original components. The linear shift
    assumption is precisely shift by one, as in the localization dependency.
11. The scalar category is the raw ScalarLocalization, with scalar-first tensor
    Hom modules, canonically equivalent to the node's Hom-first notation.
    I compared every structural binder, hshift, hQ, and hdist with
    exists_triangulated_scalarLocalization: they are the supplied induced
    structures and identity normalization, not extra geometric hypotheses.
    The object equation and pure-tensor map equation specify the extended
    bidual, the component equation specifies d tensor one, and the shift
    equation specifies its original comparison tensor one. HEq handles the
    equal object wrappers. Exactness implies additivity, so the pure-tensor
    equations determine all morphisms. All localized triangle squares and all
    shift/two-out-of-three cases are present, including fraction arrows.
12. There is no nonzero-s, perfectness, boundedness, field, finite-generation,
    or arbitrary-bidual-isomorphism hypothesis or conclusion.

## Dependencies, source checks and searches

Read the recorded declarations for derived categories, ringedSiteModules,
derivedInternalHomOfUniverses, Pretriangulated/IsTriangulated,
RingedSiteDualityModel and ringedSiteBidual, ringedInternalHom_tensor_adjunction /
restriction / exact, NatTrans.mapTriangle and its three isomorphism lemmas,
GrothendieckTopology.over / Sheaf.over / SheafOfModules.overFunctor,
ScalarLocalization and exists_triangulated_scalarLocalization, and
SignedDoubleHomCone.comparison. Also inspected coefficientHomResolutionIso and
CoefficientTensorModels.uncurry_model, since the canonical-map claim depends on
them. The older single-universe ringedInternalHom interface is imported for the
proof plan; the item does not impose its universe equality or replace the
recorded independent-universe internal Hom with it. The local clone spells its
K-flat predicate differently from the snapshot's historical dependency record;
no use of that binder occurs in the item signature.

Primary source locations read in /home/ubuntu/weil-newtargets-NY/literature/:

- stacks-project/sites-cohomology.tex, lines 8835–9000: Section 08J7,
  08J9 currying, 08JB (8934), 08JC (8948), and 0A97 (8965).
- stacks-project/derived.tex, exact-functor definition (191 onward),
  cone definition 014E (2471 onward); checked the image-triangle convention.
- stacks-project/sites-modules.tex, localization (1992–2051), especially
  the sectionwise restriction rule and exact extension by zero.
- blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
  lem-coef-rational-retract-evaluation.md and sec-smooth-purity/
  sk-lem-sf-determination/lem-sf-triangle-two-out-of-three.md.

Independent rg searches used bidual, doubleDual, double-dual, biduality and
CommShift across the pinned Mathlib CategoryTheory tree, upstream
WeilConjectures CategoryTheory / Mathlib CategoryTheory, and project
CategoryTheory, Algebra/Homology and Paper modules. Relevant hits are the reused
RingedSiteDualityMaps, SignedDoubleHomCone, and generic NatTrans triangle tools.
Perfect-duality and ambient etale/pro-etale pairing modules concern different
categories or stronger special cases; they do not supply this complete statement.
The delivery records LeanSearch, LeanFinder, Loogle and grep searches. No duplicate
of the complete theorem or private replacement of a dependency was found.

All 19 recorded declarations are present. lean.statement equals the exact
compatibility signature before `:= by` byte-for-byte. The module and declaration
docstrings carry source/blueprint references; the five theorem docstrings cover
DAG proof steps 1–13 and the induced-scalar helper construction. All five theorem
bodies are only `sorry`; no data definition contains sorry and no local proof was
introduced. No over-100-character lines, unbound variables, or silent universe
restrictions were found. There is no pro-etale substitute.

## Edge cases and compiler evidence

Checked zero objects and zero coefficient ring, unbounded complexes, characteristic
two, positive/zero/negative shifts, a non-reflexive vector space, empty underlying
site where applicable, arbitrary slice objects, independent c/v/r/w/w'/a, zero
subcategory, s=1, s=0, and nilpotent s. None is excluded. In particular localization
may collapse to a zero category; the stated formulas and closure implications
still apply and do not imply that every original d is invertible.

The immutable worker report states the validation workflow but gives no concrete
per-file timing/output. I reproduced the delivered file with the prescribed wrapper:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py NY \
      lem-coef-rational-bidual-triangle-compatibility \
      snapshot/lean/Sheaf/CategoryTheory/CoefficientBidualTriangles.lean

Exit code 0, no errors or warnings. Output:

    sandbox Sheaf/Stage2/Sandbox0.lean
    (with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-eibvw_2_/.lbuild) [18.4 s]
    library Sheaf/CategoryTheory/CoefficientBidualTriangles.lean
    [20.6 s]

The installed scompile.py currently delegates to nt_srv_compile.py
--wire-confirm on the server, rather than using the older local-overlay mode
specified in the brief. This was the prescribed wrapper, with its sandbox overlay
and library confirmation, retaining the default 60-second file limit. I invoked no
direct ssh, lake build, delivery, claim, preflight, merge, or git mutation. Only
review.md and the complete replacement report under fixes were written. The
immutable snapshot was not changed. The only finding requiring repair is the
missing actual second-reading content, now provided in full.
