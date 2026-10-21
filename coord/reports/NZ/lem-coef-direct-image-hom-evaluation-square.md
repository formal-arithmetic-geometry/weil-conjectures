## Worker report

The module `Sheaf.Paper.DirectImageHomEvaluationSquare` states
`AlgebraicGeometry.Etale.DirectImageHomEvaluation.square`. The theorem has `sorry` as
its proof. Its seven public helper definitions contain actual data, not postponed
constructions: they spell out exactly the evaluation and composite arrows in this node.
No mathematical statement has been changed, and no new node or dependency repair is needed.

I read the complete item, its six proof steps, every original statement dependency's
statement and Lean record, and the declarations and docstrings in their recorded modules.
I also read the four landed nodes added below and their declarations. The source read was
`literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md`,
paragraph 1 (evaluation-defined comparison) and paragraph 4 (comparisons defined by the
same evaluations/counits and identification by transposing). I checked the current
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.md`
and its separate `.proof.md`: they give the same evaluation and counit argument. This
item extracts only its formal ordinary direct-image/evaluation calculation, not the
constructibility or invertibility theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings and their arbitrary unital homomorphism: `{A B : Type (u + 1)}`,
  `[CommRing A] [CommRing B]`, `(φ : A →+* B)`.
- Schemes and arbitrary geometric map: `{X Y : Scheme.{u}}`, `(f : Y ⟶ X)`.
- Constant small-etale module sheaves and ordinary unbounded derived categories:
  `DerivedCategoryModule A Y` and `DerivedCategoryModule B Y`. This is the recorded
  `DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))` presentation,
  with the canonical constant-coefficient module action. There is no completion or
  full subcategory restriction. The site has object universe `u+1`, arrow universe `u`;
  coefficients/modules and the small-site bound are `u+1`, as the recorded convention
  requires. No equality of these two site universes is imposed.
- The three objects: `(L N : DerivedCategoryModule A Y)` and
  `(N' : DerivedCategoryModule B Y)`.
- The arbitrary map: `(b : (scalarExtension φ Y).obj N ⟶ N')`. It has no `IsIso`
  binder. The identities occurring in the formulas are actual categorical identities.
- F_X and F_Y: the published `scalarExtension φ X` and `scalarExtension φ Y`,
  abbreviations for `ProEtale.pbcFixedScalarExtension` on the respective site, the
  fixed left adjoint to exact derived scalar restriction. These are the existing
  ordinary derived tensor scalar extensions for arbitrary coefficient maps.
- H_A and H_B: `derivedHom (ModuleCat.{u + 1} A) Y` and its B version. The internal
  Hom contravariance is `obj (op L)`, and covariance is its inner functor's `.map`.
- Q: `((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N`.
- T: `(Functor.rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} A) f)).obj Q`.
  This exact expression occurs in the theorem, so no T has been introduced as an
  unrelated object or extra hypothesis.
- Ordinary counits alpha_A and alpha_B: `.counit.app` of
  `derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f` for R=A,B. Its left
  functor is `Functor.leftDerivedFunctor (upperStar ... f)` and its right functor is
  `Functor.rightDerivedFunctor (lowerStar ... f)`. For these constant coefficients
  the geometric inverse image is exact, so the derived presentation is the node's
  ordinary inverse image; it is not exceptional pullback.
- Evaluation: the helper `evaluation A Y L N` first applies the canonical signed
  `derivedTensorSymmetry` from H_A(L,N) tensor L to L tensor H_A(L,N), then the
  counit of `derivedTensorHomAdjunction ... L`. The recorded upstream adjunction
  tensors on the left by L. This symmetry supplies precisely the node's right-tensor
  convention and retains the Koszul sign. It does not assume a different closed model.
- u: `homComparison φ Y L N`. The canonical
  `etaleHomTensorComparison Y φ Q L` maps FQ tensor FL to F(Q tensor L), and the
  following map is F(evaluation_A). To use the upstream left-tensor adjunction the
  definition first swaps FL tensor FQ into FQ tensor FL and then transposes. Thus it
  is exactly the specified right-tensor transpose; no assertion that u is an
  isomorphism enters the statement.
- c_(f,Q): `(scalarMate φ f).app Q` inside `directImageMap`. This existing definition
  is the mate of `scalarPullbackIso φ f` under the two ordinary geometric
  adjunctions, equivalently the adjunct of the scalar-extended A-counit. Its source
  is F_X(Rf_*,A Q), its target Rf_*,B(F_Y Q); no inverse is taken.
- w: `homMap φ Y L N N' b`, defined as `homComparison ...` followed by
  `((derivedHom ... B).obj (op (F_Y.obj L))).map b`, precisely H_B(1,b) after u.
- h: `directImageMap φ f L N N' b`, defined as the above c followed by
  `Rf_*,B.map (homMap ...)`, in Lean's left-to-right composition order.
- e_A: `ordinaryPairing A f L N`, defined by `derivedTensorHom ... (alpha_A,Q)
  (𝟙 L)` followed by `evaluation A Y L N`. This tensors the counit with the identity
  on L, not on another object.
- iota: `sourceComparison φ f T L`. It starts with the inverse of
  `etaleHomTensorComparison Y φ (f_A^*.obj T) L`, hence has source
  F_Y(f_A^*T tensor_A L), and follows it with tensoring the inverse component of
  `scalarPullbackIso φ f` at T with FL. The result has target
  f_B^*F_XT tensor_B F_YL. This is exactly the factorization in proof Step 1.
- p_h: `transposedPairing φ f L N N' b`, defined by tensoring
  `f_B^*.map h ≫ alpha_B,H_B(FL,N')` with `𝟙 (F_Y.obj L)`, then evaluating over B.
  Its source and target are exactly the specified B-derived objects.
- Final equality: `square` equates this p_h with `(sourceComparison ...).inv ≫
  (scalarExtension φ Y).map (ordinaryPairing A f L N) ≫ b`. Because Lean writes
  compositions left to right, this is b composed with F_Y(e_A) composed with
  iota inverse. Neither side is replaced by an existential morphism or an equality
  only after restriction of scalars.
- All exclusions in the final paragraph are respected: there are no hypotheses
  of flatness, coefficient finiteness, properness, boundedness, constructibility,
  exceptional pullback, or invertibility of u, c, or b.

Dependency declarations used or imported for the recorded proof plan:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `def-weil-size-convention`: explicit universe convention; no Lean object.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (available through the comparison imports).
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, `derivedTensorHom`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`, generic scalar extension dependency.
  The already published constant-coefficient presentation is `scalarExtension` in
  `Sheaf.Paper.EtaleDerivedScalarTensor`, publicly reexported by the tensor-comparison
  module. This avoids writing any second scalar extension or repairing a usable record.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the recorded generic tensor comparison; the concrete constant-coefficient comparison
  used in terms is the uniquely normalized `etaleHomTensorComparison`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`; its imported
  `derivedUpperStarLowerStarAdjunction` supplies exactly the ordinary adjunction
  and counits of this dependency, as its node record specifies.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, publicly reexporting
  `AlgebraicGeometry.Etale.derivedHom` and `derivedTensorHomAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`. The latter existing declarations
  give the exact constant-coefficient specialization recorded by the dependency.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`:
  `CategoryTheory.scalarInternalHomAdjunction_exists`, retained as the original
  scalar-Hom statement dependency, without selecting arbitrary structure witnesses.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`;
  `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`:
  `CategoryTheory.RingedDerivedNative.closedAdjunction`;
  `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure`, `CoefficientTensorModels`.
  These are non-public proof-plan imports, matching the node's proof dependencies.

The item gains these four already-landed statement dependencies, owning the explicit
constructions needed to spell out the canonical maps (brief-stage2 section 5's allowance
for added landed nodes). Their statements and records were read, and none depends on
this item:

- `lem-coef-etale-tensor-model-comparison`, module
  `Sheaf.SixFunctors.EtaleHomComparisonModels`, declarations
  `etaleHomTensorComparison_existsUnique`, `etaleHomTensorComparison`. Its ordinary
  oplax-mate/K-flat normalization excludes a twisted or arbitrary tensor isomorphism.
- `def-pur-etale-scalar-pullback-iso`, module
  `Sheaf.Paper.PurEtaleScalarMateProjection`, `scalarPullbackIso`.
  Its existing theorem fixes the comparison uniquely by ordinary scalar/pullback on
  K-flat representatives.
- `def-pur-etale-scalar-mate`, same module, `scalarMate`, exactly the c of this node.
- `lem-kun-tensor-sym`, module `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`,
  `derivedTensorSymmetry`, the descended signed symmetry used to match tensor order.

Edge cases checked mathematically and against the displayed signatures: identity f,
identity coefficient homomorphism, the non-flat coefficient map Z to Z/2, b=0,
L=0, N=0, N'=0, zero coefficient rings, and empty schemes. All are admitted; the
calculation uses only inverse Hom-bijections, counit naturality, the tensor bifunctor
composition law, and naturality of the two canonical isomorphisms. It requires no
cancellation of b, u, c, or the geometric counit. The symmetry is signed, so arbitrary
integer complex degrees are retained. No additional theorem was proved to test a
special case; this is a stage-2 statement delivery.

Searches actually run:

- `msearch.py ... leanfinder`: “Ordinary derived direct image coefficient scalar extension
  comparison commutes with internal Hom evaluation transpose”. Eight hits, including
  `CategoryTheory.expComparison_ev`, `coev_expComparison`, and LightCondensed internal
  Hom evaluation lemmas. Reading `Monoidal/Closed/Functor.lean` showed the first two
  require Cartesian monoidal categories and do not give the specified derived square.
- `msearch.py ... loogle`: `"Adjunction", "counit"`. Twelve hits, including
  `Adjunction.counit`, `CoreHomEquivUnitCounit`, `mkOfUnitCounit`; none states this
  scalar/geometric/Hom composite equality.
- `msearch.py ... grep`: `scalar.*[Ee]valuation|[Ee]valuation.*scalar|homEquiv_counit`
  in Mathlib CategoryTheory. Twenty-five hits on ordinary adjunction calculations.
  Read `Adjunction/Basic.lean:160-182`: it provides the Hom equivalence and its counit
  formula, not the entire square.
- `msearch.py ... leansearch`: “Derived coefficient extension commutes with ordinary
  direct image and internal Hom evaluation transpose”. Eight hits, including
  `Functor.mapDerivedCategoryFactorsh`, restriction/coextension maps, and Ext exact
  functor maps; no exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for scalar extension, derived Hom,
  evaluation squares and direct-image Hom found the canonical APIs listed above,
  ordinary completed-adic compatibility and slice comparisons with different settings.
  Reading `EtaleDerivedScalarTensor`, `EtaleHomComparisonModels`,
  `PurEtaleScalarMateProjection`, `EtaleDerivedTensorSymmetry`, and the upstream
  `Derived/Hom`, `Derived/Tensor`, `Derived/UpperLowerStar` confirmed their complete
  signatures and docstrings. They supply components, not this equality.
- Exact-name and blueprint-id `rg` in both source trees and `dag/lean_names_upstream.json`
  found no existing `DirectImageHomEvaluation` declaration and no declaration bound to
  this item. DAG searches located the four existing ownership nodes above. The
  `derivedHom` and tensor constructions are reused rather than copied.

Validation: the complete file compiled through `scompile.py` against the published live
library. Both wrapper phases were clean (33.9 s and 38.4 s), with no compiler error or
non-sorry warning. The only postponed theorem is `DirectImageHomEvaluation.square`.
`deliver2.py NZ lem-coef-direct-image-hom-evaluation-square --no-push`
also passed: commit 5948b8739cd passed the server preflight and per-file compilation.

No `STATEMENT-DISPUTED` issue, source error, statement correction, new node, or unusable
record was found. The seven helper definitions belong to this item and are all recorded
in `lean.declarations`; each has the source and blueprint docstring. The theorem
signature is recorded verbatim and has no let/show binders or auto-bound variables.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
