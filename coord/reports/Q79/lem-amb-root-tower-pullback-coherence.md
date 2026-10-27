## Worker report

The module `Sheaf.Paper.AmbRootTowerPullbackCoherence` states
`AlgebraicGeometry.Scheme.ambRootTowerPullbackCoherence`, with one postponed proof,
and supplies concrete tensor objects and a structure spelling out its conclusion.
No theorem is proved. No definition contains sorry. No statement correction,
new DAG node or dependency repair is needed.

The node is quantified over all eligible schemes and morphisms simultaneously.
The structure's fields use `T : Scheme.{u}` and
`[∀ x : T, Invertible (l : T.presheaf.stalk x)]`, and the corresponding
binders for T' and T''. A typeclass witness of invertibility is equivalent to
being a unit; this is exactly invertibility of l on the scheme, without a
nonemptiness, affine, connectedness or characteristic-zero restriction.
`l : ℕ` and `[Fact l.Prime]` bind the prime. Every natural index s or r
represents the positive exponent s+1 or r+1, so level 1 is included.
All universes and variables are explicitly bound; autoImplicit is false.

Clause mapping:

- Small pro-etale sites and root sheaves: `ProEt.topology T`,
  `proEtaleRootsOfUnitySheaf T (l ^ (s + 1))`, and the recorded power-transition
  diagram `proEtaleRootsOfUnityTower T l Fact.out`.
- L_T and p_s: the existing `purTwistZlOne T l`, definitionally the limit of
  that very abelian sheaf diagram, and `limit.π ... (op s)`.
- Z_T and R_s,T: `purTwistZlConstant T l` and `purTwistFiniteRing T l s`,
  sheafifications of the constant lifted PadicInt and ZMod rings. The use of
  `ULift` only fits the coefficient universe and does not change the rings.
- The stated action `(a x)_s = x_s^(a mod l^s)` is the existing
  `purTwistZlAction`, restricted along `purTwistZlCompletionMap` in
  `ambRootAction`. The existing action's unique characterization is precisely
  multiplication on each projection by `purTwistZlProjection`; the completion
  map projects to `purTwistZlReduction`, induced by `PadicInt.toZModPow`.
  `ambRootTensor` restricts the same module via `SheafOfModules.restrictScalars`.
  This is not an independently chosen action and does not equate constant and
  completed coefficient sheaves.
- Scheme inverse image: recorded `proEtaleSheafInverseImage` and
  `proEtaleSheafAdjunction`; c_s is the recorded
  `proEtaleRootsOfUnityInverseImageMap`. Its adjunct is exactly
  `proEtaleRootsOfUnityDirectImageMap`, with the pullback-of-units normalization.
- Constant-ring identification: `constant_iso` uses the actual adjoint
  `proEtaleConstantInverseImageMap`, hence the prescribed structure map, rather
  than an arbitrary isomorphism. It quantifies exactly Z_l, the finite rings
  and the Z_l-algebras B used in the node. The structure's module direct images use
  `proEtaleCoefficientDirectImageMap`, the same canonical constant-section rho.
- Finite semilinearity: `root_linear` explicitly names both the inverse-image
  root action and the actual constant-ring structure map. This is the exact
  interface supplied by `proEtaleRootsOfUnityInverseImageIso`, including its
  action specified on all adjunction-unit sections. `root_transition` is its
  power-transition equation at consecutive levels. Consecutive transitions
  are exactly the inverse system in the node.
- Finite identity and composition: `root_id` and `root_comp` give equality of
  the actual direct-image adjuncts on every section, with
  `MorphismProperty.Over.pullbackId` and `pullbackComp`. These maps are the
  canonical fibre-product identity and associator. Transposing these equalities
  is precisely the node's inverse-image comparison equations: the canonical
  inverse-image comparisons are uniquely fixed as the mates of these
  direct-image comparisons under the recorded adjunctions.
- Existence of c_L is field `c`, the additive direct-image adjunct.
  `c_projection` is exactly the adjoint of p_s c_L = c_s v^{-1}p_s.
  `c_unique` records projection uniqueness; it quantifies all additive
  adjuncts, since projection uniqueness holds even before checking linearity.
  `c_linear` expresses Z_T-linearity of this adjunct through rho_Z. By the
  transported module action and the ring adjunction, this is equivalent to
  semilinearity of c_L through c_Z, or target linearity after the canonical
  constant-ring identification. The ordinary scalar-extension/direct-image
  adjunction identifies these two forms. `c_id` and `c_comp` give the full
  identity and composition equations on every original section.
- B is any `Type u` with `[CommRing B] [Algebra ℤ_[l] B]`.
  `ambRootScalar` uses this algebra map. `ambRootTensor` is H_T, the actual
  ordinary sheaf change of rings `L_T tensor_Z B_T`, not a derived tensor.
  `ambRootTensorPure` is its sheafification-unit pure tensor. The constructor
  for scalar extension puts b first, so `b tensor x` in that API means the
  node's `x tensor b` via the canonical commutative tensor convention.
- `h` is a B-linear map to the recorded constant-coefficient module direct
  image. Under the inverse-image/change-of-scalars adjunction, it is exactly
  a B_T'-linear map from the specified v^*H_T to H_T'. `h_pure` specifies
  c_L tensor 1 on every original unit tensor, including all local scalar
  sections b, not only globally constant scalars. Adjunction plus the sheaf
  tensor universal property determines the map uniquely. `h_id` and `h_comp`
  are equations on every original section of H_T, with the same canonical
  fibre-product comparisons. Consequently they are the full pullback-map
  equations, not only pure-tensor evaluations or per-degree information.
- r >= 1 is the positive-level convention r+1. The sole extra finite-level
  condition is `hB : ((l ^ (r + 1) : ℕ) : B) = 0`.
  `ambRootFiniteScalar` is the canonical ZMod cast map given by this condition,
  and `ambRootFiniteTensor` is D_r,T over the recorded finite roots module.
  The cast map factors the specified Z_l-algebra map: reduction of Z_l is
  surjective with kernel (l^(r+1)), and any Z_l-algebra killed by this power
  has exactly this factorization. No extra choice or flatness is introduced.
- `alpha` and `alpha_pure` specify the projection-induced B-linear reduction
  on every root tensor. `d` and `d_pure` similarly specify the B-linear adjunct
  of c_r tensor 1. `square` is an equality of module morphisms, exactly the
  adjunct of alpha_T' h_v = (c_r tensor 1) v^*alpha_T. It retains these
  specified maps rather than existential arbitrary commutative-square arrows.
- No `IsIso` is imposed on alpha, d, c or c_s. The only isomorphisms asserted
  are the canonical constant-ring comparisons. No inverse image of L is
  replaced with a limit or assumed to preserve this infinite limit.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and Hom.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityTower`, its transitions
  and the constant finite-ring module.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Mathlib.NumberTheory.Padics.PadicIntegers` and `RingHoms`:
  `PadicInt` and `PadicInt.toZModPow` (Mathlib match for l-adic numbers).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, reexporting the independent-universe sheaf tensor
  and change-of-rings constructions used by the object definitions.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, direct image and adjunction,
  constant comparison maps and `proEtaleConstantModuleDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  the recorded root inverse-image map and its normalized direct-image adjunct.
- `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`:
  `proEtaleRootsOfUnityInverseImageAction`,
  `proEtaleRootsOfUnityInverseImageRing`, and the semilinearity theorem.
- `Sheaf.Paper.PurTwistSheaves`: the exact existing root limit, module action
  and finite module; added its landed owning node `def-pur-twist-sheaves` to
  stmt_deps instead of copying these constructions.
- `Sheaf.Paper.PurInverseImageTensorHomDefinitions`: `purScalarSection`;
  added its landed owning node `def-pur-inverse-image-tensor-hom-sections`.
  The landed finite-root semilinearity node was also added to stmt_deps since
  its action interface occurs explicitly in the statement.

The already stated proof modules are imported privately:
`SiteInverseImageTensor.siteInverseImage_tensor`,
`ConstantLeftModuleInverseImage.constant_left_module_inverse_image`,
`SiteInverseImageCompositionGenerators.site_inverse_image_composition_generators`,
`CochainInverseComparison.CochainInversePairing.exists_inverseImageTensorComparison`,
and `ProEtaleTensorAdjointTest.proEtale_inverseImage_tensor_adjoint_test` with its
coefficient and composition evaluations. The full eight-step source proof is
in the theorem docstring. Their signatures and source docstrings were read.

Edge cases checked: the empty scheme (invertibility is vacuous and section
maps are the unique maps of zero sheaves); zero coefficient ring (allowed by
CommRing and by the cast map); smallest positive exponent (s=r=0 encodes 1);
identity morphisms; arbitrary composites; B=Z_l (no finite-level annihilation
assumed for the h/c clauses); nonflat killed B and different valid annihilating
levels. No local root basis, inverse to c_s, inverse to alpha, or limit
preservation is needed. Independent site object and Hom universes are retained
as u+1 and u, with coefficient values u+1, via the existing constructions.

Searches: prescribed msearch LeanFinder query "Canonical pullback of inverse
limit root sheaves with tensor and coefficient reduction coherence" returned
8 scheme pullback auxiliaries, no matching theorem; Loogle query
"CategoryTheory.Limits.limit.post, PadicInt.toZModPow" returned 0 hits; Mathlib
grep "rootTower|RootTower|TateModule" in CategoryTheory returned 0 hits.
LeanSearch query "Inverse image of inverse limit roots of unity tensor
coherence" returned 8 direct-limit tensor results, no root-sheaf theorem.
Raw results are in searches.jsonl. Project rg for rootTower/RootTower/tateRoot/
integralTwist identified the existing PurTwistSheaves and related Tate modules.
The upstream rg/grep for the item id and final declaration names found no
match. The parent AmbTateRootProjectionReduction was read: it specializes B
to a finite quotient of a finite p-adic extension, and does not cover arbitrary
Z_l-algebras as this item does. TateInverseLimitBaseChange assumes root-level
isomorphisms and is not this statement. PurIntegralTwistLineInverseImage adds
coefficient fields and has no full identity/composition/reduction conclusion.
No exact existing declaration was found.

Sources opened: local sites-modules.tex at lemma-tensor-product-pullback (03EL),
and the current main-20261015 vector-bundle purity proof. The inherited item is
an extracted auxiliary, not the blueprint unit statement. No source mismatch
or STATEMENT-DISPUTED issue was found.

Validation: scompile.py checked the delivered module in sandbox mode and under
its real module name, cleanly (40.3 s and 35.7 s); no errors or warnings.
Explicit result types and irreducibility of coefficient-map implementations
avoid expensive elaboration through chosen sheafification maps. A temporary
probe was removed from the delivery.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
