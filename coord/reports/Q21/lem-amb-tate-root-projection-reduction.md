## Worker report

The module `Sheaf.Paper.AmbTateRootProjectionReduction` states
`AlgebraicGeometry.Scheme.ambTateRootProjectionReduction`. Its conclusion is
`Nonempty (AmbTateRootProjectionData l E n)`. This structure packages exactly the
specified isomorphisms, their normalizations, the transition maps, and the
pullback maps with the stated equations. The only postponed proof is this
named theorem. Its docstring contains all nine steps of the node's proof.
The helper definitions contain real data and use the published constructions.

Hypotheses and objects, checked individually:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Integers, the chosen uniformizer and finite
  quotients are the recorded `Padic.coefficientExtension*` constructions.
- The positive coefficient exponent is `n + 1`, with `n : ℕ`; this parametrizes
  every exponent at least one. The ring is literally
  `Padic.coefficientExtensionRing l E (n + 1)`.
- `AmbTateBase l` is the subtype of schemes on which l is a unit in every
  stalk. This is precisely invertibility on the scheme. It imposes no finite
  field, Noetherian, quasi-compactness or separation assumption.
- `AmbTateLevel l E n` consists of natural numbers r with
  `((l ^ (r + 1) : ℕ) : A) = 0`. Its exponent is r+1, covering every positive
  admissible exponent. There is no restriction involving the ramification index.
- The sites are the original `Scheme.ProEt.topology T`, whose object universe
  is u+1 and morphism universe is u. Coefficients are lifted to u+1. No site is
  replaced by a restricted collection of affine test objects.
- Z_T, R_r,T and A_T are the published constant ring sheaves
  `purTwistZlConstant`, `purTwistFiniteRing`, and
  `integralCoefficientCommRingSheaf`; none is replaced by its completion.
- L_T is `purTwistZlOne`, literally `limit (proEtaleRootsOfUnityTower ...)`.
  `ambTateConstantRootModule` restricts its already constructed coordinatewise
  completed-ring action to the constant Z_l ring through
  `purTwistZlCompletionMap`. Thus it has exactly the action of proof step 1.
- P_T is literally the published `purTwistFiniteOne`: its two ordinary
  extensions of scalars are over the constant Z_l and O_E sheaves. It is also
  the first line of `finiteCoefficientTwist` in the recorded twist dependency.
- `ambTateReduced` is the single ordinary extension of scalars of this same
  root-limit module by Z_l -> O_E -> A. `ambTateFiniteRoots` is exactly
  the recorded roots module extended from the constant Z/l^(r+1) ring to A.
  `ambTateFiniteScalar` uses `ZMod.castHom`, with divisibility of ringChar A
  obtained from the given annihilation equality using `CharP.cast_eq_zero_iff`.
  This is the unique scalar map, not an additional datum or assumption.

Every conclusion clause:

- `j` is an A-linear isomorphism P_T -> H_T. `j_pure` says that
  `a tensor (b tensor x)` goes to `(a * quotient(b)) tensor x`.
  Coefficients are written first because the published change-of-rings tensor
  uses this order; this is the node's `(x tensor b) tensor a -> x tensor ba`.
- `theta` supplies an A-linear isomorphism for every T and every admissible r.
  `theta_pure` gives exactly `theta(j.inv(x tensor a)) = p_r(x) tensor a`,
  with p_r the actual `limit.π` of the recorded root tower.
- `transition` and `transition_pure` give P_s,r tensor 1 on D_s -> D_r.
  The root factor is the existing `proEtaleRootsOfUnityTransition`, the
  (l^(s+1)/l^(r+1))-power map, equal to the requested l^(s-r)-power map.
  `transition_theta`, `transition_isIso`, `transition_id`, and
  `transition_comp` state all four requested transition assertions.
- `c` is the direct-image adjunct L_T -> v_* L_T' of c_L. The equations
  `c_projection` use the actual `proEtaleRootsOfUnityDirectImageMap`, whose
  inverse-image adjunct is the dependency's specified c_s. Under the existing
  abelian inverse-image adjunction these are exactly p_s c_L = c_s v^-1 p_s.
  `c_unique` states uniqueness for every morphism with all those projections;
  the adjunction is bijective, so this also states uniqueness of c_L itself.
  In particular no preservation of an infinite inverse limit is assumed.
- `b` is the A-linear direct-image adjunct P_T -> v_* P_T' of b_v.
  It uses `proEtaleConstantModuleDirectImage`, with scalar action through the
  canonical constant-section rho_A, precisely the right adjoint to the
  prescribed module inverse image followed by scalar extension. `b_pure`
  fixes its value on every double pure tensor by the same c and the canonical
  constant-section maps for O_E and A. Via j_pure this is exactly the transport
  of c_L tensor 1 through j and the tensor-pullback comparison. Pure tensors
  locally generate these sheafified tensors, so this specifies the actual map.
- `delta` is similarly the adjunct of c_r tensor 1. `delta_pure` fixes its
  value by the original root pullback-of-units map and the A scalar map.
- `square` says b followed by v_* theta equals theta followed by delta.
  Transposing by the module pullback/direct-image adjunction yields literally
  theta_T' b_v = (c_r tensor 1) v^* theta_T.
- `c_id`, `c_comp`, `b_id`, and `b_comp` assert the requested identity and
  composition laws on every section. They use the actual
  `MorphismProperty.Over.pullbackId` and `Over.pullbackComp` identifications,
  rather than equalities between the different chosen fibre-product objects.
  Transposition gives the corresponding inverse-image coherence laws.
- All tensors are ordinary sheafified module tensors. There is no flatness
  hypothesis on A over any finite quotient, and no divisibility of n by e.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityModule`,
  `proEtaleRootsOfUnityTransition`, `proEtaleRootsOfUnityTower`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the existing mixed-universe sheaf tensor structure, retaining the public
  `changeOfRingsOfUniverses` construction. The module imports this recorded
  interface; no second tensor product is defined.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `proEtaleRootsOfUnityDirectImageMap` and its inverse-image adjunct
  `proEtaleRootsOfUnityInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleBaseChange`, `proEtaleCoefficientDirectImageMap`, and
  `proEtaleConstantModuleDirectImage`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the exact
  coefficient quotient, its valuation ring and uniformizer. Its finiteness
  statement is not added as a new assumption.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit` and `limit.π`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` publicly retains the
  prescribed `purTwistFiniteOne` from `PurTwistSheaves` and
  `finiteCoefficientTwist` from `CoefficientTwistsDetailed`; those exact
  constructions are used, rather than an unrelated completed or étale line.
- Pure scalar-extension sections reuse `purScalarSection` from
  `Sheaf.Paper.PurInverseImageTensorHomDefinitions`. The remaining helper
  definitions only name the composite scalar map, its tensors, admissible
  indices, and evaluation of the existing direct image.

Every stated proof-dependency module is imported. The two general-site epi
criteria are Mathlib leaves: `Sheaf.isLocallySurjective_iff_epi'` in
`Sites.EpiMono` and `Sheaf.isLocallySurjective_iff_epi` in
`Sites.LocallySurjective`. The other proof imports are the recorded root
transition epi, full-site affine weak-contractible covers, tensor section
calculus, torsion constant-module structure, root inverse-image compatibility,
site inverse-image tensor, ringed module pullback tensor, and constant
left-module inverse-image interfaces.

Edge cases checked before writing:

- The empty scheme belongs to AmbTateBase; the formulas become the unique
  morphisms between zero sheaves. No nonemptiness assumption was introduced.
- Coefficient exponent one and root exponent one are index n=0 and r=0,
  respectively; no positive level is dropped.
- For a ramified extension with e=2 and coefficient exponent 3, root exponent
  2 is admitted when l^2 kills A, even though e does not divide 3.
- The local-lift proof also works for the nonflat algebra F_l over Z/l^2:
  the kernel difference is l^2 y and tensors to zero. It does not appeal to
  tensor exactness. The declared hypotheses contain only annihilation.
- Equal root levels give the identity power, and triple levels give the
  specified composition; both are explicit fields.
- Identity and arbitrary composable scheme morphisms occur in the same
  families c and b, with the actual chosen-product comparison in their laws.
- On a separably closed field the construction reduces to the familiar
  projection of the compatible roots followed by finite coefficient extension.

Searches actually run:

- `msearch.py ... leanfinder` with “Proetale Tate root inverse limit tensor
  finite ramified coefficients equals finite roots via projection”: 8 hits,
  concerning perfectoid Fontaine projections and adic-completion tensors;
  no exact normalized sheaf comparison.
- `msearch.py ... loogle '"rootsOfUnity"'`: 12 hits, including ordinary
  `rootsOfUnity`, its kernel and divisibility results; no sheaf comparison.
- `msearch.py ... grep 'TateTwist|rootsOfUnity|proetale' AlgebraicGeometry`:
  10 hits in Mathlib's pro-etale and ell-adic cohomology site files; no match.
- `msearch.py ... leansearch` with “Proetale root inverse limit finite scalar
  extension projection isomorphism tensor”: 8 hits about ordinary tensor,
  direct limits and profinite-group limits; no exact statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for rootProjection,
  RootProjection, finiteTwist, FiniteTwist, tateRoot, TateRoot, proEtaleTate
  and ProEtaleTate, plus the item id. No exact statement was present. The
  inspected related modules include PurTwistSheaves, PurityFiniteKummerLevel,
  TateInverseLimitBaseChange, CartesianCoefficients and FiniteTateSiteDescent.
  PurityFiniteKummerLevel has a ramification-divisibility hypothesis, whereas
  the present node admits every annihilating level, and the generic
  TateInverseLimitBaseChange interface does not assert root-projection
  invertibility. Neither is an existing match for the item.

Source metadata fault: the item's source field still names Tag 093M
(completion-flat), while its recorded nine-step proof is the explicit
local-lift proof from Tags 0990/090K and 03EK/03EL. I read these places and
followed that recorded proof in the theorem docstring. This affects the
citation metadata, not the statement, and no node field except lean is changed.
There is no STATEMENT-DISPUTED assertion and no statement correction.

Validation: compiled with scompile.py against the published live library.
The first binder-precedence error was fixed. Expensive repeated elaboration
of direct-image evaluation was replaced by typed wrappers around that same
construction; the 60-second limit was retained. Temporary diagnostic copies
and development profiler options are removed from the delivery.

Final clean scompile result: sandbox 50.1 seconds, library module 38.1 seconds;
no errors or warnings.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
