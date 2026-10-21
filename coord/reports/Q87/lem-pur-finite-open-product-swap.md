## Worker report

Item: lem-pur-finite-open-product-swap. Group Q87.

The module states the product-open comparison and its signed swap equation on the
ordinary unbounded derived category of constant-coefficient module sheaves on the
small pro-etale site. It constructs the actual arrows: no arbitrary comparison,
extra adjunction, six-functor package, boundedness assumption, or etale-origin
condition is an input. Every helper is an implementation of a map specified in
this node; there are no extra independent mathematical notions.

Hypotheses and objects, clause by clause:

- `S : PurityFiniteSetting` is precisely the recorded finite datum. `S.Coefficient`
  is the datum's standard ULift of its quotient ring, not a new coefficient ring.
  `settingCoefficientFinite` uses the quotient-finiteness theorem at `S.level`.
- The five `Over (Spec (CommRingCat.of S.field.k))` objects are the five k-schemes.
  Structural `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` occur for each.
  The last two are Mathlib's definition of finite type.
- `a` and `b` are morphisms over k, with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on both
  underlying scheme maps. `j` and `k` are the two open immersions over k.
- `M` and `N` range over `FiniteD` without any subcategory restriction. This is
  `DerivedCategory (Sheaf (ProEt.topology _) (ModuleCat S.Coefficient))`, the
  ordinary category of constant-A modules. The intrinsic realization equivalence
  in the normalization dependency identifies it with constant-ring module sheaves.
- `product a b` is literally Mathlib `pullback a b`; `first` and `second`
  are its existing `fst` and `snd`. These give C,r,t. The pullback of the composites
  gives P,p,q. `productOpen` is the canonical `pullback.map j k (identity B)`.
- `tensor` applied to the two exact pullbacks is the external product expression
  for E or D, using `ProEtale.derivedTensor` itself. `finiteShriek` is exact open extension applied to complexes and
  localized. `pull` is termwise exact inverse image localized by `mapDerivedCategory`.
  `tensorPullIso` conjugates the recorded K-flat tensor comparison by
  `leftDerivedUpperStarIsoMapDerivedCategory`; `gamma` includes the same comparison
  in its right tensor argument. This is the canonical exact presentation of Lf*.

The actual map definitions and conclusions:

1. `beta` is the canonical open base-change isomorphism, on the exact inverse-image presentation. It is the normalization dependency's `finiteBetaCanonical`.
2. `gamma` is the published `finiteGamma` followed by the canonical exact-pullback
   identification inside extension and tensor, hence
   the unit-normalized extension-first tensor comparison. `rho` is explicitly
   signed symmetry, then gamma, then extension of signed symmetry.
3. `leftOpen` and `rightOpen` are the two one-factor product opens. Their Cartesian
   squares use the universal property of the chosen pullbacks. `leftComparison`
   applies beta then gamma, with the remaining projection identified canonically;
   `rightComparison` applies beta then rho.
4. `comparison` is the left comparison, then extension of the right comparison,
   then the canonical open compositor. `comparisonOp` uses the other factorization.
   The compositor is the unique left-adjoint comparison for restriction composition,
   with the canonical exact/derived identifications, as prescribed in proof Step 2.
5. The first two conjuncts assert `IsIso` for these two actual morphisms.
6. The next two conjuncts are their restrictions being the identity under the open
   units. `restrictionSource : D -> u* E` is tensor of the j,k units, followed by
   the projection/pullback-tensor identifications. The equation says that it
   followed by u*e is the u-unit at D. Since these units are invertible, this is
   exactly u*e=1_D under the specified identifications, and likewise for e-op.
7. The fifth conjunct equates e and e-op as arrows, not just up to isomorphism.
8. `swapFactors` uses pullback-tensor and projection-composition comparisons without
   swapping the tensor factors. `swapSquare` uses the actual two pullbackSymmetry
   morphisms. `transportedReverse` is pulled-back `comparison b a k j N M`, then
   normalized beta for that square, then the remaining projection identifications.
   The final conjunct is exactly sigma(R,H), transportedReverse, and u!(sigma(Q,P0)),
   in that order. The symmetry is the canonical descended Koszul symmetry.

Dependencies read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  `Ring` and `Coefficient` definitions.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded ordinary derived conventions;
  `finiteDerivedPullback` and `finiteIntrinsicDerivedTensor` are canonically realized
  in the fixed-scalar presentation used by the normalization dependency.
- Mathlib `AlgebraicGeometry.IsOpenImmersion`, `Limits.pullback`, and its scheme
  pullback instances supply the geometric objects and the openness instances.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, defined by the intrinsic module equivalence
  and `ProEtale.openImmersionLowerShriek`. We use this latter fixed-scalar functor
  through the dependency's `finiteShriek`, rather than another extension construction.
- `Sheaf.SixFunctors.OpenTensorNormalization` and its Data module:
  `openTensorNormalization`, `FiniteD`, `finiteShriek`, `finiteBetaCanonical`,
  `finiteGamma`, and the finite intrinsic realization/compatibility.
- `Sheaf.Paper.DerivedPullbackTensorIso`: `derivedPullbackTensorIso`;
  its canonical pullback-tensor comparison is used in the fixed-scalar API as
  `ProEtale.leftDerivedUpperStarTensorIso`, with the same K-flat normalization.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `Etale.openImmersionLowerShriekComp_coherence`. This is an etale-site statement;
  the pro-etale derived compositor needed here is constructed by the exact same
  generic Mathlib adjoint-uniqueness operation, not by applying the etale functor
  to pro-etale sheaves. This is a helper in the present map construction, not a
  replacement or change to the etale dependency's valid recorded statement.
- Proof plan imports retain cochain pullback/tensor coherence, independent-coefficient
  site derived tensor descent, adjunction composition and the conjugate-unit equation.

Edge cases checked against the source and types: identity opens; an empty open and
an empty product; zero input; odd/odd homogeneous degrees (both signs in rho cancel,
while the two exterior symmetries remain signed); characteristic two; unbounded
inputs in both directions; and nonproper a,b. None is excluded by a binder. No
statement correction or mathematical dispute was found. In particular, invertibility
is asserted for the actual morphisms built by the displayed chains.

Searches for existing statements and definitions:

- msearch leanfinder: "Extension by zero commutes with external derived tensor
  products on pro-etale sites and the signed swap of factors". Eight unrelated
  formally-etale/Kaehler-differential and LightCondensed projectivity results;
  no match for this theorem.
- msearch loogle: "CategoryTheory.Sheaf, CategoryTheory.Functor.Braided".
  The sheafification braided-functor instance was found, not the comparison theorem.
- msearch grep: "externalTensor|openProduct|extensionByZero", CategoryTheory.
  No matching result.
- msearch leansearch: "Canonical open extension by zero external tensor comparison
  and signed symmetry in unbounded derived categories". Unrelated zero/Ext and
  abstract Kan-extension external product results, not this statement.
- rg in WeilConjectures and Sheaf for the item id and
  "finiteOpenProduct|finite_open_product|externalProduct.*[Ss]wap|open.*external.*tensor".
  No existing theorem. The existing open tensor
  comparison, pullback-tensor isomorphism and Koszul braiding are reused.
- Read Stacks sites-cohomology.tex, Tag 0GL1, lemma-j-shriek-and-tensor, and the
  current blueprint main-20261015 six-functors Kunneth coherence proof. The former
  gives open tensor locality; the latter gives the product-open signed swap
  reduction. The node correctly labels its assertion an agent-formulated comparison.

## Second reading by Q87

This dispatcher explicitly forbids starting another agent. This is a separate
self-audit, not a claim of independent second-worker review; the maintainer's
independent review remains necessary. I reopened the node and the declarations
and checked all five scheme hypotheses, both morphism hypotheses, both opens,
the full unbounded object types, both factorization chains, both unit equations,
the equality of chains, and the transported signed-swap equation. The implementation
uses morphisms for the named comparisons and leaves their `IsIso` assertions in
the theorem. In particular, the two comparison definitions are independent, and
the reversed map really uses the ambient geometric swap and its Cartesian square.
The restriction equation uses the forward open units and is equivalent to the
node's identity after the given invertible identifications; it does not replace
the restriction assertion by a bare isomorphism of objects.

Verification: the complete module compiled cleanly via scompile.py against the
published server build and as its library module (6.3 s and 5.3 s before final
metadata cleanup). Only `finiteOpenProductSwap` is a postponed theorem. The
Cartesian-square helpers are direct applications of Mathlib universal-property
constructors, needed as data by beta; their proofs introduce no postponed claims.
No new node or dependency-record correction is needed. The named product and tensor
helpers simply evaluate the existing constructions at this node's parameters.
