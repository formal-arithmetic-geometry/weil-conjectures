## Worker report

The module `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` states
`AlgebraicGeometry.ProEtale.KunnethFirstOpen.first_open_substitution` with `sorry`.
The other three declarations are explicit constructions: the proper exchange
in exact pullback coordinates, the proper-first exchange/projection chain with
arbitrary second morphism, and the proposition comprising the two equations.
No definition contains postponed data or a proof obligation. There is one
postponed theorem, corresponding to this item, with its four-step proof in the
docstring. The node changes only in `lean`.

Hypothesis and clause correspondence:

- The distinct primes and finite-field data are `D : FiniteFieldDatum` and
  `C : D.CoefficientDatum`: `D.prime`, `D.exponent_pos`, `D.cardinality_eq`,
  `D.card_base`, `D.isAlgClosure`, `C.prime` and `C.different` give precisely the
  stated prime-power field and distinct coefficient prime. The letter `D.a`
  is the node's positive integer d.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`
  and `[FiniteDimensional (Padic C.l) E]`. The integer is `n` with `hn : 1 ≤ n`.
  The coefficient ring is the existing `Padic.coefficientExtensionRing C.l E n`.
  Its canonical `ULift` only implements the published fixed-scalar coefficient
  presentation; it imposes no restriction on E or the scheme universe.
- `S : SixFunctorDatum D C E n hn` is the stipulated datum. Its operations
  are realized by the same actual operations, using the canonical equivalence
  `sixFunctorFiniteRealization`; no operation or map is a free hypothesis.
- `B X Xb Y : SixFunctorSpace D` gives finite-type k-schemes. Each displayed
  structure map has its separatedness instance. `j` is an open immersion;
  `a` is proper; `g` is separated, locally of finite type and quasi-compact,
  which is the standard scheme encoding of separated finite type. All
  remaining maps are the displayed composites and pullback maps. In particular
  the open j is quasi-compact in this finite-type separated setting.
- `p`, `q` and `sq : IsPullback p q (j.hom.left ≫ a.hom.left) g.hom.left`
  retain an arbitrary product cone T, rather than requiring definitional
  equality with Mathlib's chosen product. `cx` is exactly the compactification
  (j,a), and `cq := cx.ofIsPullback sq` constructs U, r, s and v. Its `comm`
  supplies sv=q. U is the actual chosen product of a and g; this implements
  the U named in the node and excludes no product up to its canonical cone
  isomorphism. No Cartesian-square comparison is supplied arbitrarily.
- `K` and `L` belong to the recorded `finiteTorConstructibleCategory` on X
  and Y. `K₀` and `L₀` are their inverse images under the published intrinsic
  realization. This is the bounded constructible finite-Tor domain.
- `FiniteOpenProduct.pull`, `tensor`, `tensorMap`, `sigma` and `finiteShriek`
  are the existing derived exact inverse image, tensor, signed symmetry and
  extension by zero. The conversions from derived upper star to exact inverse
  image are all explicit `leftDerivedUpperStarIsoMapDerivedCategory` components.
- The local `beta` is the hom component of `FiniteOpenProduct.beta` for the
  canonical open square. This is the section-unit-normalized ordinary open
  base-change map of the recorded open normalization interface.
- `e₁` is `tensorMap beta (𝟙 H)` followed by `FiniteOpenProduct.gamma` for v
  and the image under J_v of the canonical pullback-composition comparison
  `composeEq v s q cq.comm.symm`. Thus it has exactly the source and target
  in the node, with D equal to the tensor of p* K and q* L. It is the
  identity-second-open specialization of the external tensor construction.
- The first conjunct of `Assertion` is precisely Ex_{aj,g} = S_s(beta) Ex_{a,g}
  in diagrammatic Lean composition order. Its left map is the existing
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, conjugated only
  by the canonical exact/derived pullback comparisons. `properExchange`
  evaluates the original `derivedBaseChangeMap` at J_j K.
- The second conjunct expands Theta_g (one signed symmetry, the original
  PF_g, then S_g of one signed symmetry), tensors Ex with identity, then
  applies the original PF_q. The right side is the corresponding proper-first
  chain followed by S_g S_s(e₁). PF_s is the actual direct-image projection
  because s is proper. This is an equality of the specified arrows, including
  both signs; it does not replace that equality by an invertibility assertion.

Composition coordinates: the node explicitly states the equations under
S_{aj} ≅ S_a J_j and S_q ≅ S_s J_v. These coordinates are literal composites
for `cx` and `cq` here. The lambda equation is written before its final common
alpha comparison, in the target S_g R_s J_v D. The natural associative
compositors of `thm-sf-comp-composition` identify this target with S_{gq}D.
Cancelling that common isomorphism gives exactly this conjunct, and composing
it back recovers the node's displayed lambda equation. The bounded
constructible inputs have the required origin witnesses by
`lem-sf-proetale-constructible-origin`; no witness, arbitrary isomorphism,
invertibility assumption, or stronger coefficient hypothesis was added.
`cg` universally ranges over presentations of g, implementing the stipulated
canonical compactification comparisons rather than choosing a new map.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`, including
  its actual finite operations, projection and coherent composition fields.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and
  its `exchange`, `compactExchange`, `projection` constructions. The finite
  specialization is the already published `ProEtale.derivedBaseChangeMap`,
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `projectionMapOfCompactification` used in the formulas.
- `Sheaf.Paper.SixFunctorDualNotation`: `SixFunctorDatum.finiteCoefficientDual`
  and its documented reuse of the finite projection operation; the module
  is imported as the node's recorded projection-notation dependency.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `ProEtale.originComposition`, `originCompositionAmbient`,
  `originCompositionWitnessed`, and the associativity normalization.
  These justify the common final composition coordinates, without a second
  composition definition.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`:
  `ProEtale.constructible_proEtale_origin` and `ConstructibleOriginComparison`.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization` and its `finite_compatibility`
  component. The public finite ordinary helpers are the same normalized maps.
- `Sheaf.SixFunctors.OpenExternalTensorNormalization`:
  `OpenExternalTensor.finite_open_external_tensor_normalization`, `comparison`
  and `inside`. Their `FiniteOpenProduct.beta`, `gamma`, `composeEq`,
  `tensorMap`, `sigma` give the explicit one-open composite here.
- Proof-only import `Sheaf.Paper.ExchangeFunctoriality` gives
  `WeilConjectures.exchangeFunctoriality` for `fix-lem-exchanges`.
  `prop-sf-pf-coherence` has no recorded Lean module in the current DAG,
  so no import is available for that proof-only dependency. Its use remains
  in the full natural-language proof; it is not a missing statement notion.

The source was read in the CURRENT blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`,
including the symmetry paragraph and its specified exchange/projection route.
All seven statement dependency nodes and their recorded interfaces were read.

Searches for an existing statement:

- `msearch.py ... leanfinder "The canonical compact support Kunneth map respects
  open extension by zero in the first input"`: eight hits concerning compact
  support of continuous functions; none is a derived shriek substitution.
- `msearch.py ... leansearch "Canonical compact support relative Kunneth morphism
  commutes with extension by zero along an open immersion in the first factor"`:
  eight continuous-function support lemmas, no match.
- `msearch.py ... loogle '"projectionFormula", "comp"'`: zero hits.
- `msearch.py ... grep 'projectionFormula|projection_formula|lowerShriek'
  CategoryTheory`: zero hits.
- `rg` in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for
  `first_open_substitution|properFirstChain|namespace .*KunnethFirstOpen`:
  no existing declarations. Broader Kunneth searches found the ordinary
  `kunnethMap_derivedBaseChangeMap` (for Rj_*, not open extension by zero),
  and the downstream `ProductCompactificationIdentity` module. The latter's
  definitions express the general product chain but the theorem only gives
  the two-open identity, not these two first-open equations. Importing that
  downstream module would obstruct its future proof import of this item;
  the present assertion instead writes the required composite in terms of
  the original operation maps, with no duplicate category, tensor, pullback,
  extension, general lambda, compositor or compactification comparison.

Edge cases checked before writing: j=id (the normalized open maps become the
identity comparisons and the equations reduce to the proper-first chain);
X empty (zero extension from the empty open, no nonemptiness assumption);
K=0 or L=0 (all functors and tensors give the corresponding zero-map equation);
g arbitrary, including identity and nonproper g (only its compactification
presentation is used, never a properness assumption on g); n=1 and arbitrary
positive field exponent; arbitrary degree shifts (the two recorded Koszul
symmetries remain explicit); arbitrary product cone T and arbitrary universe u.
No statement correction, new nodes, dependency repairs or dispute is needed.

Validation: scompile.py compiled the delivered module in both sandbox and
library module modes with no errors or warnings after removing one unused
binding. The only postponed proof is `first_open_substitution`.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
