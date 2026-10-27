## Worker report

Item: lem-sp-proetale-projection-mate-identification. Group NG, stage 2,
2026-10-22. The delivered module is
`Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification`.
It states the identification on the ordinary unbounded derived categories;
its one theorem has proof `sorry`. All helper definitions have real data.

Hypothesis and clause correspondence (namespace below is
`AlgebraicGeometry.ProEtale.ProjectionMateIdentification`):

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite commutative rings: `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The two hypotheses `_hA`, `_hB` say that
  `(ℓ : A)^n = 0` and `(ℓ : B)^n = 0` for some natural exponent.
- The given unital coefficient map is `(φ : A →+* B)`; the completely
  arbitrary scheme morphism is `{X Y : Scheme.{u}} (q : X ⟶ Y)`.
  X is the statement's Z. No geometric property of q is assumed.
- `proEtaleDerivedCategory` is the ordinary unbounded category from the
  dependencies. No completion, constructibility, boundedness or Tor bound
  is introduced. The small site keeps object universe u+1 and Hom universe u;
  module objects have universe u+2 and morphisms u+1, and the standard
  derived localization has universe u+2.
- `inverseRing` and `inverseMap` are the literal inverse images of the
  constant ring sheaves and of the given coefficient map. `restrict`
  is exactly the published restriction of action through
  `(proEtaleConstantRingComparison q A).hom`, not another identification.
  It changes only the action and is the inverse direction of the node's J_R.
  Giving equalities after this equivalence is equivalent to giving them
  after J_R in the constant-ring presentation.
- `literalPull`, `literalPush`, `literalAdj` specialize the existing ringed
  operations to the identity structural ring map. `literalTensor` specializes
  the canonical `proEtaleReductionPullbackIso` to those literal rings.
  `literalMate` is its `mateEquiv` under those exact adjunctions. This is the
  counit-mate convention of `RingedCoefficientProjection.comparison`, rather
  than an independent arbitrary map or an assumed projection isomorphism.
- `RingTransport.ordinary` identifies ordinary geometric pullbacks through
  the canonical c_R, and its first normalization proof (`t.2.2.1`) fixes its map on every
  geometric unit section. `pullback` is its actual exact termwise descent.
  `direct` identifies the fixed derived direct images. The second normalization proof (`t.2.2.2`) preserves
  the entire specified Hom adjunction bijection, hence its unit and counit.
  Thus no alternative adjunction is allowed by the witnesses.
- `ScalarTransport.ordinary` identifies the scalar-coordinate changes;
  Its first normalization proof fixes its balanced formula on every b and m. `derived` is its
  derived counterpart, and its second normalization proof identifies it on all flat-term
  K-flat representatives through the published universal scalar counits
  and exact-functor localization factors.
- `TensorModel` records the ordinary pure-tensor formula and its K-flat
  representative square for a FIXED derived tensor/pullback isomorphism.
  The two fields of `Data` instantiate it at the literal comparison and
  the given `directImageScalarPullbackIso`, respectively. Its ordinary normalization
  takes the inverse image of x tensor b to the inverse image of x tensor
  the image of b through the specified structural ring map. For constant
  b this is the same constant b. It does not test only b=1.
- `Data.Identifies` first equates these particular tensor transformations,
  with all source/target coordinate isomorphisms displayed. Its second
  equality equates the literal mate, transported through these same
  comparisons, with `directImageScalarComparison φ q` componentwise.
  The comparisons are natural isomorphisms and the mates are natural
  transformations, so pointwise equality is equality of transformations.
- The theorem asserts unique existence of these normalized comparison
  witnesses and both identifications, with no comparison supplied as a
  hypothesis. Their normalization by sections, localization counits and
  adjunction bijections determines them uniquely. The last clause quantifies
  over EVERY unbounded E and EVERY candidate morphism k: the displayed
  counit-transpose equation holds if and only if k is the prescribed gamma.
  This includes the equation for gamma and uniqueness from the equation
  alone. No flatness, finite projective dimension, properness, or invertibility
  of gamma is assumed or concluded.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and
  `FiniteCoefficientDerivedCategory`; the node's ordinary ring-sheaf
  presentation is `Scheme.proEtaleRingModules` / `proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `ProEtale.scalarExtensionFunctor`, `scalarExtensionFunctorCounit`.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`, through its public
  direct-image operations interface: `ProEtale.directImageConstantPush`,
  `directImageConstantAdjunction`, `directImageScalarPullbackIso`,
  `directImageScalarComparison`. These are the fixed q-dependent operations
  used inside the recorded compact-support definition, not a new copy.
- `Sheaf.Paper.RingedCoefficientProjectionCocycle` and its public
  `RingedCoefficientProjectionData`: the fixed counit-mate convention,
  `SheafOfModules.RingedCoefficientProjection.comparison` and
  `ringedCoefficientProjectionCocycle`. Only the convention is used here;
  the cocycle conclusion is not assumed as the desired identification.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, `proEtaleBaseChange`, constant ring maps.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:
  `Scheme.constantComparison_isIso`, giving the exact constant-section map.
- The proof imports and seven-step proof docstring follow the node's ringed
  projection mate, K-injective Hom, canonical pre-derived adjunction,
  ring-sheaf-change adjunction, inverse-image tensor comparison, K-flat
  resolution/preservation and localization tools. No additional theorem
  has been postulated for a helper.

Edge cases checked against the types and constructions: identity q; identity
phi; zero complex; empty source scheme; zero coefficient ring (including
exponent zero in the annihilation hypothesis); non-flat Z/ell^2 to Z/ell;
arbitrary unbounded complexes. None is excluded by a hidden hypothesis.
The section formulas do not assume an inverse for the direct-image map.

Searches for duplication:

- msearch leanfinder: “The normalized pro etale scalar direct image comparison
  equals the ringed topos counit mate after constant coefficient transport”:
  eight results, ordinary adjunction/counit and restriction comparisons;
  none identifies the prescribed unbounded derived presentations.
- msearch loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`:
  twelve results, generic mate and counit identities, no match.
- msearch grep: `mateEquiv|conjugateEquiv_pullbackComp` in CategoryTheory:
  twenty hits, generic mate calculus and ordinary pullback composition.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  coefficient/mate/constant-ring comparison patterns: the existing
  operations and general mate/cocycle APIs above, no theorem of this exact
  identification. The prescribed grep for the item id in WeilConjectures
  finds no declaration. No independent missing notion required a new node.

Source checked: `literature/stacks-project/sites-cohomology.tex`,
remark-base-change (Tag 07A7), its counit-transpose construction; the
normalizations in the seven proof steps use Tags 07A6, 0D6D, 0D6E, 06YY,
0G7E and sites-modules Tags 03D3 and 03EL. No statement correction or
STATEMENT-DISPUTED fault is needed. The module only states, without proving,
the node's asserted identification.

## Second reading by NG

Self-audit with the node and module open; no independent worker was spawned,
as the dispatch explicitly forbids other agents. The maintainer's independent
review remains independent. Checked every binder and clause against the
correspondence above. The final transpose clause was refined to an iff for
an arbitrary candidate k, so uniqueness follows from the counit equation
alone. Checked directions of c_R restriction, the scalar inverse in the
transported lambda equation, and the direct-image source/target coordinate
maps. The two TensorModel predicates concern the FIXED lambda isomorphisms,
not chosen substitute isomorphisms. No change to the natural-language node.

Compilation notes: Mathlib's existing abelian instance and ordinary essentially-small
instance receive priority to avoid imported maximum-universe instance ambiguity.
This supplies no hypothesis and changes no category. Generation of unused structure
size and injectivity lemmas is disabled to keep the file within the 60-second limit.

The transport data use dependent pairs of natural isomorphisms and normalization
proofs, with named projections; TensorModel is an existential predicate with the
ordinary pure-tensor and K-flat representative conditions. These package the same
maps and equations while avoiding expensive generated recursors for large records.
No object is chosen from an unnormalized existence statement.

Validation: prescribed scompile.py completed both sandbox (27.7 s) and library
(25.0 s) compilation with no errors and no warnings. The only postponed proof
is the item theorem. No scratch module remains in the delivery.
