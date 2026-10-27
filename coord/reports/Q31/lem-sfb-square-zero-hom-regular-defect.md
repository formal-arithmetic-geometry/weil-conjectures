## Worker report

The theorem is `AlgebraicGeometry.InfinitesimalRegular.squareZeroHom_regularDefect` in
`Sheaf.AlgebraicGeometry.SquareZeroHomRegularDefect`. Its proof is `sorry`; no theorem
is proved. The supporting definition module has real data throughout, including the
coordinate correction map. The existing item changes only in `lean` and by adding
one definition node to `stmt_deps`. There is no statement correction or dispute.

Clause-by-clause reading:

- The commutative ring A and the two affine group schemes are `(A D C : Type u)`
  with their three `CommRing` instances and `[HopfAlgebra A D] [HopfAlgebra A C]`.
  Here H=Spec C and G=Spec D. Mathlib's `AlgebraicGeometry.hopfSpec`, its full
  faithful interface and its affine essential image give exactly affine group
  schemes, with all group diagrams; this introduces no commutativity condition
  on the group. `Spec.mapMulEquiv` identifies convolution points with the actual
  morphisms Spec R -> G over Spec A. D is the coordinate algebra denoted B in
  the node's proof, not the coefficient base ring B used in the node's evaluation
  sentence. Ring and scheme universes are explicitly bound; none is auto-bound.
- The ideal and its square-zero hypothesis are `(J : Ideal A) (hJ : J ^ 2 = ⊥)`.
  K is literally `A ⧸ J`. The reduction `Reduced A J R` is `(A ⧸ J) ⊗[A] R`,
  canonically R/JR by the pushout universal property. Thus C0, D0 and R0 are
  canonically the specified quotients, carrying their base-changed Hopf structures.
  This representation avoids choosing quotient Hopf structures. It retains the
  specified base change, rather than assuming an arbitrary identification or map.
- Flatness of C is `[Module.Flat A C]`; this is the injection-preserving tensor
  definition, not a finite-presentation or faithful-flatness condition. Smoothness
  is the recorded `[Smooth (Spec.map (CommRingCat.ofHom (algebraMap A D)))]`.
  There is no finite-type, Noetherian, rank, field or characteristic assumption.
- `u₀ : Reduced A J D →ₐc[A ⧸ J] Reduced A J C` is precisely a homomorphism of
  the base-changed affine groups. A bialgebra map between Hopf algebras automatically
  preserves antipodes. The lift is the ordinary algebra map `(f : D →ₐ[A] C)`;
  `hf : reduceMap A J f = u₀.toAlgHom` imposes exactly its reduction. In particular
  f is not assumed to be a bialgebra map or to preserve the augmentation.
- `identityCotangent K D0` is `K ⊗[D0,epsilon] KaehlerDifferential K D0`, with the
  D0-action on K obtained from its actual counit. This is the specified identity
  cotangent module. The tensor-Hom adjunction and the existing universal property
  `KaehlerDifferential.linearMapEquivDerivation` give exactly the derivation
  characterization in the node. `identityDifferential` is `1 ⊗ d d`.
- `Coeff A J D` is `Module.Dual K P ⊗[K] J.Cotangent`. Mathlib defines the latter
  as J/(J times J), with its canonical K-module structure. Under `hJ`, the map
  `J.toCotangent : J → J.Cotangent` is bijective: its kernel consists exactly of
  elements whose underlying A-value lies in J², and it is always surjective.
  Consequently this is the actual E=L tensor J of the node, via that canonical
  module identification, with no choice of extra module data. The normalization
  below explicitly uses `J.toCotangent j`, fixing this identification.
- The existential `ρ` is an actual K-linear map E -> E tensor C0.
  `IsCoaction ρ` spells out both coassociativity and counitality using the existing
  tensor associator and right unitor. The `action` definition extends its
  evaluation to E tensor T, multiplying the two T coefficients, exactly as stated.
  Its normalization as the differentiated adjoint action is expressed by the
  conjugation clause with the *cotangent-normalized* κ. This is not a choice of an
  arbitrary representation: at the universal H-point over the flat ring C,
  v=e tensor 1, that clause determines ρ(e), because κ_C is injective. The coordinate
  formula for κ identifies this with differentiating conjugation at the identity,
  as in proof steps 5--6. Thus the claimed representation is fixed even when field
  points do not detect regular maps.
- `κ : Comparison A J D` supplies bijections from E tensor R0 to exactly the
  kernel subtype for every flat commutative A-algebra R. The first clause sends
  v+w to the product of κ(v) and κ(w). This is the additive-group-isomorphism
  assertion, expressed without installing a new, redundant group structure on
  the kernel subtype. Its group law is the existing convolution multiplication
  of points, equivalently the actual multiplication of G(R).
- The next clause is the explicit canonical cotangent normalization: on
  `(φ tensor J.toCotangent j) tensor rbar`, κ has coordinate value
  epsilon_R(d) + a*j*r, where abar=φ(d_e(dbar)). Different lifts a give the same
  value because J²=0. The tensor generators determine κ. This is precisely
  epsilon plus the derivation in the node's proof steps 2--4; no unknown map or
  merely nonempty isomorphism is used to define the notion.
- The next clause, quantified over two flat test algebras and an arbitrary
  algebra map α between them, is the full naturality equation. `reduceMap α`
  is its actual scalar-reduced algebra map, and `TensorProduct.map` extends
  coefficients. No smoothness or finite-type assumption is placed on the tests.
- The conjugation clause evaluates `action ρ` at the reduction of h, and says
  that κ sends that action to f(h)κ(v)f(h)^(-1). Inversion is the explicit
  `inverse` definition, composition with the coordinate antipode. Mathlib's
  convolution `Inv` currently asks for an extraneous bialgebra structure on the
  test ring; spelling out this canonical inverse avoids imposing that hypothesis.
- `Cochain C0 E n` is the actual tensor module E tensor (C0 tensor-power n).
  The recursive tensor power has degree-one value C0, and all higher powers
  associated to the left. Degree zero is K for the evaluation recursion.
  `powerEval` multiplies the images of the coordinate factors; `eval` tensors
  that linear map with id_E. These are regular tensors, never arbitrary functions.
- The existential regular `c` has degree two. `HasDefect A J κ f c` gives the
  displayed defect formula on every pair of points over a flat A-algebra R.
  In particular it includes the universal pair over C tensor_A C, which is flat
  because C is flat. The following quantified clause gives uniqueness among all
  regular tensors satisfying the formula. Conversely the universal formula and
  κ-naturality imply the all-flat formula, so this is the same characterization.
- The four-term cocycle identity is stated after `eval` for all K-algebras T and
  all h,k,l in H0(T), in E tensor T. This includes the universal triple over
  C0 tensor_K C0 tensor_K C0. Evaluation there is the identity under the tensor
  associator, so this is exactly an equality in regular C³; no point-detection
  hypothesis is hidden here. The first term uses the specified coaction action.
- For each regular b of degree one, `(κ C b).val` is a C-point of G, hence an
  actual S-scheme morphism H -> G. Its kernel subtype guarantees reduction to
  the identity section. `correct A J κ f b` is the convolution coordinate map
  of its product with f. The next clause states its reduction is u₀. It then
  gives a regular tensor c_b, its actual defect formula, and the equality
  c_b(h,k)=c(h,k)-(h.b(k)-b(hk)+b(h)) for every K-algebra T. The universal pair
  identifies this with the required equality in C². The order of multiplication
  is beta*f, and the minus sign agrees with the node.
- The final iff is c=0 exactly when
  `comul_C.comp f = (Algebra.TensorProduct.map f f).comp comul_D`.
  Contravariance of Spec and the canonical affine fibre-product tensor
  identification turn this into precisely f composed with m_H = m_G composed
  with (f times f), as an equality of scheme morphisms. It does not silently
  substitute a statement only about field points or assume preservation of identity.

Dependency declarations and source inspection:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
  Read their definitions in Scheme.lean, including contravariance.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `baseChange_morphism_projections`, `baseChange_iterated`, `baseChange_fiber`,
  `baseChange_section_characterization`, `Scheme.Modules.moduleBaseChange` and
  `Scheme.Hom.geometricFiberAt`; read the module and its full signatures/docstrings.
  For the present affine calculation base change is the existing tensor pushout,
  rather than the module functor mistakenly used as a scheme by some consumers.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  read its affine-local smooth-algebra signature and docstring.
- `Mathlib.LinearAlgebra.TensorProduct.Defs/Basic/Map`: `TensorProduct`,
  `TensorProduct.lift`, `TensorProduct.ext'`, `TensorProduct.map`,
  `LinearMap.rTensor`. The file uses the same tensor definition as the Mathlib leaf.
- New node `def-sfb-infinitesimal-regular-cochains` records the constructions
  summarized above and owns all 17 helper definitions, listed in lean.declarations.
- Proof dependencies with recorded modules are imported, including smooth relative
  differentials, tensor pullback, differential base change, locally free affine
  sections, projective modules, flat tensor injection and base change conventions.
  The Kahler definition and fibre-product dependencies are available through the
  public helper import and the base-change import. The three general algebraic-space
  proof dependencies (`lem-sfb-group-space-square-zero-kernel-module`,
  `lem-sfb-space-affine-module-correspondence`,
  `lem-sfb-space-square-zero-lift-linearization`) currently have no Lean record or
  Mathlib match; they are not needed to type this statement, and are named in its
  complete proof docstring. Nothing in their proof is assumed as a binder or
  replicated as an extra theorem.

Edge cases checked before writing and again against the compiled statement:

- J=0: J.Cotangent=0 and E=0; the kernel and defect are trivial. The unique lift
  is the given group map. Zero rank and the trivial group similarly give zero P.
- A=0: no `Nontrivial` instance is requested. Its only unital algebras are zero,
  which are admitted by every definition and quantified test clause.
- Positive characteristic, including 2: there is no field, divisibility or
  characteristic binder and no division in any formula.
- G additive, f(x)=u₀(x)+epsilon*q(x): the defect is q(h+k)-q(k)-q(h).
  Correction adds b, changing the defect by b(h+k)-b(k)-b(h); this verifies the sign.
  Taking q constant nonzero shows why identity preservation must not be assumed.
- Nonflat R is deliberately absent only from κ/HasDefect/naturality: for
  A=k[epsilon]/epsilon², R=k, J tensor R is nonzero while JR=0. Cochain evaluation
  and cocycle/correction identities quantify over every K-algebra, including
  nonflat ones. No flatness on E or J and no rank constancy is required.
- Universal algebras are included in the same explicit universe u as their
  coordinate rings and tensor modules. No independent smaller test universe can
  make the universal tests disappear.

Searches:

- LeanFinder, `Infinitesimal defect of affine group scheme homomorphism lift over
  square zero ideal is regular 2 cocycle`: eight cotangent-extension hits, no match.
- Loogle, `HopfAlgebra, Coalgebra, KaehlerDifferential`: no exact hit.
- LeanSearch, `regular group scheme cochains square zero homomorphism defect`:
  eight arbitrary-group/hom-complex hits, no regular group-scheme theorem.
- LeanSearch, `regular cochains module tensor powers coordinate Hopf algebra
  square zero cotangent identity`: existing cotangent/tensor/coalgebra machinery,
  reused, but no regular-cochain interface.
- LeanFinder, `regular cochains E tensor C tensor powers group scheme and coaction
  evaluation`: tensor coalgebras and finite-group representations, no exact match.
- msearch grep, `regularCochain|identityCotangent|InfinitesimalRegular|IsCoaction`:
  zero Mathlib hits. Other grep, `regularCochain|regularDefect|squareZeroHom|
  SquareZeroHom|adjointCoaction`: zero Mathlib hits.
- rg of the same patterns in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no declaration collision or exact existing theorem.
  Searched the item id in the upstream source: none. Inspected existing
  HopfCoactionLinearization and LieCotangentDual: the former concerns semilinear
  field-algebra modules; the latter concerns Lie algebras over fields, not the
  arbitrary-ring regular square-zero deformation calculation.
- `tools/blueprint_refs.py search regular cochains`: zero blueprint definition nodes.
  `ancestor` reports null, agreeing with the item's existing blueprint.from.node.
  Scanned definition-node statements for regular cochains/cotangent at identity:
  no definition of this construction. The sibling diagonalizable two-cocycle
  lemma also describes cochains in its text but has no recorded definition
  interface replacing the new node. Its notion is not redefined as a second
  existing Lean declaration.
- Opened the actual online Conrad PDF at B.2.5 and B.2.6, including the defect
  expansion and infinitesimal-kernel discussion; used no secondary attribution.
  Source: https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf .

Validation: both delivered files compile cleanly through the prescribed scompile.py,
separately in dependency order, against the live published library. The theorem's
only postponed proof is its own `sorry`. Every helper is a definition with real data.

## New nodes

`def-sfb-infinitesimal-regular-cochains` supplies the notation/interface missing from
this node's existing statement dependencies: actual cotangent-at-identity modules,
coefficient modules, recursive regular tensor cochains and their evaluation/action,
counital coassociative coactions, square-zero kernel subtypes, comparison-family types,
the defect predicate, and the actual correction coordinate map. Source: Conrad B.2,
pp.283--287. The three tool searches and the DAG/source searches are recorded above
and in mathlib_searches, with the search records as produced by msearch.py. Existing
Mathlib tensor, Kahler differential, ideal cotangent, Hopf algebra and Spec constructions
are reused; none is reimplemented. The node has no theorem and no postponed data.
Its statement does not assert the comparison, cocycle or correction theorem: those
remain precisely the item's theorem. `blueprint.from.node=null` and its inherited
via route follow the actual result of blueprint_refs.py ancestor and the item's own
record, whose source is an auxiliary Conrad input below the six-functor unit.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
