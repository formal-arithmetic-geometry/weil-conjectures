## Worker report

Delivered module: `Sheaf.Paper.CompletedCoefficientTensorNormalization`.
Main declaration:
`WeilConjectures.CompletedCoefficientNormalization.completed_coefficient_tensor_normalization`.
The sole postponed proof is that theorem. All helper definitions have real data;
the five structures package its normalized conclusion, rather than adding hypotheses.
The node's statement, dependencies and proof are unchanged. No new DAG node is needed.

Read the node, all seven statement dependencies and their recorded declarations,
the available proof-dependency declarations, and the current blueprint source
`sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`,
paragraph “The integral twist”, particularly its final coefficient-action sentence.
The docstring carries all ten proof steps of the expanded node.

### Hypotheses and objects

- Prime l: `(l : ℕ) [Fact l.Prime]`.
- Arbitrary schemes and morphism: `∀ (T' T : Scheme.{t}) (h : T' ⟶ T)`.
  There is no invertibility, dimension, Noetherian, or finite-field hypothesis.
- Finite coefficient extensions: `(H F : Type u)`, their `Field` and
  `Algebra (Padic l)` instances and `FiniteDimensional (Padic l)` instances.
  `H` plays E in the inclusion paragraph; `iota : H →ₐ[Padic l] F` represents
  the inclusion of finite coefficient fields, including the identity case.
  The general one-field assertion follows by taking F = H and iota = identity.
- The original small pro-etale category is `Scheme.ProEt T`, with topology
  `ProEt.topology T`. Its objects have universe t+1 and morphisms universe t.
  Coefficients have universe `max u (t+1)`; t and u remain independent.
- `discrete` is the sheafified constant `PadicInt l`; `integralDiscrete` is
  the sheafified constant `Padic.coefficientExtensionIntegers l H`.
  The ULifts only put these discrete rings in the common coefficient universe.
- `baseTower` consists of `baseLevel l T n`, the constant ring
  `ZMod (l^(n+1))`, with actual quotient reductions `baseTransition`.
  `baseCompletion` is `Limits.limit`, and `baseProjection` is `limit.π`.
- R_H,T and its projections are precisely the dependency's
  `completedIntegralCommRingSheafUnrestricted` and
  `completedIntegralCommRingProjectionUnrestricted`.
  Their finite levels use the dependency's chosen uniformizer and its ideals.
  Any other uniformizer generates the same ideal powers; no hypothesis fixing
  an additional uniformizer or a ramification index is imposed.

### Every formula and normalization

| Node clause | Lean rendering |
| --- | --- |
| epsilon takes a to all compatible residues | `BaseData.epsilon` and `BaseData.residue`, using the actual maps `baseResidue` induced by `PadicInt.toZModPow` |
| D_T acts on B_H,T by its actual scalar inclusion | `Presentation.integers_spec` fixes the ring homomorphism by the injective inclusion O_H into H; `scalar` sheafifies that map |
| sheafified balanced tensor | `tensor` is `pushout (d.epsilon T) (scalar ... T)` in commutative ring sheaves |
| beta is an isomorphism of ring sheaves | `Presentation.beta : ∀ T, tensor ... T ≅ completedIntegralCommRingSheafUnrestricted ... T` |
| nth projection on a pure tensor, for every admissible k | `Presentation.projection`, with n and k indexing exponents n+1 and k+1, and the exact ideal containment as antecedent |
| residue scalar multiplication pr_k(x) times b-bar | the final equation of `Presentation.projection`, on arbitrary sheaf sections x and b, using `residueFromBase` and `integralResidue` |
| finite scalar map is the canonical residue map | the first conjunct in `Presentation.projection` specifies its composite with `PadicInt.toZModPow` on every l-adic integer |
| independence of k | `Presentation.projection` quantifies over every admissible k and fixes the same beta projection for all of them |
| delta_C is canonical and preserves constant sections | `delta` is the adjoint of the sheafification of the constant-section map, the defining construction of the recorded pro-etale coefficient comparison |
| delta_C is invertible | `BasePullback.constant_iso`, for every discrete commutative coefficient ring C in the common universe |
| alpha_0 and alpha_H are projection-induced | `BasePullback.projection` and `Pullback.projection` specify their composites with every projection using delta on exactly the corresponding quotient ring |
| alpha_0 h^-1 epsilon = epsilon' delta_Z_l | `BasePullback.epsilon_square` |
| delta_O_H respects delta_Z_l scalars | `Pullback.scalar_square` |
| canonical inverse-image tensor comparison sigma | `Pullback.sigma` has target `pulledTensor`, the pushout of the inverse images of the two scalar maps |
| sigma is normalized on inverse images of pure tensors | `Pullback.sigma_left` and `sigma_right` fix it on both factor inclusions; their product is the inverse image of a pure tensor |
| alpha_0 tensor delta_O_H with indicated scalar identifications | `Pullback.change`, fixed on the two factor inclusions by `change_left` and `change_right` |
| alpha_H h^-1 beta = beta' (alpha_0 tensor delta_O_H) sigma | `Pullback.beta_square` (Lean composition runs left to right) |
| q_EF is the constant inclusion | `Extension.integers_spec` fixes the restriction of iota to integer rings, and `constantInclusion` is its constant-sheaf map |
| i_EF comes from ramified finite quotient maps | `Extension.admissible` supplies suitable indices, and `Extension.projection` gives the formula for every admissible pair k,n; `quotientInclusion` uses `Ideal.quotientMap` of the actual integral inclusion |
| 1 tensor q_EF | `Extension.tensorMap`, fixed by `tensor_left` (identity on A) and `tensor_right` (q on B) |
| i_EF beta_E = beta_F (1 tensor q_EF) | `Extension.beta_square` |
| alpha_F h^-1 i_EF = i_EF alpha_E | first conjunct of the main theorem's final conclusion, using the same BasePullback witness for E and F |
| delta_O_F h^-1 q_EF = q_EF delta_O_E | second conjunct of that conclusion |
| equalities are ring-sheaf maps | all arrows and isomorphisms live in `Sheaf (ProEt.topology T) CommRingCat`, and the section formula evaluates those maps |

The commutative-ring pushout is an existing presentation of the balanced ring tensor,
not an additional tensor operation on modules. Mathlib's `CommRingCat.pushoutCocone`
and `pushoutCoconeIsColimit` in `Mathlib.Algebra.Category.Ring.Constructions` identify
ring pushouts with algebraic balanced tensors. `Sheaf.sheafifyCocone` and
`Sheaf.isColimitSheafifyCocone` in `Mathlib.CategoryTheory.Sites.Limits` compute
sheaf pushouts by sheafifying the presheaf colimit. Thus the pure tensor in the
formula is exactly the product of the two pushout inclusions. This is the same
sheafification/balanced-tensor notion of def-pur-sheaf-tensor-product, with the
ring structure retained as the node requires. It introduces no separate module
tensor, completion, or coefficient category.

Every witness is normalized before use. Epsilon is fixed by all limit projections;
its integer-ring scalar maps are fixed by the field inclusions. The quotient maps
from ZMod are fixed by their composites with the surjective PadicInt residue maps.
Beta is fixed by its values on pure tensors at all finite projections, alpha and i
by all finite projections, and sigma/change/tensorMap by their factor inclusions.
The theorem existentially supplies these canonical maps; none of the compatibility
conclusions is assumed in the theorem's inputs. No `Nonempty` choice defines data.

### Dependencies used

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`, the existing small site.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleBaseChange`, its continuity, and the recorded inverse-image and
  constant-section-adjoint constructions. `inverse` uses exactly the same
  `Functor.sheafPullbackConstruction.sheafPullback`; `delta` uses exactly its
  adjunction and the constant-presheaf sheafification unit. These helpers only
  specialize the already recorded general construction to the common coefficient
  universe. They do not substitute another geometric morphism or add a hypothesis.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Limits.limit`, `limit.π`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, publicly reexporting
  `Sheaf.Paper.CompletedIntegralCoefficients`: the existing coefficient sheaves,
  inverse sequence, completion and commutative ring projections. `integralResidue`
  is its actual constant quotient map before forgetting commutativity.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `CategoryTheory.constant_left_module_inverse_image`, for constant ring
  invertibility/naturality in the planned proof. The explicit delta is the
  specified constant-preserving comparison, rather than an unspecified witness
  from that theorem's existence result.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  independent-universe sheaf tensor interface; the ring presentation above uses
  the existing categorical pushout and sheafification descriptions of that tensor.
- Proof imports: `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`,
  `Padic.exists_integral_basis`; `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages`,
  `Padic.local_field_coefficient_stages`; `Mathlib.NumberTheory.Padics.PadicNumbers`
  and `RingHoms` for the base l-adic field and `PadicInt.toZModPow`;
  `Mathlib.CategoryTheory.Sites.LeftExact` and `Sheafification` for exact
  sheafification and its adjunction.

The recorded scheme inverse image's shorthand has a specialized category Hom
universe. The underlying Mathlib Kan/sheafification construction is already general.
The helper `kan` applies its existing pointwise Kan extension after restricting
CommRingCat colimits to indexing sizes (t,t+1). Explicit universe arguments on
`inverse` and `delta` avoid erroneously solving `t+1 = max u (t+1)`.
All instance evidence is supplied by existing Mathlib constructions, with no sorry.
The harmless checkUnivs warning is disabled for aliases whose universes only
occur through the common maximum; this imposes no universe equation.

### Edge cases checked before writing

- Empty scheme and arbitrary scheme morphism: no nonemptiness assumption or
  restriction on characteristic; constant sheafification and categorical limits
  and pushouts still make sense, including trivial section rings.
- l = 2 and residue characteristic l: only primality is assumed. No use of
  invertibility on a scheme occurs in the tensor calculation.
- H = Q_l: the presentation reduces to the base coefficient presentation after
  identifying its valuation ring with Z_l; the integral scalar map is fixed by
  its inclusion into the field, not by a chosen basis.
- Identity coefficient inclusion and identity scheme morphism are included.
- Ramified extensions and arbitrary larger admissible indices: the projection
  fields quantify over every ideal containment, not only equal exponents or an
  arbitrarily selected cofinal subsequence.
- The first level is exponent one. Exponent zero is not silently substituted;
  n,k range over ℕ and every finite quotient exponent is n+1,k+1.
- Independent scheme/coefficient universes survive the size repair.

### Searches actually made

- `msearch.py`, leanfinder query
  “Inverse image of completed coefficient ring sheaves compatible with tensor presentation”:
  eight hits, including module-presentation transport, algebra presentation tensor
  models and `ModuleCat.tilde`; none states this normalized completed ring-sheaf diagram.
- `msearch.py`, loogle query `Algebra.TensorProduct.lift`:
  twelve hits, including the lift, its pure-tensor and inclusion equations,
  and `Algebra.pushoutDesc_apply`; generic algebraic tensor interfaces only.
- `msearch.py`, grep query `completed.*[Tt]ensor|[Tt]ensor.*[Cc]omplet`:
  nine Mathlib hits, chiefly algebraic adic completion/tensor results and unrelated
  analytic tensors; no completed coefficient sheaf normalization theorem.
- `msearch.py`, leansearch query
  “Completed constant coefficient ring sheaf is the tensor product of completed p-adic integers and discrete integers of a finite local field, naturally under inverse image”:
  eight hits in `AdicCompletion.AsTensorProduct` and `AdicCompletion.Algebra`;
  these are algebraic module completions and do not supply this sheaf statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with the completed/tensor pattern:
  found existing completed derived tensors, scalar comparisons and normalization
  interfaces for other constructions; none has this base-discrete-ring tensor
  presentation. Search for this node id in `lean/WeilConjectures` found no declaration.
- `rg` for the proposed namespace and theorem name in Mathlib, both project roots,
  and `dag/lean_names_upstream.json` found no collision.
- Read the existing Mathlib ring pushout/tensor construction and the sheaf colimit
  sheafification construction to use their universal presentations directly.

No statement dispute, source correction, dependency-node rewrite, or additional
independent mathematical notion was needed. Compiler validation and the delivery
preflight are performed with the prescribed wrappers; the maintainer supplies
independent review.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
