## Worker report

Item: lem-a1-affine-groupoid-coordinate-identities. Group: Q88. Stage: 2.

The module `Sheaf.AlgebraicGeometry.AffineGroupoidCoordinateIdentities` states
`AlgebraicGeometry.affineGroupoid_coordinate_identities`, with its sole proof
`sorry`. Three data-only helpers package the specified Mathlib tensor ring and
its two standard inclusions: `affineGroupoidTensorRing`, `affineGroupoidTensorLeft`
and `affineGroupoidTensorRight`. They belong to the coordinate notation of this
node and are listed in `lean.declarations`. They introduce no alternative tensor
product, subring, groupoid definition, or independently chosen map.

Hypothesis and clause correspondence:

- Commutative rings A and B are `(A B : CommRingCat.{u})`. The schemes U and R
  are exactly `Spec A` and `Spec B`; bundling does not impose nontriviality.
- The arbitrary source and target morphisms are `(s t : Spec B ⟶ Spec A)`.
  The identity, inverse and composition maps are the binders `e`, `i` and
  `c : pullback s t ⟶ Spec B`. The hypothesis `_hG : IsGroupoidScheme s t e i c`
  uses the recorded groupoid declaration, including its convention
  `c(alpha,beta) = alpha ∘ beta`, source from `pullback.snd` and target from
  `pullback.fst`. No finiteness, flatness or freeness hypothesis is imposed.
- Sigma, tau and epsilon are `(Spec.preimage s).hom`, `(Spec.preimage t).hom`
  and `(Spec.preimage e).hom`, respectively. `Spec.preimage` is the inverse
  equivalence to `Spec.map`, so these are exactly the induced coordinate maps.
- D is `affineGroupoidTensorRing (Spec.preimage s) (Spec.preimage t)`.
  Its underlying type is Mathlib's `TensorProduct A B B`, with its first module
  structure explicitly `sigma.toAlgebra.toModule` and its second explicitly
  `tau.toAlgebra.toModule`. Its commutative-ring structure is exactly
  `Algebra.TensorProduct.instCommRing` with these two algebra arguments.
  Thus the first B acts over A through sigma and the second through tau;
  Lean cannot accidentally select the same algebra structure for both.
- The maps p0 and p1 are `affineGroupoidTensorLeft` and
  `affineGroupoidTensorRight`, respectively. These are exactly
  `Algebra.TensorProduct.includeLeftRingHom` and the underlying ring map of
  `Algebra.TensorProduct.includeRight` with the same explicit algebra
  structures. Hence they send b to b tensor 1 and 1 tensor b. The latter's
  `AlgHom.toRingHom` is also passed its domain and tensor algebra structures
  explicitly; both helpers contain actual data, with no postponed proofs.
- The fibre-product identification is the existential `F : pullback s t ≅
  Spec (affineGroupoidTensorRing ...)`. Its first two conjuncts say
  `F.inv ≫ pullback.fst s t = Spec.map p0` and
  `F.inv ≫ pullback.snd s t = Spec.map p1`. These specify the canonical
  identification by both projections; its existence is a theorem conclusion,
  rather than extra input or a choice used to define any object.
- Under this identification, Delta is precisely
  `(Spec.preimage (F.inv ≫ c)).hom`. The arrow has domain Spec D and codomain
  Spec B, so its coordinate map has domain B and codomain D.
- `epsilon sigma = id_A` and `epsilon tau = id_A` are the first two conjuncts,
  written using `RingHom.comp` and `RingHom.id A`.
- `p0 sigma = p1 tau` is the third conjunct inside the existential, with
  `.hom.comp (Spec.preimage s).hom` on the left and composition with
  `(Spec.preimage t).hom` on the right.
- `Delta sigma = p1 sigma` and `Delta tau = p0 tau` are the last two
  conjuncts inside the existential. Their second and first tensor-factor
  inclusions, respectively, agree with the source/target ordering above.
- Injectivity of sigma and tau is stated in the third and fourth top-level
  conjuncts using `Function.Injective` on the two underlying ring maps.
- C is the existing Mathlib unital subring
  `RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom`. Reading
  `Mathlib.Algebra.Ring.Subring.Basic` shows that its carrier is definitionally
  `{a | sigma a = tau a}`; its `Subring A` type supplies zero, one, additive
  inverse, addition and multiplication closure. The fifth top-level conjunct
  equates the two `RingHom.domRestrict` maps to this exact C. Thus the
  assertion that the invariant set is a unital subring is expressed by the
  existing typed construction, and equality of its restrictions is asserted
  explicitly. There is no arbitrary invariant subring parameter.

Dependency declarations read and used:

- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`; coordinate recovery and
  contravariant functoriality are `Spec.preimage`, `Spec.homEquiv`,
  `Spec.preimage_comp` and `Spec.map_preimage` in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- def-a1-groupoid-scheme: `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme`. Its entire structure signature and
  docstring were read, especially identity_source, identity_target,
  composition_source and composition_target.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and
  `pullback.lift`, available through the recorded groupoid module's public
  `Mathlib.AlgebraicGeometry.Pullbacks` import.
- def-weil-pbc-module-tensor-product: the recorded Mathlib match
  `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`, with
  `TensorProduct.tmul` and `TensorProduct.lift`; no Lean record repair is
  needed for a Mathlib leaf.
- lem-weil-pbc-algebra-tensor-pushout-universal-property: the recorded
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight` and `ext` in `Mathlib.RingTheory.TensorProduct.Basic`.
  The full match's `productMap` and its two inclusion formulas were read in
  `Mathlib.RingTheory.TensorProduct.Maps`; that module is a plain proof import.
- Proof-only lem-weil-pbc-fibre-product-affine-spectra: the recorded Mathlib
  `AlgebraicGeometry.pullbackSpecIso`, `pullbackSpecIso_inv_fst` and
  `pullbackSpecIso_inv_snd` in `Mathlib.AlgebraicGeometry.Pullbacks`, already
  publicly available through the groupoid dependency.

Sources checked directly: `literature/stacks-project/groupoids.tex`,
`lemma-basis` (03C8), its tensor notation and first diagram; `lemma-diagram`
(02YE), its source/target triangles; and `equation-invariants`. In particular
03C8 explicitly has `c(t(x_i)) = p0(t(x_i))`, matching the last conjunct.
The imported node and its accepted stage-1 split remain unchanged outside `lean`.
There is no statement correction, missing prerequisite, or disputed assertion.

Edge cases checked before and during drafting:

- A = B = the zero ring: both spectra and their pullback are empty; D is the
  zero tensor ring, all coordinate identities hold, both functions on the
  singleton underlying ring are injective, and the invariant subring is all A.
  No `Nontrivial` assumption excludes this case.
- The identity groupoid s = t = e = i = identity has D = A tensor_A A,
  the canonical multiplication identification, and C = A.
- For the pair groupoid, an arrow alpha goes y to z and beta goes x to y.
  On a composable pair, p0 sigma and p1 tau both evaluate at y, while
  Delta sigma = p1 sigma evaluates at x and Delta tau = p0 tau at z.
  This checks both tensor factor order and the two non-interchangeable
  composition equations.
- Equality sigma = tau gives the full subring; unequal maps give their
  genuine equalizer. No nonempty index set or test-point universe occurs.
- All rings and schemes use the explicitly bound universe u; any two rings
  may be placed in a common universe. No automatic implicit binder is used.

Searches run for reuse (the msearch wrapper records the actual queries):

- LeanFinder: "Affine groupoid scheme coordinate ring identities counit source
  target comultiplication tensor product". Eight affine-space/coordinate
  hits, including `AffineSpace.isoOfIsAffine_inv_appTop_coord`,
  `AffineSpace.homOfVector_toSpecMvPoly`, and
  `AffineSpace.SpecIso_hom_appTop`; none states these groupoid identities.
- Loogle: `AlgebraicGeometry.pullbackSpecIso, RingHom.eqLocus`. Zero hits for
  the combined query. Both individual constructions were subsequently located
  and read directly in Mathlib and reused, as documented above.
- Mathlib grep via msearch:
  `HopfAlgebroid|affineGroupoid|groupoid.*[Cc]oalgebra|[Cc]oalgebra.*groupoid`.
  Zero hits.
- LeanSearch: "Affine groupoid coordinate rings have source target ring maps
  with a common retraction and a composition map to their tensor product".
  Eight hits, chiefly affine-map composition and affine-scheme facts; no match.
- Project `rg` with the same groupoid pattern, plus the proposed declaration
  names in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`. Related invariant-norm, integral-invariant,
  orbit-fibre and basis-descent modules exist, but no coordinate-identity
  theorem or proposed helper declaration does. The basis-descent theorem was
  opened and read; it states a basis and tensor comparison under an additional
  finite-basis hypothesis, not this node's identities.
- The required `grep -rn` of the item id in `lean/WeilConjectures` has no hit.
- Direct Mathlib grep located `RingHom.eqLocus` and the tensor inclusions,
  and their full signatures and docstrings were read. The equalizer ring is
  reused rather than redefined.

Validation: every compiler invocation uses the prescribed `scompile.py`.
The initial check identified implicit algebra inference at `includeRight.toRingHom`;
explicit projection arguments repair that issue without changing the statement.
The final module compiles in both the sandbox and library checks with no errors or
non-sorry warnings. `deliver2.py Q88 lem-a1-affine-groupoid-coordinate-identities
--no-push` returned `OK (dry run): commit d948a240333 passes the preflight and
compiles; nothing pushed`. The completed packet is rechecked before pushing.

## Second reading by Q88

A separate self-review pass reopened the node and final Lean source together;
the maintainer supplies the independent review specified in the assignment.
The ring, scheme and five map binders match the node, and the sole mathematical
hypothesis is the exact recorded `IsGroupoidScheme`. Both tensor module structures
are explicit in the actual data. The isomorphism has the correct direction and
both projection equations; Delta is obtained from `F.inv ≫ c`, so no unrelated
comultiplication is assumed. Reading the five ring-map equations individually
confirms epsilon-sigma, epsilon-tau, p0-sigma/p1-tau, Delta-sigma/p1-sigma and
Delta-tau/p0-tau, with neither factor reversed. Both injectivities and equality
of the two restrictions to Mathlib's exact invariant subring are present.

The subring clause was checked against the implementation of `RingHom.eqLocus`,
not inferred from its name. Its carrier and unital closure are exactly the
node's C. The existential isomorphism is constrained by both projections and
does not introduce an arbitrary-map hypothesis or a data choice from `sorry`.
The three helpers merely package existing constructions needed to distinguish
the two algebra structures on B, and are all registered in the same node.
No missing clause, strengthened hypothesis, silent statement change, duplicate
notion, unbound universe, or additional postponed theorem was found.
