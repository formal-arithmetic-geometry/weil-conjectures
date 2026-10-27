## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung` states
`AlgebraicGeometry.AffineGroupFrobeniusVerschiebung.frobenius_verschiebung`.
Its only theorem proof is `sorry`. Every helper definition has actual data. The repair adds one definition node attached to an existing instance. No source
statement correction, disputed statement or dependency-module repair is needed.

The source was read in `literature/milne-algebraic-groups_iAG2017.pdf`, PDF pp. 236–237,
printed pp. 224–225: Definition 11.39, its coordinate diagram and Proposition 11.40(a).
The theorem follows the node's expanded orbit-basis formulation of that diagram.
The example CompactObject module has been withdrawn in the current checkout; its node and
the module-mode/header conventions in the standing brief were read.

Hypothesis and clause correspondence (helper names below are in the theorem's namespace):

- The field is `(k : Type u) [Field k]`. Positive characteristic is `(p : ℕ)` with
  `[Fact p.Prime] [CharP k p]`. Primality is forced by the field characteristic; `0` and `1`
  cannot be its positive characteristic.
- The given affine k-group scheme is `(G : Scheme.{u})`,
  `[G.Over (Spec (CommRingCat.of k))]`, `[IsAffine G]` and
  `[GrpObj (G.asOver (Spec (CommRingCat.of k)))]`. Commutativity is the separate
  `IsCommMonObj` binder, exactly as the recorded group-scheme dependency specifies.
- Finite type is the conjunction represented by `LocallyOfFiniteType` and `QuasiCompact`
  on the structure morphism. No smoothness, connectedness, reducedness, perfection,
  finite-dimensionality or algebraic-closure binder occurs.
- `C=k[G]` is `Γ(G, ⊤)`. Its algebra and Hopf structures come from the existing
  `HopfAction.coordinateHopfAlgebra`, which exposes Mathlib's canonical instance. This
  is the coordinate Hopf algebra of the given operations, rather than an arbitrary Hopf
  structure. The new definition node `def-sfb-coordinate-hopf-algebra` owns this unchanged
  existing instance and is cited in `stmt_deps`. The coaction-linearization theorem
  is not a statement dependency.
- `sigma` is Mathlib's `frobenius k p`. `twist k p C` is the ring pushout of
  `algebraMap k C` and `frobenius k p`; this is `C ⊗_{k,sigma} k` by the tensor pushout
  universal property. `first` is the pushout's left leg, `twistAlgebra` its right-leg
  k-algebra structure, and `pure k p C a c` is the product of the two legs, hence
  `a ⊗ c`. The pushout equation gives `first (r*a) = r^p * first a`. This uses no inverse
  of sigma. Ring pushouts and tensor products are existing Mathlib constructions.
- `G^(p)` is explicitly `Spec (twist k p Γ(G, ⊤))` over `Spec k`.
  `Maps` existentially supplies the base-changed algebra maps `D`, `E`, `S`, fixing them
  on every `first a`: respectively `twistedComulGenerator ... a`, `epsilon(a)^p`, and
  `first (antipode a)`. Their k-algebra-map types fix the second-factor scalars, so the
  pushout universal property determines the maps completely. `twistedComulGenerator`
  uses Mathlib's proved `Coalgebra.Repr.arbitrary` finite tensor presentation; the result
  is determined by its tensor, not by a postponed existence theorem.
- `GroupMaps` supplies a `GrpObj` on this same spectrum and identifies its multiplication,
  identity and inverse with `Spec D` (via `pullbackSpecIso`), `Spec E` and `Spec S`.
  Thus the existential group structure is precisely the base-changed one. It is not an
  unconstrained group structure or a hypothesis replacing a construction. No data is
  extracted from the main theorem to define any helper.
- The relative Frobenius coordinate map is `f : twist ... →ₐ[k] Γ(G, ⊤)` with
  `∀ a c, f (pure ... a c) = c • a^p`. In `GroupMaps`, `F.left` is explicitly
  `G.isoSpec.hom ≫ Spec.map f.toRingHom`; `IsMonHom F` states it is a group homomorphism.
- The tensor power is Mathlib `PiTensorProduct k (fun _ : Fin p ↦ C)`.
  `invariants` is the intersection of kernels of permutation reindexing minus identity,
  so it is precisely the fixed subspace. The inverse convention in `reindex` makes no
  difference when quantifying over every permutation.
- `orbit p t` is the finite image of all permutations on a tuple `t`, so every distinct
  tuple is counted once. `orbitSum` sums its pure basis tensors. The first theorem
  conjunct supplies a `Module.Basis` indexed by the range of these orbit finsets, with
  each basis vector explicitly equal to that orbit sum. Equal orbits have one index.
- `projectionForBasis` is a real linear construction: apply the tensor basis `repr`, then
  the finitely supported linear combination that sends each constant tuple to
  `first (B b)` and each nonconstant tuple to zero. The second theorem conjunct explicitly
  gives the corresponding values on the orbit sums. Since `p > 0`, a singleton orbit is
  exactly a constant tuple. Hence this is precisely the node's lambda specification.
- `projection` uses `Module.Basis.ofVectorSpace` and `invariantProjection` restricts it
  to invariants. The third theorem conjunct equates every basis-defined restriction
  with `invariantProjection`, asserting basis independence rather than assuming it.
  The extension to the whole tensor power is allowed to depend on the basis.
- `iteratedComul` recursively composes the existing coproduct, tensor maps, singleton
  equivalence and tensor concatenation/reindexing. Its arity-zero value is the counit.
  The fourth theorem conjunct asserts its arity-p image is invariant. `Maps` specifies
  `v a = projection ... (iteratedComul ... p a)`, hence exactly `v=lambda Delta_p`.
- `v` and `f` are k-algebra maps. The six equalities in `Maps` assert separately that each
  preserves comultiplication, counit and antipode. Thus preservation of multiplication,
  unit, scalars and all Hopf operations is included explicitly.
- `GroupMaps` specifies `V.left = Spec.map v.toRingHom ≫ G.isoSpec.inv` and
  `IsMonHom V`. This is the spectrum homomorphism of the fully specified coordinate map.
  Its final equality `F ≫ V = 𝟙 (...) ^ p` uses Mathlib's existing convolution group
  of scheme-valued points: the power of the identity morphism is multiplication by p.
  Postcomposition on any algebra-valued point therefore sums p copies. The order is
  Lean's left-to-right composition, so it states exactly `V_G ∘ F_G = [p]_G`.

Dependencies and existing declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Algebra/Field/Defs.lean`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `IsCommMonObj`, `IsMonHom`,
  `CategoryTheory.Hom.group`, read in Monoidal/Grp, Monoidal/Mon and
  Monoidal/Cartesian/Grp; the interpretation of `[p]` was also read in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, with
  their full class signatures read in their recorded Mathlib morphism modules.
- `lem-sfb-affine-group-coordinate-hopf`: Mathlib `AlgebraicGeometry.Group.Affine`'s
  canonical global-sections Hopf instance (lines 337–343); `Coalgebra.comul/counit`,
  `Bialgebra.comulAlgHom/counitAlgHom`, `HopfAlgebra.antipodeAlgHom`, with their signatures,
  axiom declarations and documentation read. This dependency is a Mathlib match and
  does not require a new `lean` record.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec` and `Spec.map`,
  read in `Mathlib.AlgebraicGeometry.Scheme`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded tensor ring,
  `includeLeft`, `includeRight`, `productMap`, `productMap_apply_tmul`, `ext`, and
  `Algebra.TensorProduct.map`, read in TensorProduct/Basic and Maps. The pushout realization
  and tensor universal property were read in `Mathlib.Algebra.Category.Ring.Constructions`.
- `lem-sfb-hopf-spectrum-functor`: Mathlib `AlgebraicGeometry.hopfSpec`, with the
  full signature and its construction, and the existing operation identifications
  `mul_spec_asOver_spec_left`, `one_spec_asOver_spec_left`, read in Group/Affine.
- `def-weil-module-base-change` (proof dependency): `LinearMap.baseChange` and its tensor
  formula were read in `Mathlib.LinearAlgebra.TensorProduct.Tower`, imported privately.
- `def-sfb-coordinate-hopf-algebra` (new definition node, existing declaration):
  `HopfAction.affineCoordinateHopfAlgebra` and `HopfAction.coordinateHopfAlgebra`, from
  `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`, with full signatures/docstrings read.
  Only these real-data interfaces are used; no coaction theorem is assumed here.
- `lem-sfb-symmetric-invariant-frobenius-projection` has no Lean record or Mathlib match
  in the read state. It is only a proof dependency, not needed to type this statement:
  the required concrete coordinate projection is supplied here. Its full intended use
  remains in the main theorem's proof docstring. There is no missing premise or wait.

All helper declarations belong to this same coordinate construction and are listed in
`lean.declarations`; none is a separately assumed theorem. `Maps` and `GroupMaps` package
clauses of the one owning theorem to keep class instances explicit. The local `letI` inside
`GroupMaps` exposes the supplied group structure's own `MonObj`; there is no let binder in
the theorem statement and no file-local notation, private definition or local instance.

Edge cases checked before and after drafting:

- Over imperfect fields the pushout uses sigma itself, not a presumed inverse. For a
  changed basis `b'=r*b`, its pure p-tensor has coefficient `r^p`, exactly matching
  `first(r*b) = r^p first(b)`.
- The additive group has Frobenius `x ↦ x^p` and Verschiebung zero, consistent with
  primitive coproducts and the asserted multiplication-by-p composite. The multiplicative
  group has group-like coproducts and the expected nonzero Verschiebung.
- Infinitesimal groups such as alpha_p and mu_p are included; the statement assumes
  neither smoothness nor reducedness. Disconnected finite etale groups are included too.
- Arbitrary, potentially infinite bases have finite tensor expansions (`repr` is Finsupp);
  only the p! permutation set is enumerated, never the infinite basis set.
- Repeated entries in a tensor tuple do not introduce stabilizer multiplicities because
  `Finset.image` removes duplicates. For p=2 a nonconstant orbit has two distinct terms
  and is killed, while a constant tuple maps to `b ⊗ 1`.
- p=0 and p=1 are excluded by the actual positive field characteristic, not by an extra
  mathematical assumption. `iteratedComul 0` is nevertheless well defined by the counit.
  An empty basis index is covered syntactically; a coordinate algebra of a group over a
  field is nonzero because of its counit. No empty scheme can carry such a group identity.
- All universe variables and binders are explicit (`autoImplicit false`). The coordinate
  ring and its bases are in the scheme's universe u; tensor products are not restricted
  to finite-dimensional spaces.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`: “For a commutative affine group scheme in characteristic p
  Verschiebung constructed from invariant tensors satisfies V composed with relative
  Frobenius equals multiplication by p”. Eight WittVector hits; no affine-group result.
- `msearch.py ... loogle '"verschiebung"'`: twelve WittVector declarations, no affine-group
  construction or theorem.
- `msearch.py ... leansearch`: “Verschiebung on an affine commutative group scheme defined
  using symmetric invariant tensors and relative Frobenius has composite multiplication
  by p”. Eight WittVector results; no match.
- `msearch.py ... grep 'verschiebung|relativeFrobenius|FrobeniusTwist'`: 25 displayed hits,
  all WittVector operators/identities, no match for this statement.
- Direct `rg` in Mathlib AlgebraicGeometry, HopfAlgebra and PiTensorProduct for
  `verschiebung|relativeFrobenius|relative_frobenius|symmetricInvariant|projectionForBasis|iteratedComul`:
  no relevant construction. Tensor basis/reindexing and the vector-space basis were read
  and reused rather than duplicated.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: existing relative Frobenius
  material concerns model/geometric-fiber Frobenius, not this group's Frobenius twist
  together with Verschiebung and invariant-tensor projection. No matching theorem.
  The explicit item-id search in `lean/WeilConjectures` found no result.
- A coordinate-Hopf helper search found `HopfAction.coordinateHopfAlgebra`; the draft's
  temporary duplicate aliases were removed and that landed declaration is imported.

Validation: the final module is checked through the prescribed `scompile.py` in both sandbox
and library module mode; only the main named theorem is postponed. Delivery dry-run and
push results are recorded by the wrapper. No direct edit or git operation was made in the
shared checkout, no launcher file was modified, and no global/local direct build was run.

## New nodes

`def-sfb-coordinate-hopf-algebra` owns the canonical field-coordinate Hopf instance
`HopfAction.coordinateHopfAlgebra`, with `existing: true` in
`Sheaf.AlgebraicGeometry.HopfCoactionLinearization`. Its definition has exactly
`(k : Type u) [Field k] (H : Scheme.{u})`, the given `H.Over (Spec (.of k))`,
`GrpObj (H.asOver (Spec (.of k)))`, and `IsAffine H`; the result is
`HopfAlgebra k Γ(H, ⊤)`. These binders render every hypothesis of the new node.
Its body is the existing `affineCoordinateHopfAlgebra (.of k) H`, and that bundled
helper is `inferInstance` for Mathlib Group/Affine:337-343. This fixes the scalar
structure and all three Hopf maps to the given group operations. Stacks 022S
(definition-group-scheme and the following identity/inverse discussion) is the source.

The new node records raw LeanSearch, Loogle and Mathlib-grep outputs. LeanSearch
returned eight general global-sections/Hopf-algebra hits; Loogle returned twelve
Hopf-algebra declarations; Mathlib grep returned four hits including the canonical
coordinate instance. Direct project grep found the existing field interface only
in HopfCoactionLinearization; the declaration-name DAG hits attach it to a theorem
node, not a definition node. `blueprint_refs.py search 'coordinate Hopf'` returned
zero blueprint nodes; `ancestor` reports the inherited null blueprint ancestor,
which is retained with the item's complete via chain. Thus this is an existing
interface attachment, not a second construction. No new Lean module is delivered.
No finite-type, commutative-group, smoothness, reducedness or perfection hypothesis
is added to this general coordinate definition. The trivial group, additive group,
multiplicative group and nonreduced affine groups are all included.

## Repair of returned immutable head 96741b6f8055

The H2 return is repaired by replacing the previously added theorem dependency
`lem-sfb-hopf-coaction-linearization` with `def-sfb-coordinate-hopf-algebra`.
The coaction theorem's conclusion is not needed to state the item. The definition
node now records the exact existing instance used by the unchanged import.
Compared with the current main node, only `lean` and the permitted new-definition
addition in `stmt_deps` differ. The natural-language statement, proof, proof_deps,
and the Lean source (including its signature and every helper body) are unchanged
from the returned packet. No source-based statement correction is involved.

## Second reading by NY

Repair self-check by this worker (no separate agent was started, as instructed):
read the new node, the existing instance and its bundled helper, Mathlib's
coordinate-instance body, and the saved item source. The field, over-scheme,
group-object and affineness hypotheses of the new node match the instance
exactly; the helper specializes the canonical construction at `.of k`, rather
than choosing a new Hopf structure. The item still has exactly the hypotheses
and every clause matched above in the Worker report. The sole mismatch identified
by the maintainer was the ownership of the scalar-inference helper, and it is
now corrected in the DAG without changing Lean. Independent immutable-head
review remains with the maintainer.
