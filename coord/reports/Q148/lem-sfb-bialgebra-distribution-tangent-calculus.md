## Worker report

The module `Sheaf.RingTheory.BialgebraDistributionTangentCalculus` states
`BialgebraDistribution.finiteOrderConvolutionAndTangentDerivations`. Its only
postponed proof is that named theorem. The eight helper definitions are real
constructions belonging to this node's own filtration and tangent-calculus
interface; all are listed in `lean.declarations`. No new DAG node, dependency
repair, or statement correction is needed.

Hypotheses and clauses, matched with the Lean file:

- A field is `(k : Type u) [Field k]`. The commutative unital algebra is
  `(C : Type v) [CommRing C] [Bialgebra k C]`. Mathlib's `Bialgebra` includes
  `Algebra k C`, both linear maps, the coalgebra coassociativity and counit laws,
  and multiplicativity and unitality of each map. `Bialgebra.comulAlgHom` and
  `Bialgebra.counitAlgHom` package exactly the node's algebra maps. No antipode,
  cocommutativity, finite generation, finite dimension, or characteristic is imposed.
  The universes `u v` are independent and explicitly bound; `autoImplicit` is false.
- `I = ker ε` is `augmentationIdeal`, the actual `RingHom.ker` of the counit.
  `finiteOrder k C n` is the dual annihilator of the restricted-scalar submodule
  of `I^(n+1)`: exactly the linear functionals zero on that ideal power. Its
  `Submodule` type supplies its vector space structure without a separate proof.
  `orderFiltration` extends this to integers with bottom at negative indices,
  so in particular `F_(-1)=0`. `distributions` is the set of maps belonging to
  some `finiteOrder k C n`, precisely the set union in the node.
- `convolution` unwraps the product already defined by Mathlib on
  `WithConv (C →ₗ[k] k)`. `LinearMap.convMul_def` is multiplication after
  `TensorProduct.map a b` after `comul`, hence exactly `(a ⊗ b)(Δc)` with
  the scalar tensor identification. It is an alias of the existing operation.
- The first conjunct exhibits `S : Subalgebra k (WithConv (C →ₗ[k] k))`
  with `a ∈ S ↔ a.ofConv ∈ distributions k C`. This restricts the existing
  unital associative convolution algebra to exactly F, including its usual
  addition and scalar multiplication. Its last conjunct specifies that the
  convolution unit unwraps to ε. The middle conjunct is the full order bound
  for every `r s : ℕ` and every `a b : C →ₗ[k] k` of those orders.
- `tangentFunctionals` is the intersection over all `a,b` of the kernels of
  the linear maps `eval (ab) - ε(a) • eval b - ε(b) • eval a`. Membership is
  exactly `v(ab)=ε(a)v(b)+ε(b)v(a)` (commutativity of the field identifies
  `ε(b)v(a)` with `v(a)ε(b)`). This uses canonical kernels and intersections,
  with no span enlargement and no proof fields needing placeholders.
- The second conjunct is a linear equivalence from that space to
  `Module.Dual k I.Cotangent`. Mathlib `Ideal.Cotangent` is exactly I/I².
  The formula `e v (I.toCotangent x) = v.1 x.1` for every x∈I specifies
  restriction, rather than an arbitrary equivalence.
- The third conjunct characterizes the target submodule M by
  `D ∈ M ↔ invariantDerivation k C D`, with `D : Derivation k C C`.
  Mathlib's derivation type has exactly the k-linearity and ordinary Leibniz
  rule in the node. `invariantDerivation` is the equality
  `Δ.comp D.toLinearMap = (id ⊗ D.toLinearMap).comp Δ`.
  The linear equivalence `eD` has underlying map `tangentContraction`, the
  actual tensor contraction `rid ∘ (id ⊗ v) ∘ Δ`. Its inverse is explicitly
  `(eD.symm D).1 = counit.comp D.1.toLinearMap`.
- The fourth conjunct states `L ⊆ F_1` and `v(1)=0` for every v∈L.
- The fifth conjunct states invariance of `⁅D,E⁆` for every two invariant
  derivations. `Derivation.commutator_apply` identifies this with DE−ED;
  Mathlib's bracket already has the derivation Leibniz property.
- The final conjunct supplies `LR : LieRing L` and `LA : LieAlgebra k L`.
  The equalities on the underlying additive group and module preserve the
  existing vector space structure (HEq handles the dependent group argument).
  Its bracket is explicitly the difference of the two convolution products,
  and its contraction is explicitly `D_v.comp D_w - D_w.comp D_v`.
  `LieRing` includes alternation and Jacobi; `LieAlgebra` includes bilinearity.
  This gives both the transported bracket and the stated order of its factors.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-wf-lie-algebra`: `LieRing`, `LieAlgebra` in
  `Mathlib.Algebra.Lie.Basic`; the commutator convention in
  `Mathlib.Algebra.Lie.OfAssociative`, and `Derivation`'s commutator and Lie
  instances in `Mathlib.RingTheory.Derivation.Lie`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.map`,
  `TensorProduct.rid` and its universal bilinear construction from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the existing
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, and `ext` were read in
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`. The bialgebra's
  multiplication compatibility uses exactly this canonical tensor algebra.
- Proof dependency `lem-sfb-convolution-linear-map-algebra`:
  `LinearMap.convRing`, `convAlgebra`, `convMul_apply`, `convOne_apply`,
  `convAlgebraMap_apply`, `Mathlib.RingTheory.Coalgebra.Convolution`.
  This module is publicly imported since the theorem's algebra statement uses it.

The theorem's docstring gives all twelve DAG proof steps, including the cited
node ids, the augmentation splitting, the filtration pigeonhole calculation,
the inverse to restriction, both inverse identities for invariant derivations,
commutator closure and the final bracket-order computation.

Edge cases checked before finalization: C=k has I=0, F_n=kε, and L=0;
additive k[t] has the usual derivative with Δt=t⊗1+1⊗t; multiplicative k[t]
with Δt=t⊗t shows no antipode is required; characteristic two still gives
v(1)=0 by cancellation, not division; α_p is allowed in positive characteristic;
zero functionals and orders r=s=0 are included. The matrix monoid has
noncocommutative comultiplication and the same bracket order. No finiteness
condition is hidden. The zero ring cannot have a unital counit to a field,
which is already excluded by the bialgebra axioms, not by an added hypothesis.

Searches (all through the prescribed msearch wrapper or direct source rg):

- LeanFinder query: `For a commutative bialgebra finite order distributions form
  a filtered convolution algebra and tangent functionals identify with invariant
  derivations`. Eight hits, including `Bialgebra.mul_compr₂_comul`, derivation
  lemmas, and unrelated cotangent/analytic constructions; no whole-item match.
- Loogle query: `Coalgebra, Derivation`. Zero hits.
- Mathlib grep query: `Cotangent|cotangent|convMul|convAlgebra` in RingTheory.
  Found the standard cotangent and full-dual convolution APIs used here, but
  not the filtered-distribution theorem.
- LeanSearch query: `Finite order distributions at a bialgebra counit form a
  convolution algebra and tangent maps identify with invariant derivations`.
  Eight hits including `LinearMap.convRing`, `Bialgebra.mk'`, and
  `Bialgebra.counitAlgHom`, no result with the finite-order filtration and
  invariant-derivation identification.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf` and upstream names for
  `finiteOrder|distributionOrder|bialgebra_distribution` and for distribution,
  invariant derivation, tangent contraction, and cotangent terms found no
  equivalent item. The blueprint-id search in upstream Lean had no result.
  Read `WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier` and
  `WeilConjectures.RingTheory.HopfAlgebra.Cartier`: the existing
  `Bialgebra.exists_derivation_counitAlgHom_comp` and
  `exists_derivation_of_cotangent` assert existence only, without the invariance
  equation, bijection, convolution filtration or bracket clauses. The latter's
  contraction is local to its proof, not a reusable definition. Also read
  `WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent`: its
  `AlgHom.cotangentDerivation` is the explicit inverse on cotangent forms, not
  a definition of the subspace of all point derivations or this whole theorem.
  No second copy of those declarations is introduced.

Source read: Milne's PDF printed pp.195--196 and 208, and the current blueprint
unit `sk-thm-sf-ctf-stability` and its supporting ancestry. There is no statement
dispute or node fault. The node's mathematical statement and all its dependency
and proof records are unchanged.

Validation: scompile.py checks the module alone in sandbox and library contexts;
the final dry run and delivery run are recorded by the prescribed wrapper.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
