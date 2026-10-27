## Worker report

Module `Sheaf.RingTheory.FiniteCoalgebraDualBaseChange` states
`Coalgebra.finite_dual_baseChange`. Its sole postponed theorem is that declaration;
its docstring contains all six steps of the DAG proof and the source places.
No definition is added, no statement is corrected, and no node fault was found.
All repository and upstream files were read only. Every write is in this sandbox.

Source read: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175
(PDF pp.186–187), equation (77), printed p.237, and Theorem 12.18,
printed pp.237–238 (PDF pp.249–250). These define the convolution product and
scalar map without commutativity of the dual algebra and use the evaluation
character calculation in the proof of (c)⇒(d).

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`, the `Field` declaration of
  `def-weil-field` (`Mathlib.Algebra.Field.Defs`).
- A k-vector space D: `{D : Type v} [AddCommGroup D] [Module k D]`.
  Finite dimension is exactly `[FiniteDimensional k D]`, the abbreviation
  `FiniteDimensional` in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`
  recorded by `def-weil-finite-dimensional-subspace`; it means `Module.Finite`.
- The specified linear comultiplication and counit with coassociativity and
  both counit identities: `[Coalgebra k D]`. I read the whole class signature
  in `Mathlib.RingTheory.Coalgebra.Basic`. Its `CoalgebraStruct` parent has
  `comul : D →ₗ[k] D ⊗[k] D` and `counit : D →ₗ[k] k`.
  `coassoc`, `rTensor_counit_comp_comul`, and `lTensor_counit_comp_comul`
  are exactly the three identities, with the tensor unit maps made explicit.
  This bundles precisely the maps and laws in the node; it adds no other law.
- Tensor products are `TensorProduct` / `⊗[k]`, the declaration recorded by
  `def-weil-pbc-module-tensor-product`. I read the quotient definition,
  `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`, `ext'`, and
  `LinearMap.rTensor` with its pure-tensor formula.
- A = Hom_k(D,k) with the specified usual addition and scalar action is
  `WithConv (Module.Dual k D)`. This is Mathlib's public convolution wrapper,
  not another definition of a dual algebra. `WithConv.linearEquiv` identifies
  its additive and scalar structures with the ordinary linear dual.
- Associative unital algebra: `LinearMap.convRing` and `LinearMap.convAlgebra`
  already supply the instances on precisely this type. The signatures of
  algebra characters and the scalar comparison use those instances.
  `LinearMap.convMul_apply` is `mul' k k (TensorProduct.map f.ofConv g.ofConv
  (Coalgebra.comul x))`, precisely the convolution formula in the node.
  `convOne_apply` is the counit, and `convAlgebraMap_apply` sends r to
  `x ↦ r * counit x`. These declarations are the recorded Mathlib match of
  `lem-sfb-convolution-linear-map-algebra`; no new theorem restates them.
  There is no `Coalgebra.IsCocomm` or `CommRing` assumption on the dual.
- Finite-dimensional algebra: first conjunct
  `FiniteDimensional k (WithConv (Module.Dual k D))`.
- Actual evaluation is a linear isomorphism: second conjunct is
  `∃ e : D ≃ₗ[k] Module.Dual k (WithConv (Module.Dual k D)), ...` with
  `∀ x f, e x f = f x`. Specifying all values identifies exactly evaluation,
  rather than an unrelated isomorphism between the two vector spaces.
- Group-like elements: `{x : D // IsGroupLikeElem k x}`. I read
  `IsGroupLikeElem` and `isGroupLikeElem_iff` in
  `Mathlib.RingTheory.Coalgebra.GroupLike`: they are exactly
  `counit x = 1` and `comul x = x ⊗ₜ[k] x`.
- Restriction of evaluation gives the bijection to unital k-algebra maps:
  third conjunct has `c : {x : D // IsGroupLikeElem k x} ≃
  (WithConv (Module.Dual k D) →ₐ[k] k)` with `c x f = f x.val` for every
  group-like x and every functional f. Both directions and uniqueness are
  carried by `Equiv`; the formula ties this to the evaluation in the preceding
  conjunct. `AlgHom` includes unit and scalar preservation.
- Every field extension F/k: `(F : Type w) [Field F] [Algebra k F]`, exactly
  the `Algebra` interface recorded by `def-pc-field-extension`, read in
  `Mathlib.Algebra.Algebra.Defs`. The theorem is universally quantified in F.
  The field, D and extension have independent explicitly bound universes.
- Scalar-extended D_F: `F ⊗[k] D`, with `TensorProduct.instCoalgebra` from
  `Mathlib.RingTheory.Coalgebra.TensorProduct` at `(R,S,A,B)=(k,F,F,D)`.
  I read this instance and the defining comultiplication and counit maps.
  The instance is explicitly documented to specialize to base change when
  A=S. Its formula gives epsilon_F(b tensor x)=b epsilon(x), and
  Delta_F(b tensor x)=sum (b tensor u_i) tensor_F (1 tensor v_i).
- The source scalar-extended algebra uses the standard algebra tensor product
  on `F ⊗[k] WithConv (Module.Dual k D)`. The target is exactly
  `WithConv (Module.Dual F (F ⊗[k] D))` with its F-convolution algebra.
- The last conjunct states a unital F-algebra isomorphism `θ` between those
  types, using `≃ₐ[F]`, with the precise formula
  `θ (a ⊗ₜ[k] f) (b ⊗ₜ[k] x) = a * b * algebraMap k F (f x)`.
  Tensor generation makes this the specified canonical comparison. The field
  embedding in `algebraMap k F` is necessary to type the paper's abf(x).
- Zero-dimensional D is allowed: no `Nontrivial D`, positive finrank, nonempty
  basis, or nontrivial dual-algebra hypothesis occurs.

Dependencies and imports:

The four statement dependencies use `Field`, `TensorProduct`, `Algebra`, and
`FiniteDimensional` as detailed above. Public imports expose all the Mathlib
notions needed to read the signature. The convolution and group-like imports
also expose `Coalgebra` and the canonical scalar-extension coalgebra.

The stated proof dependencies have Mathlib matches, read in their source files:
`Module.Free.of_divisionRing` (`Mathlib.LinearAlgebra.Basis.VectorSpace`),
`Module.Projective.of_free` (`Mathlib.Algebra.Module.Projective`),
`Module.dual_projective`, `Module.dual_finite`, the finite-projective reflexivity
instance, `Module.evalEquiv`, and `Module.Projective.exists_dual_ne_zero`
(`Mathlib.LinearAlgebra.Dual.Lemmas` / `Dual.Defs`),
`LinearMap.convRing`, `convAlgebra`, `convMul_apply`, `convOne_apply`,
`convAlgebraMap_apply` (`Mathlib.RingTheory.Coalgebra.Convolution`), and
`TensorProduct.dualDistribEquiv` / `dualDistrib_apply`
(`Mathlib.LinearAlgebra.Contraction` / `Dual.Lemmas`).
The non-public proof imports are `Dual.Lemmas`, `Contraction`, and `Dual.BaseChange`;
the free/projective interfaces are reached through those imports.
`lem-trf-projective-exterior-scalar-comparisons` has neither a Lean record nor a
Mathlib match, so has no module to import. It is a proof dependency, not a
notion required to type this statement. The exact dual scalar comparison
component used here is already `IsBaseChange.toDualBaseChange` and
`Module.Dual.baseChange` in `Mathlib.LinearAlgebra.Dual.BaseChange`, whose
signatures, constructions, and tensor evaluation formulas were read.
No missing statement interface or helper requires an additional node.

Edge cases checked before writing:

1. D=0: the convolution algebra is the zero algebra, allowed by Ring and Algebra.
   Both linear isomorphisms and the algebra comparison are between zero spaces.
   Counit(0)=0≠1, so the group-like subtype is empty. No unital algebra map from
   the zero algebra to k exists; hence the character type is also empty.
2. Dimension one with Delta(e)=e tensor e and epsilon(e)=1: evaluation at e is
   the expected unique character of the dual k, and θ has the ordinary formula.
3. The coalgebra dual to a noncommutative finite algebra (e.g. matrix algebra)
   is admitted; no accidental cocommutativity is imposed.
4. F=k and the identity extension are included. Infinite and inseparable field
   extensions are also included; no finite-extension or separability restriction.
5. Any characteristic is admitted. Scalar multiplication in the comparison is
   in the commutative field F; multiplication in the source dual remains general.
6. Independent u,v,w retain vector spaces and field extensions of any universe.

Searches for an existing complete declaration:

- `grep` query `convAlgebra|baseChange|groupLike` in `RingTheory/Coalgebra`: 7 hits; Mathlib/RingTheory/Coalgebra/Convolution.lean, Mathlib/RingTheory/Coalgebra/Convolution.lean, Mathlib/RingTheory/Coalgebra/GroupLike.lean, Mathlib/RingTheory/Coalgebra/GroupLike.lean, Mathlib/RingTheory/Coalgebra/GroupLike.lean, Mathlib/RingTheory/Coalgebra/GroupLike.lean, Mathlib/RingTheory/Coalgebra/GroupLike.lean. Digest `b66ee8e9702cf439`.
- `loogle` query `LinearMap.convAlgebra, Module.Dual.baseChange`: 0 hits; . Digest `4f53cda18c2baa0c`.
- `leanfinder` query `The dual of a finite dimensional coalgebra is a convolution algebra with characters given by group like elements and compatible with scalar extension`: 8 hits; InnerProductSpace.algebraOfCoalgebra, InnerProductSpace.AlgebraOfCoalgebra.mul_def, LinearMap.convRing, Coalgebra.Repr.convMul_apply, LinearMap.convCommRing, LinearMap.convCommSemiring, LinearMap.convSemiring, InnerProductSpace.coalgebraOfAlgebra. Digest `773d540b149bbae9`.
- `leansearch` query `Finite dimensional coalgebra dual algebra and group like elements correspond to algebra homomorphisms to the field`: 8 hits; IsGroupLikeElem, IsGroupLikeElem.map, FGModuleCat.FGModuleCatDual, IsGroupLikeElem.mk, CoalgHomClass.toCoalgHom, isGroupLikeElem_iff, Subspace.instModuleDualFiniteDimensional, isGroupLikeElem_map_equiv. Digest `44c12e36edff154c`.

I also searched Mathlib, the project's `lean/WeilConjectures` and `lean/Sheaf`,
and `dag/lean_names_upstream.json`, for the coalgebra/dual/base-change names,
`convAlgebra`, and the intended declaration name. Existing finite subcoalgebra,
comodule, Hopf algebra, and derived dual-base-change declarations have different
statements. No declaration states the full finite-dual character and scalar
comparison result. Mathlib supplies the convolution algebra, group-like predicate,
and linear scalar comparison components, all reused here.

Validation: `scompile.py Q98 lem-sfb-finite-coalgebra-dual-base-change` compiled
the delivered file in sandbox and library module modes on the server in 2.2 s
and 2.0 s, with no errors or warnings. There is one theorem with `sorry`, and no
other proof or data declaration. All variables and universes are explicitly bound
with `set_option autoImplicit false`. The node copy changes only `lean`.

## Second reading by Q98

The delivered section said that no second reading was done (direct-delivery dispatcher policy).
The maintainer's independent reviewer wrote this reading on 2026-10-24. It replaces that
section and leaves the Worker report unchanged. The delivered Lean files and the node record
are not changed.

Node clauses and the Lean that renders each one (`Coalgebra.finite_dual_baseChange`):

1. Field k: `{k : Type u} [Field k]` (def-weil-field = `Field`). OK.
2. Finite-dimensional k-vector space D: `{D : Type v} [AddCommGroup D] [Module k D]
   [FiniteDimensional k D]` (def-weil-finite-dimensional-subspace = `FiniteDimensional`). OK.
3. Δ, ε with coassociativity and both counit identities: `[Coalgebra k D]`. I read the
   class in Mathlib `RingTheory/Coalgebra/Basic.lean`. It has comul/counit, `coassoc`, and
   `rTensor_counit_comp_comul`/`lTensor_counit_comp_comul`, with no further law. OK.
4. A = Hom_k(D,k) with convolution (fg)(x) = mul((f⊗g)(Δx)) and unit ε:
   `WithConv (Module.Dual k D)`. `Module.Dual` is an `abbrev` for `D →ₗ[k] k`
   (Dual/Defs.lean:62), so `LinearMap.convMul`/`convOne`/`convRing`/`convAlgebra`
   (Coalgebra/Convolution.lean:56,174,212,187) apply. `convMul_apply` is
   `mul' k k (map f g (comul x))` and `convOne_apply` is `algebraMap k k (counit x)`,
   which are exactly the node's formulas. The Module k structure comes from
   `WithConv.equiv`, and `Algebra.ofModule` keeps it. No commutativity (no `IsCocomm`) is used. OK.
5. A is finite-dimensional: first conjunct. The associative unital algebra structure is the instance. OK.
6. Evaluation D → Hom_k(A,k) is a linear isomorphism: `∃ e : D ≃ₗ[k] Module.Dual k (WithConv …)`
   with `e x f = f x` for all x, f. The formula fixes e as the evaluation map; it is not an
   arbitrary isomorphism. `f x` is the `CoeFun` of `WithConv` through `ofConv` (WithConv.lean:60). OK.
7. Evaluation restricts to a bijection {x : Δx = x⊗x, ε(x) = 1} ≅ unital k-algebra maps A → k:
   `∃ c : {x // IsGroupLikeElem k x} ≃ (WithConv (Module.Dual k D) →ₐ[k] k)` with
   `c x f = f x.val`. `IsGroupLikeElem` (GroupLike.lean:37) is exactly
   `counit a = 1 ∧ comul a = a ⊗ₜ a`, and `→ₐ[k]` is a unital k-algebra map. The formula
   identifies c with the restriction of evaluation. OK.
8. For every field extension F/k: `(F : Type w) [Field F] [Algebra k F]`
   (def-pc-field-extension = `Algebra`), universally quantified with an independent universe. OK.
9. D_F = F ⊗_k D with the scalar-extended coalgebra: `TensorProduct.instCoalgebra`
   (Coalgebra/TensorProduct.lean:130) at (R,S,A,B) = (k,F,F,D), with `CommSemiring.toCoalgebra`
   on F (comul = mk 1). This gives ε_F(b⊗x) = bε(x) and Δ_F(b⊗x) = Σ(b⊗u_i)⊗(1⊗v_i). OK.
10. θ_F : F ⊗_k A → Hom_F(D_F,F) is an isomorphism of unital F-algebras, with θ_F(a⊗f)(b⊗x) = abf(x)
    and convolution on the target: `∃ θ : F ⊗[k] WithConv (Module.Dual k D) ≃ₐ[F]
    WithConv (Module.Dual F (F ⊗[k] D))` with `θ (a ⊗ₜ f) (b ⊗ₜ x) = a * b * algebraMap k F (f x)`.
    The source carries the left F-algebra structure of the algebra tensor product, and the
    target carries the F-convolution algebra. Pure tensors generate both F ⊗ A and D_F, so the
    formula determines θ. OK.
11. Zero-dimensional D is allowed: there is no `Nontrivial` hypothesis. If D = 0, both sides of
    clause 7 are empty: ε(0) = 0 ≠ 1, and the zero algebra has no unital map to k. Clauses 6
    and 10 are isomorphisms between zero objects. OK.

Edge cases: D = 0 (above); F = k and infinite or inseparable extensions (no restriction);
the dual of M_n(k), which gives noncommutative A (admitted); any characteristic; independent
universes u, v, w. Every variable and universe is bound, with `autoImplicit false`.

Searches: Mathlib `RingTheory/Coalgebra`, `LinearAlgebra/Dual` (BaseChange, Lemmas) and
GroupLike; project `lean/Sheaf` and `lean/WeilConjectures` for `WithConv`, `IsGroupLikeElem`,
`Module.Dual` together with coalgebras, and the declaration name. The hits were
`CounitWordProductRule` (it uses WithConv, but states a different lemma), `FiniteDualHopfModule`
(the Hopf dual action), and Cartier/GL Hopf modules. None states this result, and no
project duplicate of the dual convolution algebra exists. H4 is satisfied.

Records: `lean.statement` is verbatim the file signature, from `theorem` through the conclusion.
The node copy changes only `lean`, compared with live. The module has the source place and
`(blueprint: …)` in its module docstring and in the theorem docstring, and the theorem
docstring gives the six proof steps. There is no definition, so nothing is hollow; the only
proof is `sorry`. There is no pro-étale content.

Mismatches found: none in the mathematics or the records. The only change is this section.
