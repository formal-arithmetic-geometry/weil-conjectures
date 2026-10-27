## Worker report

The item is stated by `RepresentationTheory.divisionFactors_bijective_of_splitGrothendieck_surjective`
in `Sheaf.RepresentationTheory.SemisimpleScalarExtensionCriterion`. Its proof is `sorry`.
The accepted stage-1 statement and split are unchanged. The inherited BLOCKED ending concerned
stage-1 `deliver.py`; the current queue explicitly assigns this item to stage 2 and it has no
Lean record. There is no released repair note. This delivery adds its missing representation-group
construction rather than retrying the unchanged stage-1 packet.

Hypothesis and conclusion correspondence:

- A field K of characteristic zero is `(K : Type u) [Field K] [CharZero K]`.
- An arbitrary algebraic closure Ω, including its structural map, is `(Ω : Type v) [Field Ω]
  [Algebra K Ω] [IsAlgClosure K Ω]`. It is not restricted to the chosen `AlgebraicClosure K`.
- A finite-dimensional unital associative K-algebra A is `(A : Type t) [Ring A] [Algebra K A]
  [Module.Finite K A]`. Mathlib's `Algebra` expresses the central unital structural map;
  `Ring` is associative and unital and is not required to be commutative or nonzero.
- The regular left modules being sums of simple submodules is `[IsSemisimpleRing A]` and
  `[IsSemisimpleRing (TensorProduct K Ω A)]`. These are exactly semisimplicity of the regular
  modules; the sum-of-simples equivalence is `sSup_simples_eq_top_iff_isSemisimpleModule`.
  `IsSimpleModule` requires nonzero and no nonzero proper submodule, as the node specifies.
- The tensor algebra is Mathlib's `TensorProduct K Ω A` with its standard ring structure;
  its product on pure tensors is `(x ⊗ a)*(y ⊗ b) = (x*y) ⊗ (a*b)`.
- The integral groups R(A), R(A_Ω) are `FiniteModuleSplitGrothendieck`, the literal quotient
  of a free abelian group by isomorphism and direct-sum relations. No rationalization or
  substitution by dimension functions occurs. Modules are bundled coefficient-field vector
  spaces with a unital algebra action, so they are precisely the compatible left modules.
- The map s is `finiteModuleSplitScalarExtension`, constructed by extending the actions
  on `Ω ⊗[K] V.space` using `Module.End.baseChangeHom` and `AlgHom.liftEquiv`, mapping the
  free generators, and descending to the quotient. Its formula on generators is the specified
  `[V] ↦ [Ω ⊗ V]`. `hs : Function.Surjective (...)` is the required integral surjectivity.
- Any decomposition with r factors is given by `(r : ℕ) (d : Fin r → ℕ)` and
  `(_e : A ≃ₐ[K] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))`.
  Every matrix size is positive by `(hd : ∀ i, 0 < d i)`.
- Each finite-dimensional division K-algebra is `(D : Fin r → Type z)` with
  `[∀ i, DivisionRing (D i)] [∀ i, Algebra K (D i)] [∀ i, Module.Finite K (D i)]`.
  A division ring is nonzero, and its inverse and central structural map are built into
  these classes; commutativity of D_i is not assumed.
- The complete conclusion is `∀ i, Function.Bijective (algebraMap K (D i))`.

The module universes u, v, t, z are independent. The representation carriers have universe
`max u v t`; extension therefore remains in the same carrier universe. This loses no
finite-dimensional isomorphism class: every module over its coefficient field is isomorphic to
`Fin n → K` (respectively `Fin n → Ω`), with its action transported along a basis. Modules
originally living in a different universe represent the same classes after that transport.
The division-algebra universe z need not be equated to any of these universes.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: its Mathlib match includes `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `IsAlgClosure` / `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The theorem uses `IsAlgClosure K Ω`, not an
  extra hypothesis beyond being an algebraic closure.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift` / `lift.tmul` / `ext'`, and `LinearMap.rTensor` / `rTensorHom`
  in the recorded Defs, Basic and Map modules were read. The construction uses that
  same tensor product, with standard algebra structure from `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-matrix`: `Matrix` in `Mathlib.LinearAlgebra.Matrix.Defs`, reexported by
  `Mathlib.Data.Matrix.Basic`, supplies matrices, multiplication and the central algebra structure.
- New definition node `def-per-finite-module-split-grothendieck` supplies all eight recorded
  declarations of `Sheaf.RepresentationTheory.FiniteModuleSplitGrothendieck`.
- Existing proof inputs are imported from `Mathlib.RingTheory.SimpleModule.Basic`
  (`IsSemisimpleModule.of_sSup_simples_eq_top`) and
  `Mathlib.RepresentationTheory.AlgebraRepresentation.Basic`
  (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`). Their full signatures were read.
  `def-weil-pbc-simple-module` is the same Mathlib `IsSimpleModule`.
  The matrix-division classification and finite-algebra Hom scalar-extension proof nodes
  currently have no Lean declarations, so there is no import to add for either yet.

Edge cases were checked before stating the theorem. The zero algebra is permitted and r=0
is permitted; its conclusion quantifies over `Fin 0` and is vacuous. Positive d_i excludes
zero-size factors exactly as in the node, without excluding empty products. Zero-dimensional
modules are allowed in the new definition. Their class is killed by the relation
`[0] = [0] + [0]`. The identity field extension gives the usual tensor action and identity
class map. For A=K or M_d(K), the conclusion holds. A nontrivial separable extension L/K
would yield a diagonal rank-one subgroup after algebraic closure and fails surjectivity;
quaternion factors over R yield multiplicity two and likewise fail integral surjectivity.
These checks distinguish the stated hypothesis from the weaker rational-surjectivity claim.
There is no statement dispute or correction.

Searches: prescribed `msearch.py` LeanFinder queried surjectivity of scalar extension on split
Grothendieck groups of semisimple algebras: eight hits (module-end surjectivity and general
scalar-extension maps), no criterion. Loogle `IsSemisimpleRing, TensorProduct` returned zero.
Grep `Grothendieck|Schur.index|splitting` in `RingTheory/SimpleModule` returned zero.
LeanSearch for the split Grothendieck group of finite-dimensional algebra modules returned
`Algebra.GrothendieckAddGroup` and generic group-completion operations plus finite-module
facts; none provides the module isomorphism monoid or group and scalar-extension map.
LeanFinder `split Grothendieck group finite dimensional modules scalar extension map`
returned generic scalar-extension equivalences and Picard base change, not this notion.
Mathlib grep `splitGrothendieck|SplitGrothendieck|Grothendieck.*Module` returned nine unrelated
Grothendieck-abelian-category hits. `rg` over both `lean/WeilConjectures` and `lean/Sheaf`
found only unrelated monoid group completions or descriptions of Grothendieck categories.
No upstream source references the item id. Searching DAG definition statements and
`tools/blueprint_refs.py search 'split Grothendieck'` found no existing definition node
(the blueprint search returned 0). All eight new declaration names and the criterion name
were checked against Mathlib, the project and `dag/lean_names_upstream.json` without collision.
The new node retains the actual msearch JSON result records.

Source read: ILO PDF pages 144–145, printed pp.138–139, including the Serre citation,
the projective Λ[G]-module V lifting V0, and equation (5). The criterion and its group
construction are honestly marked auxiliary: the source does not assert the criterion itself.
No extra claim of an available Serre text or a Stacks criterion is made.

Validation: both delivered modules compile individually through `scompile.py` against the
published server library, including dependency-order compilation of the new definition module.
There are no errors or non-sorry warnings. Definitions have actual data; the two postponed
proofs are the criterion and the named well-definedness theorem described below.

## New nodes

`def-per-finite-module-split-grothendieck` introduces the notion the item needs and no recorded
node currently supplies. It defines the finite module generators with their ordinary Mathlib
linear actions, isomorphism and sum relations, the relation subgroup, its quotient group,
extension of a generator, and the canonical quotient homomorphism. Its source is the same
explicit auxiliary algebra construction underlying ILO X 1.2's representation-lifting input.
The LeanSearch, LeanFinder and Mathlib/project/DAG grep searches above are retained in its
`mathlib_searches` and show why this is not an existing group-completion definition.
Generic `Algebra.GrothendieckAddGroup` alone does not supply the module-isomorphism monoid.

The node's mathematical statement explicitly includes preservation of the relation subgroup.
Its named theorem `finiteModuleSplitRelations_extendScalars` is the sole postponed proof
needed for the quotient construction and is listed in `lean.declarations`. Its full proof
in the docstring tensors an intertwiner and, for sum relations, composes with tensor's product
distribution; pure tensors check equivariance, then subgroup closure gives the assertion.
The definition `finiteModuleSplitScalarExtension` uses this exact proof to descend the
explicit free-generator map. No existence choice, arbitrary class map, additional assumption,
or data-valued sorry is used. All its companion definitions carry this definition node's
blueprint tag. The item's only graph change is adding this new definition to `stmt_deps`.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
