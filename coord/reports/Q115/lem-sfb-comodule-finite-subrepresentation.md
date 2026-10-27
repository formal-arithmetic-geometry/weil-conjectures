## Worker report

The module `Sheaf.RepresentationTheory.ComoduleFiniteSubrepresentation` states
`AlgebraicGeometry.RationalRepresentation.exists_finiteDimensional_subcomodule`.
Its only theorem has proof `sorry`. The real-data helper `coactionFixedVectors`
records the invariant-set notation introduced in this same node. There are no new
nodes, dependency repairs, or statement corrections.

Hypotheses and clauses, matched with the node:

- A field k is `(k : Type u) [Field k]`.
- The affine k-group scheme H is `(H : Scheme.{u})`,
  `[H.Over (Spec (.of k))]`, `[GrpObj (H.asOver (Spec (.of k)))]`, and
  `[IsAffine H]`. These are the existing group-scheme conventions, not an
  abstract group of k-points. There is no finite-type or smoothness assumption.
- An arbitrary k-vector space is `(V : Type v) [AddCommGroup V] [Module k V]`.
  Its universe v is independent of u; its dimension is unrestricted.
- The linear coaction is `ρ : V →ₗ[k] V ⊗[k] Γ(H, ⊤)`, using the actual global
  coordinate algebra with its canonical Hopf structure from the given group law.
- The coassociativity and counit hypotheses are respectively
  `HopfAction.Coassociative k Γ(H, ⊤) V ρ` and
  `HopfAction.Counital k Γ(H, ⊤) V ρ`. Unfolding their existing definitions gives
  `(TensorProduct.assoc ...).toLinearMap ∘ₗ ρ.rTensor ... ∘ₗ ρ =
  (Coalgebra.comul ...).lTensor V ∘ₗ ρ` and
  `(TensorProduct.rid ...).toLinearMap ∘ₗ
  (Coalgebra.counit ...).lTensor V ∘ₗ ρ = LinearMap.id`.
- The node's contextual notation `V^H = {v : ρ(v) = v tensor 1}` is rendered by
  `coactionFixedVectors`, whose body is precisely that set comprehension.
  It asserts no additional invariant-vector theorem.
- A finite subset is `(S : Set V) (hS : S.Finite)`. Using a finite set rather than
  a list or chosen enumeration covers exactly the node's input.
- The desired subspace and finite dimension are
  `∃ W : Submodule k V, FiniteDimensional k W ∧ ...`.
- Containment is `S ⊆ (W : Set V)`.
- The stable-image clause and the concluding restricted rational-module structure
  are expressed together by an actual linear map
  `ρW : W →ₗ[k] W ⊗[k] Γ(H, ⊤)`, both coaction laws on W, and
  `W.subtype.rTensor Γ(H, ⊤) ∘ₗ ρW = ρ ∘ₗ W.subtype`.
  At w this says `ρ(w) = (inclusion tensor id)(ρW(w))`, precisely membership in
  the image of W tensor k[H]. Over a field that tensor inclusion is injective, so
  the map is the restricted coaction; this neither replaces stability with an
  arbitrary structure nor omits either law. The node's last proof step gives
  exactly these witnesses and laws.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, a commutative division ring.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, on schemes over Spec k. Its recorded
  specialization and documentation in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs; `TensorProduct.lift`,
  Mathlib.LinearAlgebra.TensorProduct.Basic; and `LinearMap.rTensor`,
  Mathlib.LinearAlgebra.TensorProduct.Map. These supply tensor products and the
  tensor inclusion with the exact pure-tensor formula.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs, the abbreviation for Module.Finite.
- The added already landed node `def-sfb-hopf-action-module-data` supplies
  `HopfAction.Coassociative` and `HopfAction.Counital` in
  Sheaf.RingTheory.HopfActionModuleData, publicly reexported by the imported module.
- The added already landed definition node `def-sfb-coordinate-hopf-algebra` supplies
  `HopfAction.coordinateHopfAlgebra` in
  Sheaf.AlgebraicGeometry.HopfCoactionLinearization. Its data is Mathlib's canonical
  coordinate Hopf instance, exposed with an unbundled field for inference.
  Its existing:true record owns this unchanged real-data instance. The instance
  specializes Mathlib’s canonical structure through `affineCoordinateHopfAlgebra`;
  no theorem conclusion or choice operation is used.
- Proof dependencies `lem-weil-pbc-vector-space-free` and
  `def-weil-pbc-free-module` are imported privately through
  Mathlib.LinearAlgebra.Basis.VectorSpace (`Module.Free.of_divisionRing`) and
  Mathlib.LinearAlgebra.FreeModule.Basic (`Module.Free` and its basis existence).
  Their signatures and docstrings were read. The remaining proof-dependency
  modules are already imported for the statement.

Source: opened the local Milne PDF with pdftotext, Proposition 4.7, equation (26),
and Corollary 4.8 on printed p.86 (and the continuation at p.87). Proposition 4.7
uses only coassociativity, counitality, and a vector-space basis, so no finite-type
hypothesis on H or dimension hypothesis on V is needed. The theorem docstring
contains all six steps of the DAG proof, including tensor-inclusion injectivity
and descent of the two laws to the restricted coaction.

Edge cases checked before writing: S empty permits W zero and its unique zero
coaction; V zero permits both S empty and S = {0}; S containing only zero permits
W zero. Infinite-dimensional V and infinitely generated coordinate algebras are
allowed. Fields of every characteristic, finite fields, nonreduced affine groups,
and the trivial group remain covered. No nonzero-vector or nonempty-set condition
occurs. The source proof and statement are consistent; no disputed statement.

Actual searches performed:

- msearch.py leanfinder: "Every finite subset of a rational representation of an
  affine group scheme lies in a finite dimensional subcomodule". Eight hits,
  including FGModuleRepr.S and affine finite-type facts; no matching theorem.
- msearch.py loogle: `"Comodule", "FiniteDimensional"`: zero hits.
- msearch.py grep: `finite.*subcomodule|subcomodule.*finite|finite.*subrepresentation`:
  zero hits in Mathlib.
- rg in both lean/WeilConjectures and lean/Sheaf for comodule, coordinate Hopf,
  and finite-subrepresentation phrases found the existing coaction laws, canonical
  Hopf instance, and rational-representation dictionary. None states this theorem.
  The dictionary's alias restricts V to the scheme universe, so this delivery uses
  its underlying existing right-coaction laws directly, retaining independent v.
- The exact blueprint id was searched in lean/WeilConjectures with grep: no hit.
  The Sheaf hits in PGLGeometricReductivity and AffineGroupTensorReconstruction are
  proof-plan citations of this node, not declarations proving or stating it.
- Declaration-name and invariant-vector searches in the relevant project and
  coalgebra directories found no existing `coactionFixedVectors` or
  `exists_finiteDimensional_subcomodule` declaration and no duplicate coordinate
  coaction fixed-vector definition.

Validation: scompile.py compiled the file separately as a sandbox module and at
its library module path, each in 1.6 seconds, with no errors or additional warnings.
All variables and universes are explicit and autoImplicit is false. The node's
statement and proof are unchanged; only its Lean record and the two landed
statement-dependency ids were added.

## Return repair

H2 of immutable head d9ad7a16af5f: replaced
`lem-sfb-hopf-coaction-linearization` in stmt_deps with the already landed
definition node `def-sfb-coordinate-hopf-algebra`, which owns the plain instance
`HopfAction.coordinateHopfAlgebra`. Updated the dependency paragraph above.
The Lean module and the complete lean record remain unchanged, as requested.
The current read-only main node has the original four statement dependencies;
this repaired delivery adds only the coaction-data and coordinate-Hopf definition
nodes. The delivery wrapper rebases these authorized fields onto current main.
No change to the mathematical statement, proof plan, or proof dependencies.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
