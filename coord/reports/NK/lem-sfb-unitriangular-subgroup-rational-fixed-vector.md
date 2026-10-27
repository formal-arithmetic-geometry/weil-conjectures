## Worker report

The delivery states `AlgebraicGeometry.exists_rational_fixed_vector_of_unitriangular_closedImmersion`
in `Sheaf.AlgebraicGeometry.GroupScheme.UnitriangularRationalFixedVector`. It also supplies the
missing actual upper unitriangular group scheme in
`Sheaf.AlgebraicGeometry.GroupScheme.Unitriangular`, owned by the new definition node
`def-sfb-unitriangular-group-scheme`. The item's mathematical statement, proof and proof dependencies
are unchanged; its statement dependencies gain that definition node. Nothing is proved in this
stage. The only postponed theorems are the fixed-vector statement and the uniquely specified
group-structure verification in the new definition node. Neither definition contains `sorry` data.

Clause-by-clause comparison with the item:

- The field is `{k : Type u} [Field k]`.
- A k-group scheme is `(U : Over (Spec (.of k))) [GrpObj U]`. A morphism in this over
  category is a morphism over k; `[IsMonHom ...]` requires compatibility with the group laws.
- Affineness is `[IsAffine U.left]`.
- Finite type is exactly `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]`, as required
  by the recorded finite-type dependency, with no extra finiteness hypothesis.
- The positive unitriangular size is `(n : ℕ) (hn : 1 ≤ n)`.
- The closed immersion of group schemes is `(i : U ⟶ UnitriangularGroup.scheme k n)`
  with `[IsMonHom i] [IsClosedImmersion i.left]`. The target is the actual Spec of the
  polynomial ring in the strictly upper entries, with the explicit matrix-multiplication
  coordinate map. It is not an abstract group of k-points or a supplied arbitrary group law.
- The representation dimension is `(d : ℕ) (hd : 1 ≤ d)`.
- The rational representation is the actual scheme morphism
  `(ρ : U ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} d) k) [IsMonHom ρ]`.
  This reuses the existing GL scheme of the recorded dependency. `Index d = ULift (Fin d)`
  merely transports the d standard indices into the common universe; it changes neither
  matrices nor dimension.
- The chosen vector is `∃ v : LinearGroupSchemes.Index.{u} d → k, v ≠ 0 ∧ ...`.
  This is exactly k^d, with lifted indexing, and the nonzero condition is on the vector over k.
- Every commutative k-algebra and every point are quantified by
  `∀ (A : Type u) [CommRing A] [Algebra k A] (x : points U A), ...`.
  `points U A` is the existing abbreviation for `Spec A ⟶ U` over k. These are all
  algebra-valued points, including nonreduced algebras; no field-valued or k-point restriction
  is made. The single common universe contains k, U and the test algebras, following the
  existing group-scheme and representation-dictionary conventions. In particular it contains
  the coordinate algebra and the universal point, which detect rational invariance.
- `GeneralLinearGroup.homMulEquiv ... (x ≫ ρ)` is precisely the matrix ρ_A(x).
  `Matrix.GeneralLinearGroup.toLin' ((Pi.basisFun k (Index d)).baseChange A)` is its
  A-linear action on the actual tensor product `A ⊗[k] (Index d → k)` in the scalar-extended
  standard basis. Thus the displayed conclusion is literally its action on `1 ⊗ₜ[k] v`
  equalling `1 ⊗ₜ[k] v`, not an unrelated coordinate-only fixed-point equation.
- There are no smoothness, reducedness, connectedness, perfectness, algebraic closedness,
  characteristic, or cardinality assumptions. `hn` and `hd` record exactly the two positive-size
  hypotheses in the node. Every variable and universe is explicitly bound, and `autoImplicit`
  is disabled in both files.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom` in
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Mon`. The upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents their exact group-scheme
  interpretation. `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring` supplies the
  existing `AlgebraicGeometry.points` abbreviation; it is imported publicly because the
  statement uses it. No private copy is introduced.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `.QuasiCompact` respectively.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-sc-general-linear-group`: `Sheaf.AlgebraicGeometry.LinearGroupSchemes` and its
  reused upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
  The declaration actually used for GL is the existing `AlgebraicGeometry.GeneralLinearGroup`,
  with its `homMulEquiv`; `LinearGroupSchemes.Index` provides the established lifted finite
  indexing convention. The dependency's main recorded declaration `specialLinear` is the
  special-linear clause of that multi-declaration node; its module explicitly reuses upstream
  GL for the general-linear clause needed here, so no dependency repair is necessary.
- `def-weil-matrix`: Mathlib `Matrix`.
- `def-weil-pbc-mv-polynomial-ring`: Mathlib `MvPolynomial`, `MvPolynomial.aeval` and
  `MvPolynomial.algHom_ext`, read in `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`.
- `def-weil-affine-spectrum`: the existing `Spec`, `Spec.map`, and `algSpec` construction
  from Mathlib's affine-spectrum API, used by the new definition.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the existing commutative
  algebra structure on tensor products and the monoidal affine Spec comparison; the new
  multiplication is induced by the specified algebra map through `Functor.LaxMonoidal.μ`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`; the fixed-vector expression
  uses its actual pure tensors. `Mathlib.LinearAlgebra.TensorProduct.Basis` supplies the
  scalar-extended standard basis.
- The proof-only import `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`
  supplies `AlgebraicGeometry.RationalRepresentation.dictionary` and `.finite_dictionary`.
  Its full signatures and docstrings were read, including its right-coaction / left scalar
  extension flip. The other proof-only import `Mathlib.AlgebraicGeometry.Group.Affine`
  supplies the coordinate Hopf instance recorded by `lem-sfb-affine-group-coordinate-hopf`.
  The filtered-coalgebra lemma has no recorded Lean declaration yet, so there is no module
  to import for it; it remains explicitly named in the main theorem's proof docstring.

Edge cases checked against Milne's source and the concrete definitions:

- `n=1`: the strictly upper position type is empty, P=k, and the unitriangular group is
  trivial. Its closed subgroup scheme U is trivial; every nonzero representation has fixed
  vectors. The construction also supports `n=0`, though the item correctly requires `n≥1`.
- `d=1`: the statement still requires one vector fixed over every algebra, giving triviality
  of a character of such a subgroup. `d=0` is excluded exactly as in the node.
- The trivial group and trivial representations satisfy the statement. An empty underlying
  group scheme cannot have its required identity section over a field, so no artificial
  nonemptiness hypothesis is added.
- In characteristic p the subgroup schemes alpha_p of G_a and the constant Z/p subgroup
  are allowed. No smoothness or reducedness assumption discards them. The matrix inverse
  is the finite series in -N over any commutative algebra, in every characteristic.
- Zero test algebras are allowed by `[CommRing A]`; the tensor product is then zero and the
  fixed-vector equality holds. The nonzero vector is required only over k.
- For n=2 the coordinate maps are Δ(x)=x tensor 1+1 tensor x, ε(x)=0, S(x)=-x.
  For n=3 the (0,2) coordinate is x_02 tensor 1+1 tensor x_02+x_01 tensor x_12,
  and the antipode sends it to -x_02+x_01*x_12. These are the expected formulas (92).
- The finite inverse series contains r=0 through n-1. Multiplication by I+N gives I
  because N^n=0. There is no determinant inversion, choice of representation, or quotient
  by a reduced ideal that would change the functor on nonreduced algebras.

Searches actually run through `batch2/msearch.py` for NK and this item:

- LeanFinder: `Every rational representation of a closed subgroup scheme of upper
  unitriangular matrices has a nonzero vector fixed over every algebra` returned eight
  unrelated matrix, cusp and Hilbert-90 results (including `Subgroup.mem_strictPeriods_iff`,
  `Matrix.instNonemptyTransvectionStructOfNontrivial`, and
  `groupCohomology.Hilbert90.aux_ne_zero`), not this theorem.
- Loogle: `"Representation", "invariants"` returned twelve hits including
  `Representation.invariants`, `mem_invariants`, and `invariants_eq_inter`. These describe
  the fixed space for an already supplied abstract group representation and give no
  rational group-scheme existence result.
- Mathlib grep: `unitriangular|Unitriangular|Unitriang|unitriang` returned zero hits.
- LeanSearch: `The affine group scheme of upper unitriangular matrices with diagonal
  entries one` returned eight hits on `Subgroup.periods`, `Subgroup.strictPeriods`, unitary
  groups and affine equivalences, none constructing this scheme.
- LeanFinder: `coordinate Hopf algebra of the upper unitriangular matrix group scheme`
  returned eight hits on general Hopf-algebra constructions (including
  `CommSemiring.toHopfAlgebra` and monoid-algebra Hopf instances), none this group.
- Direct project `rg` searches over `lean/WeilConjectures` and `lean/Sheaf` found only
  unrelated matrix-inverse/block-chart material and references in other algebraic-group
  proof plans, not a definition of this group or a statement of the item. A direct search
  for the item id in `lean/WeilConjectures` found no occurrence. The proposed declaration
  names were also checked in Mathlib, both project source trees and
  `dag/lean_names_upstream.json`: no collision.
- `rg -l --glob 'def-*.json' 'unitriangular|Unitriangular|unitriang|Unitriang' dag/nodes`
  found only `def-pur-complete-flag-bundle` and `def-sfb-adjoint-kernel-points`.
  Reading both statements confirmed that neither defines U_n. The broader DAG hits are
  theorem/proof uses of the inline description. `python3 tools/blueprint_refs.py search
  unitriangular` returned zero blueprint nodes.

Source checked directly: Milne's PDF, the definition before Proposition 14.3 and Theorem
14.5 with proof (b)⇒(c)⇒(a), printed pp.280–282; it explicitly allows alpha_p and Z/p.
The current blueprint direct-image proof (3) was read in `literature/blueprint/latest/`.
No mathematical statement dispute or correction is necessary. Advisory metadata fault:
`blueprint_refs.py ancestor` reports `None` for this pre-existing item (its reviewed
`blueprint.from.node` is also null); the new definition preserves that computed ancestor
and prepends the item to its inherited via list rather than inventing an ancestor.

Validation: both delivered modules were compiled together in dependency order with the
prescribed `scompile.py` wrapper against current server sources. Both server compilations
passed (about 3 and 2.4 seconds), with no errors or non-sorry warnings. The wrapper's local
cache attempt reported no free space and automatically used its authorized server fallback;
the server compile itself completed successfully. No library source or launcher tool was edited.

## New nodes

`def-sfb-unitriangular-group-scheme` supplies the actual U_n construction, missing from the
DAG definitions and both source trees. Its source is Milne Theorem 14.5, p.281, equation (92).
The searches above are recorded in its `mathlib_searches`, including their actual hit counts
and names. The node gives P=k[x_ij:i<j], the universal matrix, coordinate multiplication,
zero upper-coordinate counit and finite-series inverse, and the Spec group scheme. Its module
reuses `MvPolynomial`, `Matrix`, `algSpec`, tensor products and `LinearGroupSchemes.Index`;
it does not redefine any of those notions. `Position` is just the explicitly stated set of
strictly upper positions, and the other helpers belong to this one construction.

Matching its clauses to Lean: `CoordinateRing` is P; `matrix` is M; `comul`, `counit` and
`antipode` give exactly the three displayed generator substitutions. `scheme` is Spec P over k.
`multiplication`, `identitySection`, and `inverse` are the canonical contravariant Spec maps,
using the monoidal Spec comparison for the product and unit. `group_existsUnique` states
that these precise maps uniquely give a `GrpObj`; its docstring includes the full group-axiom
and uniqueness argument, including the empty-index case. `group` selects only that uniquely
specified structure. Evaluation of P at an arbitrary family of upper entries is the existing
`MvPolynomial.aeval` universal property; the generator substitutions make its group operation
matrix multiplication and its inverse the finite geometric series. This gives precisely the
stated functor on every algebra. The new node's `import_flags` is `[]` because the item's
existing target route reaches it. It is directly cited by the item.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
