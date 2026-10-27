## Worker report

The module `Sheaf.RingTheory.FiniteComoduleCoefficientCoalgebra` states
`Coalgebra.finite_comodule_coefficient_coalgebra`, with `sorry` as its whole proof.
Its two supporting definitions belong to the coefficient construction explicitly
introduced in this node: `Coalgebra.matrixCoefficient` extracts the specified
coefficient using a basis coordinate functional and the left tensor unitor;
`Coalgebra.coefficientSpan` is the span of their range on `I × I`.
Both definitions have real data, and both are listed in `lean.declarations`.
There is no new independent notion, new node, dependency repair or statement change.
The accepted stage-1 split is preserved verbatim.

Source read: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175
(PDF pp.186–187), the displayed coefficient equations and the paragraph before
Theorem 9.32. The current blueprint unit `sk-thm-sf-ctf-stability/_section.md`
was also read. The present node is a supporting input, not that unit's statement.

Hypotheses and definitions, matched individually:

- The field k is `{k : Type u} [Field k]`.
- The vector space C is `{C : Type v} [AddCommGroup C] [Module k C]`.
  `[Coalgebra k C]` supplies the linear comultiplication and counit, exactly
  coassociativity and both counit laws. No algebra multiplication or
  cocommutativity on C is required.
- The vector space M is `{M : Type w} [AddCommGroup M] [Module k M]`.
- The given right coaction is `(ρ : M →ₗ[k] M ⊗[k] C)`.
- `hcoassoc` is `(assoc k M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
  (Coalgebra.comul ...).lTensor M ∘ₗ ρ`, the equation
  `(ρ tensor 1)ρ = (1 tensor Delta)ρ` after the canonical associator.
- `hcounit` is `(rid k M).toLinearMap ∘ₗ (Coalgebra.counit ...).lTensor M ∘ₗ ρ =
  LinearMap.id`, precisely the right-comodule counit identity after M tensor k = M.
- Finite dimension is `[FiniteDimensional k M]`, the recorded Mathlib notion.
- The arbitrary finite index set and basis are `{I : Type t} [Fintype I]` and
  `(b : Module.Basis I k M)`. `[DecidableEq I]` supplies equality decisions for the
  displayed Kronecker delta; every finite index set admits this structure.
  There is no `Nonempty I` and no restriction on the universes u, v, w, t.
- The node's defined c_ij is `matrixCoefficient b ρ i j`, explicitly
  `TensorProduct.lid k C ((b.coord i).rTensor C (ρ (b j)))`.
- The node's D is `coefficientSpan b ρ`, explicitly
  `Submodule.span k (Set.range fun ij : I × I => matrixCoefficient b ρ ij.1 ij.2)`.

Every clause of the conclusion:

- The first conjunct states `ρ (b j) = ∑ i, b i ⊗ₜ[k] matrixCoefficient b ρ i j`.
  This verifies the coefficient definition against the expansion in the node;
  it does not assume an arbitrary family of coefficients or add a hypothesis.
- The second conjunct is `comul c_ij = ∑ a, c_ia ⊗ₜ[k] c_aj`, in the node's order.
- The third is `counit c_ij = if i = j then 1 else 0`, the Kronecker delta in k.
- The fourth is `FiniteDimensional k (coefficientSpan b ρ)`.
- The fifth is `Function.Injective (TensorProduct.map D.subtype D.subtype)`,
  explicitly justifying the node's identification of D tensor D with its image.
- The final conjunct quantifies `∃ d : Coalgebra k D`. This is a proposition about
  the actual coefficient span, not a definition choosing data from a sorry.
  The field `d` contains coassociativity and both counit identities.
  Its two required equations are
  `(iota tensor iota) ∘ₗ d.comul = Coalgebra.comul ∘ₗ iota` and
  `d.counit = Coalgebra.counit ∘ₗ iota`.
  These say precisely that the two maps are the ambient restrictions and that
  the inclusion is a coalgebra homomorphism. Together with tensor injectivity,
  they pin down the comultiplication uniquely. No arbitrary coalgebra structure
  without the restriction equations is accepted.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (publicly available through
  the statement imports); its docstring and full class signature were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, its bilinear construction,
  `TensorProduct.map`, `LinearMap.rTensor` and `lTensor`, and
  `TensorProduct.assoc`, `lid`, `rid` from Mathlib's tensor-product modules,
  exposed by `Mathlib.RingTheory.Coalgebra.Basic`.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`, the abbreviation
  for `Module.Finite`, from `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- Proof dependency `lem-trf-vector-subspace-complement`:
  `Submodule.exists_isCompl`, from `Mathlib.LinearAlgebra.Basis.VectorSpace`,
  imported without `public`, following the accepted proof plan.

The full signatures and docstrings of `CoalgebraStruct`, `Coalgebra` and
`Module.Basis.coord` were also read. In particular, the existing Mathlib
coalgebra structure already encodes the exact three coalgebra laws, and no
private version of it was introduced. The specialized Hopf-action comodule
predicates in `Sheaf.RingTheory.HopfActionModuleData` require a commutative
Hopf algebra, so they cannot encode this general coalgebra input; here the two
laws are written directly as hypotheses, without defining another predicate.

Edge cases checked before writing: I empty forces M zero; its coefficient range
is empty and D is the zero subspace. The coefficient formulas are then vacuous,
finite dimension holds, the tensor inclusion is an injection from zero, and the
zero coalgebra has zero counit and comultiplication, satisfying both counit
identities on zero. For I singleton the identities say that the single coefficient
is group-like. C zero is allowed and counitality then forces M zero. Coefficients
need not be independent. C may be infinite-dimensional, k may have any
characteristic, and all four object/index universes remain independent.

Fresh searches for reuse, all through the prescribed msearch wrapper:

- LeanFinder: "The matrix coefficients of a finite dimensional comodule span a
  finite dimensional subcoalgebra" returned eight hits, headed by
  `Coalgebra.Repr.index`, `.arbitrary`, `.ι`, and
  `FiniteDimensional.span_of_finite` / `.span_finset`. Reading their source shows
  a finite presentation of one comultiplication or finite dimension of a span,
  not the comodule identities and coefficient-subcoalgebra theorem.
- Loogle: `"Coalgebra", "FiniteDimensional"` returned no hits.
- Mathlib grep: `[Cc]omodule|[Cc]oefficient|[Ss]ubcoalgebra` in
  `RingTheory/Coalgebra` returned only the MonoidAlgebra documentation mentioning
  its coefficients. No matching definition or theorem.
- LeanSearch: "Matrix coefficients of a finite dimensional coalgebra comodule
  form a subcoalgebra" returned eight hits on `Pi` coalgebra maps, `Coalgebra.Repr.eq`
  and `CoalgCat` comonoid equivalences. None states this coefficient theorem.
- Project rg searches for `comodule|subcoalgebra|coefficientcoalgebra|coefficient_coalgebra`
  in `lean/Sheaf` and `lean/WeilConjectures` found only specialized Hopf action
  predicates, documentation and proof sketches. The exact node-id search in
  `lean/WeilConjectures` found no declaration. Searches for the proposed
  `matrixCoefficient` / `coefficientSpan` names found no existing declaration.

Validation: `scompile.py NM lem-sfb-finite-comodule-coefficient-coalgebra` compiled
both the sandbox module and its final library name with no warnings or errors.
All universes and variables are explicitly bound, and `autoImplicit` is false.
The theorem docstring includes each of the seven accepted natural-language proof
steps, including complement-based tensor injectivity and descent of both counit
laws. Every theorem proof is `sorry`; no proof was supplied in stage 2.

No disputed statement or mathematical node fault was found. The previous
unchanged-item refusal concerned stage-1 work; the current stage-2 queue lists
this item as `state`, and the live node has no Lean record, so this delivery adds
that record and a new module without reopening the split.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
