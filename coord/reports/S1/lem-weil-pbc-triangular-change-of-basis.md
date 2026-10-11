## Worker report

The module `Sheaf.LinearAlgebra.TriangularChangeOfBasis` states
`Module.Basis.exists_basis_of_triangular_unit_diagonal`, with proof `sorry` only.
It introduces no definitions or additional nodes and makes no statement correction.

Hypothesis and clause correspondence:
- A commutative ring R: `{R : Type u} [CommRing R]`.
- An R-module F: `{F : Type v} [AddCommGroup F] [Module R F]`.
- A nonnegative integer m: `{m : ℕ}`, including zero.
- F free with the specified basis b_1,...,b_m: `b : Module.Basis (Fin m) R F`.
  Index k in `Fin m` corresponds to the paper's index k+1. A supplied basis itself
  witnesses freeness (`Module.Free.of_basis`), so a separate `Module.Free` hypothesis
  would add redundant data. This uses the dependency's recorded Mathlib basis notion,
  not a private definition.
- Vectors v_1,...,v_m: `v : Fin m → F`.
- Coefficients t_kl in R: `t : Fin m → Fin m → R`.
- The coordinate expansion: `hcoords : ∀ k, v k = ∑ l : Fin m, t k l • b l`.
- Either zeros for l<k or zeros for l>k: `htriangular` is the disjunction
  `(∀ k l, l < k → t k l = 0) ∨ (∀ k l, k < l → t k l = 0)`.
  The choice of orientation is global, as in the node, not made separately for each entry.
- Each diagonal coefficient is a unit: `hdiag : ∀ k, IsUnit (t k k)`.
- The family v is a basis of F: `∃ c : Module.Basis (Fin m) R F, ∀ k, c k = v k`.
  Equality of every basis vector ensures precisely the specified family, with the same order.

Dependency: `def-weil-pbc-free-module`, status mathlib, records `Module.Free` in
`Mathlib.LinearAlgebra.FreeModule.Basic`. Its full signature and docstring were read,
as were `Module.Basis` and its coordinate equivalence in
`Mathlib.LinearAlgebra.Basis.Defs`. The module imports the recorded FreeModule.Basic,
which exports Basis.Basic and the finite-sum operations needed by the statement.

Edge cases: m=0 is admitted without a positivity or nonempty assumption; the basis binder
then identifies F with the zero coordinate module and the conclusion is the empty basis.
For m=1, triangularity is vacuous and the assertion is unit scaling. The zero ring is
admitted (no Nontrivial or domain assumption), where the module with a basis is subsingleton
and the assertion remains valid. Both upper and lower triangular families are admitted,
and R and F have independently explicit universes u and v. No field, domain, finite-rank
instance, or independently chosen freeness witness is required.

Source check: the local `literature/stacks-project/algebra.tex` is absent on this machine.
Read the official https://stacks.math.columbia.edu/tag/00MT instead: the proof uses a first
basis change and then the replacements of source vectors by subtracting multiples of the
first vector. The node supplies the elementary triangular generalization justifying these
changes. Its docstring includes every proof step: coordinate identification, the empty
case, descending spanning and ascending independence for upper triangular matrices,
reversed orders for lower triangular matrices, and assembling the basis.

Searches:
- `msearch.py ... leansearch "triangular coordinate matrix with unit diagonal gives a basis
  over a commutative ring"`: service unavailable (Internal Server Error).
- `msearch.py ... leanfinder "A family of vectors whose coordinates in a finite basis are
  triangular with unit diagonal is a basis"`: eight hits, including Smith normal form over
  PIDs, basisOfPiSpaceOfLinearIndependent over division rings, reindexRange, and unitsSMul;
  none is the statement over an arbitrary commutative ring.
- `msearch.py ... loogle "Module.Basis, Matrix.BlockTriangular"`: zero hits.
- `msearch.py ... grep "triangular.*basis|basis.*triangular|is_basis_iff_det" LinearAlgebra`:
  two hits in Determinant.lean at lines 634 and 653. Read the full is_basis_iff_det
  signature: its hypothesis/conclusion concerns unit determinant, not triangular entries.
- `rg -n 'triangular|is_basis_iff_det|lem-weil-pbc-triangular-change-of-basis'` in
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: unrelated triangularization
  and characteristic-polynomial declarations, and prose references in UnitEntrySplits;
  no existing statement of this node.
- `grep -rn 'lem-weil-pbc-triangular-change-of-basis'` in WeilConjectures: no hits.
- `rg -n 'triangular_change_of_basis|basis_of_triangular'` in Mathlib, WeilConjectures,
  and lean/Sheaf: no hits, including no name collision for the new declaration.

No statement dispute or dependency fault was found. Server compilation and the delivery
preflight are checked before handing this statement to the independent second reader.

## Second reading by S1

I independently opened the node copy, its complete four-step proof, the delivered module,
and the sole statement dependency `def-weil-pbc-free-module`. No new definition nodes,
dependency modules, or statement correction are present. No mismatch was found; the Lean
module and node record are left unchanged. This reading adds only this report section.

Object/hypothesis/conclusion checklist (all verdicts: exact):
1. Commutative ring R: `{R : Type u} [CommRing R]`. No field, domain, local,
   Noetherian, nontriviality, or characteristic hypothesis is added.
2. R-module F: `{F : Type v} [AddCommGroup F] [Module R F]`. Its independent universe
   is explicit. These are the standard module structures over a ring.
3. Integer m >= 0 and ordered basis b_1,...,b_m of the free module:
   `{m : ℕ} (b : Module.Basis (Fin m) R F)`. Index k represents source index k+1;
   strict inequalities and the order are preserved. A basis already gives freeness:
   I read `Module.Free` and `Module.Free.of_basis` in FreeModule/Basic.lean:43--65.
   I also read Basis/Defs.lean:79--113: `Basis.repr` is precisely the linear
   equivalence with finitely supported coordinates, and coercion supplies its basis
   vectors. Thus this uses the dependency's notion without a duplicate predicate or
   an additional freeness instance.
4. The new ordered vectors v_1,...,v_m: `(v : Fin m → F)`.
5. Ring coefficients t_kl: `(t : Fin m → Fin m → R)`; these are supplied data,
   quantified before the hypotheses, not coefficients chosen after the conclusion.
6. The expansion v_k = sum_l t_kl b_l:
   `(hcoords : ∀ k, v k = ∑ l : Fin m, t k l • b l)`.
   The sum ranges over all m indices and scalar multiplication has the correct order.
7. One global triangular orientation, either zero for l<k or zero for l>k:
   `(htriangular : (∀ k l, l < k → t k l = 0) ∨
   (∀ k l, k < l → t k l = 0))`. The disjunction is outside both universal
   quantifiers, so it cannot allow a different orientation for each row.
8. Every diagonal entry is a unit:
   `(hdiag : ∀ k, IsUnit (t k k))`. Nonzero would be too weak over rings;
   this is actual invertibility, including in the zero ring.
9. Precisely the ordered family v is a basis of the same F over the same R:
   `∃ c : Module.Basis (Fin m) R F, ∀ k, c k = v k`.
   Pointwise equality imposes every vector, in its original index order, and states
   both spanning and independence through the standard Basis structure.

Source reading: the local Stacks checkout is absent. I read the official page
https://stacks.math.columbia.edu/tag/00MT and independently retrieved the raw Stacks
`algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
locating `lemma-add-trivial-complex` and its complete proof (current lines 24608--24654;
line numbers have shifted from the node's source snapshot). Its ring is arbitrary and
its modules are finite free; there is no hidden local, field, or Noetherian assumption.
The elementary source replacement e'_j = e_j - a_j1 e_1 is the lower triangular,
unit-diagonal case. The node explicitly expands the basis changes into the general
triangular lemma; it does not claim that the general lemma is stated verbatim in Stacks.
The module docstring reproduces all four node proof steps: coordinate map and m=0,
descending spanning/ascending independence, the reversed order for lower triangular
rows, and construction of the basis. Both source and blueprint markers are present.

Edge cases: `Fin 0` is empty and is accepted, with an empty sum and vacuous diagonal
and triangular hypotheses. The supplied empty basis identifies F with the zero module,
and the conclusion asserts its empty basis. For m=1 this is multiplication by a unit.
For a zero module over a nonzero ring, only m=0 can satisfy the basis hypothesis; no
extra exclusion is imposed. The zero ring is allowed for every m, and its modules are
subsingleton, so the given and resulting coordinate bases still make sense. All
characteristics are admitted. Universes u and v are independent and explicitly bound;
the finite index type excludes no possible finite ordered basis. Schemes and empty
schemes are not objects of this node. Neither hypothesis is hollow in general:
triangularity restricts entries and units restrict diagonal entries over ordinary rings.

Independent searches, using different wording from the worker:
- `msearch.py ... leansearch "triangular matrix with invertible diagonal sends basis to
  basis"`: unavailable (Internal Server Error), recorded without a mathematical verdict.
- `msearch.py ... leanfinder "Invertible triangular matrix acting on a finite free module
  transforms its given basis into another basis"`: eight hits, including
  `Module.Basis.toMatrix_isUnitSMul`, `Module.Basis.invertibleToMatrix`,
  `Matrix.toLinearEquiv`, and `LinearEquiv.ofIsUnitDet`. These concern diagonal scaling,
  matrices of already-known bases, or a unit determinant; none states this node.
- `msearch.py ... loogle 'Module.Basis, IsUnit'`: twelve hits, again diagonal scaling,
  determinant units, and general matrix/linear-map invertibility; no exact statement.
- `msearch.py ... grep 'BlockTriangular|IsUpperTriangular|IsLowerTriangular'
  LinearAlgebra`: 21 hits, mostly determinant formulas and rank statements.
- Direct `rg` over Mathlib LinearAlgebra, WeilConjectures, and this project's lean/Sheaf
  for `unitriangular`, triangular/basis/linearindependent combinations, and
  basis-of-IsUnit names: only determinant constructions, field triangularization,
  and UnitEntrySplits prose references. Direct name search in the upstream declaration
  map and both project sources found no collision with the delivered declaration.
  I read Determinant.lean:616--653 and Matrix/Block.lean:336--346: the determinant
  criterion and triangular determinant computations must be combined, with a transpose
  of the row-coordinate convention; they are not an existing declaration of the item.
  FreeModule.Basic exports Basis.Basic, so its one import supplies the notions used.

H5/H6/H9: there are no definitions or local notations, no private copy, and nothing is
proved: the sole theorem has only `sorry`. All variables and universes are bound;
the namespace and topic directory follow Mathlib. The node's `lean.statement` is
verbatim the file's signature. No source or node correction is needed.

Validation: `scompile.py S1 lem-weil-pbc-triangular-change-of-basis` on the delivered
module compiled on the server in 1.1 seconds, exit code 0, with no warnings or errors.
