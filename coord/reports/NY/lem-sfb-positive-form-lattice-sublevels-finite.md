## Worker report

The module `Sheaf.LinearAlgebra.PositiveFormLatticeSublevelsFinite` states
`LinearMap.BilinForm.finite_lattice_sublevel`. Its only proof is `sorry`, as required
in stage 2. No definitions, helper theorems, new nodes, dependency repairs, or
statement corrections are needed. Only the item's `lean` field changes.

Hypothesis and clause correspondence:

- The abelian group is `{M : Type u} [AddCommGroup M]`. Its integer-module
  structure is Mathlib's canonical `AddCommGroup.toIntModule`; no separate
  `Module ℤ M` instance is needed. This includes every abelian group in any universe.
- A free abelian group with a finite integer basis is rendered by `{ι : Type v}
  [Finite ι] (_b : Module.Basis ι ℤ M)`. The basis is the exact basis notion
  underlying the dependency `Module.Free`. A supplied finite basis and a finite
  free group are equivalent data here. There is no nonemptiness restriction on ι.
  The index universe `v` is independent of `u` and imposes no size restriction.
- The vector space is literally `M ⊗[ℤ] ℚ`, using the dependency's `TensorProduct`.
  Its canonical rational action on the second factor is written explicitly as
  `((TensorProduct.comm ℤ M ℚ).toAddEquiv.module ℚ)` in the form's type. This is
  Mathlib's existing additive-equivalence transport of the usual left action on
  `ℚ ⊗[ℤ] M`; on pure tensors it sends `q • (m ⊗ₜ a)` to `m ⊗ₜ (q*a)`.
  No arbitrary scalar action is assumed and no new scalar-action notion is defined.
- The map identifying the lattice with its image is literally
  `m ⊗ₜ[ℤ] (1 : ℚ)`. Its injectivity follows from the supplied basis: after tensor
  commutation, `(b.baseChange ℚ).repr (1 ⊗ₜ m) i` is the rational cast of `b.repr m i`.
  Equality of tensors gives equality of each integer coordinate by injectivity of
  `ℤ → ℚ`, hence equality of lattice elements. The node's identification introduces
  neither a new hypothesis nor an extra conclusion.
- `B : @LinearMap.BilinForm ℚ _ (M ⊗[ℤ] ℚ) _ ...` is a rational-valued form
  linear in each of its two arguments, using the canonical rational action above.
  Mathlib's `BilinForm` abbreviates `V →ₗ[ℚ] V →ₗ[ℚ] ℚ`.
- Symmetry is exactly `hsymm : ∀ x y : M ⊗[ℤ] ℚ, B x y = B y x`.
- Positive definiteness is exactly
  `hpos : ∀ x : M ⊗[ℤ] ℚ, x ≠ 0 → 0 < B x x`.
- The arbitrary rational bound is `(c : ℚ)` with no sign restriction.
- The entire conclusion is
  `{m : M | B (m ⊗ₜ[ℤ] (1 : ℚ)) (m ⊗ₜ[ℤ] (1 : ℚ)) ≤ c}.Finite`,
  so it concerns lattice elements themselves, not just their tensor images.

Dependencies read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free`, with its defining basis `Module.Basis` from
  `Mathlib.LinearAlgebra.Basis.Defs`. Both full declarations and docstrings were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.tmul`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`, publicly imported through
  `Mathlib.LinearAlgebra.TensorProduct.Basic`. Read the quotient construction and
  pure-tensor map, as well as `TensorProduct.comm` and its pure-tensor formula.
- The action transport is the existing `AddEquiv.module` in
  `Mathlib.Algebra.Module.TransferInstance`, whose full signature and data were read.
- Proof-only imports are `Mathlib.LinearAlgebra.TensorProduct.Basis`
  (`Module.Basis.baseChange`, `Module.Basis.baseChange_apply`,
  `Module.Basis.baseChange_repr_tmul`; node
  `lem-weil-pbc-free-module-base-change-free`) and
  `Mathlib.LinearAlgebra.QuadraticForm.Basic`
  (`LinearMap.BilinForm.exists_orthogonal_basis`; node
  `lem-sfb-rational-symmetric-form-orthogonal-basis`). Their recorded Mathlib matches,
  signatures, and docstrings were read. The theorem docstring carries all four
  proof steps, including the explicit coordinate bounds and finite integer box.

Edge cases checked before writing:

- Empty basis: `M` and its rationalization are zero; the sublevel is empty for
  `c < 0`, and the singleton zero for `c ≥ 0`. `Finite ι` permits this case.
- Negative `c` in any rank: bilinearity gives `B 0 0 = 0`, positivity gives
  nonnegative self-values everywhere, so the sublevel is empty.
- `c = 0`: positive definiteness and lattice injectivity give just zero.
- Rank one with `B(x,y) = d*x*y`, any positive rational `d`: bounded integral
  coordinates are finite; no integrality or lower bound on `d` is assumed.
- The positivity hypothesis is on every rational vector, exactly as the node says;
  the theorem does not assume a real extension, topology, norm, chosen real
  embedding, nonzero rank, or nondegenerate matrix as extra input.

Searches (all performed on 2026-10-24):

1. `msearch.py ... leanfinder`, query “A positive definite rational bilinear form
   has finite bounded sublevels on a finite free integer module”: 8 hits,
   including `ZLattice.normBound_pos`,
   `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`,
   `ZLattice.tsumNormRPowBound_pos`, `ClassGroup.normBound_pos`,
   `ZLattice.normBound`, and the unit-lattice finite-ball theorem. These concern
   real normed lattices or specific number-field embeddings and do not give the
   exact rational abstract-module statement.
2. `msearch.py ... loogle`, query `"QuadraticMap", "finite"`: 0 hits.
3. `msearch.py ... grep`, query
   `finite.*sublevel|sublevel.*finite|finite.*posDef|posDef.*finite` in
   `LinearAlgebra`: 6 hits (quadratic-form signatures and matrix positivity
   documentation), none stating the item.
4. `msearch.py ... leansearch`, query “A positive definite bilinear form on a
   rational vector space has finite bounded sublevel sets on a finite free integer
   module”: 8 hits on `QuadraticMap.PosDef`,
   `LinearMap.BilinForm.nondegenerate_iff'`, nonnegative forms, and root forms;
   no finite-sublevel theorem.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `positive.*[Ll]attice|[Ll]attice.*sublevel|posDef.*finite|finite.*posDef|positiveFormLatticeSublevels`:
   only unrelated grading, monoid-algebra, character-lattice, and adic-lattice
   comments. Searching the exact item id in `lean/WeilConjectures` gave no match.
   Searching `finite_lattice_sublevel` in Mathlib, both project roots, and
   `dag/lean_names_upstream.json` gave no match.

Source read: Milne AV PDF page 68 (printed p.62), including Theorem 14.3 and the
proof of Proposition 14.4(a). Also read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
The source's sentence asserting that the entire real endomorphism space is compact
is the already recorded typo for the fixed positive-form level set. The node's
bounded-ellipsoid auxiliary statement is correct; no statement dispute or
correction is required.

Validation: server compilation through the prescribed `scompile.py`; the initial
instance diagnostic was resolved by using the canonical integer-module structure
on an abelian group and writing symmetry directly as its quantified equality.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
