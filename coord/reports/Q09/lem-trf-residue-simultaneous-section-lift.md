## Worker report

The module `Sheaf.RingTheory.ResidueSimultaneousSectionLift` states
`IsLocalRing.residue_simultaneous_section_lift`, with exactly one postponed theorem.
Two data-complete helpers belonging to this statement define coordinate reduction:
`IsLocalRing.residueCoordinates` applies the quotient coordinatewise, and
`IsLocalRing.residueCoordinateMap` reduces `LinearMap.toMatrix'` and applies
`Matrix.toLin'`. They introduce no independent mathematical notion and use no
choice from a postponed existence theorem. Both have source/blueprint docstrings
and are listed in `lean.declarations`. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0FJK,
`lemma-homotopic-surjections`, especially its final paragraph (lines 37092–37104),
and the preceding construction of the common-summand inverse. Stacks explicitly
omits the lifting details; the eight accepted proof steps are reproduced in the
main declaration's docstring. The current blueprint's `sk-i-curve-zero/_section.md`
and `lem-trf-local-term-locality.md` were also read. This is an auxiliary node,
not a change to that unit.

Hypotheses and clauses, in node order:

- The arbitrary commutative ring with exactly one maximal ideal is
  `(R : Type u) [CommRing R] [IsLocalRing R]`. Mathlib's local-ring convention
  excludes the zero ring, as does existence of a maximal ideal. There is no
  Noetherian, domain, flatness or characteristic assumption.
- `k` is Mathlib's `IsLocalRing.ResidueField R`, definitionally the quotient by
  `maximalIdeal R`; `rho` is `IsLocalRing.residue R`. No arbitrary replacement
  residue field or quotient map is quantified over.
- The nonnegative integers are `(m n : ℕ)` and the coordinate modules are
  `Fin t → R` and `Fin t → ResidueField R`. These are the standard finite free
  modules, including the empty basis. The finite product equals the finite
  direct-sum model used in the node.
- `(α β : (Fin n → R) →ₗ[R] (Fin m → R))` are arbitrary linear maps. Their
  coefficientwise reductions are exactly `residueCoordinateMap R α` and its
  beta analogue. Neither original map is assumed surjective.
- The first conjunct is `IsField (ResidueField R)`. The canonical `Field`
  instance supplied by Mathlib is used for all subsequent linear types; this
  proposition asserts its underlying field property without selecting a new
  field structure.
- `IsLocalHom (residue R)` and the explicit `Ideal.comap` equality render locality
  and the stated inverse-image equality of maximal ideals.
- The implication `Function.Surjective γ → Function.Surjective
  (residueCoordinateMap R γ)`, for either alpha or beta, renders both separate
  descent assertions without inserting surjectivity as a hypothesis.
- The `∀ t` conjunct specifies the scalar identifications by both formulas:
  `TensorProduct.piScalarRight ... (c ⊗ₜ[R] x)` has coordinate
  `residue R (x i) * c`, and its inverse is
  `∑ i, z i ⊗ₜ[R] Pi.single i (1 : R)`. The dependency's recorded convention is
  `k ⊗[R] M` rather than `M ⊗[R] k`; swapping the factors by
  `TensorProduct.comm` gives exactly the node's formulas. Thus there is no
  unspecified comparison equivalence. The equivalence is k-linear.
- For every `q : k^m →ₗ[k] k^n`, the existential `s` has the literal equality
  `residueCoordinates R n (s x) = q (residueCoordinates R m x)` for every x.
- For every column family `v`, the only condition is its reduction on standard
  vectors `Pi.single j 1`. `Pi.basisFun ... |>.constr R` is the actual linear
  extension of these columns. Both its reduction equality and the explicit
  formula `∑ j, x j • v j` are asserted; no preselected lift is used.
- For every s satisfying the reduction equality, the conjugation of
  `(γ.comp s).baseChange k` by `TensorProduct.piScalarRight` equals
  `(residueCoordinateMap R γ).comp q`, for each of alpha and beta. The canonical
  `LinearMap.baseChange` of the recorded dependency is used directly.
- The two `Function.Bijective` premises on the reduced composites render
  precisely their being linear isomorphisms. The conclusion separately gives
  bijectivity of both original composites and `Function.Injective s`.
- `U` is literally `LinearMap.range s`. The equivalence `e` is required to have
  `e.toLinearMap = s.rangeRestrict`; existence of an unrelated isomorphism
  between these modules would not suffice.
- For each gamma, the equivalence `g` is required to have
  `g.toLinearMap = γ.comp (LinearMap.range s).subtype`. These are exactly the
  two restrictions, with codomain R^m.
- `h : IsCompl (LinearMap.ker γ) (LinearMap.range s)` expresses the two internal
  direct-sum decompositions. The final equality uses Mathlib's canonical
  `Submodule.projectionOnto` with `h.symm` and identifies it with
  `g.symm (γ x)`, an equality in the actual subtype U.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`, read its full
  declaration and documentation; `IsField` and the canonical residue-field
  instance express the field assertion.
- `def-weil-pbc-free-module`: `Module.Free`, in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, read the class and its basis
  formulation. Coordinate bases use `Pi.basisFun` and `Module.Basis.constr`.
- `def-weil-module-base-change`: `LinearMap.baseChange`, in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, read the definition and the
  pure-tensor/composition formulas. `TensorProduct.piScalarRight` and its
  inverse, in `Mathlib.LinearAlgebra.TensorProduct.Pi`, implement the displayed
  finite-coordinate identification.
- Proof dependency `lem-weil-pbc-local-ring-unit-criterion`:
  `IsLocalRing.notMem_maximalIdeal`, in
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, read its signature/docstring;
  available via the public residue-field import.
- Proof dependency `lem-sc-local-free-base-change-reflects-iso`:
  `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`,
  in `WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso`, read
  the complete source, signature and proof docstring; imported without `public`.

Edge cases checked mathematically before writing:

- `m = 0`: q and s have zero source, their composites are automorphisms of the
  zero module, U is zero and each kernel is the full source. Empty sums and
  tensor identifications have the required values.
- `n = 0 < m`: the q-lifting and descent implications remain valid; the reduced
  composites cannot be bijective, so no impossible injective/surjective
  conclusion is forced.
- `m = n = 0` is covered with no positivity binder.
- When R is a field the assertions become the usual coordinate calculations.
- Over Z/4, alpha=(1,0), beta=(1,2), and q=(1,0) modulo 2, any lift has odd
  first and even second coordinate; both composites are units. This checks
  the quantification over every lift and the absence of a surjectivity premise.
- Arbitrary characteristic and arbitrary ring universe are permitted. No
  independent smaller coefficient universe restricts the quotient.

Searches (all run via the prescribed wrapper unless stated):

- LeanFinder: “Lift columns of a common section over a residue field to a finite
  free module over a local ring so both composites are invertible and its image
  complements both kernels.” Eight results included
  `Module.exists_basis_of_basis_baseChange`,
  `Module.IsLocalRing.linearCombination_bijective_of_flat`, and
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective`. None states
  this whole two-map result with the specified tensor and projection clauses.
- Loogle: `IsLocalRing, LinearMap, Function.Bijective`. One result:
  `Module.IsLocalRing.linearCombination_bijective_of_flat`. Read its source and
  the split-injection criterion in `RingTheory/LocalRing/Module.lean`; these
  provide single-map criteria, not this statement.
- Mathlib grep: `residue.*[Ll]ift|[Ll]ift.*residue|pi.*[Ee]quiv|[Ee]quiv.*pi`
  in `LinearAlgebra/TensorProduct`. Two hits in `Free.lean` concerning
  `Algebra.TensorProduct.equivPiOfFiniteBasis`, not the theorem. Further direct
  source searches located and reused `TensorProduct.piScalarRight`,
  `LinearMap.toMatrix'`, `Matrix.toLin'`, and `Submodule.projectionOnto`.
- LeanSearch: “For a local ring lift a linear section from the residue field so
  two composites are bijective and the image is a common complement to their
  kernels.” Eight results concern residue-field ring-map lifts, localization,
  and the same linear-combination criterion; no exact theorem.
- Project/upstream rg: `residueSimultaneous|simultaneous.*[Ll]ift|section.*[Ll]ift|
  lem-trf-residue-simultaneous-section-lift` in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`; results were unrelated
  sheaf-section lifts. A narrower conceptual search found the parent
  `LocalCommonSummandSurjections.lean` and `SimultaneousResidueBases.lean`.
  Both were read and neither is the present theorem: the former assumes
  surjectivity and asserts existence of U, the latter is infinite-field
  avoidance for residue bases.
- `grep -rn 'lem-trf-residue-simultaneous-section-lift' lean/WeilConjectures`
  and exact rg for all three proposed names in Mathlib/upstream/Sheaf/the
  upstream-name table gave no matches.

Validation: prescribed `scompile.py` compiled the sandbox probe and the actual
library module cleanly (9.4 s and 3.2 s). The first compile required marking the
coordinate helper noncomputable because Mathlib's residue-field instance is
noncomputable; this was repaired. No source repository file was changed, and no
local/global build was run. No statement correction, disputed assertion,
unusable dependency, or new DAG node was needed.

## Second reading by Q09

A separate self-audit checked the source/node against the final signature clause
by clause, especially the order of tensor factors, all-lifts quantifier, fixed
range/corestriction, both restrictions, and the direction `h.symm` of the
projection. All binders and the universe are explicit; `autoImplicit` is false.
No additional mismatch was found. This is not an independent agent review:
the dispatch brief prohibits starting other agents and assigns independent
review to the maintainer after delivery.
