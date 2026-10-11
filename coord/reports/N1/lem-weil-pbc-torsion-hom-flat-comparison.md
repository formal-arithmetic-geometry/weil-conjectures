## Worker report

The module `Sheaf.RingTheory.TorsionHomFlatComparison` states
`LinearMap.baseChange_bijective_of_ideal_power_torsion`, with its proof `sorry`.
It introduces no definitions and changes only the item's `lean` field.

Hypothesis and clause correspondence:
- Commutative rings R and S: independent `Type u`, `Type v` binders and `CommRing` instances.
- The arbitrary ring homomorphism: `[Algebra R S]`, with its map `algebraMap R S`.
  Any given ring map supplies this algebra via `RingHom.toAlgebra`; no map is excluded.
- Flatness: `_hflat : (algebraMap R S).Flat`.
- The finitely generated ideal: `(I : Ideal R)` and `_hI : I.FG`.
- The canonical quotient map is an isomorphism: `_hquot : Function.Bijective
  (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)`.
  `I.map` is IS, and `Ideal.quotientMap` is the specified induced ring homomorphism;
  bijectivity of this ring homomorphism is exactly being an isomorphism.
- R-modules K and N: independent `Type w`, `Type x`, additive commutative group
  and R-module instances. No finiteness is imposed on either module.
- Elementwise ideal-power torsion of K: `_hK : ∀ k : K, ∃ n : ℕ,
  ∀ r ∈ I ^ n, r • k = 0`. An exponent zero implies k = 0, so allowing it
  agrees with the convention of strictly positive powers (zero is also killed by I).
- The specified Hom map is bijective: `Function.Bijective (LinearMap.baseChange S ...)`.
  Mathlib's factor order is S tensor K. The dependency's recorded identification
  via `TensorProduct.comm` gives precisely the paper's K tensor S, with its S-action.
  `baseChange_tmul` reads `s ⊗ k ↦ s ⊗ f k`, the specified tensor extension.
- Naturality in both modules: the second conjunct quantifies over independent K',N'
  universes and maps a:K'→K, b:N→N', f:K→N, and asserts
  `baseChange (b ∘ f ∘ a) = baseChange b ∘ baseChange f ∘ baseChange a`.
  This is the commuting Hom square, contravariant in K and covariant in N.
  The identity holds for all module maps, hence in particular between torsion sources.

Dependency declarations read and used:
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`;
  its definition is `Module.Flat R S` via the map's algebra. Also read
  `Module.Flat` and `iff_lTensor_preserves_injective_linearMap` in Flat.Basic.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `LinearMap.baseChange` (full signature, surrounding variables, docstring and
  tensor formula read); `TensorProduct.leftModule` in Defs gives the S-module action.
  `baseChange_comp` gives the naturality equation's standard interpretation.
- Mathlib's `Ideal.quotientMap` in Ideal.Quotient.Operations and `Ideal.le_comap_map`
  in Ideal.Maps supply the canonical quotient map, without a private definition.

Source checked: https://stacks.math.columbia.edu/tag/05EC, statement (2) and its
proof, because the local literature TeX is absent. The torsion-source case has exactly
these hypotheses. The docstring follows the node's three proof steps: the torsion-target
adjunction comparison, identification of the target torsion submodule after tensoring,
and unique factorization through that submodule plus the commuting comparison square.
No statement fault or dispute found.

Edge cases checked: K=0, N=0 and zero rings are permitted. For I=0 every module
is torsion and the quotient hypothesis makes the original map an isomorphism.
For I=R torsion forces K=0; the Hom sets are singletons. Exponent zero is harmless
as explained above. There are no Noetherian, nontriviality, characteristic, or finite-module
assumptions. All universes and variables are explicitly bound.

Searches (2026-10-11):
- msearch LeanFinder: "Hom from ideal-power torsion module is bijective under flat base
  change inducing isomorphism modulo ideal": eight hits, including flat local-module
  linear combination and faithfully-flat tensor bijectivity; none states this Hom comparison.
- msearch Loogle: "LinearMap.baseChange, Function.Bijective": zero hits.
- msearch LeanSearch: "Hom from ideal power torsion module unchanged by flat ring extension
  isomorphic modulo ideal": service unavailable (Internal Server Error).
- msearch grep, RingTheory: `baseChange.*[Bb]ijective|[Tt]orsion.*[Hh]om|neighbourhood`:
  eleven unrelated trace, étale, ideal-filter, smooth and localization hits; no match.
- rg of Mathlib, WeilConjectures and lean/Sheaf for torsion/Hom, baseChange/bijective,
  and neighbourhood: no exact comparison. Existing FormalGlueingData uses baseChange;
  CyclicExtensionFlatDescent cites this node but does not state its Hom comparison.
- rg for the node id in WeilConjectures: no hits. rg for the chosen declaration name
  in dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf: no hits.

Validation: scompile.py compiled the file cleanly on the server (1.7 seconds), with no warnings.

## Second reading by N1

I reread the node statement, its dependency records, the Lean module, and Stacks Project
More on Algebra, Lemma 05EC (lemma-neighbourhood-equivalence), part (2), at the source
place recorded in the node.

The node's objects and hypotheses match the Lean as follows:

- The commutative rings (R,S) are the explicitly universe-bound `Type u` and `Type v`
  binders with `[CommRing R]` and `[CommRing S]`.
- The arbitrary ring map φ is represented by the supplied `[Algebra R S]`, whose map is
  `algebraMap R S`; the flatness hypothesis is exactly
  `(algebraMap R S).Flat`.
- The ideal (I : Ideal R), finite-generation hypothesis `I.FG`, and bijectivity of
  `Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
  Ideal.le_comap_map` render the node's finitely generated ideal and
  (R/I \to S/IS) isomorphism.
- The modules (K,N) are independently universe-bound additive commutative groups with
  `Module R` structures, with no finiteness assumptions. The source torsion condition is
  rendered elementwise by `_hK : ∀ k, ∃ n : ℕ, ∀ r ∈ I ^ n, r • k = 0`.
  Allowing (n=0) adds only the zero element case and therefore does not exclude any
  source module covered by the source convention.
- The first conclusion is `Function.Bijective` for
  `LinearMap.baseChange S`, whose domain and codomain are the Mathlib scalar-extension
  Hom spaces. Mathlib's order `S ⊗[R] K` is the dependency's standard tensor order and
  is canonically identified with the node's (K\otimes_R S) by tensor symmetry.
- The naturality clause quantifies over arbitrary additional module universes and maps
  `a : K' →ₗ[R] K`, `b : N →ₗ[R] N'`, and `f : K →ₗ[R] N`, and states the exact
  contravariant-in-source/covariant-in-target composition equation from the node.
  Quantifier order and both composition parentheses agree.

I checked edge cases (K=0), (N=0), zero rings, (I=0), and (I=R); none is
excluded by the Lean binders. The (I=0) quotient condition and the (I=R) torsion
condition behave as in the source. No characteristic, Noetherian, nontriviality, or
finite-module assumption was introduced, and all universe variables are bound.

Searches for an existing declaration were repeated with LeanFinder and Loogle queries
for torsion Hom comparison/base change, LeanSearch, and repository/Mathlib/source `rg`
searches for torsion, Hom, baseChange, and the node id. No exact declaration exists;
the recorded Mathlib declarations `RingHom.Flat`, `Module.Flat`, and
`LinearMap.baseChange` are the dependency notions and are used directly.

No mismatch was found, so no Lean or node statement change was necessary. The module
compiled cleanly with `scompile.py`; its only proof is the required `sorry`.
