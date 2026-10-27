## Worker report

The module `Sheaf.AlgebraicGeometry.GenericOpenPrincipalMultiplicationData` states
`AlgebraicGeometry.generic_open_principal_multiplication_data`, with its sole proof `sorry`.
It formalizes the third paragraph of Stacks Tag 0573, read in
`literature/stacks-project/more-morphisms.tex`, lines 6563 onward, together with the
multiplication criterion of Tag 0565, read in `literature/stacks-project/algebra.tex`,
lines 4405 onward. The theorem docstring includes all four accepted DAG proof steps.
No statement correction, new notion, dependency replacement, or disputed statement is needed.

Hypotheses and conclusions, in node order:

- A commutative integral domain: `(A : Type u) [CommRing A] [IsDomain A]`.
- A commutative finite type A-algebra: `(B : Type v) [CommRing B] [Algebra A B]`
  and `hB : (algebraMap A B).FiniteType`. This uses the dependency's exact recorded
  `RingHom.FiniteType`; its `finiteType_algebraMap` identifies this with
  `Algebra.FiniteType A B` for the given algebra structure.
- The fraction field: `(K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]`.
  `IsFractionRing` is localization at `nonZeroDivisors A`; because A is a domain,
  these are exactly its nonzero elements. This permits any chosen fraction-field model.
- `B_K` is the actual Mathlib algebra tensor product `B ⊗[A] K`.
- `X` and `X_K` are `Spec (.of B)` and `Spec (.of (B ⊗[A] K))`.
- The arbitrary open subscheme is `(U : (Spec (.of B)).Opens)`; the standard restricted
  scheme and its canonical open immersion are supplied by Mathlib. There is no
  compactness assumption on U.
- The canonical projection on points is
  `PrimeSpectrum.comap (algebraMap B (B ⊗[A] K))`. The tensor product's canonical
  left algebra structure has algebra map `b ↦ b ⊗ₜ[A] (1 : K)`; this is exactly the
  ring map defining the projection, not an arbitrary map or chosen comparison.
- Its inverse image `U_K` is written using `TopologicalSpace.Opens.comap` of that map
  with the canonical continuity proof `PrimeSpectrum.continuous_comap`. This writes
  the same inverse-image open directly and allows independent universes u, v, w.
  It imposes no universe equality to bundle the projection as a scheme morphism.
- The sheaf injection hypothesis is `hU : SchematicallyDenseOpen (Z := Spec ...)
  (TopologicalSpace.Opens.comap ... U)`. The existing definition asserts injectivity
  of restriction `O(W) → O(W ∩ U_K)` for EVERY open W, exactly equivalent to the
  canonical sheaf injection `O_X_K → (j_K)_* O_U_K` in the node.
- `∃ (m : ℕ) (g : Fin m → B)` is the finite list, including m = 0; no positivity or
  nonemptiness assumption is present.
- The first conjunction clause is
  `∀ i : Fin m, PrimeSpectrum.basicOpen (g i) ≤ U`, exactly `D(g_i) ⊆ U`.
- The second clause equates the SAME inverse-image open with
  `⨆ i : Fin m, PrimeSpectrum.basicOpen (g i ⊗ₜ[A] (1 : K))`, exactly its required
  union, not merely a containment or coverage of a smaller open.
- The final clause is `Function.Injective (fun b : B ⊗[A] K ↦ fun i : Fin m ↦
  (g i ⊗ₜ[A] (1 : K)) * b)`. The finite product `Fin m → B_K` is the canonical
  coordinate representation of `B_K^{⊕ m}`. Thus this is precisely mu_K, with the
  specified multiplication order. For m = 0 its codomain is a singleton.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (definition and docstring),
  `RingHom.finiteType_algebraMap`, `Algebra.FiniteType`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and `TensorProduct.mk`;
  `.Basic`: `TensorProduct.lift`, `lift.tmul`, `ext'`; `.Map`: `LinearMap.rTensor`.
  Tensor multiplication, `Algebra.TensorProduct.includeLeftRingHom`, and its canonical
  `leftAlgebra` were read in `Mathlib.RingTheory.TensorProduct.Basic`, which is imported
  publicly to provide the ring structure used in the statement.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the open is represented by the standard `Scheme.Opens`/restricted-scheme interface.
- `Sheaf.TraceFormula.SchematicallyDenseOpen`: `AlgebraicGeometry.SchematicallyDenseOpen`.
  Its already-landed definition node `def-trf-schematically-dense-open` is added to
  stmt_deps under brief-stage2 section 5, STMT_DEPS MAY GAIN LANDED NODES.
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: `PrimeSpectrum.basicOpen`,
  `PrimeSpectrum.continuous_comap`, `PrimeSpectrum.comap_basicOpen`, and the recorded
  basic-open basis/localization results, used in the proof plan.
- Proof imports cover all stated proof dependencies: `Mathlib.RingTheory.FiniteType`
  (`Algebra.FiniteType.isNoetherianRing`); `Mathlib.AlgebraicGeometry.Noetherian`
  (`IsLocallyNoetherian`, `IsNoetherian`, open-subscheme instances and
  `IsNoetherian.noetherianSpace`); `Mathlib.AlgebraicGeometry.AffineScheme`
  (`Scheme.compactSpace_of_isAffine`); `.Morphisms.QuasiSeparated`
  (`quasiSeparatedSpace_of_isAffine`); and
  `Sheaf.AlgebraicGeometry.AffineSchematicDensityCriterion`
  (`AlgebraicGeometry.affine_schematic_density_criterion`).
  Statement imports are public; proof-only imports are plain imports.

Edge cases checked before writing:

- B = 0 and B_K = 0 are permitted. Both spectra are empty as appropriate; m = 0
  has empty union and injective map from the zero ring to the empty tuple.
- B can be nonzero with B_K = 0 (for example A = Z, B = Z/2Z). For U empty the
  density hypothesis on the empty generic scheme holds, and the empty family works.
- U_K empty with B_K nonzero fails the sheaf-injectivity hypothesis, already on
  global sections. The conclusion is therefore not forced incorrectly in that case.
- U = X admits g_0 = 1 and m = 1, with identity multiplication.
- Nilpotents and zero divisors in B or B_K are permitted: no reducedness or domain
  assumption is imposed on B. For k[x,y]/(xy), D(x) alone kills y and is not
  schematically dense, whereas D(x) union D(y) has injective tuple multiplication.
- An arbitrary non-quasi-compact U is allowed. Only U_K is quasi-compact in the
  proof, because B_K is finite type over a field and is consequently Noetherian.
- Independent universes u, v, w are explicitly bound; both auto-implicit options
  are disabled. The inverse-image construction works across these universes.

Searches for an existing exact statement:

- msearch.py LeanSearch: `finite principal open cover of schematically dense generic
  fibre with injective multiplication by defining functions` returned eight results:
  open-cover constructors, finite-subcover, and germ-injectivity tools. None combines
  total-space principal-open selection, generic-open equality, and injective multiplication.
- msearch.py LeanFinder: `A schematically dense open in the generic fibre of a finite
  type algebra over a domain has a finite cover by total space principal opens whose
  tuple multiplication is injective` returned eight results on germ injectivity,
  dominance, rational maps and a dense affine Zariski subsite; none is this theorem.
- msearch.py Loogle: `PrimeSpectrum.basicOpen, Function.Injective`: zero hits.
- msearch.py grep in AlgebraicGeometry:
  `schematicallyDense|SchematicallyDense|generic.*principal|principal.*generic`: zero hits.
- Direct rg in lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `generic_open_principal_multiplication_data|GenericOpenPrincipalMultiplicationData`
  found no existing declaration. Searching the item id in lean/WeilConjectures found none.
- Direct concept searches `generic.*principal|principal.*generic` found related
  generic-principal, generic-flatness and fibre-assassin proofs, but not this selection
  statement. Direct schematic-density searches found and reused SchematicallyDenseOpen
  and the affine criterion. The parent SchematicDensityGenericFibreOpen states a
  spreading conclusion, not this finite family and injective map.
- Raw machine search records are in the sandbox's searches.jsonl, maintained by msearch.

Validation: scompile.py compiled both the sandbox probe and final library module cleanly
(15.9 s and 5.0 s respectively); no errors or disallowed warnings.

## Second reading by Q84

I reread the node statement and the complete generated module together after compilation.
This was an in-thread second pass: the dispatcher explicitly forbids starting other agents;
the maintainer's independent review remains the next review stage.

The domain hypothesis applies only to A, finite type is relative to its actual algebra map,
and K is a field with the exact fraction-ring property. The tensor is B tensor_A K, in the
order specified by the node. Both occurrences of U_K use the identical prime-contraction
inverse image for the canonical left tensor map. SchematicallyDenseOpen quantifies over
all ambient opens, not only global sections, so the sheaf hypothesis has its full meaning.
The existential uses Fin m with no nonempty restriction; its first clause gives total-space
containment, its second is equality to the entire generic open, and its third multiplies
by g_i tensor 1 on B_K. The finite product is the coordinate form of the finite direct sum,
including the empty one. No reducedness, flatness, or compactness was added.

No mathematical mismatch was found. Reusing the existing density definition requires its
already-landed node in stmt_deps; the record adds that node and otherwise changes only lean.
The module has one theorem with a sorry-only proof, source/blueprint docstrings and the
complete four-step natural-language proof; no helper definition or extra theorem is introduced.
