## Worker report

Item: `lem-trf-contracted-prime-tensor-comparison`.
Module: `Sheaf.RingTheory.ContractedPrimeTensorComparison`.
Main declaration: `LocalizedModule.contractedPrime_tensor_comparison`.

The module states exactly the two canonical tensor comparisons in Stacks Project,
Algebra, Tag 05CL, proof of `lemma-universally-injective-check-stalks`, together with
their naturality and the already-localized coefficient specialization. The theorem
has its whole proof postponed with `sorry`; no theorem is proved in this delivery.
The node's statement, dependencies and proof plan are unchanged.

The public abbreviation `LocalizedModule.ContractedPrimeTensorComparison` expands
this very proposition. Its body installs the canonical scalar structures with
`letI`; these are concrete constructions from existing Mathlib declarations, not
postponed data. The theorem's signature contains no let binders and there are no
file-local instances, private definitions, or local notation. The abbreviation is
an elaboration helper for the owning statement, not a separate mathematical notion.

Hypotheses and objects, clause by clause:

- A homomorphism of commutative rings R to A is represented by independent
  `R : Type u`, `A : Type v`, `[CommRing R]`, `[CommRing A]`, `[Algebra R A]`.
  Its map is `algebraMap R A`. Every unital map between commutative rings supplies
  this algebra structure by `RingHom.toAlgebra`.
- The prime q is `q : PrimeSpectrum A`; p is written everywhere as
  `q.asIdeal.comap (algebraMap R A)`. Thus the contracted prime is not an extra
  choice or an independently assumed prime.
- P and P' are `Type w` and `Type x`, with `AddCommGroup` and `Module A`.
  Their `Module R` and `IsScalarTower R A` binders express the prescribed
  restriction of scalars. These impose no additional mathematical hypothesis:
  the canonical restricted structures are provided by `Module.compHom` and
  `IsScalarTower.of_compHom`.
- N is `N : Type y`, `[AddCommGroup N]`, `[Module R N]`. The five universes
  u, v, w, x, y are independent; no finite generation, flatness, domain or
  nontriviality assumption is made.
- Localization is the dependency's `LocalizedModule S M`, with
  `S = q.asIdeal.primeCompl` or `p.primeCompl`. Ring localizations are
  `Localization.AtPrime`. Tensors are the dependency's `TensorProduct`, with
  the base ring explicitly written in each tensor notation.
- The map R_p to A_q is precisely
  `Localization.localRingHom p q.asIdeal (algebraMap R A) rfl`.
  Mathlib's `Localization.localRingHom_mk'` gives its required formula
  r/t maps to phi(r)/phi(t). Its `toAlgebra` and `Module.compHom` give exactly
  the actions requested by the node. `IsScalarTower.of_compHom` supplies the
  compatibility needed to restrict the localized module maps.

Conclusions, clause by clause (read the abbreviation's body):

- `α` and `α'` are `LinearEquiv` over `Localization.AtPrime q.asIdeal` from
  the localization of P tensor_R N (respectively P' tensor_R N) to
  P_q tensor_R N (respectively P'_q tensor_R N).
- The first and second conjuncts give, for every p, n, s,
  `α (LocalizedModule.mk (p ⊗ₜ[R] n) s) = LocalizedModule.mk p s ⊗ₜ[R] n`,
  and the identical formula for α'. Thus these are the canonical maps, rather
  than unspecified isomorphisms. Pure fractions generate the source, so the
  formulas determine them uniquely. No choice of a comparison is defined.
- `β` and `β'` are `LinearEquiv` over the same A_q, with targets
  P_q tensor_{R_p} N_p and P'_q tensor_{R_p} N_p. The third and fourth conjuncts
  specify `β (z ⊗ₜ[R] n) = z ⊗ₜ[R_p] LocalizedModule.mk n 1`, and similarly
  for β'. Again, the pure tensor formulas determine these maps uniquely.
- The fifth conjunct quantifies every `f : P →ₗ[A] P'` and every element z of
  the localized tensor module. Its left side is β' applied to α' applied to
  the localization (`LocalizedModule.map`) of
  `TensorProduct.AlgebraTensorModule.rTensor R N f`. Its right side is the
  right tensor of the localized f, restricted to R_p, applied to `β (α z)`.
  This is exactly c_{P',N} composed with localized (f tensor 1), equal to
  (localized f tensor 1) composed with c_{P,N}. An equality on all elements
  is the equality of the node's linear maps.
- The sixth conjunct quantifies every compatible R_p-action on N by
  `[Module R_p N] [IsScalarTower R R_p N]`; it does not assume such an action
  in the general comparison. It gives `δ : N_p ≃ₗ[R_p] N` with
  `δ.symm n = LocalizedModule.mk n 1`. Thus n maps to n/1 as an R_p-linear
  isomorphism in the direction the node specifies.
- The next clause states
  `δ (LocalizedModule.mk n t) = IsLocalization.mk' R_p 1 t • n`,
  precisely the inverse n/t maps to t^{-1}n. The reciprocal is the fraction
  1/t; no field inverse or domain hypothesis is used.
- The final clause is the corresponding naturality square after applying
  `δ.toLinearMap.lTensor P_q` or `δ.toLinearMap.lTensor P'_q` on the second
  tensor factor. Its right side tensors localized f with `1_N`. These maps
  are isomorphisms since δ, α and β are linear equivalences. The formulas
  also identify the resulting comparison on a pure fraction as
  (p tensor n)/s maps to (p/s) tensor n.

The theorem is stated for an arbitrary pair P, P' so naturality is simultaneous
for all maps between them. This is equivalent to the node's canonical family:
the fraction formulas uniquely determine each comparison, including when P = P'.
The specialization uses the same four comparisons chosen before quantifying
compatible localized actions on N, as required by the source.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule`, `LocalizedModule.mk`,
  `LocalizedModule.mkLinearMap` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`; the induced map
  `LocalizedModule.map` and its full localized-linear signature in
  `Mathlib.RingTheory.Localization.Module`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`. The underlying set of the dependency's
  spectrum is `PrimeSpectrum A`, used for q here.
- `def-weil-pbc-module-tensor-product` (Mathlib leaf): `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `LinearMap.rTensor`,
  `LinearMap.lTensor`, from the recorded Defs/Basic/Map modules. The A-linear
  version used before localization is
  `TensorProduct.AlgebraTensorModule.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- Proof dependencies `lem-weil-pbc-localization-tensor-over-base` and
  `lem-weil-pbc-localization-tensor-product` are Mathlib leaves with no lean
  field. Their `IsLocalizedModule.rTensor`, `IsLocalizedModule.map_lTensor`,
  `IsLocalization.instIsLocalizedModuleTensorProductMap`,
  `IsLocalization.moduleTensorEquiv` signatures and docstrings were read in
  `Mathlib.RingTheory.Localization.BaseChange`, imported as a proof dependency.
  No replacement records or dependency modules are necessary.
- `Localization.localRingHom`, `localRingHom_to_map`, `localRingHom_mk'` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` give the canonical scalar map.
  The existing `algebraOfLiesOver` was also inspected; the direct localRingHom
  representation avoids adding a lies-over instance to the theorem's inputs.

Edge cases checked mathematically before and after writing:

- A = 0 has no prime q; the theorem correctly has no applicable q. R = 0
  forces A = 0. No nonzero ring assumption is introduced.
- P = 0, P' = 0, or N = 0 yields the expected zero tensor modules and the
  same naturality equations; arbitrary zero and identity maps are included.
- For Z to Z[X], q = (X), p = (0), N = Z/2, both comparisons give zero,
  since the denominators invert 2. The unrestricted N case is essential.
- For a field base, localization at its zero prime changes no base modules;
  the formulas reduce to the usual tensor localization formula.
- If N already has a compatible R_p action, 1/t acts as the inverse of t;
  the specialization is valid even for rings with zero divisors and torsion
  modules. It does not identify N with N_p without this hypothesis.
- P and P' can lie in different universes. Denominators always belong to
  the actual prime complements, with no assumption that they are nonzero
  divisors in the original rings.

Searches performed (recorded also in the sandbox searches.jsonl):

1. `msearch.py ... leanfinder`: "Localization of an algebra module tensor a base
   module at a prime equals tensor over the contracted prime naturally in the
   algebra module". Eight hits, including `IsLocalizedModule.rTensor`,
   `IsLocalization.moduleTensorEquiv`, and localization base-change lemmas.
   These provide ingredients, not the full pair of comparisons and squares.
2. `msearch.py ... loogle`: `IsLocalization.moduleTensorEquiv`. One hit:
   tensor over the localization versus tensor over the original base for two
   modules already equipped with localized actions. It does not supply the
   arbitrary N localization comparison or the stated naturality package.
3. `msearch.py ... grep`: `moduleTensorEquiv|localRingHom|rTensor` in
   `RingTheory/Localization`. Ten hits in AtPrime/Basic and BaseChange,
   including exactly the canonical ring-map and tensor ingredients used.
4. `msearch.py ... leansearch`: "localization tensor product at an algebra prime
   and the contracted prime natural in the module". Eight hits, including
   `IsLocalizedModule.rTensor`, the localized tensor-map instance,
   `LocalizedModule.AtPrime`, and localization-of-localization equivalences;
   no declaration states the whole node.
5. Project source `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `contracted.*[Tt]ensor|[Tt]ensor.*[Cc]ontracted|tensor.*[Aa]tPrime|[Aa]tPrime.*tensor`
   and the item id; no existing complete comparison. Related published modules
   `FlatModuleAtPrime` and `UniversalInjectiveCheckStalks` use the same canonical
   restriction along `localRingHom`, and were read for the scalar conventions.
   A search for the item id in `dag/lean_names_upstream.json` found no match.
6. The node's latest blueprint ancestor `lem-trf-local-term-locality` and unit
   `sk-i-curve-zero` were read under `literature/blueprint/latest`. Their current
   text does not restate this auxiliary algebra argument. The item's exact
   source is the explicit Stacks 05CL paragraph, which was read locally.

No statement correction, disputed statement, new node, or dependency repair.

Validation: the complete module compiled with scompile.py, both as the isolated
sandbox module and as `Sheaf.RingTheory.ContractedPrimeTensorComparison`, with
no errors or non-sorry warnings. The first compile exposed an omitted
`TensorProduct` namespace qualification; it was corrected before the clean run.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
