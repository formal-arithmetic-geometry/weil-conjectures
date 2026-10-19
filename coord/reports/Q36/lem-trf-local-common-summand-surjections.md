## Worker report

The module `Sheaf.TraceFormula.LocalCommonSummandSurjections` states the existence of a common submodule for two surjective maps between finite tuple modules over a commutative local ring. The tuple modules `(Fin n → R)` and `(Fin m → R)` are the finite free modules `R^{\oplus n}` and `R^{\oplus m}` (including rank zero). The theorem has the following rendering of each part of the node statement:

- “`R` is a commutative local ring” is `{R : Type u} [CommRing R] [IsLocalRing R]`.
- “`m,n ≥ 0`” is `(m n : ℕ)`; naturals include zero.
- “`α, β : R^{\oplus n} → R^{\oplus m}` are `R`-linear” is `(α β : (Fin n → R) →ₗ[R] (Fin m → R))`.
- “both maps are surjective” is `hα : Function.Surjective α` and `hβ : Function.Surjective β`.
- “there exists an `R`-submodule `U ⊆ R^{\oplus n}`” is `∃ U : Submodule R (Fin n → R)`.
- “the restrictions are isomorphisms” is expressed by `Function.Bijective (α.domRestrict U)` and `Function.Bijective (β.domRestrict U)`, where `domRestrict` has domain the subtype `U` and codomain `(Fin m → R)`.
- “in particular, both kernel direct-sum decompositions hold” is rendered by `IsCompl (LinearMap.ker α) U ∧ IsCompl (LinearMap.ker β) U`.

The statement dependency is `def-weil-pbc-free-module`, recorded as Mathlib's `Module.Free` in `Mathlib.LinearAlgebra.FreeModule.Basic`; that declaration says an `R`-module has a basis. The present finite tuple modules are the standard finite free modules, so the module imports `Mathlib.LinearAlgebra.FreeModule.Basic` and uses its notion rather than introducing a duplicate definition. The other imports provide `LinearMap.domRestrict`, `Submodule`, `IsCompl`, and local-ring structures.

I checked the edge cases `m = 0` and `n = 0`: both are represented by `Fin 0 → R` without excluding them, and the empty finite bases are allowed. The statement does not assume `m ≤ n`, since that follows from surjectivity and is not an additional source hypothesis. No field or characteristic assumption is added; `IsLocalRing` includes the local-ring condition used by the source.

Searches for an existing declaration found no exact match. The node's recorded searches are: LeanFinder for “Over a commutative local ring two surjective linear maps between finite free modules ... common section submodule” (8 hits, no simultaneous complement); LeanSearch for “two surjections of finite free modules over a local ring admit a common direct summand” (8 hits, no match); LeanFinder for “Any two subspaces ... common complementary subspace” (8 hits, only individual complements); Loogle for `Submodule.IsCompl, Submodule.IsCompl` (0 hits); Loogle for `IsCompl, IsCompl` (12 generic complement hits); and grep searches for common-complement/simultaneous-complement patterns in Mathlib and `WeilConjectures` (hits only individual complement machinery). I also searched `WeilConjectures/` and `lean/Sheaf/` for the target identifier and for finite-free common-summand declarations; no exact declaration was found.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q36

I reread the node and the Lean file independently. The local-ring, natural-number, linear-map, and surjectivity hypotheses correspond one-for-one. The existential submodule is exactly the source's common summand. Each restriction is represented by `domRestrict` on the submodule subtype, and bijectivity gives the stated isomorphism. The two final `IsCompl` conjuncts encode exactly the two kernel direct-sum decompositions, with no extra hypotheses or conclusions. The use of `Fin n → R` and `Fin m → R` includes zero ranks and is the standard finite free tuple realization. No mismatch was found.
