## Worker report

The module `Sheaf.RingTheory.PolynomialModuleGoodLocusExtension` states
`MvPolynomial.polynomialModuleGoodLocus_inter_subset_of_exact`, with one `sorry` proof.
It reuses the landed definition `MvPolynomial.polynomialModuleGoodLocus`; no definition,
dependency module, or auxiliary theorem is introduced. The only node changes are `lean`
and adding the already landed `def-sfb-polynomial-module-good-locus` to `stmt_deps`, as
permitted by brief-stage2 §5 and STATE's STMT_DEPS MAY GAIN LANDED NODES rule.

Source read: `literature/stacks-project/algebra.tex`, equations
`equation-flat-and-finitely-presented` and `equation-good-locus`, and
`lemma-generic-flatness-locus-extension` (Tag 051W), including its proof. The source's
additional condition on the algebra itself is automatic for the polynomial algebra:
`R_f[x_1,...,x_n]` is finitely presented as an `R_f`-algebra and free as an `R_f`-module.
Thus the node's two module conditions give exactly this specialization. The theorem's
docstring follows all eight proof steps of the node.

Clause-by-clause rendering:

- Commutative base ring: `(R : Type u) [CommRing R]`, with no nontriviality,
  reducedness, or finiteness assumptions.
- Nonnegative integer `n`: `(n : ℕ)`, allowing zero. The ring `P` is exactly
  `MvPolynomial (Fin n) R`; indexing by `Fin n` relabels the variables `1,...,n`.
- Each of the three arbitrary `P`-modules: `(Mᵢ : Type vᵢ) [AddCommGroup Mᵢ]
  [Module (MvPolynomial (Fin n) R) Mᵢ]`. Their universes are independent of one
  another and of the base; all universes and binders are explicit.
- The given `P`-linear maps: `(u : M₁ →ₗ[MvPolynomial (Fin n) R] M₂)` and
  `(v : M₂ →ₗ[MvPolynomial (Fin n) R] M₃)`.
- Injectivity of `u`: `(hu : Function.Injective u)`.
- Surjectivity of `v`: `(hv : Function.Surjective v)`.
- Equality `im u = ker v`: `(h : Function.Exact u v)`, meaning for every `y`,
  `v y = 0 ↔ ∃ x, u x = y`. There is no additional zero-composite assumption.
- The good locus: each term is the existing `polynomialModuleGoodLocus R n Mᵢ`.
  Reading its complete definition, membership is `∃ f : R, f ∉ p.asIdeal ∧
  Module.Free R_f M_f ∧ Module.FinitePresentation P_f M_f`. This is the union
  of exactly the specified `D(f)` inside `PrimeSpectrum R`, the underlying space
  of `Spec (CommRingCat.of R)`.
- The localized ring is `Localization.Away f`. The localized module in that
  existing definition is `LocalizedModule ((Submonoid.powers f).map C) M`.
  Its fractions `m/C(f)^a` identify canonically with `m/f^a` in the underlying
  base-module localization: `C(f)^a • m = f^a • m`, so their fraction relations,
  addition, and base scalar actions agree. This also applies when `C` is not
  injective or the ring is zero.
- The polynomial action is the existing `localizedPolynomialModule`, constructed
  by `LocalizedModule.moduleOfIsLocalization` and `MvPolynomial.isLocalization`;
  `localizedPolynomialBaseModule` restricts along constants using `Module.compHom`.
  It sends `X i • (m/f^a)` to `(X i • m)/f^a`, as required. There is no arbitrary
  module structure or existentially chosen action.
- Freeness uses `Module.Free`, whose basis index can be infinite or empty;
  finite presentation is over `MvPolynomial (Fin n) (Localization.Away f)`,
  not over the base localization.
- Conclusion: `polynomialModuleGoodLocus R n M₁ ∩ polynomialModuleGoodLocus R n M₃ ⊆
  polynomialModuleGoodLocus R n M₂`. The intersection and inclusion are ordinary
  set operations, with no extra assertion of density, openness, or equality.

Dependency declarations read and used:

| Node | Module and declaration |
| --- | --- |
| def-weil-pbc-mv-polynomial-ring | `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`; universal-property evaluation read in `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval` |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`; underlying points `PrimeSpectrum R` |
| def-weil-pbc-free-module | `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, `Module.free_iff_set` |
| def-sc-finitely-presented-module | `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`, `Module.FinitePresentation.exists_fin'` |
| def-weil-ring-localization-away | `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`; ring structure supplied through the polynomial good-locus import |
| def-weil-pbc-module-localization-away | `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`, `IsLocalizedModule.lift` |
| def-sfb-polynomial-module-good-locus | `Sheaf.RingTheory.PolynomialModuleGoodLocus`: `MvPolynomial.polynomialModuleGoodLocus`, `MvPolynomial.localizedPolynomialModule`, `MvPolynomial.localizedPolynomialBaseModule` |

The six original dependency modules and the landed good-locus module are public
imports. For proof dependencies, `Module.finitePresentation_of_ker` and the localized
finite-presentation instance are supplied by the public finite-presentation module;
`IsLocalizedModule.map_exact` is available through the plain proof import
`Mathlib.Algebra.Module.LocalizedModule.Exact`. The proof-only imports are private.
The source signatures of these Mathlib proof inputs were also read.

Edge cases checked before writing: `n = 0` leaves constants only and is allowed by
`Fin 0`; the zero ring has empty prime spectrum so the inclusion holds vacuously;
`f = 0` and nilpotent denominators contribute no primes, since their principal opens
are empty; zero modules have empty bases and are finitely presented; infinite free
bases and modules not finite over the base are admitted; the general extension
argument splits over the localized base because the free quotient is projective,
while finite presentation is preserved over the localized polynomial ring. Nothing
requires the base to be reduced or the original modules to be finitely generated.

Searches actually run (all via the prescribed wrapper unless marked `rg`/`grep`):

- LeanFinder: “Short exact sequences of polynomial modules preserve the locus where
  localization is free over the base and finitely presented over the polynomial ring”.
  Eight hits, including `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`, `Module.basicOpen_subset_freeLocus_iff`, and
  `exact_of_isLocalized_span`. None states the combined good-locus inclusion.
- LeanSearch: “The good locus where a polynomial module is free over the base and
  finitely presented over the polynomial ring is preserved by extensions”. Eight hits,
  including the localization finite-presentation instance, `Module.freeLocus`, and
  `Algebra.TensorProduct.instFree`. None states this theorem.
- Loogle: `LocalizedModule.map, MvPolynomial.module, Module.FinitePresentation` returned
  zero hits and “unknown identifier 'MvPolynomial.module'”; this exploratory name was
  unavailable, not evidence that a module action is missing.
- Loogle: `ModuleCat.free_shortExact` returned its exact statement. It supplies the
  separate freeness extension input, not the combined localization-locus statement.
- Mathlib grep: `goodLocus|good_locus|genericFlatness|generic_flatness`: zero hits.
- `rg` across `lean/Sheaf` and `lean/WeilConjectures`:
  `goodLocus|good_locus|polynomialGood|polynomial_good|LocalizedModule.*MvPolynomial|MvPolynomial.*LocalizedModule`.
  Found the landed `Sheaf.RingTheory.PolynomialModuleGoodLocus` and its generic-freeness
  consumer, plus unrelated localization declarations; no extension theorem.
- `grep -rn 'lem-sfb-polynomial-good-locus-extension' lean/WeilConjectures`: no hits.
- `rg 'PolynomialModuleGoodLocus|polynomialModuleGoodLocus' dag/nodes lean/Sheaf`
  found the exact landed definition node and its module; both were read in full.
- Name collision search for `polynomialModuleGoodLocus_inter_subset_of_exact` in
  `lean/Sheaf`, `lean/WeilConjectures`, Mathlib, and `dag/lean_names_upstream.json`:
  no hits.

No statement correction, disputed statement, new node, or dependency repair is needed.
The prescribed `scompile.py` compiled the file in sandbox and library module modes
successfully (1.2 seconds each), with no errors or unexpected warnings.

## Second reading by Q97

This is the author's second reading; the maintainer supplies the independent review.
I reread the node, the complete good-locus definition and its two scalar-action helpers,
the Stacks equations and Tag 051W, and the delivered theorem. The base has precisely
`CommRing`, `n` is arbitrary, and the three modules have independently quantified
universes. The two linear maps are over the original polynomial ring. Each of the
three short-exactness clauses appears once as `Injective`, `Surjective`, and `Exact`.
Unfolding the reused locus gives the same existential principal-open witnesses,
arbitrary-basis freeness, and polynomial finite presentation as the node. The mapped
powers-of-constants localization has the same fraction equivalence relation as the
underlying base localization, with the required variable action. The conclusion is
precisely the displayed intersection inclusion. There is no hidden finite-rank,
reducedness, domain, or nonzero-ring restriction. The proof docstring follows the
node's eight steps, including both distinct scalar rings. No mismatch was found and
no mathematical statement was changed. Reusing the already landed definition required
adding its node id to `stmt_deps`; no new construction was necessary.
