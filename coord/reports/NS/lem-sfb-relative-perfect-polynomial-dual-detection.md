## Worker report

The module `Sheaf.RingTheory.RelativePerfectPolynomialDualDetection` states
`ModuleCat.relativePerfect_polynomialDual_detection`. Its only postponed theorem has
proof `sorry`. The node statement is unchanged, and only its `lean` field is set.
There are no new nodes, dependency repairs, auxiliary definitions, or statement corrections.

The theorem is a conjunction of zero detection and morphism detection. Every object and
operation is in the ordinary unbounded module derived categories from the dependencies.
The polynomial coefficient is expanded in the statement, avoiding another definition of it.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary commutative rings and map R → A | `{R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)` |
| Flat | `hflat : RingHom.Flat φ` |
| Finitely presented | `hfp : RingHom.FinitePresentation φ`, exactly `Algebra.FinitePresentation` for `φ.toAlgebra` |
| Chosen presentation with n ≥ 0 | `(n : ℕ) (p : MvPolynomial (Fin n) R →+* A)` |
| Surjection of R-algebras | `hp : Function.Surjective p` and `hcomp : p.comp MvPolynomial.C = φ` |
| P[0] | `(DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj (of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))` |
| Coinduced A-action on C | `derivedCoinduction p` applied to that object; its definition derives `coextendScalars p`, with `(a • h)(a') = h(a' * a)` |
| Shift by n | The entire coinduced object is shifted by `⟦(n : ℤ)⟧` |
| Z, X, Y are R-perfect | For each object T separately, `DerivedCategory.IsPseudoCoherent T` and the displayed existential Tor interval |
| One interval valid for every R-module | `∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ), ...` |
| Vanishing outside the interval | `i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor ... i).obj ...)` |
| Derived tensor over R | Restrict T by `(restrictScalars φ).mapDerivedCategory`, then use the existing derived `⊗` with `Q[0]` in D(R) |
| RHom_A(C,Z) = 0 implies Z = 0 | The first conjunct uses `ordinaryModuleDerivedInternalHom A` at `(op C, Z)`, followed by `IsZero Z` |
| Every morphism X → Y | The second conjunct quantifies `(X Y : DerivedCategory (ModuleCat.{u} A)) (f : X ⟶ Y)` |
| RHom_A(C,f) invertible implies f invertible | `IsIso` of the map of the curried recorded Hom bifunctor at `op C`, followed by `IsIso f` |
| No diagonal dualizing, Noetherian or nonzero assumptions | No such binders occur. The two perfection hypotheses are retained even though the proof gives stronger zero detection. |

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, the `Module.Flat` condition
  under the algebra structure of the ring map.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` and its ring-map
  wrapper `RingHom.FinitePresentation`; no choice of algebra structure is omitted.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and its structure map `MvPolynomial.C`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  and the localization; `singleFunctor` is the shared degree-zero derived embedding.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the abbreviation for the established
  K-injective-derived closed internal-Hom bifunctor. Currying changes its presentation only.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`; I read its definition and the ordinary complex action,
  evaluation, K-injective comparison and adjunction in the same module.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, a bounded-above finite-free representative.

All recorded proof-dependency modules are imported without `public` unless already public
statement imports, including the Mathlib matches for flat and Noetherian localization,
projectives, exact Hom sequences and zero cones. Four proof dependencies have no recorded
Lean module yet and therefore no import is currently possible:
`lem-sfb-flat-fp-presentation-noetherian-model`,
`lem-sfb-arbitrary-polynomial-dual-properties`,
`lem-trf-flat-coherent-homothety-base-change`, and
`lem-sfb-noetherian-full-support-localizing-generation`.
These are proof-only prerequisites, not missing notions needed for the statement.
The docstring records all eight proof steps with their cited nodes, including the stronger
arbitrary-object detection used for the cone. No proof is supplied in stage 2.

Source reading: Stacks `dualizing.tex`, `lemma-dualizing` (0A7C) and
`lemma-relative-dualizing-algebraic` (0BZW), and `algebra.tex`,
`lemma-flat-finite-presentation-limit-flat` (02JO). I also read the latest blueprint
`sk-thm-sf-ctf-stability-direct-images` statement and proof. The agent node explicitly
warns that arbitrary-base detection is not the statement of 0A7C, and the module preserves
that warning and its accepted Noetherian-model/localizing-generation argument.

Edge cases checked before writing:

- `n = 0`: `Fin 0` is empty; the polynomial ring and degree-zero shift remain valid,
  and surjectivity/compatibility impose exactly the chosen zero-variable presentation.
- `A = 0`: the module category has only zero objects, so both conclusions apply;
  no `Nontrivial` or prime-spectrum witness is required. A zero base forces a zero algebra.
- Zero objects and zero morphisms are included; an isomorphism is required only on the
  specified image map. Identity maps and the identity polynomial presentation are included.
- Each Tor interval belongs to its own object; the statement does not require a common
  interval for X and Y. `a = b` is allowed and `a ≤ b` rules out an unintended empty interval.
- Arbitrary unbounded objects are available in the category; relative perfection is the
  exact pair of hypotheses, not an absolute perfectness or finite A-Tor assumption.
- `R` and `A` and their modules use the shared ordinary-module universe `u`, with the
  canonical existing small-Hom derived category used by the recorded Hom interface.
  The test-module universe contains R itself, so testing is not vacuous. All variables
  and universes are explicitly bound; `autoImplicit` is disabled.

Searches for an existing declaration (no exact match found):

- `msearch.py leanfinder`: “Derived Hom from a polynomial relative dualizing complex
  detects zero objects and isomorphisms of relatively perfect complexes”; eight hits,
  headed by `Ext`, `CategoryTheory.hasExt_of_hasDerivedCategory`,
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`, and K-projective
  comparison/truncation lemmas. None states this polynomial-duality assertion.
- `msearch.py loogle`: `"DerivedCategory", "IsZero"`; four t-structure support lemmas
  (`isZero_of_isGE`, `isZero_of_isLE`, and their Plus versions), no match.
- `msearch.py grep`: `polynomial.*dual|relative.*perfect` in `Algebra/Homology`;
  zero Mathlib hits.
- `msearch.py leansearch`: “Derived Hom from a polynomial relative dualizing complex
  detects zero relatively perfect complexes over an arbitrary flat finitely presented
  algebra”; results recorded by the search wrapper in the sandbox search log.
- `rg` on project `lean/Sheaf` and upstream `lean/WeilConjectures` for relative perfection,
  polynomial duals, and detection, and the prescribed blueprint-ID search in upstream.
  The upstream ID search has no hit. The project consumer
  `ArbitraryRingRelativeDualizingIsomorphism` cites this node only in its proof docstring;
  its theorem is uniqueness of supplied diagonal-dualizing objects, not this assertion.
  The polynomial presentation-data and shriek modules define different coefficients
  or provide properties, not the requested detection theorem. No duplicate of the new name.

Validation: `scompile.py NS lem-sfb-relative-perfect-polynomial-dual-detection` compiles the
single delivered file in sandbox and library mode with no errors or warnings. The first
probe exposed product-category endpoint inference on the bifunctor map; expressing that
same map by currying fixed the inference without changing the mathematical statement.
The final statement uses no diagnostic commands and all lines are at most 100 characters.
There is no statement dispute.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
