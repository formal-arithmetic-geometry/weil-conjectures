## Worker report

Item: `lem-trf-polynomial-resolution-extension-trivial-kan`.
Module: `Sheaf.AlgebraicTopology.PolynomialResolutionExtension`.
Main declaration:
`AlgebraicTopology.PolynomialResolutionExtension.polynomial_resolution_extension_trivial_kan`.
Its proof is `sorry`, the only postponed proof in this delivery. The node's statement and dependency lists are unchanged.

The four helpers are concrete canonical-map constructions belonging to the statement:
`polynomialFunctor` uses `MvPolynomial.mapAlgHom`; `polynomialExtension` applies Mathlib's augmented whiskering; `additiveAugmentation` applies Mathlib's alternating augmentation and extends along `n ↦ -n`; `underlyingAugmentation` applies augmented whiskering with the forgetful functor. Their data contain no `sorry` and make no existential choice. They are listed in `lean.declarations`. They assemble existing notions and do not introduce a separate polynomial-ring, simplicial-object, complex, or fibration notion.

Hypothesis and clause correspondence:

- The commutative base ring is `{A : Type u} [CommRing A]`. The target ring `B` is `P.right : CommAlgCat.{v} A`; this includes its specified homomorphism from A. Bundling B in the augmentation is equivalent to separately binding B and its algebra structure, with no condition on the map A → B.
- The augmented simplicial commutative A-algebra is `P : SimplicialObject.Augmented (CommAlgCat.{v} A)`. Its left object is a genuine functor from `SimplexCategoryᵒᵖ`, and `P.hom` is a natural transformation to the constant target. All algebra maps preserve A and all operators commute with the augmentation.
- The arbitrary set is `(E : Type w)`. Its universe is independent of both A's `u` and the algebra carriers' `v`; the polynomial output uses `max v w`. There is no `Finite`, `Fintype`, or `Nonempty` binder.
- Degreewise surjectivity is exactly `h_surj : ∀ n : ℕ, Function.Surjective (P.hom.app (op ⦋n⦌))`, including n = 0.
- The assumed quasi-isomorphism is `h_qis : QuasiIso (additiveAugmentation P)`. This is the underlying additive map, which detects the same homology isomorphisms as underlying A-modules. The construction forgets multiplication, then uses `AlternatingFaceMapComplex.ε.app`, whose degree-zero component is the given augmentation and whose other components vanish, then `HomologicalComplex.extendMap ... ComplexShape.embeddingDownNat`. Thus source degree -n is P_n, with the unnormalized alternating-face differential and zero positive terms; the target is the extension of `ChainComplex.single₀` on B, precisely B[0]. No normalized-complex substitution is made.
- `polynomialExtension P E` is P[E] → const(B[E]): the functor's objects are `MvPolynomial E R`, and its morphisms are coefficient maps `MvPolynomial.mapAlgHom f.hom`. Mathlib's `map_X` says variables are fixed and `map_C` says coefficients follow f. `Augmented.whiskeringObj` supplies the canonical constant-composition identification; its components are identities, not extra arbitrary maps.
- The first conclusion is `∀ n : ℕ, Function.Surjective ((polynomialExtension P E).hom.app (op ⦋n⦌))`.
- The second conclusion is `QuasiIso (additiveAugmentation (polynomialExtension P E))`, using the same negative cochain indexing and augmentation as in the hypothesis.
- The last two conclusions are `SSet.Enhanced.trivialKanFibration (underlyingAugmentation P)` and its counterpart for `polynomialExtension P E`. The recorded definition is Mathlib's right lifting property against every boundary, including the empty boundary in degree zero. `underlyingAugmentation` uses the actual algebra-forgetful functor and canonical constant-target identification.
- No polynomial presentations of the P_n are supplied or assumed.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-object`: `Mathlib.AlgebraicTopology.SimplicialObject.Basic`, `CategoryTheory.SimplicialObject`, `.δ`, `.σ`; its `.Augmented` and `.Augmented.whiskeringObj` give the augmentation and functor transport.
- `def-weil-pbc-module-chain-complex-homology`: `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, `HomologicalComplex.homology`; imported through the derived-category/alternating-complex dependencies. The `QuasiIso` class quantifies over this homology in all degrees.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and `HasDerivedCategory`, with the actual quasi-isomorphism notion `QuasiIso` from `Mathlib.Algebra.Homology.QuasiIso`. The present statement only needs quasi-isomorphisms, so it imposes no derived-localization choice.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; evaluation and coefficient maps are in `Mathlib.Algebra.MvPolynomial.Eval`, publicly importing Basic. Read `MvPolynomial`, `mapAlgHom`, `map_id`, `map_map`, `map_X`, and `map_C`.
- `def-weil-pbc-trivial-kan-fibration`: `Sheaf.AlgebraicTopology.TrivialKanFibration`, `SSet.Enhanced.trivialKanFibration`; read its full definition as `SSet.modelCategoryQuillen.I.rlp`.
- The only extra proof dependency, `lem-trf-polynomial-augmentation-boundary`, has no Lean record or Mathlib match in the read clone. There is no module to import. Its general criterion is reproduced in the natural-language proof citation, not restated as another theorem or used as an additional hypothesis.

Source reading: opened `literature/stacks-project/cotangent.tex`, `remark-resolution` (Tag 08QI) and the complete `lemma-polynomial-on-top` proof (Tag 08QV), particularly its last paragraph; also `simplicial.tex`, `lemma-qis-simplicial-abelian-groups` (Tag 08P1), including the termwise-surjective kernel argument. The expanded finite-support argument in this node proves the stronger arbitrary-term assertion directly and is recorded step by step in the theorem docstring.

Edge cases checked before writing:

- E empty: the monomial basis has only the unit monomial, so the polynomial map is the original map under the canonical polynomial/constant-ring equivalence. No nonemptiness is assumed.
- E infinite: every individual polynomial has finite monomial support, allowing finitely many coefficient or primitive choices. There is no bound on support or variables in the statement.
- n = 0: surjectivity is explicitly included, and degree-zero augmentation-kernel boundaries provide injectivity on H⁰. The fibration alias includes the boundary of Δ[0].
- Zero rings: no `Nontrivial` instance is required. Polynomial coefficients and the underlying vertex lifting continue to make sense for singleton carriers.
- A constant augmented algebra with identity augmentation: the unnormalized complex has identity differentials in positive even chain degrees and zero in odd ones; its augmentation to degree zero is a quasi-isomorphism. Thus the hypothesis is consistent with constants, despite the unnormalized positive chain terms.
- Original terms need not be polynomial: their only supplied structure is `CommAlgCat A`, and the coefficient argument only uses the two explicit assumptions.
- Independent universes: u, v, w are explicitly declared and the polynomial functor raises the carrier universe to max v w. No equality of universes is assumed; `set_option autoImplicit false` is enabled.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A surjective augmented simplicial commutative ring quasi-isomorphism remains a trivial Kan fibration after adjoining polynomial variables"`: 8 hits, including classifying-space extra degeneracy and fibrant/cofibrant-object surjectivity results; none states this polynomial extension assertion.
- `msearch.py ... loogle '"MvPolynomial", "QuasiIso"'`: 0 hits.
- `msearch.py ... grep 'MvPolynomial.*(Trivial|Kan|QuasiIso)|[Pp]olynomial.*[Ss]implicial'`: 4 unrelated polynomial algebra hits, no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for polynomial/simplicial combinations and the proposed helper names; `rg` for this item's exact id in `lean/WeilConjectures`: no existing statement. Read related `FinitePolynomialSimplicialResolution`, `CotangentResolutionCoherence`, `SimplicialAlgebraShuffleNormalization`, and the upstream `Mathlib.Algebra.Category.Ring.Constructions` module. These respectively concern existence of finite resolutions, coherence/cotangent constructions, shuffle quotient normalization, and single-variable ring functors. None gives this theorem; the existing generic augmented-whiskering and alternating-augmentation APIs are reused directly.

No statement fault or disputed assertion was found. No new nodes, dependency repairs, or statement correction are needed.

## Second reading by Q16

Worker rereading of the finished node and module: all four conclusion clauses are present in the order of the node; h_surj covers zero and h_qis targets B[0], not the unnormalized constant complex. The polynomial functor preserves the actual variables and maps actual coefficients. The target's A-map is contained in `P.right`, not omitted. The statement keeps all three universes independent and has no polynomiality or finiteness assumptions. The original statement and dependency lists are unchanged. Compiler corrections concern only explicit functor-law proofs and the additive-category import.

This is a worker self-check. The dispatcher explicitly prohibits starting other agents; the maintainer's independent delivery review remains the independent reading, as stated in the task brief.

## Validation

Every compiler invocation uses the prescribed `scompile.py` wrapper against the live published build; no local or global build is used. Initial diagnostics repaired the functor-law extensionality and explicitly imported the additive abelian-category instances. Final `scompile.py` passed both the sandbox and named-library checks (1.6 s and 1.8 s), with no diagnostics. `deliver2.py --no-push` printed OK: preflight and per-file compilation pass (dry-run commit `7c41952ec08`). Local record verification confirms only the `lean` key changed, every Lean line is at most 100 characters, and the sole `sorry` is the main theorem.
