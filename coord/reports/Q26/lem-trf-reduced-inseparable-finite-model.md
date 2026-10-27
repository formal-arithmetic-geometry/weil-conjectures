## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedInseparableFiniteModel` states
`AlgebraicGeometry.reduced_inseparable_finite_model`, with its sole proof `sorry`.
No new definitions or additional postponed theorems are introduced. The node's
statement and accepted seven-step proof are unchanged. The docstring carries all
seven steps, including the cartesian-square argument for finiteness of the factor.

Source read: `literature/stacks-project/varieties.tex`, label
`lemma-normalization-and-change-of-fields`, Tag 0C3N, including its affine proof.
The supplied-finite-model variant is the agent-origin variant explicitly recorded
by the node, rather than the literal normalization comparison in that Stacks lemma.
The reduction and reduced-source factorization declarations used by that proof were
also opened, together with the current base-change conventions. No source or node
fault was found.

For the correspondence below put `π = Spec.map (CommRingCat.ofHom (algebraMap k K))`,
`X = W.nilradical.subscheme`, `iX = W.nilradical.subschemeι`,
`Y = pullback ((f ≫ iX) ≫ σ) π`, `WK = pullback σ π`,
`XK = pullback (iX ≫ σ) π`, `Z = WK.nilradical.subscheme`,
`iZ = WK.nilradical.subschemeι`, and `T = XK.nilradical.subscheme`.
These are explanatory abbreviations only: the Lean signature expands every one.

Hypotheses, in the order of the node:

- The field and field extension are `(k K : Type u) [Field k] [Field K]
  [Algebra k K]`. The specified finite purely inseparable extension is
  `[Module.Finite k K] [IsPurelyInseparable k K]`. No characteristic restriction is added.
- The finite-type k-scheme is `(W : Scheme.{u}) (σ : W ⟶ Spec (CommRingCat.of k))`
  with `[LocallyOfFiniteType σ] [QuasiCompact σ]`. An explicit structure morphism
  is equivalent to supplying a scheme over k, with no extra scalar action on W.
- X is exactly the nilradical subscheme, and its integrality is the binder
  `[IsIntegral W.nilradical.subscheme]`.
- The supplied integral scheme is `(N : Scheme.{u}) [IsIntegral N]`.
  The finite surjective map is `(f : N ⟶ W.nilradical.subscheme)
  [IsFinite f] [Surjective f]`. Its k-structure is the composite `(f ≫ iX) ≫ σ`.
- The dense open is `(U : W.nilradical.subscheme.Opens)` and
  `hU : Dense (U : Set W.nilradical.subscheme)`. The map on its inverse image
  is the canonical restriction: `hfU : IsIso (f ∣_ U)`.
- Y and Z are the specified base change and reduction, expanded in every occurrence.
  `hnormal : ∀ y : ↥Y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)` gives exactly the assumption on every
  local ring of Y. The point-type coercion `↥` keeps categorical pullbacks in Scheme.

Conclusions, clause by clause:

- `IsNormalScheme Y` is the existing definition
  `IsIntegral Y ∧ ∀ y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)`. Thus it gives both the integrality
  and normality of Y, without silently assuming integrality in the hypothesis.
  `IsIntegral Z` is the separate assertion about Z.
- `∃ p : Y ⟶ Z` is accompanied by both equations
  `p ≫ iZ ≫ pullback.fst σ π = pullback.fst ((f ≫ iX) ≫ σ) π ≫ f ≫ iX`
  and `p ≫ iZ ≫ pullback.snd σ π = pullback.snd ((f ≫ iX) ≫ σ) π`.
  By the pullback universal property these say precisely that `p ≫ iZ` is the
  base-changed composite induced by f. Writing both projections avoids needing
  an auxiliary chosen lift or proof argument in the signature.
- The following `∀ p' ... → ... → p' = p` uses the same two equations and
  asserts uniqueness among ALL factorizations of that map, independently of
  finiteness or any further property. Then `IsFinite p ∧ Surjective p` gives
  the two properties required of the factor.
- `∃ q : Z ⟶ X` has the equation `q ≫ iX = iZ ≫ pullback.fst σ π`, so it is
  the map induced by projection to W, rather than an unconstrained homeomorphism.
  `IsHomeomorph q.base` is the assertion about its underlying map.
- The open V is exactly `q ⁻¹ᵁ U`. The two `Dense` conjuncts concern V in Z
  and `p ⁻¹ᵁ (q ⁻¹ᵁ U)` in Y, respectively. The next conjunct is
  `IsIso (p ∣_ (q ⁻¹ᵁ U))`, the actual restriction of p to that inverse image.
- `∃ e : T ≅ Z` has two equations after `iZ` and the projections of WK.
  Their right sides are respectively `T → XK → X → W` and `T → XK → Spec K`.
  Hence `e.hom ≫ iZ` is exactly the composite of the reduction immersion
  `T → XK` and the canonical base change of `iX`. This is the asserted
  identification induced by the canonical closed immersion `XK → WK`.
  Equality after both pullback projections is equivalent to equality over WK;
  these are characterization equations, not additional mathematical assumptions.
- The open `U ×_k K` of XK is represented by
  `UK = pullback.fst (iX ≫ σ) π ⁻¹ᵁ U`. The conjunct `IsReduced UK.toScheme`
  asserts its reducedness. The final `∃ eU : UK.toScheme ≅ (q ⁻¹ᵁ U).toScheme`
  is accompanied by the two projection equations to W and Spec K. These
  express exactly that the isomorphism is over WK. Since `V → Z → WK` is a
  monomorphism, this also determines the isomorphism canonically; there is no
  arbitrary unidentified isomorphism. The same cancellation determines e.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with its `algebraMap`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the node's
  scheme-base-change convention is `Limits.pullback`, with `pullback.fst`
  and `pullback.snd`; its `moduleBaseChange` declaration concerns modules and
  is not incorrectly substituted for scheme base change.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  the normal-ring dependency is used as the specified domain plus integrally
  closed condition, directly on the actual scheme stalks.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`: `IsNormalScheme`.
  Its owning, already landed definition node `def-sbc-normal-dominant-galois`
  was added to stmt_deps as authorized by brief-stage2 §5, solely to reuse the
  existing notion in the combined integral-and-normal conclusion. No copied
  definition and no dependency repair are needed.
- `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict` (notation `∣_`),
  `Scheme.Opens.toScheme`, and `Scheme.Opens.ι` represent actual open subschemes.

All stated proof dependencies are imported, using ordinary imports for the
proof-only modules: `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
(`isHomeomorph_baseChange_of_isPurelyInseparable`),
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`
(`reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`IsClosedImmersion.existsUnique_fac_of_range_subset_range`), and the Mathlib
closed-immersion, universally-injective, finite and pullback-carrier modules for
base-change and composition instances. No dependency import was omitted for a cycle.

Edge cases checked mathematically before writing:

- K = k and characteristic zero are included, with the identity field extension.
- Nonreduced W is retained: the map is to `(W_K)_red`, never an implicit
  replacement of W by X. For W = Spec(k[ε]/ε²), N = X = Spec k, the comparison
  reduces to the expected reduction identity after every allowed field extension.
- A zero-dimensional X = N = Spec k with U = X gives the expected field-base-change
  identity. U = X in general is allowed and imposes no artificial proper-open condition.
- Empty X and empty N are excluded by the node's own integrality assumptions.
  An empty U cannot be dense in integral X; no extra nonempty binder was added.
- The positive-characteristic example k = F_p(t), K = k(t^(1/p)) confirms why
  normality of N_K is a real hypothesis: with N = X = Spec K over k the tensor
  K ⊗_k K has nilpotents, and the stalk-domain assumption fails.
- No separatedness, dimension, smoothness, normality of X, or geometric
  normality of N was added. Universes are explicit (`universe u`, all fields
  and schemes in u), with no smaller independently quantified test universe.

Searches actually run for an existing statement:

- `msearch.py ... leanfinder "finite normal models over reduced purely inseparable
  field base changes with dense open isomorphism"`: eight hits, including the
  uniqueness of purely inseparable algebra maps and prime-spectrum homeomorphisms;
  no finite-model comparison or dense-open theorem matching this statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsIntegral"`:
  OK, zero hits.
- `msearch.py ... grep "normal.*purely|purely.*normal|reduc.*base.?change"
  AlgebraicGeometry`: OK, zero hits.
- `msearch.py ... leansearch "finite normal model over reduction of purely
  inseparable field base change is an isomorphism over a dense open"`: eight hits,
  including `IsPurelyInseparable.normal` and
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`; neither states this node.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `reduced.*inseparable|inseparable.*reduced|normal.*purely|purely.*normal|reducedInseparableFinite`
  found neighboring geometric-reducedness and normalization results but no exact
  theorem. The exact-id grep in `lean/WeilConjectures` found no declaration.
- Searching declaration definitions for normal schemes found the existing
  `IsNormalScheme` in `WeilConjectures.AlgebraicGeometry.NormalScheme`; its full
  definition and owning node were read and reused. The parent
  `NormalizationInseparableBaseChange` was also opened; its normalized-model
  theorem has different hypotheses and conclusion and cannot replace this item.

Validation: `scompile.py Q26 lem-trf-reduced-inseparable-finite-model` compiled
both the sandbox module and the named library module cleanly. An initial type
inference ambiguity treated bare pullbacks in type positions as categorical
pullbacks of types; explicit `↥` coercions on the quantified point and the
point-set annotation repaired it. There are no diagnostic commands in the delivery,
no auto-bound implicits (`set_option autoImplicit false`), and no proved theorem.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
