## Worker report

The module `Sheaf.AlgebraicGeometry.ExcellentQuasiprojectiveNormalizedBlowup` states
`AlgebraicGeometry.excellent_quasiprojective_normalizedBlowup`, with `sorry` as its entire
proof. It introduces no definition, axiom, helper theorem, or replacement construction.
The module docstring and declaration docstring identify the source. The declaration
contains all ten DAG proof steps, with their dependency names, for stage 3.

Hypothesis-by-hypothesis correspondence:

- The excellent Noetherian commutative ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] (hA : IsExcellent A)`. The node explicitly includes Noetherianity,
  although the existing excellent predicate also implies it.
- The affine base is literally `Spec (.of A)` throughout.
- The integral scheme is `(X : Scheme.{u}) [IsIntegral X]`; this includes nonemptiness.
- The specified base morphism is `f : X ⟶ Spec (.of A)`. Its finite-type hypothesis is
  `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded finite-type convention.
- The locally closed embedding hypothesis is `hX : ∃ (m : ℕ) (i : X ⟶
  ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A))), IsImmersion i ∧ i ≫ … = f`.
  The equality makes the immersion an embedding over the specified base. Mathlib's
  `IsImmersion` means a locally closed immersion, as its full signature and docstring state.
  The coordinate type has exactly `m + 1` elements. `ULift` puts it in the scheme universe;
  it imposes no extra size restriction on schemes or on the base ring.
- The quasi-coherent ideal subsheaf is `J : X.IdealSheafData`. The actual associated
  module is the canonical `J.toModules`, the kernel of the structural quotient map.
- Nonzero means `(hJ₀ : J ≠ ⊥)`, not the existence of a nonzero global section.
- The finite-type quasi-coherent condition is
  `(hJ : J.toModules.IsQuasiCoherentFiniteType)`. This uses the recorded declaration for
  `pqf-def-coherent`, whose body is exactly quasi-coherence AND finite type. It does not
  replace finite type by finite presentation.

Object and conclusion correspondence:

- The ordinary blowup and its map are the existing `J.blowup` and `J.blowupMap` in
  `WeilConjectures.Blowup.Gluing`. The source glues affine Rees-Proj blowups. On an
  integral affine chart, the degree-zero localization at `at` is `R[J/a]` inside
  `Frac R` for `a ≠ 0`: send `b t^n/(at)^n` to `b/a^n`. This is the ordinary blowup
  described in the node, not a log blowup or a different center.
- The initial conclusion `∃ hZ : IsIntegral J.blowup, …` asserts that the actual ordinary
  blowup is integral. It does not assume that fact. An existential proof witness is needed
  because the recorded function-field normalization takes that instance as an argument.
- The scheme `N` is literally `@Scheme.normalization J.blowup hZ`, and its morphism `ν`
  is literally `@Scheme.fromNormalization J.blowup hZ`. These are the recorded
  normalization in the function field, not the relative normalization of `p` or a chosen
  normal scheme. The witness is a proposition, so proof irrelevance removes any ambiguity.
- `IsNoetherian J.blowup`, `IsIntegral (@Scheme.normalization J.blowup hZ)` and
  `IsNoetherian (@Scheme.normalization J.blowup hZ)` give all remaining integral and
  Noetherian clauses. Mathlib's `IsNoetherian` extends exactly `IsLocallyNoetherian` and
  `CompactSpace`, so both local Noetherianity and quasi-compactness are present.
- `LocallyOfFiniteType (J.blowupMap ≫ f)` AND `QuasiCompact (J.blowupMap ≫ f)` say that
  `Z` is finite type over `S`. The same two predicates on
  `@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap ≫ f` say that `N` is finite type.
- Two separate existential clauses supply a natural projective dimension, an immersion
  from the actual `Z` or actual `N` into `ℙ(ULift (Fin (m+1)); Spec A)`, and its equality
  over `S` with the specified structural composite. These are the two required finite
  projective-space locally closed embeddings; they need not use the same dimension.
- `IsFinite (@Scheme.fromNormalization J.blowup hZ)` is the required finiteness of `ν`.
- `IsHProjective (@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap)` uses the recorded
  global finite-projective-space convention. Its existing definition factors through a
  closed immersion into projective space with finitely many coordinates, not merely a
  projective bundle or a locally projective morphism.
- The final clause provides `U : X.Opens`, density of `U` in `X`, density of its full
  inverse image in `N`, and `IsIso ((ν ≫ p) ∣_ U)`. Thus the actual composite identifies
  dense open subschemes. These are the inverse-image dense opens constructed by Step 10
  of the node proof. No bare assertion that `X` and `N` happen to be birational is used.

Dependency declarations read and used:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (and its canonical contravariant map).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `def-sc-normalization`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `AlgebraicGeometry.Scheme.normalization` and `Scheme.fromNormalization`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; the same module's `IsNoetherian` bundles
  this with compactness exactly as the item asks.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`. The live source was read with `scompile.py --source`;
  the older local source checkout lacks this module.
- The two existing definition nodes `def-nagata-global-blowup` and
  `def-nagata-projective-space-base-change` are added to `stmt_deps` to register the
  already defined objects actually used: `Scheme.IdealSheafData.blowup` from
  `WeilConjectures.Blowup.Gluing` and `ProjectiveSpace` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. No new node or dependency repair
  is needed. Both were read, including their definitions and module docstrings.
- The ideal-module bridge `Scheme.IdealSheafData.toModules` and its canonical inclusion
  come from `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`; its source and
  affine sections identification were read locally and through the live source wrapper.

The stated proof dependencies are imported without `public` when they are not already
needed publicly by the signature. This includes the Rees module identified by the closed
upstream audit of `def-nagata-sheaf-rees-algebra`, the relative Proj functoriality module,
projective-bundle properness and conversion, finite projective bundles, H-projective
composition, Segre, the affine scalar-extension comparison, quasi-coherent symmetric
algebras, ample twists, excellence on affine covers, and normalization preparation.
`lem-trf-ample-restrict-closed-immersion` has no Lean record or Mathlib match, so there is
no module to import for that proof-only dependency; it is not needed to type the statement.

Edge cases checked before writing:

- `J = ⊤` is allowed: the ordinary blowup is `X`, while its normalization need not be `X`.
  The conclusion does not incorrectly assert that normalizing a nonnormal `X` is trivial.
- `J = ⊥` is excluded: its blowup can be empty, so integral/nonempty would fail.
- Empty `X` is excluded precisely by the node's integrality convention. A zero base ring
  admits no such nonempty integral scheme; the theorem then has no instance of its data.
- A nonreduced excellent base ring is permitted. No domain, reducedness, characteristic,
  field, or finite-dimensionality hypothesis on `A` was introduced.
- `m = 0` is represented by the one-coordinate projective space, not by an empty set of
  coordinates. All output dimensions may also be zero.
- Nonzero ideal subsheaves need not have nonzero global sections, which is why `J ≠ ⊥`
  is used. In particular the hypothesis makes sense for projective schemes.
- All normalization occurrences explicitly use the existential integrality witness;
  integrality of the blowup is not silently turned into an additional assumption.

Searches made for existing declarations (2026-10-18 UTC):

- `msearch.py ... leanfinder`: “The normalization of a blowup of an integral quasi
  projective scheme of finite type over an excellent affine base is finite and projective”.
  Eight hits, all on Mathlib's relative normalization and its properties; none states this
  blowup theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsIntegral`.
  Zero hits; the service does not know the project's `IsHProjective`.
- `msearch.py ... grep`: `blowup|Blowup|IsHProjective` in Mathlib `AlgebraicGeometry`.
  Zero hits.
- `msearch.py ... leansearch`: “normalized blowups preserve quasi projectivity over an
  excellent affine base”. Eight hits on relative normalization; no theorem matching this
  statement.
- `rg` in upstream `WeilConjectures`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and normalized-blowup/integrality names:
  no exact existing statement. Related results are `normalizedBlowup_calculus` over
  rational schemes, and the log-blowup normalization comparison. Their sources were read;
  neither has this theorem's excellent affine base or projective-space conclusions.
- DAG lookup located the existing global-blowup and projective-space definition nodes;
  their recorded declarations are reused. No duplicate definition was written.

Source verification: read Stacks divisors.tex, labels `lemma-blow-up-integral-scheme`
(Tag 02ND) and `lemma-blowing-up-projective` (02NS), and morphisms.tex,
`lemma-nagata-normalization` (035S) and
`lemma-projective-over-quasi-projective-is-H-projective` (087S). These agree with the
node's ordinary normalized-blowup consequence and its specified proof route.
No statement correction or STATEMENT-DISPUTED fault is needed.

Validation: `scompile.py Q89 lem-per-excellent-quasiprojective-normalized-blowup` on the
single delivered module passed the sandbox and library checks without errors or warnings
(2.6 seconds and 2.5 seconds respectively). Only the named main theorem is postponed.
The worker delivers directly; the maintainer supplies the independent review.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
