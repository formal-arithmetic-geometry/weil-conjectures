## Worker report

The delivery states `lem-sfb-trait-absolute-normalization-local-sections` in
`Sheaf.AlgebraicGeometry.TraitAbsoluteNormalizationLocalSections`. The helper
`AlgebraicGeometry.traitAbsoluteNormalizationMap` is the actual `Spec.map` of
`algebraMap R (integralClosure R Ω)`; it has real data. The single theorem
`AlgebraicGeometry.trait_absolute_normalization_local_sections` has proof `sorry`.
The item statement, dependencies, and proof are unchanged. No new nodes or dependency
repairs are needed.

Hypotheses and clauses, in order:

- The DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. This is the precise recorded DVR notion, which excludes
  fields and the zero ring, and supplies the local PID structure.
- Its fraction field is `(K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]`.
- Its chosen algebraic closure is `(Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]`. The structural `[Algebra R Ω] [IsScalarTower R K Ω]`
  expresses the given composite embedding; it is compatibility data, not a new
  algebraic restriction.
- The uniformizer is `(π : R)` with
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`, exactly the definition in
  `def-sc-discrete-valuation-ring`. For a DVR this implies `π ≠ 0` and is equivalent
  to Mathlib's `Irreducible π` by `irreducible_iff_uniformizer`.
- `B` is literally `integralClosure R Ω`, the existing Mathlib subalgebra of `Ω`.
  `S` and `T` are literally `Spec (CommRingCat.of R)` and
  `Spec (CommRingCat.of (integralClosure R Ω))`. The helper is their canonical map.
- Flatness, surjectivity, and quasi-compactness are the first three conjuncts
  `Flat`, `Surjective`, and `QuasiCompact` of that map, using the standard scheme
  morphism classes. The fourth is `Presieve.singleton ... ∈ Scheme.fpqcPrecoverage S`,
  the recorded definition of the singleton fpqc covering.
- The generic open is `PrimeSpectrum.basicOpen (algebraMap R B π)`. Its identification
  with `Spec Ω` is an actual scheme isomorphism `e`, whose composite with the open
  inclusion equals `Spec.map (CommRingCat.ofHom (integralClosure R Ω).val.toRingHom)`.
  Thus the identification is the one induced by the actual inclusion `B ⊆ Ω`.
- The next conjunct says, for every `t`, membership in that basic open is equivalent
  to the image prime being `⊥`. For a domain this is the generic point, so this is
  exactly the full generic inverse image, not merely an isomorphic open somewhere.
- For every point outside the basic open, the next conjunct gives all three claims:
  its image ideal is `IsLocalRing.maximalIdeal R`, `IsClosed {t}` in `T`, and
  `IsAlgClosed (T.residueField t)`. These use the scheme residue field as recorded,
  not a substituted quotient or a separably closed field.
- The final conjunct quantifies over every `Y : Scheme.{u}` and `f : Y ⟶ S`, with
  exactly `Flat f` and `LocallyOfFiniteType f`. The chosen `Y_T` is the recorded
  `pullback f (traitAbsoluteNormalizationMap R Ω)`.
- The point `t` is arbitrary subject to its image ideal being the maximal ideal of
  `R`. The prescribed `y : Spec (T.residueField t) ⟶ Y_T` is over `T` precisely
  when its composite with `pullback.snd` is `T.fromSpecResidueField t`; this is the
  antecedent of the local-section assertion. This is the usual meaning of a
  `κ(t)`-point of the `t`-fibre viewed as a `T`-morphism into `Y_T`.
- The conclusion gives `W : T.Opens`, `t ∈ W`, and `σ : W.toScheme ⟶ Y_T` with
  `σ ≫ pullback.snd ... = W.ι`, the required `T`-morphism. It also gives a map
  `τ : Spec κ(t) ⟶ W.toScheme` satisfying `τ ≫ W.ι = T.fromSpecResidueField t`.
  This map is uniquely determined because the open immersion is a monomorphism;
  its existence is precisely the canonical factorization through the open
  neighbourhood. The equality `τ ≫ σ = y` states the restriction to the prescribed
  residue-field morphism, including all field-map data.
- There is no Noetherian instance on `B`, no quasi-compactness hypothesis on `Y`,
  and no separatedness, smoothness, reducedness, or characteristic restriction.
  All schemes and rings live in the arbitrary ambient universe `u`, as required
  for maps and pullbacks in `Scheme.{u}`; no lower independent test universe is used.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` (DVR and uniformizer).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` and `IsAlgClosed` (chosen
  algebraic closure and algebraically closed residue fields).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` (the actual
  integral-closure subalgebra; its existing `.val` is used for the generic map).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (exposed by the fpqc import).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (through fpqc).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.snd`, with `HasPullbacks Scheme` from the scheme imports.
- For the open scheme and its inclusion, `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict` are used directly.

Proof imports retain all stated proof prerequisites. Their sources read include
`WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations`
(`gabber_quotient_localizations`),
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`
(`Scheme.Hom.IsQuasiFiniteAtPoint`),
`WeilConjectures.RingTheory.FlatLocalizedModuleBaseChange`
(`Module.Flat.localizedModule_of_isPushout`),
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(`exists_algHom_ker_eq_of_isMaximal`), and
`Sheaf.TraceFormula.FiniteResiduePointClosedInFibre`
(`Scheme.Hom.isClosed_singleton_asFiber_of_finiteDimensional`). The remaining
Mathlib proof imports provide the recorded finite/integral affine dictionary,
function field, finite presentation, torsion-free flatness, going down, integral
residue extension, and fraction-field/localization results.
At the time of writing, `lem-sfb-quasi-section-nearby-open`,
`lem-trf-quasi-finite-henselian-tensor-factor`, and
`lem-sfb-finite-normal-generic-section-extension` have no recorded Lean modules;
these are proof-only nodes, so no fabricated imports or new statements are added.
The docstring reproduces all ten proof steps and identifies these prerequisites.

Edge cases checked before writing:

- A field or zero ring is not a DVR, so neither introduces a spurious generic or
  closed-point case. A uniformizer cannot be zero or a unit under the stated
  maximal-ideal equality.
- `Y` may be empty or have empty closed fibre: then there is no `y` over a closed
  `t`, so the local assertion has no instance to satisfy. No surjectivity of `Y → S`
  is assumed.
- `Y` may be a disjoint union of arbitrarily many affine charts; the assertion is
  local at the image of `y` and never adds quasi-compactness. Nonreduced and
  inseparable examples remain included.
- For a ramified flat algebra such as `R[X]/(X^2-π)`, the algebraic closure and
  integral closure supply roots; no étale or smooth assumption was accidentally
  inserted.
- For `Y=S` the pullback projection is an isomorphism and the assertion gives the
  expected section. Changing the residue-field embedding of a prescribed point
  changes `y`, and the final equality still requires that exact morphism.
- The generic point is in the identified open and is not incorrectly required to
  be closed. All other points are explicitly quantified, even when `B` has many
  maximal ideals.
- Zero generator sets in denominator spreading use the product `1`; the proof
  docstring records this. No noetherianization of `B` is implicit in the statement.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "Integral closure of a discrete valuation ring in an
  algebraic closure gives Zariski local sections of flat locally finite type
  schemes through prescribed closed fibre points". Eight hits, including
  `Scheme.Hom.normalizationDiagram`, `Algebra.ZariskisMainProperty` and valuative
  criterion declarations; none gives the node's statement.
- `msearch.py ... loogle`: `"integralClosure", "Flat"`. One hit,
  `TensorProduct.toIntegralClosure_injective_of_flat`, not this result.
- `msearch.py ... leansearch`: "A flat locally finite type scheme has Zariski local
  sections over the integral closure of a discrete valuation ring in an algebraic
  closure". Eight hits on affine flatness, locally finite type, and closed-point
  criteria, none on the claimed sections.
- `msearch.py ... grep` in Mathlib `AlgebraicGeometry`:
  `quasi.?section|absoluteIntegralClosure|integralClosure.*[Ss]ection|[Ss]ection.*integralClosure`.
  No hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `absoluteNormalization|absolute_normalization|trait.*[Ss]ection` and the exact
  node id. Trait divisor/transverse-section lemmas were found, but no absolute
  normalization local-section theorem and no exact blueprint-id hit. A broader
  `absolute.*normalization|absolute.*integral.*closure` search found normalization
  dominant lifts and unrelated normalizations; these are not this result.
- Read the ten statement dependency nodes and the full signatures and docstrings
  of their recorded declarations (including the Mathlib-match DVR and algebraic
  closure nodes). Read Stacks `more-morphisms.tex` 05GU and `more-algebra.tex`
  0DCQ/0DCS. Read the latest blueprint direct-images unit and proof; this item is
  an inherited geometric tool, not the unit's own statement. The absent
  Anantharaman scan is not claimed as read.

No statement dispute or node fault was found. The named helper is only the
canonical structural map for the existing integral-closure notion, as permitted
by the launcher helper rule; it does not introduce another integral closure.

## Second reading by Q91

Worker self-audit after reopening the node and module; no additional agent was
started, as instructed. The maintainer supplies the independent review.
Checked the eight consecutive conjuncts against the node: the first four give
flat/surjective/quasi-compact/fpqc, the next gives the compatible generic-open
isomorphism, the next identifies the whole generic inverse image, the next gives
all three assertions for the complementary points, and the last is the exact
local-section statement. In the last conjunct, both `y` and `σ` have explicit
structure-map equalities; `τ ≫ σ = y` retains the field morphism, rather than
merely its topological image. Checked that the uniformizer equality is on `R`,
the basic open uses its image in `B`, and the residue field belongs to `T`.
No mathematical mismatch required a node correction. The canonical helper has
no postponed data, and the theorem alone has the expected `sorry`.
