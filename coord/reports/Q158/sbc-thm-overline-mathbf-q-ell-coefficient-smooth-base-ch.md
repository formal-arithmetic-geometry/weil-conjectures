## Worker report

The delivery states `AlgebraicGeometry.Scheme.qbarCoefficientSmoothBaseChange` in
`Sheaf.Paper.QbarCoefficientSmoothBaseChange`. The DAG statement and dependencies are
unchanged. Its witnesses construct the specified ambient completed exchange by actual
finite-stage localization, finite-stage Karoubi extension, common-stage quotient descent,
and outer Karoubi extension. No constructible direct-image landing is asserted. All theorem
proofs are `sorry`; definitions have real data. No dependency record is replaced and no new
independent notion or definition node is needed.

The interrupted packet contained a module and node record but no report. The prescribed
initial dry run confirmed the missing report. Self-reading of the saved statement then found
that it assumed finite-stage invertibility as `hE`, asserted invertibility of a whole ambient
natural transformation, omitted the chosen object's descended component and its lattice
existence, and left the scalar comparisons unspecified. These defects are repaired here;
none requires a change to the mathematical node.

Hypotheses, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`; the chosen algebraic closure is `(Ω : Type v)
  [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. Schemes have independent
  universe `u`, with the dependency's canonical `pbcFiniteField.{u}` models of finite fields.
- The square is `sq : ChosenCartesianSquare h e f g`, with `f : X ⟶ S`, `g : T ⟶ S`,
  `h : Y ⟶ X`, `e : Y ⟶ T`. Thus both exchange endpoints lie over X.
- Smoothness and the two finiteness properties are `[Smooth f] [QuasiCompact g]
  [QuasiSeparated g]`. All four `[IsNoetherian ...]` and all four finite dimension facts
  `dX`, `dS`, `dT`, `dY` are bound. The dimension bound is existential, not a fixed bound.
- The only invertibility hypothesis is `hInvS : IsUnit (l : Γ(S, ⊤))`. Every stalk fact
  needed by the categories is obtained from `sbcPrimeUnitOnSource`, using f, g, e≫g and
  the identity on S. No independent invertibility hypotheses on X, T or Y are added.
- K belongs to the recorded raw `pbcQbarCategory l Ω T`. The existence premise supplies
  E, a raw constructible stage object J, an `IntegralLattice ... J`, its
  `IsFiniteLevelEtaleAdmissible` property, and `Nonempty ((⟨E,J⟩ : pbcQbarCategory ...) ≅ K)`.
  This permits a representative isomorphic to K; it does not require K's literal stored
  stage to carry the lattice. The lattice includes its specified raw rationalization
  isomorphism by the dependency definition.
- Preservation under passage to common finite overfields is the universal premise over
  `M` and `a : E ≤ M`, supplying an admissible lattice for the actual
  `(pbcScalarSystem ...).T a` image of J. It includes identity extensions. The geometric
  finite-E hypotheses already hold uniformly, with the same schemes and prime.

Conclusion, clause by clause:

- The theorem supplies `∃ P : Presentation ...`; P is a presentation of the canonical
  operations, not an assumed preservation or arbitrary comparison family.
  `smoothLeftStage`, `smoothRightStage` are exactly Karoubi extensions of the recorded
  `sbcRationalLeft`, `sbcRationalRight`. `P.F_eq`, `P.G_eq` identify their stage functors.
- `IntegralComparisons.push_eq` and `.pull_eq` fix every component using the actual
  scalar/direct-image mate and unit-normalized scalar/completed-pullback comparison of
  `PbcScalarExtension`. `pushModel` is the adjoint mate of the published normalized
  ordinary-pullback comparison; `pullModel` reuses the published uniquely unit-normalized
  strict-tower/reflector comparison. `tensorModel_eq` identifies the two published
  coefficient tensors by their equal finite projections. `tensorModel` is equality
  transport, not an arbitrarily selected tensor isomorphism.
- `P.leftBeta_eq`, `P.rightBeta_eq` localize the precise composites of these integral
  scalar comparisons. They retain `pbcAmbientCompleteIntegralComparison` on both sides,
  including the tensor unit in the repeated-field case. `P.F_beta`, `P.G_beta` fix the
  finite-stage Karoubi comparisons as their actual `functorExtension₂.mapIso` images.
  `StageSystem.Morphism.coh` supplies all tower equations, and `P.alpha.comm` is the
  exchange/scalar compatibility equation. No arbitrary functors replace the composites.
- `P.alpha_eq` identifies the full finite-stage transformation with
  `smoothExchangeStage`, namely `functorExtension₂.map (sbcRationalExchange ...)`.
  At a raw input with identity projector this is precisely the image of the canonical
  raw E-exchange under the identity-idempotent inclusion; arbitrary projectors are also
  retained by Mathlib's extension formula. This asserts no raw-to-Karoubi equivalence.
- `Presentation.ambientExchange` is the actual Karoubi extension of
  `StageSystem.Morphism.descNatTrans P.alpha`. `Presentation.exchange` restricts it along
  the published `pbcRawQbarToComplete` and `pbcConstructibleCompleteQbarInclusion`.
  Consequently `IsIso (... .app K)` is the specified arrow in the recorded ambient
  `pbcAmbientCompleteQbarCategory l Ω X`, with the two indicated completed composites
  as its endpoints. It asserts invertibility at the admissible input, not throughout
  the ambient category.
- The second conjunct equates the descended component on every ambient pair Q with
  `Presentation.atStage Q M a` for every finite overfield. That definition is the actual
  representative `mkHom M a a (betaF ; alpha_M ; betaG inverse)`. This gives the stated
  coefficient-extension formula and independence of common stage. Outer Karoubi
  extension preserves this equality. Independence on isomorphic object presentations
  is also built into the natural transformation `Presentation.exchange` and quotient
  functors, rather than an assumption about chosen representatives.
- The final conjunct says the two `sbcTransportedExchange` maps for any two admissible
  lattices L and L' of the same raw stage object are equal. Combined with `alpha_eq`,
  it is precisely lattice independence of the constructed exchange. No
  square-constructible hypothesis or constructible landing clause is inserted.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`, with its imported
  `ChosenCartesianSquare` datum and the same orientation of f, g, h, e.
- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`, the actual raw
  finite-stage pair category, with no outer Karoubi envelope.
- `Sheaf.Paper.AmbientCompleteCoefficientCategories`: `pbcAmbientCompleteKaroubiStage`,
  `pbcAmbientCompleteSystem`, `pbcAmbientCompleteQbarCategory`, `pbcRawQbarToComplete`,
  and `pbcConstructibleCompleteQbarInclusion`, in `AlgebraicGeometry.Scheme`.
  Its imported `AmbientCompleteRawSystem` supplies the actual integral/raw tensors
  and `pbcAmbientCompleteIntegralComparison` including the identity branch.
- `Sheaf.Paper.ECoefficientSmoothBaseChange`: `WeilConjectures.sbcRationalLeft`,
  `sbcRationalRight`, `sbcRationalExchange`, `sbcTransportedExchange`,
  `sbcPrimeUnitOnSource`, and `eCoefficientSmoothBaseChange`.
- `Sheaf.Paper.AdmissibleLattices`: `AlgebraicGeometry.Scheme.IntegralLattice` and
  `IntegralLattice.IsFiniteLevelEtaleAdmissible`, with the completed sheaf, actual
  n+1 reductions, raw presentation and essential-image predicate unchanged.
- `Sheaf.Paper.PbcScalarExtension`: `pbcScalarDirectImageIso`,
  `pbcScalarCompletedPullIso` and their coefficient/tower/exchange normalization;
  `PbcActualStrictPullback.pbcActualCompletedPullback_tower` is reused for the actual
  strict-tower/reflector comparison. The sbc operation module supplies the normalized
  ordinary derived comparison and adjunction used by `pushModel`.
- `Sheaf.CategoryTheory.StageSystemFunctorDescent`:
  `CategoryTheory.StageSystem.coefficientPairFunctor_exists` and its representative
  formula were read. The theorem uses the already constructed equivalent upstream
  `StageSystem.Morphism.functor` and `.descNatTrans` on that exact quotient carrier,
  from `WeilConjectures.CategoryTheory.StageSystem.Functor`; its `.Hom.comm` and `.coh`
  are the same compatibility equations. No second pair category is defined.
- `Sheaf.Paper.SbcCompletedOperations`: the actual complete categories and additive
  linear completed operations and canonical integral exchange, as proof step 1 requires.
- Mathlib `CategoryTheory.Idempotents.Karoubi`, `toKaroubi`, `functorExtension₂`, and
  `conjugateIsoEquiv`; `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`:
  `Padic.FiniteCoefficientFields` and its finite common-overfield construction.

Edge cases checked: empty schemes are allowed and their stalk conditions are vacuous,
while the global-unit pullback theorem also covers them. Zero complexes and zero
idempotents remain legitimate objects. No nonzero lattice condition or cohomological
window is added. All natural degrees of the lattice predicate remain present, including
n=0 (quotient exponent 1). `a : E ≤ M` allows M=E and is not required to be strict.
Both the equal-field tensor unit and arbitrary later-field tensor comparisons are kept.
The independent coefficient closure universe v does not restrict scheme universe u.
The output is the ambient X category, not S and not the constructible subcategory.

Search evidence retained from `searches.jsonl` of the interrupted worker:
LeanFinder, query “Smooth base change for algebraic closure of l-adic coefficient fields
via common stage descent”: eight hits headed by `Algebra.IsStandardSmooth.baseChange`
and `RingHom.Smooth.isStableUnderBaseChange`, all ordinary algebraic smoothness, no match.
Loogle, `CategoryTheory.Idempotents.functorExtension₂`: twelve hits identify the exact
Karoubi extension infrastructure, which is reused. Mathlib grep,
`qbar.*[Ee]xchange|[Ee]xchange.*[Qq]bar|[Ss]mooth.*[Bb]ase[Cc]hange`: 21 hits concern
ordinary scheme/ring smooth base change, with no coefficient exchange theorem.
Repeated source and `lean/Sheaf` searches for this node id, qbar/exchange and the intended
namespace found the proper and compact-support Qbar theorems, not this smooth theorem.
The proper theorem's presentation was inspected as a convention example, without copying
its constructible preservation assumptions. Exact-name searches for the new namespace,
`qbarCoefficientSmoothBaseChange`, `pullModel_exists` and `tensorModel_eq` in Mathlib,
upstream WeilConjectures and `lean/Sheaf` found no collisions. No exact existing statement
matches the item. The DAG's earlier LeanSearch outage is not treated as match evidence.

Source checked: the node's own blueprint markdown and sketch32 lines 1191–1228,
1291–1338 and 1412–1469, together with all statement dependency records and their
recorded module signatures/docstrings. No STATEMENT-DISPUTED issue remains. The original
source markdown's output-corner typo was already corrected by stage 1 in the current
node; this delivery follows the unchanged node and its six-step proof.

Validation: the final module passed `scompile.py` in both its sandbox and library forms,
with no errors or warnings (10.4 s and 30.9 s). Static self-check found no line over 100
characters, exactly two named postponed theorems (`tensorModel_eq` and the item theorem),
no sorry in definition data, a verbatim primary signature record, and only `lean` changed
in the node copy. The coefficient-tensor equality helper is the finite-projection
identification used in this node's canonical scalar-comparison construction, with its
source and proof in the docstring; it introduces no independent mathematical claim.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
