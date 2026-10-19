## Worker report

The module `Sheaf.Paper.IntegralCoherenceTower` states
`WeilConjectures.IntegralCoherence.integralCoherenceTower`. The sole postponed
proof is this theorem. Helper structures and definitions package this node's
vertices, canonical arrows and equations; their data contain no `sorry`.

Hypothesis and clause correspondence:

- The binders `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`
  and `[FiniteDimensional ℚ_[l] E]` are the prime and finite coefficient extension.
  The coefficient constructions use `Padic.coefficientExtensionUniformizer`.
- `W : S → Scheme.{t}` names the schemes; `_hl` says that l is invertible
  at every residue field. For the displayed diagrams take three locations
  carrying Y, X, Z and arrows f and h. There is no finite-field datum or
  assumption that any of these schemes is nonempty.
- `coefficientSequenceCommRingSheaf` is the actual sheaf with value B_(n+1)(U)
  and the actual quotient restrictions. `scalarReductionSource` uses the
  inverse-limit completed ring R, not the discrete constant integral ring.
  Site objects have universe t+1, morphisms t, coefficients max u (t+1).
- The `P`, `hP`, `_hflat` binders range over integer-indexed K-flat complexes
  with flat terms over that completed ring. `QuotientPresentation.evaluation`
  identifies their levels with ordinary scalar reduction; `.transitions` is
  the recorded `CoefficientReductionPresentation`, including ALL quotient
  transition squares and the fixed finite derived-reduction comparison.
- `Complex` is a cochain complex of modules on the ringed sequence site.
  A chain map there is a strict tower map. `value` interprets the recorded
  finite operation syntax using ordinary total tensor, coefficient unit in
  degree zero and termwise actual system inverse image. In particular it
  includes both triple parentheses and h*f* as well as (f h)*.
- `PullbackComparison.tensor` is an isomorphism of these strict complexes.
  Its `generators` equation fixes the image of 1 tensor (x tensor y), in
  each direct-sum total-degree summand; module linearity gives
  s tensor (x tensor y) ↦ (s tensor x) tensor (1 tensor y).
  Invertibility fixes the contraction inverse uniquely. All maps are
  sequence-site module maps, so this includes horizontal quotient compatibility.
- `PullbackComparison.toCoreMonoidal` uses Mathlib CoreMonoidal for
  naturality, the two associativity routes and both action-unit equations
  (equivalently written for the invertible contraction map). `Coherent`
  supplies the symmetry equation for the same maps. Symmetry uses the existing
  `CochainComplex.Monoidal.braiding`, whose summand formula is (-1)^(pq).
- `CompositionLaw` is exactly the displayed compositor equation in Lean's
  left-to-right composition order. `compositor` is the termwise lift of
  `integralComparisonSequenceComposition`, the adjunction mate fixed by
  fibre-product pasting, rather than an arbitrary comparison.
- `Realization.good` retains K-flatness and flat terms of whole expressions;
  `.normalized` asserts normalizedness with the dependency's universal
  derived scalar-extension criterion. This includes the three quotient towers,
  all units and every allowed finite tensor/pullback expression.
- `Realization.system_input`, `.system_unit`, `.system_tensor` and
  `.system_pullback` recursively fix every vertex comparison on representatives.
  `.structural` fixes the images of reassociators, action unitors, signed
  symmetries, adjunction-normalized compositors, their inverses and contexts.
- `Realization.completed_normalization` identifies completed expressions with
  the derived limits of these very strict expressions, by the recorded
  completed substitution comparison. `completedArrow` applies localization
  and the functorial total derived limit, then conjugates by these fixed
  identifications. Consequently each equality of strict composites is the
  corresponding equality of completed composites, and inverse strict maps
  remain mutually inverse. `ComparisonLaws`, `SubstitutionLaw` and
  `StructuralLaw` retain the existing completed-operation identifications,
  naturality, substitution compatibility and normalization of structural maps.
- `Realization.reduction_normalization` specifies the coherent counit, and
  `ReductionLaw` identifies the reduction of EVERY transported strict arrow
  with its original arrow. Its second square explicitly retains every
  B_m → B_n, including m=n. Thus it applies to both sides of each coherence
  equation, not merely independently to finite objects.

Dependency declarations used (available through the public imports):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: `Padic.coefficientExtensionRing`, the chosen uniformizer,
  quotient ideals and quotient homomorphisms.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  completed coefficient sheaves and projections reexported by this record.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift` and
  `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`:
  direct-sum total tensor, associator, unitors and Koszul braiding.
  `Mathlib.CategoryTheory.Monoidal.Functor`: `Functor.CoreMonoidal` supplies
  the ordinary naturality/associativity/unit law interface, without duplicating it.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleBaseChange`, reexported to the actual sequence inverse image.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, whose
  generator, composition and coefficient clauses supply the proof route.
- `Sheaf.Paper.NormalizedDVRTower`:
  quotient restrictions and the universal transition-adjoint criterion,
  used through `IsNormalizedCoefficientSequence`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  the functorial total derived limit underlying `coefficientSequenceLimit`.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`:
  `CompletedOperations.Models`, `Expression`, `StructuralMap`, `systemValue`,
  `completedValue`, `comparison`, `structuralValue` and all three law predicates.
- `Sheaf.Paper.NormalizedDVREffectivity`:
  coherent normalized-tower counit effectivity, through the canonical
  reduction/limit calculus in `Models.calculus`.
- Its published sequence-site and evaluation-calculus interfaces give
  `CoefficientReductionPresentation`, `CoefficientTensorModels.iso`,
  `coefficientTensorGenerator`, actual sequence adjunction generators,
  `integralComparisonSequenceComposition` and exact localization factors.

Edge cases read before writing: positive exponent 1 (Lean index 0); all
identity quotients m=n; repeated inputs and both tensor parentheses; unit-only
expressions; identity scheme maps and composable identity maps; zero complexes;
empty schemes, empty input sets and empty scheme-location sets; unbounded
cochains with all integer degrees. No boundedness, constructibility, common
stratification or equality of site/coefficient universes is imposed.

Searches:

- msearch LeanFinder: “coherence identities for normalized integral quotient
  towers tensor pullback associativity symmetry unit composition”: returned
  scheme normalization identities and free monoidal normalization, no match.
- msearch Loogle: `CategoryTheory.Functor.map_comp, CochainComplex.mapBifunctor`:
  zero hits; these generic components do not state the node.
- msearch grep: `quotient.*tower|[Ii]ntegral[Cc]oherence|[Tt]ensor[Cc]oherence`
  under Algebra/Homology: zero hits.
- msearch LeanSearch: “cochain tensor pullback comparison compatible with
  quotient transitions inverse systems”: returned ordinary module tensor
  quotient/right-exactness and inverse-system facts, no whole statement.
- rg of `integralCoherenceTower|IntegralCoherence` in Mathlib, upstream
  WeilConjectures and side Sheaf: no preexisting declaration.
- rg of this exact node id in upstream WeilConjectures: no match.
- rg of quotient towers in upstream/side sources found the existing cochain
  coefficient coherence, quotient presentation and completed substitution
  interfaces used above, but none states the whole conjunction.

Source reading: sites-cohomology.tex, label lemma-pullback-tensor-product
(07A4), constructs the comparison on flat-term K-flat total tensors;
label lemma-derived-limit-is-ok (0941) uses simultaneous K-injective strict
systems. The six-step proof docstring follows the node's six proof steps.
No statement correction, new node, dependency replacement or disputed statement.

## Second reading by Q50

Author self-reading; no independent worker was started, as the dispatcher brief
prohibits starting agents. The maintainer supplies the independent review.

I reread the node and the file together. The prime/finite extension, invertibility,
completed coefficients, flat-term K-flat hypotheses, actual reductions,
normalizedness, strict cochain comparisons, associativity, sign, both units,
composition mate, limit substitution and coherent reduction all have the
counterparts listed above. In particular the statement does not infer an equality
in the system category just from evaluated equalities: the equations are on
sequence-site chain maps and the realization equations are on whole systems.
The finite quotient exponent convention is n+1 throughout. The initial broad
realization clause was restricted to actual quotient presentations; the final
version builds on these presentations rather than arbitrary independently
chosen derived towers. A missing explicit site argument in flatness was fixed
during compilation. No source hypothesis or finite level was removed.

## Validation

The prescribed `scompile.py Q50 lem-pur-integral-coherence-tower` check
passed against the current server sources for the final module (52.2 seconds),
with only the expected postponed-proof warning. The wrapper retried an initial
local timeout through its prescribed server-confirmation path.

The prescribed `deliver2.py Q50 lem-pur-integral-coherence-tower --no-push`
finished with OK: preflight and per-file compilation passed (dry-run commit
`c332e2b55b`).
