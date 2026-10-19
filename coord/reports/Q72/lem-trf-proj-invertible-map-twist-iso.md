## Worker report

The module `Sheaf.AlgebraicGeometry.ProjInvertibleMapTwistIso` states
`AlgebraicGeometry.Scheme.Modules.exists_proj_invertible_map_twist_iso`, with one
postponed theorem and seven explicit auxiliary definitions belonging to this comparison.
No definition chooses a map or module from an existence theorem. The auxiliary definitions
only name the generation domain, restriction of sections, the canonical tensor-pullback
section, the existing homogeneous twist section, multiplication on restricted powers, and
the two equations defining the comparison's normalization and multiplicativity.

Source read: `literature/stacks-project/constructions.tex`,
`lemma-invertible-map-into-proj` (Tag 01NK), including the characterization and localization
proof, and `lemma-converse-construction` (Tag 01N8), including its local basis maps and
uniqueness. The six proof steps of the node are recorded in the theorem docstring.

Hypothesis and conclusion correspondence:

- The nonnegative grading on the commutative ring A is `(A : Type u) [CommRing A]`,
  `(𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]`. An arbitrary internal grading can be
  expressed by its additive homogeneous subgroups; this does not require degree-one
  generation or any finite-generation condition.
- The scheme T is `{T : Scheme.{u}}`. The module and its invertibility are
  `(L : T.Modules) [L.IsInvertible]`, using the recorded scheme-module predicate.
- The graded homomorphism is `(ψ : A →+* InvertibleSectionRing L)` together with `hψ`:
  every element of `𝒜 n` maps to `sectionRingGrade L n`. Evaluation `(ψ a) n` is the
  actual section of the n-th tensor power in the existing direct-sum section ring.
- `projSectionMapDomain 𝒜 L ψ` is exactly the supremum of `generatingLocus ((ψ a) e)`
  over every positive e and every homogeneous a in `𝒜 e`. There are no restrictions
  on the size of the cover.
- The positive degree is `(d : ℕ) (hd : 0 < d)`, equivalent to d >= 1.
  The open subscheme is `(V : T.Opens)` and its containment in U(ψ) is `hV`.
- The generation assumption is `hgen : V ≤ ⨆ a : 𝒜 d, generatingLocus ((ψ a) d)`.
  For an invertible sheaf power this is equivalent to generation by the indicated
  sections: locally in a basis, their coefficients generate the unit ideal of each
  local ring if and only if some coefficient is a unit. Thus it expresses exactly
  the stated generation condition, not a global free-basis or single-section condition.
- The conclusion supplies `r : V.toScheme ⟶ Proj 𝒜` and one family `θ` in all
  nonnegative degrees. Here r is the restriction of the canonical map, specified
  simultaneously with its comparison by the characterizing properties of Tag 01NK,
  rather than a map supplied as an arbitrary parameter. The first conjunct says that
  the image in T of `r ⁻¹ᵁ D_+(a)` is `V ⊓ generatingLocus ((ψ a) e)`, for every
  positive homogeneous a. The next two conjuncts impose the homogeneous-section
  diagram and the graded multiplication law. Together these are the canonical
  triple's defining properties from 01NK, restricted to V; localization forces the
  fraction formula used in the proof. In particular the existential r is not an
  arbitrary morphism with an arbitrary isomorphism of modules.
- The source of `θ n` is `(tensorPullback r).obj (Proj.twist 𝒜 (n : ℤ))`, the recorded
  tensor-formula pullback of O(n). Its target is `(L.tensorPow n).restrict V.ι`, the
  restriction of the power on T (not a silently replaced tensor power on V).
- `ProjTwistComparisonPreservesSections` applies θ to the canonical tensor-pullback
  of each section `a/1` and equates its image to the restriction of `(ψ a) n`.
  The helper for `a/1` uses `Proj.unitToTwist` and an explicit `0+n=n` transport.
  The pullback section helper is the actual inverse-image unit followed by `1 ⊗ -`
  and the module-sheafification unit; it does not choose an unspecified adjunction.
- The isomorphism clause is `IsIso (θ d)`.
- The final universal quantifier ranges over every module morphism τ with the same
  source and target, and asserts `τ = θ d` whenever τ sends each degree-d homogeneous
  section to its prescribed image. It does not assume τ invertible or require a
  complete graded comparison for τ. This is the node's full uniqueness clause.
- `ProjTwistComparisonMultiplicative` quantifies over every i,j, every open W of
  Proj(A), and every pair of local twist sections s,t. For their product st (specified
  by equality of pointwise values in the existing homogeneous localizations), it says
  that θ(i+j) of its pullback equals the product of θi and θj of the pullback sections.
  `projRestrictedPowerMul` uses the existing `tmulSection` and `tensorPowAddIso`.
  Local products always exist by `ProjectiveSpectrum.Twist.isLocallyFraction_mul`
  (with the natural-number cast identity), so the implication does not omit any
  products. These tests include fractions on every basic chart. Pure tensors generate
  the inverse-image tensor sheaf locally, hence the displayed equation is exactly
  compatibility with the graded sheaf multiplication maps, including after arbitrary
  coefficients are introduced. It therefore includes different positive generated
  degrees without incorrectly assuming that Proj twist multiplication is always an
  isomorphism.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the Mathlib Proj interface is available through the twist imports, with
  `AlgebraicGeometry.Proj` and `Proj.basicOpen` (and the recorded `projIsoSpec` chart).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso`; imported publicly
  through the recorded section-ring module.
- `Sheaf.AlgebraicGeometry.InvertibleSectionRing`: `InvertibleSectionRing`,
  `SectionRingComponent`, `sectionRingGrade` and its graded ring instance.
- `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`:
  `Scheme.Modules.generatingLocus`, `GeneratesAt` and their neighborhood criterion.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `Proj.twist`; `...Twist.UnitToTwist` publicly imports this exact module and gives
  `Proj.unitToTwist` with its `val_unitToTwist_app_top` formula. The module also uses
  the actual section values of this twist construction for the multiplication law.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `tensorPullback`,
  `tensorPullbackRingMap`, and the explicit inverse-image/change-of-rings construction.
  The file was missing in the older upstream checkout; its full current source was
  read successfully through `scompile.py --source`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` is imported as the
  recorded general-site tensor interface. On scheme modules the existing monoidal
  tensor and `tmulSection` specialize the same sheafified sectionwise tensor; no
  alternative sheaf tensor construction is introduced.
- The recorded proof modules are imported non-publicly:
  `Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists` and
  `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`.

Edge cases checked: empty V and empty T (no nonempty assumption; unique empty sheaf maps),
A concentrated in degree zero or ψ with zero positive image (U empty and hV forces V empty),
zero ring (Proj empty), zero sections (empty generating opens on a nonempty invertible
module), d=1 and arbitrary d>1, lack of degree-one generators, and non-quasi-compact V.
There is no claim that O(d) is globally invertible on an arbitrary Proj, or that its
multiplication maps are globally isomorphisms. Multiplication also includes degree zero;
there are no hypotheses of ampleness, finite generation, separatedness, or quasi-compactness.
All universe variables and all term variables are explicitly bound.

Searches actually run with `msearch.py Q72 lem-trf-proj-invertible-map-twist-iso`:

- LeanFinder: `Canonical Proj morphism from graded sections of an invertible module pulls
  back twists with multiplication compatible comparison`. Eight hits, including
  `Proj.pullbackAwayιIso`, `Proj.fromOfGlobalSections_morphismRestrict`, and chart-map
  lemmas; none states the arbitrary invertible-module twist comparison.
- Loogle: `AlgebraicGeometry.Proj.twist, AlgebraicGeometry.Proj.unitToTwist`.
  Parser reports unknown identifier `AlgebraicGeometry.Proj.twist`: unavailable,
  not evidence of absence.
- grep: `fromOfGlobalSections|invertible.*[Pp]roj|twist.*[Cc]ompar`. Seven hits: Mathlib
  `ProjectiveSpectrum/Basic.lean` global-functions construction and unrelated
  ring-theoretic Picard-group comments; no exact match.
- LeanSearch: `pullback of Proj twist along morphism from invertible sheaf graded section
  ring canonical comparison`. Eight hits, consisting of generic pullback and Proj
  chart-comparison results; no exact match.
- Direct `rg` searches in the prescribed upstream `WeilConjectures` and side `lean/Sheaf`
  directories for twist, section-map and canonical-Proj keywords found the upstream twist
  construction and side `AmpleProjCanonicalMap`, `AmpleProjChartFormula`, and
  `AmpleProjPreimage`. Their signatures were read: they concern Proj of the entire section
  ring and do not state this arbitrary graded-map twist comparison. Searching the item id
  upstream produced no match. The proposed declaration names were also checked against
  these directories and `dag/lean_names_upstream.json`; there is no collision.

There is no statement correction, new independent notion, or dependency repair.

## Second reading by Q72

A second author pass compared the source, node, and file. No second agent was started,
as the dispatch brief explicitly forbids it; the maintainer supplies the independent review.
This pass checked the ring/grading, invertible scheme module, graded ψ, union U(ψ), positive
d, arbitrary V, containment, and local generation hypotheses individually against the
binders above. It checked the pullback source and restricted-power target, the `a/1` image
condition, `IsIso (θ d)`, uniqueness among all module maps, and the all-open multiplication
condition against every conclusion clause. The canonical-map characterization is supplied
in the conclusion, not postulated as an unconstrained map or isomorphism. Auxiliary data
are explicit and only the main named theorem is postponed. The pass retained arbitrary
non-quasi-compact opens and arbitrary positive degrees, and checked the empty-open case.
Compiler repairs added the `ChangeOfRings` notation scope and used the global
`Opens.grothendieckTopology` namespace in the explicit pullback-section definition.

Validation: the prescribed `scompile.py Q72 lem-trf-proj-invertible-map-twist-iso`
compiled both its sandbox probe and the named module successfully, with no errors or
warnings (21.1 s and 25.6 s respectively). The Lean file has no lines over 100 characters,
no local notation or instances, and no hidden proofs or unbound implicit variables.
