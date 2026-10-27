## Worker report

This delivery states `AlgebraicGeometry.Scheme.Modules.exists_lineProj_affine_chart_atlas`
in `Sheaf.TraceFormula.LineProjAffineChartAtlas`. Its sole theorem has proof `sorry`.
All helper definitions have actual data. There are no new nodes, dependency repairs,
or changes to the natural-language statement. Q156's reviewed delivery was the
stage-1 split: the current node has no `lean` record, so it does not supersede this
stage-2 statement. No repair note for this item was present.

The source read was `literature/stacks-project/constructions.tex`,
`lemma-invertible-map-into-proj` (01NK), including uniqueness by localization and
local construction in a frame, and the setup and all three clauses of
`lemma-invertible-map-into-relative-proj` (01O9), including its affine-base gluing proof.

Hypotheses and objects:

* The schemes and morphism are `{W T : Scheme.{u}} (f : W ⟶ T)`.
* The quasi-coherent graded commutative algebra is `A : RelativeProjAlgebra T`.
  This is the published sheaf input, with actual `A.algebra`, homogeneous sheaves
  `A.piece`, algebra structure `A.graded`, and direct-sum identification
  `A.decomposition`. Its canonical affine presentation is the recorded `A.affineData`.
  Neither finite generation nor generation in degree one nor `A_0 = O_T` is assumed.
* The invertible module is `(L : W.Modules) [L.IsInvertible]`.
* The graded homomorphism is the family
  `ψ : ∀ n, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n`.
  Each component is an O_W-linear sheaf morphism; thus linearity and restriction
  compatibility are inherent. `hunit` asserts compatibility with the given degree-zero
  structural unit, on every base open and every scalar. `hmul` asserts the homogeneous
  product equation, on every base open, pair of degrees, and pair of sections.
  These are the unit and multiplication laws of the stated graded algebra map,
  not extra geometric assumptions. Such pulled-back sections locally generate the
  tensor pullback, so these equations express precisely the sheaf algebra-map laws.
* `lineProjImage` applies ψ to the actual `tensorPullbackSection` (1 tensor a).
  For affine V, `lineProjElement` includes a section of `A.piece d` into the actual
  graded section ring `A.grade V`. The decomposition identifies the two descriptions
  of A_d; this does not choose an arbitrary map or a different algebra.

Every conclusion clause:

* `W_V` is literally `f ⁻¹ᵁ V.1`. The open `lineProjGeneratorOpen f A L ψ V d a`
  uses the recorded `generatingLocus` on its open subscheme, transferred by the open
  inclusion to W. The intersection with `W_V` only exposes its already true inclusion.
  The first conclusion identifies membership with bijectivity of the stalk scalar map
  `r ↦ r • germ(ψ(a))`: exactly that the germ freely generates the stalk.
* The second conclusion equates the underlying set of the supremum over V, d>0, a
  with `{x | ∃ d, 0 < d ∧ Function.Surjective (stalkFunctor.map (ψ d).mapPresheaf)}`.
  Thus the right side is actual stalkwise surjectivity of ψ_d, rather than a renamed
  generator locus or a hypothetical surjectivity predicate.
* The existential family q gives a morphism from each full generator open to
  `Spec (.of (HomogeneousLocalization.Away (A.grade V) a))`.
* `LineProjFractionFormula` uses `HomogeneousLocalization.Away.mk` for b/a^m,
  with b in degree `m • d` (natural-number multiplication). `lineProjScalar` is the
  actual ring map of q, through the canonical `ΓSpecIso` and `Opens.topIso`.
  The equation is `q#(b/a^m) • ψ(a)^m = ψ(b)`. `lineProjPower` constructs the
  denominator tensor power and transports it by `L.tensorPowMulIso` to degree m*d.
  Hence the equation means unique division by the indicated free generator.
* The third conclusion states, for every smaller source open C and every candidate
  morphism r, that this fraction formula holds iff
  `r = W.homOfLE hC ≫ q V d hd a`. Taking C to be the full generator open gives
  existence and uniqueness there. General C gives compatibility with all open
  refinements of W, without requiring C to be affine.
* `lineProjChartToLocal` composes q with Mathlib's canonical `Proj.awayι`.
  `lineProjChartToRelative` then composes with `A.affineData.relProjι V`.
  The fourth conclusion equates these compositions on the intersection of two
  generator opens. Both base opens and both positive degrees are independent;
  no equality of degrees or affineness of the base intersection is assumed.
* `LineProjTrivializationFormula`, the fifth conclusion, quantifies over every affine
  B in W_V, every free frame e, and its coefficients αa and αb. It identifies the
  restricted chart open with `W.basicOpen αa` and states
  `q#(b/a^m)|_(W_a ∩ B) * (αa|_(W_a ∩ B))^m = αb|_(W_a ∩ B)`.
  Since αa is invertible on that open, this is exactly αb/αa^m. The same q works
  for every frame, so changing the trivialization leaves the map unchanged.
* `LineProjBaseRefinement`, the final conclusion, identifies the generator open for
  a restricted section on affine C⊆V with `W_a ∩ f⁻¹(C)`, and identifies the chart
  morphisms after the canonical Proj restriction map. This map is written as
  `(A.gradeIso C).inv ≫ A.localTransition hCV ≫ (A.gradeIso V).hom`.
  `localTransition` is exactly Proj of section restriction, and the grading isomorphisms
  only pass between the existing subgroup and submodule descriptions of the grading.
  This equals the canonical affineData transition by the published
  `RelativeProjAlgebra.gradeIso_naturality`. It also avoids expensive elaborator
  unfolding of affineData and its base-change proofs.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso`, `tensorPowMulIso`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the recorded normalized adjunction and `tensorPullbackSection`; it publicly imports
  the actual `WeilConjectures.AlgebraicGeometry.TensorPullback.tensorPullback` construction.
* `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`:
  `Scheme.Modules.generatingLocus`, `GeneratesAt`; its input is a global section
  on the inverse-image open scheme, using `restrictAppIso` to identify its sections.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj`, `relProjι`; and the recorded additional module
  `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`:
  `RelativeProjAlgebra.affineData`, `grade`, `gradeIso`, `localTransition`.
* `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `QuasiCoherentAlgebra`; `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `GradedSheafAlgebra`, its unit and homogeneous multiplication.
  `RelativeProjAlgebra` is the published sheaf input retained by the relative-Proj node.
* `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `AlgebraicGeometry.Proj`,
  `Proj.awayι`, its `basicOpenIsoSpec` chart identification. This is the usable
  declaration of the Mathlib-matched Proj node; no replacement Proj definition is made.
* `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `Away.mk`, `Away.mk_surjective`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded `SheafOfModules.cochainModulesMonoidal` and retained tensor structure.
* Proof imports: `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`
  (`nonvanishing_section_trivializes`),
  `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
  (`exists_tensorPullback_affine_sections`),
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
  (`ΓSpec.locallyRingedSpaceAdjunction`, and its scheme specialization), and
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`
  (`Proj.awayι_preimage_basicOpen`, `Proj.basicOpen_mul`).

Edge cases checked before writing: empty W or T and empty affine opens; zero/nilpotent
homogeneous a (empty generator open and the corresponding zero localization ring);
zero divisors (ordinary localization relation, no cancellation of a itself);
m=0 (the denominator is the tensor-unit basis); arbitrary positive d and e;
no positive generators (empty union and empty chart family); arbitrary A_0;
nonaffine W_a; nonaffine intersections V∩V′; arbitrary rather than principal affine
base refinements. For a nonempty W with algebra concentrated in degree zero, the
surjectivity of ψ_0 is deliberately excluded. The existing node already carries Q156's
correction to positive degrees, which this delivery preserves.

Searches actually run:

* `msearch.py ... leanfinder`, query: “A graded algebra map into tensor powers of an
  invertible sheaf induces compatible homogeneous fraction chart morphisms to relative
  Proj”. Eight hits, including `Proj.fromOfGlobalSections`, `toBasicOpenOfGlobalSections`,
  `awayToSection`, and `awayMap_awayToSection`; no complete graded line-module atlas.
* `msearch.py ... loogle`, query:
  `AlgebraicGeometry.Proj.fromOfGlobalSections, HomogeneousLocalization.Away.mk`.
  Zero hits for that combined query.
* `msearch.py ... grep`, query: `fromOfGlobalSections|toBasicOpenOfGlobalSections`,
  subtree `AlgebraicGeometry/ProjectiveSpectrum`. Five hits in Basic.lean; the local
  constructions take maps to ordinary functions, not the given line-module tensor powers.
* `msearch.py ... leansearch`, query: “A graded morphism of algebra sheaves into tensor
  powers of a line bundle on a scheme”. Eight hits, tensor and graded-object APIs;
  none states this chart atlas.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for graded line maps, relative
  Proj, generating loci and tensor-power sections; exact blueprint-id search found no
  existing module for the item. `RelativeGradedLineMap` in
  `Sheaf.TraceFormula.GradedImmersionAmpleCriterion` has the equivalent affine-section
  input, but imports the parent `SpaceLineModuleProjMap`; importing that downstream
  theorem here would create a cycle. This module introduces no second bundled graded
  line-map notion: it binds the actual homogeneous sheaf maps and their algebra laws.
* `rg` across Mathlib and both project roots for every proposed helper and main
  declaration name found no duplicate declaration. Name fragments matched only unrelated
  projective-line chart modules. The full signatures and docstrings of the usable
  dependencies were read directly from their recorded source files.

No statement is disputed. No hollow definition, arbitrary comparison map, strengthened
geometric hypothesis, or theorem beyond the assigned node is introduced.

Validation: scompile.py passed for the delivered file in both sandbox (9.5 seconds)
and library (6.9 seconds) compilation, with no errors or warnings. The explicit
`lineProjRestrict` helper fixes the expensive inference of the affine-section
restriction by specifying its ambient category `T.Opens`; no compiler limit was raised.
The prescribed deliver2.py dry-run result is appended after it finishes.

Delivery dry run: `deliver2.py Q108 lem-trf-line-proj-affine-chart-atlas --no-push`
printed `OK (dry run): commit d924bb6a943 passes the preflight and compiles; nothing pushed`.
The packet changes the item's `lean` field only, plus its new module and this report.
The final source has one theorem and one `sorry`, no auto-bound variables, no lines
exceeding 100 columns, and no diagnostic commands. The Lean signature in the node
was checked verbatim against the source.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
