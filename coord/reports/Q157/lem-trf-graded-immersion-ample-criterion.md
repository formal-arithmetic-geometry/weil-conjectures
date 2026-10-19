## Worker report

The module `Sheaf.AlgebraicGeometry.GradedImmersionAmpleCriterion` states
`AlgebraicGeometry.Scheme.Modules.isAmple_of_graded_canonical_immersion`, with `sorry`
as its entire proof. Its docstring carries all five steps of the node's proof.
The only helper, `schemeLineTestFamily`, constructs the ordinary-scheme specialization
of the existing scheme-test interface, using the actual tensor pullbacks of L.
It does not introduce a second graded-map, generation-locus, or canonical-map definition.
All its data and comparison morphisms are written out, with no postponed helper theorem.

Clause-by-clause correspondence:

* Schemes Z, S and h : Z → S: `{S : Scheme.{u}} (Z : Over S)` packages the source
  `Z.left` and morphism `Z.hom` with no restriction on them.
* Quasi-compactness of h: `[QuasiCompact Z.hom]`. There is no finite-type,
  quasi-separatedness, separatedness, or properness assumption.
* The invertible O_Z-module: `(L : Z.left.Modules) [L.IsInvertible]`, using the
  recorded scheme invertibility predicate.
* The quasi-coherent graded commutative O_S-algebra:
  `(A : S.GradedAlgebraData)`, the existing affine-basis presentation used by the
  recorded relative Proj construction. Its graded algebra structures include scalar,
  unit, product, and coefficientwise base-change restriction data. There is no
  generation-in-degree-one assumption, and A's degree-zero structural algebra is
  unrestricted; in particular it need not equal O_S.
* The graded O_Z-algebra map from h-star A to the tensor powers of L is `ψ :
  AlgebraicSpace.GradedLineMap ... A (schemeLineTestFamily Z L)`.
  The base map is the Yoneda image of `Over.homMk Z.hom (Category.comp_id Z.hom)`
  to `Over.mk (𝟙 S)`. The existing `GradedLineMap.component`, `smul`, `one`,
  `mul`, `naturality`, and `restriction` encode the adjoint graded sheaf map on
  affine base charts. Each test module in the supplied family is literally
  `(tensorPullback (yoneda.preimage W.hom).left).obj L`; its transition iso is
  the existing normalized composition iso followed by transport along the test
  triangle. Thus the input is the given L on every test, not unrelated line data.
* U(ψ) is the union of positive-degree surjectivity loci, and equals Z:
  `(hgen : ψ.IsGenerationOpen ⊤)`. The recorded predicate tests exactly the union
  through local positive-degree sections that are free generators. At a rank-one
  local module, a surjective degree map has a generating image of a local homogeneous
  section; conversely such a generator makes the degree map surjective. Testing on
  all scheme maps expresses the same open subfunctor and includes the identity test.
* The canonical map to relative Proj is `(r : Z ⟶ AlgebraicSpace.projOver
  (Over.mk (𝟙 S)) A)` with `hr : ψ.IsCanonicalMap ⊤ (top.ι ≫ yoneda.map r)`.
  Here `top.ι` denotes the fully written top-subfunctor inclusion in the file.
  The target's underlying scheme is precisely A.relProj; its structural morphism
  is A.relProjHom followed by the identity of S. Thus r is a map over S.
  The reused canonical-map predicate fixes the homogeneous-fraction formula on
  every trivializing chart, not merely the structural triangle or an arbitrary map.
* The immersion hypothesis is `[IsImmersion r.left]`, on that canonical map.
* The conclusion over EVERY affine base open is `∀ V : S.Opens, IsAffineOpen V → ...`.
  The restricted module is exactly `(tensorPullback (Z.hom ⁻¹ᵁ V).ι).obj L`.
  The existential `hL` supplies its invertibility proof for the dependent argument
  of `@IsAmple`; the substantive conclusion is the recorded absolute ampleness
  predicate on the open subscheme `(Z.hom ⁻¹ᵁ V).toScheme`. Invertibility here is a
  consequence of the given L and supplies no additional assumption.

Dependency declarations and source inspection:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and its QuasiCompact import:
  `AlgebraicGeometry.QuasiCompact`, requiring compact inverse images of compact opens.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `IsInvertible.of_iso`, and `tensorPow`.
* `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`; and
  `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`.
  Both signatures/docstrings were read through `scompile.py --source`, because
  these modules are absent from the older source checkout.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.GradedAlgebraData`:
  `Scheme.GradedAlgebraData`, whose full structure was read; its quasi-coherence is
  the degreewise base-change property, equivalent to the two preceding sheaf notions.
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`: `relProj`, `relProjHom`,
  `relProjι`, and affine restriction identifications. These modules were read from
  the project's framework source. This is the dependency's recorded presentation.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSectionComp`, and the section-normalized adjunction.
  The adapter additionally uses the already imported `boundaryPullbackComparison`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` retains the
  recorded sheaf tensor construction; scheme powers are the existing `tensorPow`.
* `Sheaf.TraceFormula.SpaceLineModuleProjMap`: `space_line_module_proj_map`.
  Its publicly imported `SpaceLineModuleProjInput` supplies `TestLineFamily`,
  `GradedLineMap`, `IsGenerationOpen`, `IsCanonicalMap`, and `projOver`.
  All these definitions and the theorem's complete signature/docstring were read.
  The already landed node `def-trf-space-line-module-proj-input` is added to
  stmt_deps because the explicit adapter uses its interface directly.
* `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
* `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`, the absolute
  positive-tensor-power affine nonvanishing-cover definition, and `nonvanishingLocus`.
  This source was read from the framework checkout. The other upstream predicate
  `AlgebraicGeometry.IsAmple` is projective/very-ample and is deliberately not used.

The stated proof dependencies are imported without `public`:
`AmplePositiveTensorPower.isAmple_positive_tensorPow`,
`ProjCanonicalMapTwistComparison.exists_proj_canonical_map_twist_comparison`,
`ProjQcOpenTwistAmple.exists_common_degree_twist_ample`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion` with
`Scheme.Hom.exists_isCompact_isClosedImmersion`.
The proof-only node `lem-trf-ample-restrict-closed-immersion` has no Lean record yet,
so has no import to add at this time. It is not needed to type this statement.

Edge cases checked: empty source, empty base and empty affine open are allowed;
there is no `Nonempty` binder. A grading with no positive part cannot generate at
a point of a nonempty source, but the empty-source case is retained. Noetherianity,
finite generation and degree-one generation never occur in the signature. Weighted
gradings and A_0 different from O_S are included. All scheme tests use the same
standard scheme universe u, and no independently smaller test universe is introduced.
The conclusion uses all affine opens, rather than a chosen cover. Only the theorem
has `sorry`; the adapter has real data. No statement correction or dispute was found.

Searches for an existing statement and adapter:

* `msearch.py leansearch`, query “invertible sheaf ample when the canonical morphism
  to Proj of a graded algebra is an immersion”: eight hits, including `Proj`,
  `Proj.toSpecZero`, `Proj.fromOfGlobalSections`, and standard-chart results;
  no ampleness criterion.
* `msearch.py leanfinder`, query “An invertible sheaf is relatively ample if its
  everywhere-defined graded canonical morphism into relative Proj is an immersion”:
  eight Proj/chart hits, no matching criterion.
* `msearch.py loogle`, query `IsAmple, IsImmersion, Proj`: zero hits;
  reported unknown identifier `IsAmple` in Mathlib.
* `msearch.py grep`, regex `ample.*immersion|immersion.*ample|graded.*ample`
  under `AlgebraicGeometry`: zero hits.
* `rg` over the source `WeilConjectures` and project `lean/Sheaf`, regexes
  `graded.*immersion|immersion.*ample` and the item id: general Proj closed-immersion
  and projective/very-ample results only; none states this arbitrary-algebra criterion.
* `rg GradedLineMap|TestLineFamily|IsCanonicalMap lean/Sheaf` found the recorded
  generic space input and `SchemeAmpleCanonicalProjCriterion`. The latter concerns
  only the canonical section algebra and an open immersion, so is not this statement.
  Its scheme chart formulation was read for comparison. Reuse the generic interface
  instead of duplicating its definitions.
* `rg` for both new declaration names in Mathlib, source `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions.

Validation: `scompile.py Q157 lem-trf-graded-immersion-ample-criterion` compiled the
module both as the sandbox file and under its final library module path, cleanly
and within the standard 60-second per-file limit (about two seconds per file).
The source places were read directly in `literature/stacks-project/morphisms.tex`
(01VJ, including the full proof of (6) implies (1)) and `constructions.tex` (01O9).

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
