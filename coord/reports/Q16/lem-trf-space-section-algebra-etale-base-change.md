## Worker report

The module `Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.space_section_algebra_etale_base_change` with `sorry`.
Its six helper declarations package the section algebra and its normalized comparisons;
their data are explicit functions or structure fields, and no definition contains `sorry`
or selects an object from an existence theorem. They belong to the section-algebra notion
of this item, under the missing-helper authorization. No independent notion is introduced.
The original mathematical statement is unchanged.

Hypothesis and conclusion correspondence:

| Node text | Lean |
| --- | --- |
| Schemes S and T, and T over S | `S : Scheme.{u}`, `T : Over S` |
| Algebraic space X over S | `X : AlgebraicSpace S` |
| Morphism f:X to T over S | `f : X.obj.obj ⟶ yoneda.obj T`; this is exactly a natural transformation over S to the represented scheme |
| Quasi-compact and separated in the recorded terminology | `hqc : IsQuasiCompactPresheafMap f`, `hsep : IsSeparatedPresheafMap f` |
| Line module L on the small étale site | `L : X.Modules`, `hL : X.IsLineModule L` |
| The actual restriction of L to scheme tests | The recorded `lineTestFamily X L hL`; its descent universal property fixes it up to the unique cartesian isomorphism preserving the original small-étale module |
| Tensor powers, including O in degree zero | `(lineTestFamily X L hL).module W` followed by the existing `Scheme.Modules.tensorPow n`; its zeroth power is the monoidal unit |
| Homogeneous direct images | `SpaceSectionAlgebra.degree` and `sections`: on every Zariski open, sections are uniquely the compatible tensor-power sections on scheme tests lying over that open |
| Interpretation through the Zariski/étale equivalence | That inverse equivalence is restriction to Zariski opens. The chart-section limit in `sections` is exactly that restriction of module direct image. Étale tests identify the line-family sections with the given L; arbitrary tests are its recorded cartesian extension |
| Quasi-coherent graded Zariski algebra | `degree_quasiCoherent`, `graded : GradedSheafAlgebra degree`, and `total : QuasiCoherentAlgebra T.left` |
| Equality A = direct sum of homogeneous direct images | `inclusion` and `sum : IsColimit (Cofan.mk ...)`; the coproduct is in module sheaves, with no false claim that its sections are always pointwise finite sums |
| Multiplication and unit of that algebra | `mul`, `unit` specify the tensor-power products on all chart sections; `sum_mul`, `sum_unit` specify their extension to the total commutative algebra |
| Evaluation f* A to the sum of powers | `evaluation W n` are tensor-pullback sheaf maps. `sectionAlgebraImage` is evaluation on `1 ⊗ s`; linearity gives `a ⊗ s ↦ a s|_W`. `naturality` makes these maps cartesian. Summing the homogeneous counits gives the displayed evaluation, since pullback is a left adjoint |
| Every étale scheme map g:T' to T | `∀ (T' : Over S) (g : T' ⟶ T) (_ : Etale g.left)`; no surjectivity assumption |
| X' = X ×_T T', projections h and f' | An arbitrary presheaf `F'` and `IsPullback h f' f (yoneda.map g)`. The universal property implies it is isomorphic to the fibre-product algebraic space; this formulation allows every realization of the fibre product and does not assume a scheme source |
| L' is the restriction of L | `(lineTestFamily X L hL).pullback h`, the recorded literal precomposition, with the same test modules and pullback isomorphisms |
| Canonical graded base-change isomorphism | `SpaceSectionAlgebraBaseChange.degree` uses the actual scheme `tensorPullback g.left`; `total` and `inclusion` give its sum; `mul` and `unit` ensure it is an algebra comparison |
| Canonical normalization and compatibility of evaluation | The base-change `evaluation` equation compares the two images of every section on every scheme chart. It fixes the map on the `1 ⊗ s` generators. Linearity supplies all scalar multiples; varying opens and tests supplies all local tensor generators. Therefore it is equality of the pullback evaluations, including on the coproduct |
| Ordinary Zariski direct images and evaluation when the source is a scheme | `AgreesWithSchemes` quantifies over every `k : yoneda.obj U ⟶ F` with `IsIso k`. Its degree isomorphisms land in the existing Zariski `pushforward`; its equality identifies evaluation with the counit of `tensorPullbackSectionAdjunction`. The ordinary invertible module is the actual test-family module at k. The property is stated both for A and for every A' |

The section-limit characterization is not an arbitrary family of maps: `sections` has
existence AND uniqueness for every compatible family, and `naturality` says the displayed
evaluation projections themselves are compatible. Hence it determines every homogeneous
direct image and its evaluation up to its unique normalized isomorphism. The sum and
product equations then determine the graded algebra. A base-change comparison is likewise
fixed on every local tensor generator. It is not a mere nonempty isomorphism class.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`, `IsLineModule`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `IsSeparatedPresheafMap`, and the recorded étale-local theorem.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`: `QuasiCoherentAlgebra`,
  `Scheme.IsQuasiCoherentAlgebra`; its underlying module uses `CommAlgebraSheaf.toModule`.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction`, retaining the upstream `tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `IsInvertible`, `tensorPow`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: the recorded general
  site tensor interface, imported for the tensor-product proof dependency. The actual
  scheme tensor powers and `tmulSection` are those already used in the line realization.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `scheme_zariski_etale_quasiCoherent_equivalence`, with its restriction-to-opens and
  section-normalized unit/counit clauses, imported for the comparison proof.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `etale_module_pushforward_restriction` and its imported normalized chart-limit direct
  image, imported as the recorded proof dependency.
- Newly cited, already landed `def-trf-space-line-module-proj-input`, module
  `Sheaf.TraceFormula.SpaceLineModuleProjInput`: `SchemeTests`, `testToBase`,
  `TestLineFamily`, `TestLineFamily.powerMap`, `TestLineFamily.pullback`, `lineTestFamily`.
  This avoids duplicating line-module descent or arbitrary scheme pullback.

Proof-dependency modules without a recorded Lean declaration were not imported:
`def-trf-space-quasi-coherent-module`,
`lem-trf-space-qc-separated-quasi-coherent-pushforward`. They are proof inputs only;
the current statement uses existing scheme quasi-coherence and the section-limit
description of the specified direct image. No missing notion is treated as a wait.
The existing general ringed-topos adjunction/tensor lemmas and coproduct-closure theorem
are imported from `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, respectively. Their
recorded declarations are `SheafOfModules.module_pullback_pushforward_adjunction`,
`SheafOfModules.module_pullback_tensor_iso`, and
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma`; the proof docstring names
the exact uses.

Sources opened: local `spaces-properties.tex`, lemma-pushforward-etale-base-change-modules
(03LX), including its pullback footnote; `spaces-morphisms.tex`, the representable scheme
comparison preceding lemma-pushforward (03M9); `spaces-descent.tex`,
lemma-descending-property-ample (0D3C), the section-algebra, psi_d and graded-map paragraphs.
The statement is their étale-base specialization, as the existing node requests.

Edge cases checked before writing:

- `n = 0`: the actual scheme tensor power is O, the unit is present, and every
  base-change/evaluation equation quantifies over all natural degrees.
- Empty source, empty base and empty open: `sections` uses all compatible test families,
  including the unique empty-scheme sections; neither a point nor a nonzero section is
  assumed. `sum` is a categorical sheaf coproduct.
- Non-surjective étale g, and g = identity: both remain in the quantified cases.
- X and X' need not be schemes. A presheaf Cartesian realization retains the entire
  fibre-product algebraic space, rather than replacing it by an atlas.
- If either is a scheme, every representing isomorphism k is tested; the final comparison
  includes equality of the actual counits, rather than just object isomorphisms.
- No finite-type, Noetherian, ample, quasi-projective or representability condition on f
  is introduced, and no universe equality beyond the recorded algebraic-space size
  convention is imposed. All binders and universe u are explicit.

Searches made:

- `msearch.py ... leanfinder "The graded algebra of direct images of tensor powers of a
  line bundle on an algebraic space commutes with etale base change"`: eight hits,
  concerning étale tensor algebras, Kähler differentials and scheme base change;
  none states the algebraic-space graded section-algebra comparison.
- `msearch.py ... loogle '"GradedSheafAlgebra", "pushforward"'`: zero hits.
- `msearch.py ... grep 'sectionAlgebra|section_algebra|AlgebraicSpace' AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Graded sheaf algebra of sections of tensor powers of an
  invertible module on an algebraic space"`: unavailable, service rate limit
  `Rate limit exceeded: 60 per 1 minute`. No result was inferred from that failure.
- `rg` for `sectionAlgebra|section_algebra|lem-trf-space-section-algebra-etale-base-change`
  in the upstream `WeilConjectures` tree and project `lean/Sheaf`: no existing declaration
  states the item; hits are references to the intended theorem and unrelated affine
  fibre section-algebra results. Searches for `IsLineModule`, `GradedSheafAlgebra` and
  algebraic-space/scheme comparisons found the reused line-test realization and module
  direct-image/restriction APIs, whose full source signatures and docstrings were read.
- `tools/blueprint_refs.py search 'section algebra'`: zero blueprint-unit matches;
  ancestor is `lem-trf-local-term-locality`. DAG text search found the existing item,
  line-module Proj input, and scheme restriction nodes; none already states this theorem.
- `scompile.py --source` read the current published `GradedSheafStructures`,
  `QuasiCoherentAlgebra` and `CommAlgebraSheaf` modules, absent from the older local source.

No STATEMENT-DISPUTED flag, correction, new DAG node, or dependency-record repair.

Validation: `scompile.py` checked the module in sandbox and library positions.
An initial line-length warning was corrected. The first `deliver2.py --no-push`
passed compilation and server preflight (commit 77ddfcc86a); the required remaining
proof-dependency imports were then added. The final dry run also passed compilation
and server preflight (commit 8e0358f416), with no errors or warnings.
There is exactly one postponed theorem, with its full seven-step proof docstring.

## Second reading by Q16

No independent second worker was started: this dispatcher brief forbids starting
other agents, and the maintainer supplies the independent mathematical review.
The author reread the node and Lean together. The correspondence table above checks
every hypothesis and every clause. In particular it checks degree zero, the actual
line module, the sheaf coproduct, multiplication/unit, normalization on local tensors,
the canonical total comparison, and the ordinary Zariski counit equation. No hypothesis
or clause was changed. The only extra statement dependency is the already landed
canonical line-test realization, so the missing construction is reused rather than copied.

## Maintainer review fix (cc second reader, 2026-10-18)

The worker table says that `naturality` makes the evaluation maps cartesian. It does not:
`naturality`, `sections`, `mul` and `unit` constrain `evaluation W n` only through
`sectionAlgebraImage`, i.e. on global sections of tests lying over one open `V`. For a
test meeting several opens the sheaf map was otherwise free. Example: `X = T = P^1`,
`f = id`, `L = O(-1)`, test `P^1 × A^1 → P^1`: replacing its degree-1 evaluation by `0`
kept every field, `AgreesWithSchemes` and the base-change clause true. The fix adds the
field `evaluation_cartesian` to `SpaceSectionAlgebra`. It says that the evaluation of a test
is the tensor pullback of the evaluation of any test it maps to, through
`tensorPullbackCompositionIso`, `boundaryPullbackPowIso` and `boundaryTensorPowIso` of
`L.pullbackIso`. These are the same comparisons that `TestLineFamily.powerMap` and
`IsCoherent` use. With `sections` on the open subtests, every evaluation is now the
adjunction counit. The canonical counits satisfy it (Stacks 03D7, 0097), so the statement
is unchanged and is not stronger than the node. The structure and proof docstrings were
updated. The theorem signature is verbatim unchanged. The per-file compile is clean.
