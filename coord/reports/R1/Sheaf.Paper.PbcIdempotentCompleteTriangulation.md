## What changed

Replaced the sole proof hole in `AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation`
in `Sheaf.Paper.PbcIdempotentCompleteTriangulation`. Its signature and public imports are
unchanged. The proof applies `qbarScalarRep_rel` and `qbarScalarHom_mkHom` to the actual
`pbcQbarScalarCompatible` witness, retains the constructed Qbar-linear structure, and projects
the triangulation, idempotent-completeness and exact-equivalence assertions from
`pbcVerdierAxioms` and `pbcQbarIdempotentComplete`.

For the final scalar equation, a proved private generic stage-system helper expresses
the stage inclusion at E using `ι_map_eq`, computes Qbar multiplication with
`qbarScalarHom_mkHom` at M=N=E, simplifies the transported transition image by `tr_map`,
and applies semilinearity at E<=E. The helper is instantiated once for the concrete
coefficient system. The existing additive inclusion instance provides additivity, and
Verdier exactness supplies the exactness clause.

Updated the item's DAG proof, proof dependencies and proof origin to match this reuse of the
existing interfaces and the explicit final calculation. No new public declarations, definitions,
axioms, hypotheses or nodes are introduced. The current blueprint statement and proof were
read in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`.
The unit record has no realized statement or proof steps that this route would bypass.

Searches: LeanFinder returned triangle-category linear structures and homological-complex
idempotent-completeness, which do not state this varying-coefficient category result. Loogle
returned `toKaroubi_isEquivalence`, whose required idempotent completeness is already provided
by the stipulated `pbcQbarIdempotentComplete`. The remote grep returned zero matches; local
source search found the existing scalar quotient formulas, inclusion formula and `tr_map`.

## Proved and sorry left

The candidate proof replaces the one original hole:
`AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation`
(node `thm-weil-pbc-idempotent-complete-triangulation`). Zero holes added, zero split off,
and zero `sorry` tokens left in the candidate module. This uses existing named dependency
theorems; their remaining proof obligations are unchanged.

The retained generic calculation had one remaining equality between a scalar subtype
and its image under the identity field inclusion. Added `rfl` after the three interface
rewrites to close that equality. The main theorem statement text is unchanged and all
Lean lines have at most 100 characters.

Validation (2026-10-19): the direct compile succeeded in 14.4 seconds with no diagnostics.
The required delivery dry run passed compilation, the axiom probe, and preflight at
`a77288cdfa` (review class CODEX solely because a node file changes). The initial preflight
had flagged an added top-level universe `v` used only by the private helper. Restored the
original `universe w u` command and used `Category*` in the private helper, preserving its
generality without changing a public command or signature. The successful dry run validates
this repair. Static checks also confirm unchanged main theorem text and public imports,
100-character Lean lines, and proof dependencies equal to the union of step uses.
Several earlier requests received no answer from the compile server; retries through the
standard tool succeeded. No launcher tools or shared repository files were modified.

## No longer needed

Removed these private proof imports:

- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.Paper.FiniteStagePairCategory`
- `Sheaf.Paper.CommonStageCalculus`
- `Sheaf.Paper.PbcVerdierAxioms`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.IntrinsicQbarCategory`
- `Sheaf.Paper.PbcScalarExtension`

FiniteStagePairCategory, CommonStageCalculus and PbcVerdierAxioms remain available through
the retained public PbcQbarCategory import and are used by the proof. The lower coefficient
and tensor infrastructure required by that interface remains its responsibility; no claim
is made that those modules leave the entire targets' import closure.

Removed direct proof dependencies `def-weil-linear-scalar-localization`,
`def-weil-pbc-rational-category`, `lem-pur-derived-change-of-rings` and
`prop-weil-pbc-scalar-extension`: their scalar-transport calculation is already encapsulated
by `pbcQbarScalarCompatible`. Removed the corresponding obsolete top-level tool-use entries
`prop-weil-pbc-scalar-extension` and `lem-pur-derived-change-of-rings`. The common-stage
calculus tool use remains for the transition-image transport identity. The intrinsic-category
wrapper is not needed for this theorem about the published `pbcQbarCategory` interface.
No other node or module is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair is needed. The original proof plan expands scalar
semilinearity that the existing scalar-category interface already states, so the delivery
uses that declaration instead of duplicating the tensor and localization argument. The
current blueprint's final proof sentence also calls j_E Qbar-linear, although its domain
is E-linear; the assigned theorem correctly requests E-linearity and is preserved.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
