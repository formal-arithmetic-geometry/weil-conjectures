## Worker report

The module `Sheaf.TraceFormula.LocalDimensionFormula` defines the canonical
function-field algebra structure induced by a dominant scheme morphism and states
`AlgebraicGeometry.local_dimension_formula` with a postponed proof.

The hypotheses and clauses of the node are rendered as follows. Integral schemes
are `[IsIntegral X]` and `[IsIntegral S]`. The morphism is
`f : X ⟶ S`, locally of finite type by `[LocallyOfFiniteType f]`, dominant by
`[IsDominant f]`, and the locally Noetherian target by `[IsLocallyNoetherian S]`.
The point is `x : X`, with `s` represented by `f x`. The local dimensions are
`ringKrullDim (X.presheaf.stalk x)` and
`ringKrullDim (S.presheaf.stalk (f x))`, using the recorded module-stalk and
Krull-dimension notions. The generic stalks are the existing abbreviations
`S.functionField` and `X.functionField`, definitionally the stalks at the
scheme generic points. The helper
`Scheme.Hom.dominantFunctionFieldAlgebra f` is the stalk map transported along
the generic-point equality supplied by dominance. The residue-field term uses
`f.residueFieldMap x` and the recorded `Algebra.trdeg` notion. Since subtraction
is not an operation on `WithBot ℕ∞`, the displayed source inequality is rendered
in the equivalent finite-dimension form
`dim O_X,x + trdeg_{κ(s)} κ(x) ≤ dim O_S,s + trdeg_{R(S)} R(X)`.

Dependency declarations used: `AlgebraicGeometry.IsIntegral` from
`Mathlib.AlgebraicGeometry.Properties`; `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.QuasiCompact` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; `AlgebraicGeometry.IsLocallyNoetherian`
from `Mathlib.AlgebraicGeometry.Noetherian`; `TopologicalSpace.IsGenericPoint`
from `Mathlib.Topology.Sober`; `AlgebraicGeometry.Scheme.residueField` and
`Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`;
`Algebra.trdeg` from `Mathlib.RingTheory.AlgebraicIndependent.Basic`; and
`ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic`.
The affine-dimension and localization statements are statement-only dependencies
with no Lean declarations yet, so no private copies were introduced.

Edge cases checked: the identity morphism gives equality and zero generic and
residue transcendence terms; a polynomial extension over a field gives the usual
local dimension bound; finite algebraic extensions have zero generic
transcendence degree; and the generic-point map is well-defined for every
integral nonempty scheme. The generic-point helper does not exclude zero
transcendence degree or zero-dimensional local rings.

Searches made: `msearch.py ... leanfinder "local dimension formula for a locally finite type morphism of integral schemes over a locally Noetherian base"` returned only generic locally-Noetherian and stalk declarations, no scheme formula; `msearch.py ... loogle "ringKrullDim, Algebra.trdeg, Ideal.height"` returned 0 hits; `msearch.py ... grep "dimension-formula|ringKrullDim.*trdeg|height.*trdeg" AlgebraicGeometry` returned no exact match; `msearch.py ... leansearch "dimension inequality for a finite type morphism of integral schemes locally Noetherian"` returned only topological monotonicity and ring height bounds. `rg` over `WeilConjectures/` and project `lean/Sheaf` found no declaration of this item. The existing `Scheme.functionField`, residue-field, generic-point, and dimension declarations were read and reused.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Statement corrected

The original statement used the source subtraction display. Lean has no subtraction on `WithBot ℕ∞`, so the statement is rendered by the equivalent additive inequality, retaining both transcendence-degree terms. The source is Morphisms Tag 02JU, equation (dimension-formula). The sole citer `lem-trf-closed-dominant-dimension` still holds: its proof drops the nonnegative residue term after applying this additive inequality.

## Second reading by Q11

I reread the node, Stacks Morphisms Tag 02JU, and the module. Every source
hypothesis is present: integral source and target, locally Noetherian target,
locally finite type, dominance, and a chosen point. The local, generic, and
residue terms use the same schemes and points as the node. The only Lean
normalization is the additive form of the subtraction inequality because
`WithBot ℕ∞` has no subtraction; the source terms are finite under the stated
Noetherian and finite-type hypotheses. The canonical generic stalk map is
explicitly transported along the equality of generic points, so it is not an
arbitrary algebra structure. Compilation with `scompile.py` is clean with only
the expected postponed proof.
