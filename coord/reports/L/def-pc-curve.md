# def-pc-curve (L, stage 2)

## Worker report

Worker W-cur0537 (group L). Module `Sheaf.AlgebraicGeometry.Variety` (sandbox
`lean/.sandbox/L/Variety.lean`, to land as `lean/Sheaf/AlgebraicGeometry/Variety.lean`) defines two
Prop-valued classes on the structure morphism `f : X ⟶ Spec (.of k)`, `k : Type u` a field,
`X : Scheme.{u}`. Compiles clean (no error, no warning) with `tools/lean_file.sh`.

Form of a `k`-scheme: the source repository's `AlgebraicGeometry.IsCurve`
(`WeilConjectures/AlgebraicGeometry/Curve.lean:75`) takes `(f : C ⟶ Spec (.of K))` and is a class
extending `IsSeparated f, LocallyOfFiniteType f, QuasiCompact f`; the same form is used here.

Clause by clause:
- "k a field" → `{k : Type u} [Field k]`; "X a k-scheme with structure morphism f : X → Spec k"
  (def-pc-scheme, def-weil-scheme-over-base, def-weil-affine-spectrum) → `{X : Scheme.{u}}`,
  `(f : X ⟶ Spec (.of k))` (Mathlib `Scheme`, `Spec`; the `X ↘ Spec k` of an `X.Over (Spec k)` is
  such an `f`).
- "X integral" (def-pc-integral-scheme) → field `isIntegral : IsIntegral X` (Mathlib).
- "f separated" (def-weil-proper-morphism, its separated clause) → `extends IsSeparated f`.
- "f of finite type" (def-weil-finite-type-morphism, match: `LocallyOfFiniteType f ∧ QuasiCompact f`)
  → `extends LocallyOfFiniteType f, QuasiCompact f`.
- variety (Tag 020D) → `class Scheme.Hom.IsVariety f`.
- "curve = variety of dimension exactly 1" (def-pc-dimension → `AlgebraicGeometry.Scheme.dim`,
  `Sheaf.AlgebraicGeometry.Dimension`, valued in `WithBot ℕ∞`) →
  `class Scheme.Hom.IsCurveOverField f extends f.IsVariety` with `dim_eq_one : X.dim = 1` (Tag 0A23).
- Remark on def-sc-curves: in the docstring of `IsCurveOverField`. `IsCurve` (recorded for
  def-sc-curves) asks only separated + finite type + `topologicalKrullDim C ≤ 1`: no integrality
  (empty, reducible, nonreduced allowed), dimension 0 allowed, and the blueprint takes `k`
  algebraically closed. `IsCurve` is only described, not imported.

Edge cases: empty `X` is excluded by `IsIntegral` (nonempty) and by `X.dim = 1` (`dim ∅ = ⊥`);
`Spec k` itself is a variety (dimension 0) but not a curve; no universe restriction beyond the
`Scheme.{u}`/`Type u` pairing that `Spec (.of k)` requires (same as the source's `IsCurve`).

Searches: `grep -rn 'IsVariety\|structure Variety\|class IsCurve\|IsCurveOverField\|IsStacksCurve'`
over Mathlib and `WeilConjectures/` → only the source's `class IsCurve` (Curve.lean:75, the
def-sc-curves convention, different); `dag/lean_names_upstream.json` has no `IsVariety`; the node's
stage-1 searches (LeanFinder, grep of Mathlib AlgebraicGeometry) found no scheme-level variety or
curve predicate. No existing declaration states the Stacks variety or curve, so a module is written.
Names `AlgebraicGeometry.Scheme.Hom.IsVariety`, `AlgebraicGeometry.Scheme.Hom.IsCurveOverField` are
absent from Mathlib and the source.

No STATEMENT-DISPUTED; no node fault.

## Second reading by L

Independent review by R-cur0541 (reviewer sub-agent of L): PASS; every clause matched.
