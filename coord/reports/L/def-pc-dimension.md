# def-pc-dimension (L, stage 2)

## Worker report

Worker W-dimx0530 for L, stage 2, item `def-pc-dimension`. Module written at
`lean/.sandbox/L/SchemeDimension.lean`, to land as `lean/Sheaf/AlgebraicGeometry/Dimension.lean`
(module `Sheaf.AlgebraicGeometry.Dimension`). Compiles clean with `tools/lean_file.sh` (group L,
1.5 s): only the `declaration uses sorry` warning of the comparison theorem.

### Clause by clause

- (1) "X a nonempty scheme; dim X = sup over x ∈ X of the Krull dimensions of O_{X,x}":
  `noncomputable def AlgebraicGeometry.Scheme.dim (X : Scheme.{u}) : WithBot ℕ∞ :=
  ⨆ x : X, ringKrullDim (X.presheaf.stalk x)`. Dependencies: `AlgebraicGeometry.Scheme`
  (def-pc-scheme), `ringKrullDim` (def-weil-pbc-krull-dimension-ring), stalks
  `X.presheaf.stalk x`. Nonemptiness: no hypothesis on the def (lead's preference); the docstring
  says the node assumes X nonempty, that the value then lies in ℕ∞ (local rings are nonzero), and
  that for the empty scheme the value is ⊥ = -∞, the convention the citers
  lem-pc-cartier-divisor-finite-over-field and lem-pc-degree-base-change need (lead_note).
- Comparison (not a clause, asked by the lead): `theorem Scheme.dim_eq_topologicalKrullDim
  (X : Scheme.{u}) : X.dim = topologicalKrullDim X` with `sorry`; docstring gives the proof via
  Mathlib `ringKrullDim_stalk_eq_coheight` (Properties.lean:376), `irreducibleSetEquivPoints`
  (Topology/Sober.lean:161), `Order.krullDim_eq_iSup_coheight` (Order/KrullDimension.lean:860).
  NOTE: this is exactly the statement of node lem-pc-scheme-dimension-local-rings; the lead may
  record it as that node's `lean` or drop it here to keep one statement per node.
- (2) "f : X → S of finite type, s ∈ S with nonempty fibre X_s; relative dimension = dim X_s":
  `noncomputable def Scheme.Hom.relativeDimAt {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
  WithBot ℕ∞ := (f.fiber s).dim`; fibre is Mathlib `Scheme.Hom.fiber` = `pullback f
  (S.fromSpecResidueField s)` (Fiber.lean:38; def-pc-scheme-fibre). Finite type and nonempty
  fibre are standing assumptions of the use, recorded in the docstring, not binders (⊥ on an
  empty fibre).
- (3) "f is of relative dimension d if every nonempty fibre has dimension d":
  `def Scheme.Hom.IsOfRelativeDimension (f : X ⟶ S) (d : ℕ) : Prop := LocallyOfFiniteType f ∧
  QuasiCompact f ∧ ∀ s : S, Nonempty (f.fiber s) → f.relativeDimAt s = d` (finite type as in
  def-weil-finite-type-morphism's record: `LocallyOfFiniteType ∧ QuasiCompact`). `Nonempty
  (f.fiber s)` elaborates to nonemptiness of the carrier `↥(f.fiber s)`. `d : ℕ` (a dimension
  "d" of a nonempty finite-type fibre is a natural number), cast into `WithBot ℕ∞`.

### Edge cases

Empty scheme: dim = ⊥ (sup of the empty family). Empty fibres: no condition in (3), value ⊥ in
(2). Zero ring stalks cannot occur (local rings). Universe: one `u` for X and S, as Mathlib's
`Scheme.Hom.fiber` requires.

### Searches

- grep `def.*dim\b|Scheme.dim|relativeDimension|def .*[dD]imension` in
  `WeilConjectures/AlgebraicGeometry`, `WeilConjectures/Mathlib/AlgebraicGeometry`: only
  `IsAbelianVariety.dim` (abelian varieties, ℕ); no scheme dimension.
- grep `ringKrullDim.*stalk|topologicalKrullDim|RelativeDimension|relativeDim` in Mathlib
  AlgebraicGeometry and `WeilConjectures/`: Mathlib `ringKrullDim_stalk_eq_coheight`; source
  `ringKrullDim_stalk_le_topologicalKrullDim` (WeilConjectures/Mathlib/AlgebraicGeometry/
  Properties.lean:281, inequality only); the source measures dimension by `topologicalKrullDim`
  and `topologicalKrullDimAt`, and relative dimension only by `SmoothOfRelativeDimension`
  (Mathlib Morphisms/Smooth.lean:135, smooth morphisms only, narrower than clause (3)) and
  `Algebra.IsStandardSmooth.relativeDimension` (rings). No declaration is literally clause (1),
  (2) or (3); `topologicalKrullDim X` is the same number only through the comparison theorem.
- Names: grep of `Scheme.dim`, `relativeDimAt`, `IsOfRelativeDimension`,
  `dim_eq_topologicalKrullDim` in Mathlib, `WeilConjectures/` and `dag/lean_names_upstream.json`:
  none. The node's stage-1 searches (LeanFinder, Loogle, grep; LeanSearch HTTP 500) found no match.

No STATEMENT-DISPUTED. Remark (lead_note): clause (3) is weaker than Stacks 02NJ (equidimensional
fibres); the docstring says so.

## Second reading by L

Independent review by R-dimx0533 (reviewer sub-agent of L): FIX (comparison theorem re-tagged to lem-pc-scheme-dimension-local-rings, recorded signature corrected); every clause matched.
