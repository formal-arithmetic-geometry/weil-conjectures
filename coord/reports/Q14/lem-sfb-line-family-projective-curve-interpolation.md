## Worker report

The module `Sheaf.AlgebraicGeometry.LineFamilyProjectiveCurveInterpolation` states
`AlgebraicGeometry.exists_projectiveCurve_lineFamily_fibres`, with one `sorry` and no
new definitions. Its docstring contains all five steps of the node's assembled proof.
Only the item's `lean` field changes. No new node, dependency replacement, or statement
correction is needed.

Hypothesis and conclusion audit:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Z and S are k-schemes | `Z S : Scheme.{u}` with `Z.Over (Spec (.of k))` and `S.Over (Spec (.of k))` |
| Z is smooth | `Smooth (Z ↘ Spec (.of k))` |
| Z is separated | `IsSeparated (Z ↘ Spec (.of k))` |
| Z is finite type | `LocallyOfFiniteType (Z ↘ Spec (.of k))` and `QuasiCompact (Z ↘ Spec (.of k))` |
| S is smooth | `Smooth (S ↘ Spec (.of k))` |
| S is separated | `IsSeparated (S ↘ Spec (.of k))` |
| S is finite type | `LocallyOfFiniteType (S ↘ Spec (.of k))` and `QuasiCompact (S ↘ Spec (.of k))` |
| S is nonempty and connected | `ConnectedSpace S`; this extends `PreconnectedSpace S` and includes `toNonempty` |
| s0,s1 are k-rational points | `(s0 s1 : (S ↘ Spec (.of k)).fieldPoints k)`; these are sections |
| L is a module on Z times S | `(L : (pullback (Z ↘ Spec (.of k)) (S ↘ Spec (.of k))).Modules)` |
| L is invertible | `[Scheme.Modules.IsInvertible L]` |
| There is a smooth projective curve C over k | `∃ (C : Scheme.{u}) (f : C ⟶ Spec (.of k)), IsSmoothProjectiveCurve f ∧ ...`; the class extends `IsIntegralCurve`, `Smooth`, and `IsProjective`, and includes dimension one, integrality, separatedness, and finite type |
| C is geometrically integral | `GeometricallyIntegral f` |
| a,b are k-rational points | `∃ (a b : f.fieldPoints k) ...` |
| E is an invertible module on Z times C | `(E : (pullback (Z ↘ Spec (.of k)) f).Modules)` and `Scheme.Modules.IsInvertible E` |
| E_a is isomorphic to L_s0 | First `Nonempty` of a module-category isomorphism between the two displayed tensor pullbacks |
| E_b is isomorphic to L_s1 | Second `Nonempty` of a module-category isomorphism between the two displayed tensor pullbacks |
| Fibres are tensor pullbacks | Both isomorphisms use `Scheme.Modules.tensorPullback`, never the unrelated `Modules.pullback` functor |
| The two curve points need not differ | No inequality or distinctness binder |
| No properness, integrality, affineness, dimension restriction on Z | No such hypothesis appears |

For a point `p : f.fieldPoints k`, `f.fieldPointBaseChange p (Over.mk (Z ↘ Spec (.of k)))`
has source Z and target C times Z. Composing with
`(pullbackSymmetry f (Z ↘ Spec (.of k))).hom` has target Z times C, with first projection
identity and second projection the composite Z -> Spec k -> C. Thus it is exactly the fibre
inclusion z -> (z,p). The identical construction for S yields the required original fibres.
The rational-point base-change projection formulas and pullback-symmetry formulas were read
in their source files. There is no arbitrary comparison map or choice of an isomorphism
substituted for these inclusions.

Statement dependency declarations used (full signatures and docstrings inspected):

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  as explicitly included in that node's `mathlib_match.how`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` in Mathlib's `Morphisms.FiniteType` and
  `Morphisms.QuasiCompact`; the conjunction is the node's recorded finite-type convention.
- `def-pc-rational-point`: recorded `Scheme.Hom.baseChangeFieldPoint` in
  `WeilConjectures.AlgebraicGeometry.DensePoints`; the general induced section is the same
  node's `Scheme.Hom.fieldPointBaseChange` in
  `WeilConjectures.AlgebraicGeometry.Picard.RationalPointBaseChange`, including its
  `_fst`, `_snd`, and `fieldPoints_comp_eq_id` formulas. Both modules are public imports.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullbackSymmetry` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-pc-smooth-projective-curve`: `AlgebraicGeometry.IsSmoothProjectiveCurve` in
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`.
- `def-pc-module-pullback`: `AlgebraicGeometry.Scheme.Modules.tensorPullback` in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, publicly provided by the recorded
  module `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, which is imported.

All presently recorded proof-dependency modules and Mathlib-match modules are imported
without `public`. Three proof dependencies currently have no Lean record or Mathlib match:
`lem-sfb-integral-variety-smooth-curve-interpolation`,
`lem-trf-geonormal-geoconnected-finite-type-integral`, and
`lem-sfb-invertible-extension-factorial-complement`; their statements are not needed to type
this theorem, and their proof steps remain in the docstring for stage 3.

Source checks: opened Charles--Poonen Corollary 1.9 (printed p.4), which supplies a curve
through a finite set in positive dimension; opened Milne I.3.5(a,b), printed p.18 (PDF p.24),
for smooth completion and normalization; read Stacks divisors.tex
`lemma-extend-invertible-module` (Tag 0BD9) in full. The latter applies to a locally
Noetherian scheme with factorial local rings on the complement; it imposes no integrality
or connectedness hypothesis. These are the sources named by the node, an assembled result.

Edge cases checked:

- Empty Z: there is no nonemptiness binder on Z and the pullbacks and module categories
  remain defined; the conclusion still has its intended meaning.
- Disconnected or nonproper Z: no connectedness, integrality, or properness hypothesis;
  smoothness supplies local regularity componentwise for the extension argument.
- Coincident s0,s1 and coincident a,b: both are permitted; each fibre isomorphism is retained.
- Zero-dimensional S: a connected smooth finite-type scheme over the algebraically closed
  field is a point. A constant family over the projective line realizes both fibres;
  the statement does not assume positive parameter dimension.
- Positive characteristic: no characteristic-zero or separability restriction is added.
- Universes: every universe is explicitly bound (`universe u`), both auto-implicit options
  are false, and there is no independent smaller test-field universe.

Searches (run through the prescribed msearch wrapper with this group and item):

- LeanFinder query: "Two fibres of an invertible sheaf family over a smooth connected
  variety are realized by a family over a smooth projective geometrically integral curve".
  Eight results: affine-transition limits, scheme-cover point lifting, pointsPi,
  scheme fibres, and affine space. None states line-family curve interpolation.
- Loogle query: `AlgebraicGeometry.IsSmoothProjectiveCurve, AlgebraicGeometry.Scheme.Modules.IsInvertible`.
  Zero hits; the service does not index the project's `IsSmoothProjectiveCurve` identifier.
- Mathlib grep query: `line.family|projective.curve.*interpol|curve.*family`, scoped to
  AlgebraicGeometry: zero hits.
- LeanSearch query: "Two fibres of a line bundle family over a smooth connected variety
  can be realized over a smooth projective curve". Eight results, all scheme fibre or
  topological fibre-bundle declarations; none asserts the required geometric existence.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `line.family|projective.curve.*interpol|algebraicEquiv|algebraically.trivial` found
  existing line algebraic equivalence and abelian-variety material, not this theorem.
  A separate exact node-id and declaration-name search found no existing declaration.
  The new theorem does not replace the weaker/different algebraic-equivalence predicate.

Validation: prescribed scompile.py succeeded for the sandbox and library module, with no
errors or warnings. All theorem proof content is the single `sorry`.
No STATEMENT-DISPUTED issue and no node correction.

## Second reading by Q14

A separate second pass by the same worker reopened the node and completed the clause audit
above; the dispatcher explicitly prohibits starting other agents. The maintainer's
independent delivery review remains required. Checked the order of pullback factors and the
target of every point-section composite, both isomorphism clauses, and that
`ConnectedSpace` includes nonemptiness. Checked the upstream curve class really includes
integrality and dimension one, and geometric integrality is an additional explicit clause.
No mismatch or statement change was found. The source proof's zero-dimensional parameter
case is covered by a constant projective-line family, as recorded above.
