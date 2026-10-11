## Worker report

The module `lean/Sheaf/AlgebraicGeometry/VeryAmpleSeparationCriterion.lean` states
`AlgebraicGeometry.Scheme.veryAmple_of_divisor_dimension_drops`. Its only proof is `sorry`.
The theorem docstring carries all four proof steps of the node. The item is changed only
in `lean`; there is no statement correction and no new definition node.

Hypothesis and clause matching:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Curve C over k: `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`.
  `[IsConnectedCurve f]` supplies finite type, separatedness, nonemptiness, connectedness
  and dimension exactly one; `[Smooth f]` and `[IsProper f]` are precisely smoothness
  and properness over k. No GlobalSectionsBijective hypothesis is added.
- Line bundle M: `(M : C.Modules) [M.IsInvertible]`, the recorded scheme-module class.
- Every rational point P: `∀ P : closedPoints C`. Over algebraically closed k, closed
  points and k-rational points correspond bijectively by the Nullstellensatz; each
  closed point has residue field k and a unique k-rational parametrization. Thus this
  changes the representation of points, not the quantifier or objects covered.
- M(-P): `M ⊗ Divisor.moduleOfSmoothConnectedCurve k C f (Finsupp.single P (-1))`.
  This uses the actual divisor module, not a copied definition or unnamed ideal twist.
- First dimension drop: `h₁` is the finrank of the above global section module plus
  one equal to the finrank of M's global sections. This is exactly h0(M(-P))=h0(M)-1
  as an integer dimension equality, avoiding false natural-number truncated subtraction.
- Every pair, possibly coinciding: `∀ P Q : closedPoints C`, without `P ≠ Q`.
- M(-P-Q): divisor module of `Finsupp.single P (-1) + Finsupp.single Q (-1)`, tensored
  with M. At P=Q this is the coefficient -2 at P, not a reduced two-point subscheme.
- Second dimension drop: `h₂` is the finrank of this section module plus two equal
  to the finrank of M's section module.
- H0 and its k-vector-space structure: global sections are `F.val.obj (Opposite.op ⊤)`;
  `ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom` restricts
  scalars along the actual structure map k→Γ(C,O_C). H0 is global sections; no alternate
  positive-degree cohomology definition or arbitrary scalar structure is introduced.
- Degree convention: the point divisor is `Finsupp.single P 1` in the recorded divisor
  group. Its degree is one by `Scheme.Divisor.degree_single`. The theorem contains no
  degree hypothesis or Pic0 conclusion, so adding `picZero` or a degree equation to the
  Lean signature would add a clause absent from the node.
- Very ample conclusion: `IsVeryAmpleCompleteLinearSystem k C f M`, the dependency's
  complete-linear-system notion. It expands to a finite basis `b` of ALL global
  sections, a family `s : I → M.sections` with top-open values `b i`, generation
  `hs : Epi (M.freeHomEquiv.symm s)`, closed immersion of the recorded
  `ProjectiveSpace.homOfGeneratingSections I f M s hs`, and an isomorphism of the
  tensor pullback of `ProjectiveSpace.twist I (Spec (.of k)) 1` with M. Choosing a
  finite coordinate basis identifies the target with P(H0(M)^dual), as in the node.
  Existence of a basis of the whole space ensures every section comes from a linear form.
  This does not replace the complete system by an arbitrary embedding.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve`, with their full class fields.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, with local triviality field.
- `Sheaf.AlgebraicGeometry.DivisorModule`:
  `AlgebraicGeometry.Scheme.Divisor.moduleOfSmoothConnectedCurve` and its underlying
  section-condition/module construction. Its instances derive integrality, regularity
  and Noetherianness from the curve assumptions, so none are added to the theorem.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`: `Scheme.Divisor`,
  `Scheme.Divisor.degree`, and `Scheme.Divisor.degree_single` for the point convention.
- `WeilConjectures.AlgebraicGeometry.Curve`: `Scheme.Hom.picZero` and `picDegree`
  were read; neither is needed in this degree-free signature.
- `WeilConjectures.AlgebraicGeometry.Modules.Ample`: `AlgebraicGeometry.IsAmple`
  and `AlgebraicGeometry.IsVeryAmple` were read. Their record is repaired below.
- Existing projective-space data is reused from
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`
  (`AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`),
  `Sheaf.AlgebraicGeometry.ModulePullbackTensor` (`Scheme.Modules.tensorPullback`),
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` (`ProjectiveSpace.twist`),
  and the source's `SheafOfModules.tensorPow`. Mathlib supplies `Module.Basis`,
  `Module.finrank`, `ModuleCat.restrictScalars`, `Finsupp.single`, `IsClosedImmersion`.

Edge cases checked before drafting: the empty scheme and Spec k are excluded by the node's
connected dimension-one curve assumption, not by additional binders. The repeated-point
case is included and measures order-two vanishing. Dimension zero/one cannot satisfy the
second drop on a nonempty curve; addition rather than truncated subtraction preserves
this. All characteristics are permitted. Finite coordinate types can be empty in the
general definition; the empty proper scheme has zero sections and its complete system
has an empty basis. No finiteness assumption on section spaces is added: it is provided
by properness and line-bundle coherence. Universe u allows arbitrary fields and curves
in that universe; the finite coordinate type also lives in u.

Searches (logged in searches.jsonl):

- LeanSearch: "dimension drop twisting by one and two points implies very ample line
  bundle on smooth proper curve" returned HTTP 500/Internal Server Error. Unavailable;
  no absence conclusion is drawn from this service.
- LeanFinder: "very ample line bundle criterion dimension of global sections after
  subtracting points" returned eight unrelated convex, projective-cardinality,
  polynomial-rank and basic-open hits; no matching statement.
- Loogle: `"VeryAmple"` returned zero declarations.
- msearch grep, AlgebraicGeometry: `VeryAmple|separat.*tangent` returned zero hits.
- LeanFinder: "very ampleness defined by closed immersion of the complete linear system
  of all global sections" returned eight general closed-immersion results, no definition
  of complete-linear-system very ampleness.
- msearch grep, AlgebraicGeometry: `complete.*linear.*system|IsVeryAmple` returned zero hits.
- rg in the source RiemannRoch module found
  `Scheme.isVeryAmple_of_finrankH_zero_tensorObj_toModules_ker`: its ideal twists,
  added GlobalSectionsBijective hypothesis and unspecified IsVeryAmple conclusion
  do not literally state this node. Source grep for the item id returned no result.
- rg in `lean/Sheaf/AlgebraicGeometry` found `CompleteLinearSystemClosed.lean` and
  `PointTangentSeparationClosedImmersion.lean`: these are subsystem-to-complete and
  point/tangent-separation theorems, not divisor dimension-drop criteria or standalone
  definitions of the complete-system notion.
- rg for `complete.*linear.*system|def IsVeryAmple|def IsAmple` in project and source
  found source existential IsVeryAmple, IsAmple and those theorem docstrings.
- rg for all three proposed declaration names in Mathlib, source, project and
  `dag/lean_names_upstream.json` returned no collision.

Source: the local Stacks checkout was absent; read the actual tag at
https://stacks.math.columbia.edu/tag/0E8S. It concludes that the canonical section
morphism is a closed immersion. The node adds an explicit base-point-free dimension
condition, covering the generation prerequisite. No mathematical fault is alleged.

## Dependency modules

`def-sc-ample` receives `lean/Sheaf/AlgebraicGeometry/CompleteLinearSystemAmple.lean`.
Only its `lean` record changes, with the required `note`.

The old `AlgebraicGeometry.IsAmple` record uses `AlgebraicGeometry.IsVeryAmple`, which
asserts existence of an unspecified projective closed immersion. The node expressly
asks for the complete linear system, with all sections coming from linear forms.
The separate complete-system predicate is necessary to render that clause literally;
it does not redefine the underlying modules, projective spaces, twists, pullbacks,
sections or canonical section morphisms.

`AlgebraicGeometry.IsVeryAmpleCompleteLinearSystem` renders the very ample clause by
exactly the finite basis/sections/generation/closed-immersion/pullback data above.
`AlgebraicGeometry.IsAmpleCompleteLinearSystem` renders the ample clause by
`∃ m : ℕ, 1 ≤ m ∧ IsVeryAmpleCompleteLinearSystem k C f (M.tensorPow m)`.
Both take the node's proper scheme over a field and line-bundle hypotheses. No
algebraic closedness or curve assumption is inserted in these general definitions.
Both definitions have full data and no sorry; the only sorry in this delivery is the
item's theorem. The module imports the existing Ample module for properness,
invertibility and tensor-power infrastructure, and the recorded projective morphism
module and Mathlib basis definitions.

Validation: the item alone initially compiled in 2.9 seconds. The final two-module
server compile passed with exit code 0 in 2.6 seconds and no warnings. Distinct explicit
universe names avoid the remote compiler's concatenation collision; all binders are
explicit and autoImplicit is disabled.

## Second reading by U1

The node introduces an algebraically closed field `k`, a scheme `C` with structure map
`f : C ⟶ Spec (.of k)` carrying connected-curve, smooth, and proper instances, and an
invertible `C.Modules` object `M`. The Lean binders in
`VeryAmpleSeparationCriterion.lean` render these objects exactly; `IsConnectedCurve f`
provides the curve conditions without adding hypotheses. The first hypothesis quantifies
all `P : closedPoints C` and states `Module.finrank` of the scalar-restricted global
sections of `M ⊗ moduleOfSmoothConnectedCurve ... (Finsupp.single P (-1))`, plus one,
equals that of `M`. This is the node's `M(-P)` drop. The second quantifies all ordered
pairs `P Q`, including equality, uses the sum of the two single-point divisors, and adds
two to the same `finrank`; this is exactly the `M(-P-Q)` drop, including order-two
vanishing when `P = Q`. The conclusion is
`IsVeryAmpleCompleteLinearSystem k C f M`, whose dependency module explicitly gives a
finite basis of all global sections, generation, closed immersion, and pullback of the
projective twist. Thus it renders the node's complete linear-system very-ampleness
clause. Quantifier order and scalar structure agree, and no degree, Picard, global
sections bijectivity, Noetherian, or characteristic hypothesis was added.

Edge cases checked: repeated points are included; all characteristics are allowed; the
connected dimension-one curve assumptions exclude the empty and zero-dimensional scheme
cases; additive equalities avoid truncated subtraction; arbitrary universe `u` is used
consistently; the finite basis index in the complete-system predicate may be empty.

I searched the project, source repository, and Mathlib with grep, LeanFinder/Loogle, and
LeanSearch (the latter unavailable); no exact criterion or complete-system declaration
was found. The source Tag 0E8S and the recorded blueprint statement were read. No
mismatch was found and no source or Lean statement was changed. The only delivery
addition is the dependency module `CompleteLinearSystemAmple.lean`, required because the
old `IsVeryAmple` notion allowed an unspecified subsystem rather than the complete
linear system.
