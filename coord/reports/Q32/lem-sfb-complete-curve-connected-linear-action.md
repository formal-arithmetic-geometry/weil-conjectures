## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.CompleteCurveConnectedLinearAction` states
`AlgebraicGeometry.complete_curve_connected_linear_action`, with its sole proof `sorry`.
No definition, helper theorem, new node, dependency repair or statement correction is needed.
The copied node differs from the shared node only in `lean`.

I read Milne, Algebraic Groups (2017), printed p.408 (PDF p.420), especially 20.2,
20.3 and Proposition 20.5 with its proof. The proposition is precisely the smooth
complete curve classification used here. The accepted DAG split uses the coordinate
path in a split solvable group in place of passing a nontrivial action through a
solvable series; the module docstring retains all eight accepted proof steps and
their node citations. I also read the latest blueprint direct-images proof,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3), the ancestor recorded by the node. This prerequisite is not the unit's
own statement. The stage-2 handoff paragraph in brief-stage2 section 0 resolves
the inherited stage-1 stale-dispatch ending: preserve Q15's accepted split and
attach its Lean statement. The live queue lists this node at stage 2; it has no
Lean record, and no item-specific repair note exists.

Clause-by-clause correspondence:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
  There is no characteristic binder or separability hypothesis.
- Both F-schemes are `(H C : Over (Spec (.of F)))`. Their underlying schemes are
  `H.left`, `C.left`, and their actual structure maps are `H.hom`, `C.hom`.
- The group scheme structure is `[GrpObj H]`, using the recorded group-object
  interface, including its actual multiplication, unit and inverse and their laws.
- Affineness of the acting group is `[IsAffine H.left]`. Its finite type is the
  pair `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, exactly the recorded
  finite-type convention.
- Smoothness and connectedness of H are `[Smooth H.hom] [ConnectedSpace H.left]`.
- Smoothness, properness and integrality of the curve are
  `[Smooth C.hom] [IsProper C.hom] [IsIntegral C.left]`. Its finite type is already
  included in properness: `IsProper` extends `LocallyOfFiniteType`, and
  `UniversallyClosed` supplies `QuasiCompact`. No additional curve-class predicate
  is imposed. Its dimension is `(hdim : topologicalKrullDim C.left = 1)`.
- The actual F-morphism a is `(a : H ⊗ C ⟶ C)`. The canonical cartesian monoidal
  structure on `Over (Spec (.of F))` is constructed from pullbacks, so this is
  exactly H ×_F C → C, with compatibility with the base structure maps built in.
- The action unit identity is
  `MonObj.one (X := H) ▷ C ≫ a = (λ_ C).hom`. It says that acting by the identity
  gives the canonical identification Spec F ×_F C → C.
- The multiplication identity is
  `MonObj.mul (X := H) ▷ C ≫ a = (α_ H H C).hom ≫ H ◁ a ≫ a`.
  Both sides have domain (H ×_F H) ×_F C; they say (hh')x = h(h'x).
- Nontriviality is `(hnontrivial : a ≠ CartesianMonoidalCategory.snd H C)`.
  This compares morphisms of schemes over F, as required, without replacing it
  by an action on only rational points. Equality in Over is equivalent to equality
  of the underlying morphisms, since the over-map compatibility is a proposition.
- The conclusion is an existential scheme isomorphism
  `e : C.left ≅ ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of F))` with
  `e.hom ≫ (ProjectiveSpace ... ↘ Spec (.of F)) = C.hom`.
  This asserts an F-isomorphism, not just an absolute scheme isomorphism.
  `ULift.{u} (Fin 2)` has exactly the two homogeneous coordinates {0,1}, lifted
  to the universe required by the dependency. The projective scheme is the
  dependency's integral-Proj base-change construction, not a replacement model.
  The inverse is automatically over F by the isomorphism equations.
- The opening convention about closed subgroup schemes has no separate subgroup
  variable in this statement. It introduces no additional hypothesis to encode.
  Its recorded module is publicly imported; Borel subgroups occur only in the
  proof plan. In particular, the result does not require a chosen Borel as data.

Recorded statement dependencies and the declarations used (their full source
signatures and defining docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, through its Basic import:
  `IsAlgClosed`; no chosen algebraic closure is required by this item.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, whose parent is
  `CategoryTheory.MonObj`; unit and multiplication are `MonObj.one`, `MonObj.mul`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` give the closed-subgroup
  terminology in the convention; the module also documents GrpObj on Over.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` (available through the
  public statement-dependency imports).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and
  `ProjectiveSpace.over`; this is the exact base-change projective-space notion.

Auxiliary categorical expressions are existing Mathlib morphisms, not new
definitions: tensor, whiskering, unitors and associator from MonoidalCategory;
`CartesianMonoidalCategory.snd`; and the canonical cartesian monoidal structure
on Over, whose tensor is the pullback of the two structure maps.
The instance for schemes over a base is in `Mathlib.AlgebraicGeometry.Pullbacks`;
its chosen products are `CategoryTheory.Over.cartesianMonoidalCategory` from
`Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.

All currently recorded proof-dependency modules are imported without `public`:
SpaceSmoothReducedLocality, SplitSolvableTorsorsAndVariety, StandardGroupSchemes,
ProjectiveLineGenusZero, SmoothConnectedCurveLocalRings,
ProjectiveSpaceStandardCharts, Curve.ProperFunctionFieldMorphisms, and the
Mathlib modules AlgClosed.Basic, FunctionField, Morphisms.Separated,
Limits.Shapes.Pullback.HasPullback and FieldTheory.RatFunc.Luroth.
The finite-type/proper/spectrum modules are already public statement imports.
The following proof nodes have no recorded Lean module or Mathlib match, so
there is currently no module to import for them: lem-sfb-stack-smooth-permanence,
lem-sfb-borel-conjugation-cover, lem-sfb-curve-nonconstant-generic-criterion and
lem-sfb-curve-function-field-arithmetic. They are not needed to type this statement.

Edge cases checked before writing:

- The empty curve is excluded by IsIntegral, and also by dimension one; no
  nonempty hypothesis was inserted. ConnectedSpace uses the recorded nonempty
  definition, excluding an empty acting group.
- The trivial group and a trivial action do not satisfy nontriviality; no
  faithfulness, transitivity, positive group dimension or chosen moved point is
  assumed. A nonfaithful but nontrivial action remains included.
- Positive characteristic, including inseparable orbit maps, is included.
  The proof plan explicitly avoids needing separability in the Lüroth argument.
- Two homogeneous coordinates give a line, rather than using a singleton or
  three-coordinate index. ULift changes only the universe, not the finite set.
- All objects lie in the same ambient Scheme universe u as Spec F, consistent
  with the recorded scheme APIs. `universe u` and `autoImplicit false` make every
  universe and variable explicit; no small test-object quantification is used.
- The two action identities are equations of morphisms over F, including scheme
  structure, not equations just of underlying sets or F-rational points.

Searches for an existing statement:

- msearch LeanFinder: "A smooth proper integral curve over an algebraically
  closed field with a nontrivial action of a smooth connected affine algebraic
  group is isomorphic to the projective line". Eight results concerned
  Weierstrass curve models and their coordinate changes, not this statement.
- msearch Loogle: `"ProjectiveLine"`. No results.
- msearch LeanSearch: "A smooth proper curve with a nontrivial action of a
  connected affine algebraic group is isomorphic to the projective line".
  Eight results concerned point-set projective lines, proper topological
  actions and Weierstrass variable changes; none classified scheme curves.
- msearch grep in Mathlib/AlgebraicGeometry:
  `homogeneous.*curve|curve.*homogeneous|nontrivial.*action.*curve`.
  Five results were descriptions of homogeneous Weierstrass formulas.
- Direct rg of WeilConjectures, Sheaf and the upstream name index for
  `complete_curve_connected_linear_action`, the node id, and connected-linear
  curve/action phrases found no existing declaration. Broader searches for
  `connected.*linear|complete.*curve|curve.*[Aa]ction` found unrelated
  constructible-module descent and stable-curve constructions.
- Direct source inspection found GrpObj and the cartesian structure on Over.
  Mathlib's ModObj already packages the same two action equations; here they
  are ordinary hypotheses on the node's given morphism a, so no second action
  definition or extra DAG notion is introduced.

No statement dispute or mathematical node fault was found. The previously
recommended CompactObject example in Sheaf is withdrawn; its node now records
the identical upstream WeilConjectures module, which I read instead.

Validation: scompile.py compiled this module both in the sandbox and at its
library module name, with no errors or non-sorry warnings (1.9 s and 1.8 s).
The delivered theorem remains intentionally unproved for stage 3.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
