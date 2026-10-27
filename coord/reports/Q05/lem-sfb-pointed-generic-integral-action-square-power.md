## Worker report

The module `Sheaf.AlgebraicGeometry.PointedGenericIntegralActionSquarePower` states
`AlgebraicGeometry.Scheme.Modules.exists_pointedGenericIntegralAction_square_tensorPower`.
Its only theorem has proof `sorry`. No definitions, auxiliary theorems, new nodes,
dependency repairs, or statement corrections are introduced. All original node
fields are preserved; only `lean` is added.

Clause-by-clause reading:

- The nonempty affine Noetherian integral base is `(S : Scheme.{u}) [IsAffine S]
  [IsLocallyNoetherian S] [IsIntegral S]`. Integrality includes nonemptiness;
  affineness implies quasi-compactness, so locally Noetherian here is Noetherian.
- Normality is `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`, precisely the stated local-ring condition.
- The generic point is `genericPoint S`. `S.functionField` is definitionally the
  stalk there; `S.fromSpecStalk (genericPoint S)` is therefore the canonical
  `Spec k(S) → S`, without a new function field or a choice of a generic point.
- The group scheme is `H : Over S` with `[GrpObj H]`. Mathlib's group object includes
  multiplication, identity, associativity, both unit laws and inverse identities.
  `[Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom]
  [QuasiCompact H.hom]` express smooth, separated, finite type. Separatedness is
  the closed-immersion condition on the diagonal. `[GeometricallyConnected H.hom]`
  is nonempty connectedness after every field-valued base change, equivalently
  the stated algebraically closed extensions of residue fields.
- `Y : Over S`, `[Smooth Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsIntegral Y.left]` express
  exactly the properties of `p : Y → S` and integral total space.
- `(e : S ⟶ Y.left) (he : e ≫ Y.hom = 𝟙 S)` is the section with `p e = id`.
  `[ModObj H Y]` is an actual morphism `H ×_S Y → Y` with unit and associativity
  identities; its definition was read in Mathlib's Monoidal/Mod.lean. No
  equivariance condition is put on `e`.
- `hη : GeometricallyIntegral (pullback.snd Y.hom
  (S.fromSpecStalk (genericPoint S)))` concerns precisely `Yη → Spec k(S)`.
  This class requires integral (hence nonempty, reduced and irreducible) base
  changes to every field extension. No hypothesis is put on special fibres of Y.
- `(L : Y.left.Modules) [L.IsInvertible]` is any invertible structure-sheaf module.
- `∃ r : ℕ, 1 ≤ r ∧ ∀ (B : Over S) (g h : B ⟶ H), ...` puts the positive
  exponent before every test scheme and both group-valued points. Positive
  natural numbers are exactly the positive integer exponents in the statement.
- In the chosen cartesian monoidal structure on `Over S`, `Y ⊗ B` is `Y ×_S B`;
  `fst Y B` is its projection to Y and `snd Y B` its projection to B.
  `(tensorPullback (fst Y B).left).obj (L.tensorPow r)` is `M_B`.
- By Mathlib's `Hom.smul_def`, `(snd Y B ≫ g) • fst Y B` sends `(y,b)` to
  `g(b)y`. Its tensor pullback is canonically `τ_g^* M_B`: the composite
  `τ_g` followed by projection to Y is exactly this morphism. Using this
  composite rather than an iterated pullback changes no existence assertion,
  by the recorded pullback-composition isomorphism. The product `g * h` uses
  the group of morphisms into the specified group object, in that order.
- `∃ N : B.left.Modules, N.IsInvertible ∧ Nonempty (... ≅ ...)` is exactly an
  invertible base module and existence of an isomorphism. The left side has
  the `gh`-translated M and M; the right side has the g- and h-translated M,
  then `(tensorPullback (snd Y B).left).obj N = q_B^*N`. Parentheses group the
  first two factors; all tensor products are the sheaf tensor products of the
  existing symmetric monoidal category of structure-sheaf modules.
- B is arbitrary: no reducedness, Noetherianity, affineness, flatness, or
  connectedness restriction. Neither properness nor commutativity is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; affine quasi-compactness
  is already provided by the affine scheme instances, so no redundant binder.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  together with `IsDomain`, used on every stalk, as the normal-ring record says.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Morphisms.QuasiCompact`: `QuasiCompact` (finite type is their conjunction).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Morphisms.Separated`: `IsSeparated`, defined using the diagonal.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; cartesian products in `Over S` are these
  fibre products, via the standard `Over.prodLeftIsoPullback`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`. The geometric-connectedness class is the
  field-valued-fibre formulation of the node's residue-field condition.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: recorded
  `Scheme.functionFieldOfComponents` and its integral-scheme clause reusing
  Mathlib `Scheme.functionField`; the latter is the generic stalk used here.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  the recorded irreducible and reduced definitions are imported there.
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, which includes nonemptiness.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Modules.IsInvertible`,
  `Modules.tensorPow`, and the existing symmetric sheaf-tensor structure.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: recorded
  `tensorPullbackSectionAdjunction`, the public upstream `tensorPullback`
  construction, and the canonical `tensorPullbackSectionComp` comparison.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  sheaf-tensor interface, publicly imported; no alternative tensor is defined.
- Group and action structures use Mathlib's `GrpObj`, `ModObj`, and the
  cartesian monoidal structure on `Over S`, not a private substitute.

Plain imports retain the stated proof plan: finite presentation, proper/smooth
base change, flatness, quasi-separatedness, affine pullbacks, torsion-freeness,
`WeilConjectures.AlgebraicGeometry.Morphisms.Slicing`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`,
`Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct`, and
`Sheaf.AlgebraicGeometry.FieldProductSquarePower`. The two proof-only nodes
`lem-sfb-smooth-normal-ascent` and
`lem-sfb-normal-noetherian-generic-line-pullback` have no recorded module in
this checkout, and are not needed to type the statement, so no import is
invented for them. Their full argument and uses remain in the docstring.

Edge cases checked before writing:

- The empty base is excluded exactly by the original integrality assumption;
  the group and Y have sections, so their relevant fibres are nonempty.
- r = 0 is excluded by `1 ≤ r`; r = 1 is allowed. `tensorPow` uses the same
  sheaf tensor and its associators, so positive powers agree with the node's
  recursive convention up to canonical isomorphism.
- B may be empty, nonreduced, or non-Noetherian. The existential base line and
  isomorphism remain meaningful, and there are no extra test-scheme assumptions.
- For trivial H, Y = S, or g = h = 1 the formula is the expected trivial square.
- For a noncommutative group the product remains gh, never hg. The supplied
  specialization `(g,1,h⁻¹,1)` gives gh,1,g,h using only associativity/inverses.
- Integral total Y with disconnected special fibres is permitted: only the
  base change to `Spec k(S)` is required geometrically integral.
- The single explicit scheme universe u is the ordinary fixed universe of the
  category of schemes, including all test objects; no smaller independent
  field/test universe makes the geometric hypotheses vacuous.

Searches (all through the prescribed wrapper, with raw results in searches.jsonl):

- LeanFinder: “A uniform positive tensor power of a line bundle satisfies the
  theorem of the square for a pointed smooth family with geometrically integral
  generic fibre and connected group action”. Eight hits, including
  `Proj.pow_apply`, `Scheme.basicOpen_pow`, and purely inseparable tensor-power
  results; inspected returned signatures, none states this assertion.
- Loogle: `"square", "tensor"`; zero hits.
- Mathlib grep: `square_power|theorem.of.the.square|square_condition` in
  AlgebraicGeometry; zero hits.
- LeanSearch: “A line bundle admits a positive tensor power satisfying the
  theorem of the square for a connected smooth group action over a normal
  integral base”. Eight results about module tensor powers, zpow and squares;
  no scheme-action square theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name
  index, for `exists_pointedGenericIntegralAction_square_tensorPower`,
  `pointedGenericIntegral`, `theorem.of.the.square`, `square_power`, and
  `square_tensorPower`: no duplicate declaration.
- Broader action/square searches found and led to reading
  `NormalProductSquareDescent`, `FieldProductSquarePower`,
  `SquareActionGenerationLocusStable`, and `SquareActionProjImmersionLocusStable`.
  The first requires geometrically integral fibres of all factors and is not
  this generic-fibre assertion. The field theorem is the proof dependency.
  The other two assume a square condition instead of proving its existence.
  Their established `GrpObj`/`ModObj` and composite action-map notation is reused.

Source checked online: author PDF
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf,
Proposition 5.9 final assertion (1), Lemma 5.7, and the pointed preliminary case
in Proposition 6.4. The factor reordering and section argument agree with the
node. No statement fault or disputed claim was found. The latest blueprint is
not used to replace this auxiliary's supplied source route.

## Second reading by Q05

A separate second pass in this worker session reopened the node and complete
Lean signature and checked the binders and both sides of the isomorphism.
No other agents were started, as the dispatcher expressly forbids that; the
maintainer's independent delivery review remains the independent reading.

In particular, the base is affine and locally Noetherian, not merely a
Noetherian topological space; the hS conjunction is the stated stalk normality.
The generic stalk really is the recorded integral function field. GrpObj and
ModObj supply group/action identities and do not impose commutativity. The
section binder is p e = id, and has no hidden equivariance requirement.
Geometric integrality is imposed on `pullback.snd` to the generic spectrum,
not on the whole map Y.hom. The quantified B is unconstrained, and the
existential r is outside its quantifier. Finally the four pulled-back factors
are respectively gh,M,g,h, followed by q_B^*N on the right. The action-pullback
notation expands by `Hom.smul_def` and the canonical pullback-composition
comparison, so it has the same content as the displayed translations in the
node. No mismatch was found, and no statement correction was made.
