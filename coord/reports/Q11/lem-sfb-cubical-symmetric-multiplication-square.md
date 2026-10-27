## Worker report

The module Sheaf.AlgebraicGeometry.CubicalSymmetricMultiplicationSquare states
AlgebraicGeometry.CubicalRigidifiedLine.symmetric_multiplication_square with its sole
proof `sorry`. No theorem is proved. No statement correction or disputed statement.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, with u explicitly declared.
- A commutative group scheme p:G→S and its identity: `(G : Over S) [CommGrpObj G]`.
  Its structure morphism is G.hom, its identity is `(η[G]).left`. The class includes
  group identities and commutativity for morphisms in the over category, as required.
- The cubical rigidified line (L,r,tau): `(L : CubicalRigidifiedLine G)`. Its fields are
  the invertible module, rigidification, sectionIso and Compatible predicate of the
  recorded dependency, without a private reconstruction.
- The supplied cubical rigidification-preserving symmetry: `(symmetry : Iso
  (L.pullback (𝟙 G)⁻¹) L)`. The scoped inverse is the inverse under the pointwise
  group law on morphisms into G, not an inverse to an arbitrary scheme morphism.
  Mathlib Hom.inv_def identifies it with identity followed by the inversion morphism.
  Iso includes both rigidification and cube-section preservation.
- Every integer d≥1: `(d : ℕ) (hd : 1 ≤ d)`. Positive integers and positive naturals
  coincide; negative and zero integers are not in the assertion.
- The multiplication map is `((𝟙 (Grp.mk G) ^ d).hom.hom)` in the scoped pointwise
  commutative group of homomorphisms of the bundled group object. It is the d-fold
  sum of the identity (written multiplicatively). Grp.Hom.hom_pow identifies this
  with the pointwise power; each multiplication is the group law, not composition.
  Bundling supplies IsMonHom canonically, so pullback has no extra hypothesis.
- The claimed isomorphism is the existential f from the actual tensor pullback line
  to `L.line.tensorPow (d ^ 2)`, together with `IsTensorPowerIso ... f`.
  The first conjunct of that predicate is exactly preservation of the tensor
  rigidification. Its second conjunct is equality of the cube section with the
  product of d² copies of the original cube section, tested in tensor frames over
  every test scheme. The cube values are endomorphisms of its structure module;
  composition multiplies scalars, so the displayed nth power is the tensor-product
  scalar. The eight tensor frames are transported through f by powerIsoFrame.
- Every pullback in these definitions uses the dependency's tensorPullback, its
  section-normalized composition, and the recorded cubical pullback construction.
- There is no condition on d being invertible, no characteristic or smoothness
  restriction, no field hypothesis and no connectedness hypothesis.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.CubicalRigidifiedLine: CubicalRigidifiedLine,
  CubicalRigidifiedLine.Iso, CubicalRigidifiedLine.pullback, CubicalLine.Frame,
  CubicalLine.Framed and CubicalLine.value. Its full source and docstrings were read.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullback,
  tensorPullbackSectionAdjunction, tensorPullbackSectionComp, tensorPullbackSectionId;
  publicly available through the cubical module. Its definition and normalization
  were read. The extra predicate uses the same tensorPullback.
- WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons:
  Scheme.Modules.boundaryPullbackPowIso and boundaryTensorPowIso, real recursive
  tensor and unit comparisons already used by the cubical dependency itself.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Grp and CommGrp_: CommGrpObj, Grp.mk,
  Hom.commGroup, Hom.inv_def, Grp.Hom.hom_pow and bundled homomorphism instances.
- Mathlib.CategoryTheory.Endomorphism: End.of and End.asHom keep composition powers
  distinct from the pointwise group powers used for multiplication maps.
- Proof import: WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor,
  Scheme.Modules.invertible_pullback_tensor. The other proof dependency,
  lem-sfb-cube-section-cubical-compatibility, has no Lean record on the read base,
  so there is no module to import. Its role is included in the proof docstring.

Edge checks: d=1 gives the identity pullback and a first tensor power up to its unit
factor; the preservation clauses account for that canonical unit. The new predicate
also handles n=0: tensorPow 0 is the unit, powerToUnit/powerFromUnit/powerUnitIso
are identities, and the section scalar is the identity endomorphism. Empty schemes
are allowed, as are characteristic dividing d and nonreduced test schemes. Frames
need only trivialize the finitely many eight line factors and exist locally; they
are not a global-triviality assumption. Validity for the transported tensor frame
follows from f being an isomorphism, the tensor comparisons, and validity of b on
those factors. Testing all schemes includes the open covers trivializing them.
No unbound universes or auto-bound implicits; both modules explicitly disable them.

Searches: msearch.py leanfinder query “Symmetric cubical rigidified line bundle on a
commutative group scheme pullback by multiplication d tensor power d squared” found
scheme product/group-object results, no matching theorem. Loogle query “CommGrpObj,
pow, tensor” returned unknown CommGrpObj and no hits; a second query “tensorPow, Iso”
returned no hits. msearch grep “Cubical|cubical|cubist” gave zero Mathlib hits. A broader
symmetric-line grep returned unrelated quadratic-form and modular-form lines.
LeanSearch “tensor power cubical rigidified invertible sheaf” returned TensorPower,
ordinary module invertibility and Cartesian sheaf tensor products, none preserving
cubical data. Additional exact queries and full results are recorded on the new node.
rg of lean/WeilConjectures for cubical/Cubical/cubist returned no matches; grep for the
item ID likewise returned none. rg of lean/Sheaf found the recorded cubical dependency
and unrelated lattice cubical complexes; no multiplication-square theorem. The exact
new declaration names do not occur in upstream names or Mathlib. DAG and
blueprint_refs.py search found no separate tensor-power compatibility definition.

Source: the item's source names Moret-Bailly I 5.5 (local original WANTED). I read
literature/blueprint/latest/blueprint/sec-abelian-varieties/sk-prop-av-mult-n-pullback/
lem-sc-mult-n-pullback.proof.md: the substitutions (x,x,-x), (x,x,[n-1]x) and the
quadratic exponent induction. The docstring carries all four item proof steps,
including the cubical-compatibility input, cancellation and the simultaneous induction.

Validation: scompile.py checked each file separately in dependency order, both as
sandbox and library modules, within 2.3 seconds each. No errors or warnings.

## New nodes

`def-sfb-cubical-tensor-power-iso` defines the missing compatibility predicate for an
isomorphism to an existing tensor power. It supplies real recursive maps to/from the
unit, the unit-power isomorphism, and transported tensor frames. It does not choose a
cubical object or an unspecified comparison. The predicate imposes the exact tensor
rigidification and product cube-section formula from Moret-Bailly I §2 and I 5.5;
its frame formulation uses the existing Frame and value API. Existing sheaf tensor
powers, pullbacks, and cubical data are reused. The node records LeanSearch, LeanFinder,
Loogle and Mathlib/project/DAG grep searches, whose results contain no existing notion.
The item's stmt_deps gains this node. All other item fields are unchanged except lean.

## Second reading by Q11

A separate self-review pass reopened the item JSON, the new definition JSON and both
Lean files and checked each correspondence listed above. The dispatcher explicitly
forbids starting another agent, so this is not represented as an independent worker
review; the maintainer supplies the independent delivery review as stated in the brief.

The review checked particularly the two different meanings of power: bundled Grp
morphisms use the scoped pointwise group law for [d], while End.of/asHom makes cube
scalars use composition. It checked the direction of rigidification composition
(from e*M through f to e*L^n to O_S), and both directions of the transported frame.
The cube clause compares the section of the actual pullback object, rather than
merely asserting an isomorphism of underlying lines. Tensor-frame equality is the
same factorwise equality as in the original cubical API. No mathematical mismatch
or statement change was found. Compile repairs were an explicit End.of/asHom wrapper
for composition powers and renaming the reserved notation ι to symmetry.
