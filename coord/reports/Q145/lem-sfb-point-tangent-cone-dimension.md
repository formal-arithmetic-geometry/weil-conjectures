## Worker report

The module `Sheaf.AlgebraicGeometry.PointTangentConeDimension` states
`AlgebraicGeometry.point_tangent_cone_dimension`, with the sole proof `by sorry`.
It introduces no definition, instance, auxiliary theorem, or axiom. The node statement,
proof and proof dependencies are unchanged. Two new existing:true definition nodes are
added to statement dependencies for the already implemented base-field tangent-module/stalk
helpers and symmetric algebra. The returned H2 theorem-dependency mistake is repaired.
No statement is disputed.

Hypothesis-by-hypothesis reading:

| Node hypothesis | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| k-scheme Y | `(Y : Scheme.{u}) (s : Y ⟶ Spec (.of k))` |
| Smooth | `[Smooth s]` |
| Separated, meaning closed diagonal | `[IsSeparated s]`; Mathlib's class is exactly closed immersion of `pullback.diagonal s` |
| Geometrically integral | `[GeometricallyIntegral s]` |
| Finite type | `[LocallyOfFiniteType s] [QuasiCompact s]`, the recorded conjunction |
| Rational point p | `(p : s.fieldPoints k)`, the existing section type used by the recorded DensePoints module |
| Name its underlying point | `(y : Y) (hp : p.1 (IsLocalRing.closedPoint k) = y)`; this just names the point of p, with no restriction |
| Reduced closed subscheme Z | `(Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]` |
| Contains p | `(z : Z) (hz : i z = y)`; a closed immersion is injective, so z is the unique point over y |
| Local ring R and maximal ideal m | `Z.presheaf.stalk z` and `IsLocalRing.maximalIdeal (Z.presheaf.stalk z)` throughout |

Clause-by-clause reading:

| Node assertion | Lean rendering |
| --- | --- |
| d = dim Y is a finite nonnegative integer | `∃ d : ℕ, topologicalKrullDim Y = (d : WithBot ℕ∞)` |
| E is the recorded tangent space, with dimension d over k | `Module.Finite k (schemeTangentSpace k Y s y)` and `Module.finrank k ... = d`; scalars are the existing `schemeTangentSpaceBaseModule` |
| Algebraic cone is Spec of the actual associated graded ring | Every occurrence of the cone is literally `Spec (.of (Ideal.associatedGraded (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))))` |
| Affine space of E has coordinate ring Sym(E*) | The domain of F is `SymmetricAlgebra k (Module.Dual k (schemeTangentSpace k Y s y))`; Mathlib constructs this as the tensor-algebra quotient by the stated commutativity relations |
| Cone is canonically a closed subscheme there | `IsClosedImmersion (Spec.map (CommRingCat.ofHom F))`, together with the next three canonical-map conditions |
| Canonical evaluation of cotangent classes | `c a : Module.Dual k E`, with `residueStructure ... (c a θ)` equal to the epsilon coordinate of the actual stalk homomorphism of θ applied to a |
| Coordinate map on scalars | The `∀ b : k` clause identifies F on constants with the structural field map into R followed by the degree-zero `Ideal.associatedGradedRingHom` |
| Coordinate map on degree one | The `∀ a : maximalIdeal ...` clause sends `SymmetricAlgebra.ι ... (c a)` to the class of the image of a under the actual stalk map in `m^1/m^2`, using `DirectSum.of ... 1` |
| dim cone = dim R | The displayed equality between `topologicalKrullDim (Spec gr)` and `ringKrullDim (Z.presheaf.stalk z)` |
| dim R <= dim Z <= d | The next two inequalities, with the same stalk, Z, and d |
| Proper underlying Z gives dim cone < d | `Set.range i ≠ Set.univ → topologicalKrullDim (Spec gr) < (d : WithBot ℕ∞)` |
| Any smooth locally closed k-subscheme D through p inside Z | Universal `D`, `j : D ⟶ Y`, `IsImmersion j`, `Smooth (j ≫ s)`, `Set.range j ⊆ Set.range i`, `q : D`, and `j q = y` |
| Locally closed means closed in an open subscheme | The recorded `IsImmersion` interface is equivalent to this factorization; its Mathlib docstring and factorization theorem were checked |
| Differential identifies T_D with a linear subspace of E | The existential k-linear `L`, `Function.Injective L`, and the pointwise `HEq` with the existing `schemeTangentMap` |
| Associated affine linear subspace lies in the cone | The final inclusion of ranges of spectrum maps; the first map is `SymmetricAlgebra.lift ((SymmetricAlgebra.ι ...).comp L.dualMap)`, and the second is `Spec.map F` |

The epsilon-coordinate formula determines c uniquely: the structural residue map from k
is bijective at this rational point, and equality of linear functionals is pointwise equality.
Rational tangent-cotangent duality and finite dimensionality show that these c(a) span E*.
Thus the formulas for F on constants and c(a) characterize the canonical graded quotient
map; no arbitrary embedding is substituted. The formula also fixes the grading on
generators. For D, the image point `j q` need only be propositionally equal to y.
`HEq (L θ) (schemeTangentMap ... θ)` identifies the actual tangent vectors after this
point equality; it does not replace the differential by an arbitrary injective map.
The associated affine map uses the contravariant dual L*, as required, not Sym(L).
The existential he expresses the induced residue-field isomorphism, which follows from
rationality and the immersion and is not an extra assumption.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (mathlib leaf for def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed clause
  of def-weil-algebraic-closure's mathlib_match; no choice of algebraic closure is needed).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`: the section-type interface
  `s.fieldPoints k` used by `Scheme.Hom.baseChangeFieldPoint`; no base change is required here.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`, its
  additive/residue-field module instances, and `schemeTangentMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`; and
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` in the equivalent factorization.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`: the stalk interface built on
  `TopCat.Presheaf.stalk`; this statement uses the structure-ring stalk, not a module stalk.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, the commutative-ring instance, and
  `Ideal.associatedGradedRingHom`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Sheaf.AlgebraicGeometry.PowerMapSmoothGraphLocalData`:
  `schemeTangentSpaceBaseModule`, `PowerMapLocalData.residueStructure`,
  `PowerMapLocalData.stalkStructure`, and `PowerMapLocalData.stalkMapAt`.
  The new definition node `def-sfb-tangent-base-scalars-stalk-maps` owns these four
  declarations. The theorem node `lem-trf-power-map-smooth-graph-local-data` is not added.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`, `ι`, and `lift`;
  the new definition node `def-sfb-symmetric-algebra-construction` owns these three
  definitions. The universal-property theorem stays in proof_deps, not the added stmt_deps.
  `Mathlib.LinearAlgebra.Dual.Defs` supplies `Module.Dual` and `LinearMap.dualMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated` renders the explicit
  diagonal condition already present in the item's text.

All recorded modules of stated proof dependencies are imported, without making them
public merely for the proof: Regular, RationalPointStalkTopologicalLocalDimension,
DimensionLocallyAlgebraic, RationalTangentCotangentDuality, HilbertSamuelGrowthDimension,
KrullDimension-at-point, SmoothGeometricallyNormal, and the reduced-source factorization
in the upstream ClosedImmersion module. Already public statement imports also cover
several proof dependencies. Unstated proof dependencies are not needed to elaborate
a statement; no additional theorem or proof has been fabricated for them.

Sources checked locally: Stacks algebra.tex at lemma-regular-graded (00NO),
lemma-dimension-graded (00P6), and lemma-dimension-closed-point-finite-type-field (00OU),
with the tag/label mapping verified. The statement is an auxiliary historical Milne
I.3.6 lemma, not the blueprint unit's own statement; its node records that the latest
blueprint unit no longer contains this historical branch. No unit statement changes.

Edge cases checked before writing:

- Y = Spec k, dimension zero: E = 0, its symmetric algebra is k, and the cone of the
  only reduced closed subscheme through p is the point. The proper-subset premise is false.
- Z = Y: the canonical graded map is the regular-local symmetric-algebra identification;
  the strict inequality is not asserted.
- Z = {p}: R = k, cone dimension zero, and the degree-one map is zero.
- A singular reduced Z, such as a cusp in a smooth plane: the cone may be nonreduced;
  the statement does not assume its reducedness or replace it by its reduction.
- Z may have components away from p of larger dimension; dim R <= dim Z is retained
  as an inequality, not incorrectly replaced by equality.
- D can have dimension zero, can be disconnected, and need only be locally closed.
  No irreducibility, global closedness, or global finite-type assumption is added for D.
- Empty schemes cannot supply the required point; this is a consequence of the given p,
  z or q, not an added nonempty assumption. All field characteristics are covered.
- The single explicit universe u follows the recorded scheme tangent interface and
  covers arbitrary schemes by choosing a common ambient universe; there is no test-object
  quantification in a smaller independent universe.

Searches for an existing statement (full msearch receipts are in sandbox searches.jsonl):

- msearch leanfinder: "For a closed subscheme of a smooth variety the algebraic tangent
  cone embeds in the tangent space and has the dimension of the local ring". Eight hits:
  standard-smooth relative dimension, cotangent finrank, closed-subscheme preimmersion,
  and analytic tangent cones. None gives this statement.
- msearch loogle: `"Ideal.associatedGraded", "SymmetricAlgebra"`: zero hits.
- msearch leansearch: "Algebraic tangent cone of a closed subscheme at a smooth point
  has the dimension of its local ring". Eight hits, mainly analytic tangent cones;
  no algebraic tangent-cone theorem.
- msearch grep in RingTheory: `tangent.?[Cc]one|associatedGraded.*[Mm]ap`: zero hits.
- msearch grep across Mathlib: `algebraic.*[Tt]angent[Cc]one|point_tangent_cone_dimension|tangent.?[Cc]one.*[Dd]imension`:
  one hit in Analysis/Calculus/TangentCone/DimOne, unrelated.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for tangent cones, rational tangent/
  cotangent interfaces, and associated-graded maps: existing associated graded and
  tangent-space declarations found and reused; no theorem with all this item's clauses.
- grep -rn of this node id in `lean/WeilConjectures`: no match.
- Focused rg for a base-field tangent instance found the existing
  `schemeTangentSpaceBaseModule` and the stalk helpers in PowerMapSmoothGraphLocalData;
  these are imported rather than duplicated.

Validation: scompile.py compiled the sandbox and library module successfully (2.8 s and
2.7 s for the first pass), with no errors or warnings. The file sets `autoImplicit false`.
The final header and record are rechecked by deliver2.py below.

## Second reading by Q145

Worker self-check after reopening the node and the complete Lean file; the independent
maintainer review is performed after delivery, as the dispatcher brief specifies.
No second agent was started and no independent worker review is claimed here.
The two tables above record the actual hypothesis/clause comparison. In particular,
I rechecked the direction of the dual affine map, strict inequality's proper-subset
premise, the nonreduced cone case, and the use of HEq to identify the differential at
propositionally equal points. No statement correction was needed. Reused the existing
base-field module instead of introducing an overlapping instance. The repair now records
the plain definitions through two existing:true definition nodes. Every proof remains sorry.

## Repair of returned head bcdb6abb57e4

H2 is repaired exactly as requested. Removed the two newly added theorem nodes
`lem-trf-power-map-smooth-graph-local-data` and
`lem-weil-pbc-symmetric-algebra-universal-property` from the additions to stmt_deps.
Added the two definition records described below, citing only those instead. The original
16 statement dependencies remain in their original order. No field of the item changes
except lean and stmt_deps. Its Lean source is byte-for-byte the returned version.
The sandbox item was compared with current shared main: before repair the only
differences were lean and the two offending added stmt_deps. It is now based on current
main with the corrected definition-node additions. deliver2.py refreshes its own worktree
and constructs the current-base delivery; no direct Git command was run in the shared clone.

The maintainer's independent reading of immutable head bcdb6abb57e4 found the mathematical
statement correct, including canonical F, all dimension clauses and the D differential/
affine inclusion clause. This repair changes only definition ownership in the DAG.
I reopened the four helper definitions and the three Mathlib definitions and matched
their actual formulas to the new node texts; no theorem about power maps is used by them.

## New nodes

`def-sfb-tangent-base-scalars-stalk-maps` records the existing four declarations in
`Sheaf.AlgebraicGeometry.PowerMapSmoothGraphLocalData`: structural stalk homomorphism,
structural residue homomorphism, identified contravariant stalk map, and the restriction
of tangent-space scalars to k. Sources: Stacks 01HV/01I1 and 0B2C. LeanSearch gave related
residue/stalk definitions, Loogle and Mathlib grep had no project-helper hit, and direct
project grep located exactly these four existing declarations. DAG/blueprint searches
found no definition-node owner; the old theorem node lists the helper declarations but
its main theorem is neither needed nor used to define them. This is existing:true: no
new Lean code is written. At a nonrational point scalar restriction is still defined;
stalkMapAt also handles every point equality, including reflexivity. No smoothness,
finite type, rationality or power-map assumptions are introduced.

`def-sfb-symmetric-algebra-construction` records existing `SymmetricAlgebra`,
`SymmetricAlgebra.ι` and `SymmetricAlgebra.lift` in
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`, following Stacks 00DM. LeanSearch and
LeanFinder identified the exact declarations; grep confirmed their definitions at
lines 50, 60 and 99. Project grep showed imports and uses, not a competing construction;
DAG searches found specialized sheaf/graded constructions and the universal-property
theorem, but no definition owner for these plain module symmetric-algebra definitions.
This is existing:true and creates no duplicate Lean construction. Zero modules and the
zero ring are permitted; their symmetric algebras and lift have the same quotient
definition. The definition node has empty proof/proof_deps, unlike the existing theorem.

Both nodes carry full source, search receipts, creation metadata, blueprint ancestry,
empty import_flags and none Lean audits as required. The ancestry command returns None
for this historical auxiliary item, so blueprint.from.node is null, with the item's
existing historical place and the item-prefixed via path retained.

Preflight repair during validation: its existing-declaration source regex did not recognize
`instance (priority := 100) schemeTangentSpaceBaseModule` as a primary declaration.
The definition record now uses the first plain abbreviation,
`AlgebraicGeometry.PowerMapLocalData.stalkStructure`, with its verbatim signature, as
primary declaration; all four exact names remain in lean.declarations. This is the same
mathematical definition record and module, and no source or tool is edited. The standalone
scompile retry passed cleanly (17.4 s sandbox / 2.4 s library).
