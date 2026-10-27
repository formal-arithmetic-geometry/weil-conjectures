## Worker report

`Sheaf.AlgebraicGeometry.CurveTangentFiniteness` states
`AlgebraicGeometry.ProperCurveFamily.finite_tangent_and_infinitesimalAut` with a
single `sorry`. It asserts existence of finite-dimensional K-vector space structures
on the actual marked deformation classes and infinitesimal automorphisms, with their
operations characterized by the usual deformation operations. No theorem is proved.
`Sheaf.AlgebraicGeometry.MarkedCurveDeformations` supplies the missing concrete
objects and operation relations; its definitions have real data and no sorries.

The source was read in `literature/stacks-project/quot.tex`, situation-curves,
lemma-curves-tangent-space (Tag 0D57), and the embedding into proper flat algebraic
spaces, and in `artin.tex`, sections tangent-spaces and inf, especially the definition
of Lift, its isomorphism classes, infinitesimal automorphism kernel, and split
square-zero trivial deformation. The example CompactObject module is withdrawn;
the module header and public-section convention follow the standing brief and the
landed ProperCurveModuli module instead.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and algebraic spaces in the prescribed universes: `Scheme.{u}` and the
  existing `AlgebraicSpace S` inside `ProperCurveFamily`. The auxiliary `S` and
  `a : Spec (.of K) ⟶ S` record the ambient relative presheaf category. In particular
  the source's base is obtained by taking S to be Spec Z (with the universe lift
  of Z if needed) and a its canonical field-valued point. This formulation imposes
  no extra condition on K or X; it equally allows S = Spec K and a = identity.
- Any field K: `(K : Type u) [Field K]`. No finite-type-over-Z, algebraic-closure,
  characteristic, or perfection hypothesis is imposed. Thus the arbitrary-field
  conclusion includes the finite-type-field clause of Tag 0D57.
- A family x = X → Spec K in C(K): `X : ProperCurveFamily (Over.mk a)`. Its `space`
  is an algebraic space, and `projection` is a natural transformation to the
  representable field spectrum. Its existing `isCurve` predicate expands to
  chartwise `Flat`, a closed-immersion diagonal, quasi-compactness, chartwise
  `LocallyOfFiniteType`, universally closed point maps, quasi-compact diagonal,
  chartwise `LocallyOfFinitePresentation`, and geometric fibres of
  `topologicalKrullDim ≤ 1`. These are precisely flat, proper, finitely presented
  and fibre dimension at most one. Testing universal closedness on all scheme
  base changes is equivalent to all algebraic-space base changes by an etale
  atlas; this is the already reviewed moduli convention. The geometric-fibre
  formula is the sheaf pullback with the existing field-valued point topology.
- Arrows in C(T) are T-isomorphisms and arrows over a base map are cartesian:
  `MarkedDeformation.square` and `IsBaseChange` use actual `IsPullback` squares;
  `MarkedDeformation.Rel` uses a natural isomorphism respecting base and marking.
  `IsBaseChange` explicitly requires `i ≫ b = j`, including for the empty curve.
  Hence the quotient keeps the whole specified groupoid, including automorphisms.
- A deformation with chosen identification of special fibre with X:
  `MarkedDeformation X (dualReduction K a)` consists of a genuine proper curve
  family over `dualBase K a`, a marking map from X and its cartesian square.
  The existing dualBase is Spec(TrivSqZeroExt K K), definitionally DualNumber K.
- Its isomorphism classes T_x: `Tangent X := Quot MarkedDeformation.Rel`. The
  relation is already an equivalence by identity, inverse and composition of
  marking-preserving isomorphisms, so generated quotient does not identify more.
- The trivial deformation supplies zero: `IsTangentZero` pins it by a cartesian
  projection to X over `dualProjection` whose composite with the marking is id.
- Tangent scalar multiplication: `IsTangentSMul` is marked cartesian pullback by
  `directionMap K a (c • LinearMap.id)`, i.e. epsilon maps to c epsilon.
- Tangent addition: `IsTangentAdd` uses a marked curve deformation over the split
  square-zero algebra with directions K × K; its first and second projection
  restrictions give the two inputs and the sum-of-projections restriction gives
  the output. This is exactly glue over the common special fibre then pull back
  along the addition of square-zero directions. Existence of such a family and
  uniqueness of the resulting class are asserted in the theorem, not assumed.
- Inf_x: `InfinitesimalAut X` is the subtype of actual natural automorphisms of
  the sheaf pullback representing the trivial family. Its first equation says
  restriction to X is id; its second fixes the projection to the dual-number
  base. It does not fix the projection to X. This is exactly the kernel group
  in artin.tex, not the unrelated group of automorphisms over X.
- Its zero is identity and addition is composition: `iadd.zero.val = Iso.refl _`
  and `(iadd.add α β).val.hom = α.val.hom ≫ β.val.hom`.
- Its scalar pullback: `IsInfinitesimalAutSMul` fixes the canonical scaling map q
  by both pullback projections, and fixes the output automorphism by its first
  projection after q and its unchanged base projection. This is the standard
  base-change automorphism even at c = 0; no invertibility of scaling is assumed.
- Both spaces are vector spaces with these operations: the conclusion quantifies
  `tadd, tmod, iadd, imod`; all three tangent operation relations and the
  automorphism scalar relation hold iff their output equals the specified group
  or module operation. Thus arbitrary structures cannot satisfy the conclusion
  by ignoring the source's operations. No data are chosen from a mere existence
  theorem in any definition.
- Both are finite-dimensional: the two `@FiniteDimensional` clauses refer to
  those exact additive-group and K-module structures. They are not assertions
  about the dimension of unrelated replacement vector spaces.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: Scheme, Scheme.Hom, Spec and Spec.map.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: pullback,
  pullback.fst, pullback.snd, and the canonical pullback constructors.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: AlgebraicSpace, IsRepresentableWith,
  IsEtale, and the existing full-subcategory/presheaf conventions.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli` (newly cited existing node
  def-sfb-proper-curve-moduli): ProperCurveFamily, ProperCurveModuli,
  AlgebraicSpace.IsProperCurveFamily and its local/global component predicates,
  dualBase, dualProjection, dualReduction and infinitesimalReduction. The new
  operations extend the specified maps rather than replacing that category.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Proper`
  and `.FiniteType`: Flat, LocallyOfFinitePresentation, IsProper,
  LocallyOfFiniteType and QuasiCompact, reused through the reviewed curve-family
  definition. Scheme-geometric-fibre and fibre-product dependency records both
  name the existing categorical pullback, not an alternative construction.
- `Mathlib.Topology.KrullDimension`: topologicalKrullDim, reused in isCurve.
- `Mathlib.Algebra.Field.Defs`: Field (the field dependency is a Mathlib leaf).
- `Mathlib.Algebra.TrivSqZeroExt.Basic` (def-sc-trivial-square-zero-extension):
  TrivSqZeroExt, inlHom, fstHom and map; `Mathlib.Algebra.DualNumber`: DualNumber.
  For arbitrary direction modules the helper binds the compatible opposite
  action and IsCentralScalar required by this existing API; these give the
  ordinary central action, not an extra restriction on the curve or field.
- `Mathlib.LinearAlgebra.Prod`: LinearMap.fst and LinearMap.snd.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: FiniteDimensional, which is
  Module.Finite over a division ring.

All four proof-dependency nodes were read. None currently has a Lean record or
usable declaration, so there is no module to import for them. Their precise
roles and all six proof steps are in the theorem docstring. The requested item
has no missing statement prerequisite after adding the definition node below.
The proof-dependency nodes themselves are not restated or edited.

Edge cases checked: the empty curve has no excluded nonemptiness assumption
(and gives zero tangent/automorphism spaces); dimension-zero fibres remain
allowed; nonreduced, singular, disconnected and nonstable curves remain allowed.
Every characteristic, including 2, and transcendental/non-finite-type fields
remain allowed. Scalar zero is a genuine noninvertible base change and the
scalar relations include it; negatives and the trivial class are included.
The marking is preserved on all arrows and the infinitesimal automorphism
condition does not accidentally fix X as a base. K, dual numbers, K × K and
all geometric-field tests use the existing single universe u; quotient and
automorphism carriers are in u+1. There are no auto-bound variables, local
notation, private definitions, hidden let binders, or extra map hypotheses.

Searches: msearch.py LeanFinder, first-order deformations/infinitesimal
automorphisms of proper algebraic-space curves (8 ring/scheme smoothness hits,
no match); Loogle `DualNumber, Module.Finite` (0); Mathlib grep
`CurveFamily|MarkedDeformation|InfinitesimalAut|AlgebraicSpace` (0).
Further LeanSearch and LeanFinder searches for the marked-deformation notion
returned only ring derivation/cotangent and manifold tangent results; verbatim
outputs are in the new node's mathlib_searches. Direct rg of WeilConjectures,
Sheaf and dag/lean_names_upstream.json found the landed ProperCurveModuli,
which is reused, and scheme-only marked automorphisms, which do not supply the
current object. DAG searches found theorem uses but no definition for marked
curve deformation classes/operations. blueprint_refs.py searches for
`marked curve deformation` and `infinitesimal automorphism` both returned zero
matches. The node has the full queries/results and verdicts.

Validation: both modules were compiled separately by scompile.py, including
compilation under their final module names and the sibling import. They pass
with no errors and no non-sorry warnings. No live source was modified, no git
command was run by this worker, and no global build was run.

Edge-case review added `i ≫ b = j` to the generic base-change relation: a
marking-compatibility equation alone cannot force the reduction-map square to
commute when X is empty. This is part of the definition, not a new hypothesis
on the finiteness theorem. No statement correction, dependency repair, or
STATEMENT-DISPUTED issue.

## New nodes

`def-sfb-marked-curve-deformations` defines marked proper-curve deformations,
their isomorphism relation and quotient, the canonical zero/scalar/addition
relations, and the subtype of infinitesimal automorphisms with its scalar
pullback relation. Its only module is MarkedCurveDeformations.lean, which has
no theorem or sorry. It builds on the landed proper-curve moduli definition
and Mathlib's split square-zero algebras and pullbacks. Source: artin.tex,
sections tangent-spaces and inf, applied to quot.tex situation-curves and
Tag 0D57. The search results above and in the node show why this is a new
notion; the existing HasTrivialInfinitesimalAutomorphisms only supplies a
predicate asserting triviality, not the actual group, deformation quotient or
operation relations. Every declaration in this module belongs to this single
notion and is listed in its lean.declarations.


## Returned-delivery repair and self-check

The return at immutable head `2346c11df42e` reported incremental DAG
reachability failures for `def-sf-constructible-exceptional-coefficient-construction-data`,
`def-sfb-algebraic-moduli-stack`, `def-sfb-marked-curve-deformations`,
`def-sfb-proper-curve-versality`, and `def-trf-implicit-transverse-coefficient`.
The saved packet was checked first, as instructed, against the current server
base with `deliver2.py Q140 lem-sfb-curve-tangent-finiteness --no-push`.
It passed preflight and every per-file compile (dry-run commit `fd508c1963b`).
The packet's new node `def-sfb-marked-curve-deformations` is explicitly in the
item's `stmt_deps`, and the item imports its module and uses its actual tangent,
automorphism, and operation declarations. The other four names are not nodes
created or modified by this delivery; no unrelated node is added to its scope.
The earlier global reachability diagnostic is no longer reproduced by the
prescribed current-server preflight. No mathematical definition or signature
was changed to address that diagnostic.

The retained modules and node records were reopened for this self-check.
The arbitrary field, proper flat finitely presented curve family, geometric
fibre bound, marked isomorphism classes, identity-reducing automorphisms,
zero, addition, scalar pullbacks, and both finite-dimensional conclusions
match the clause correspondence above. The new module has no sorry; the item
has exactly its single named theorem with sorry. Both explicitly disable
auto-bound implicits and have no line over 100 characters. Compared with the
current read clone, the item's only changed fields are `lean` and the two
additional statement dependencies described above. The existing saved work
is retained rather than replaced.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
