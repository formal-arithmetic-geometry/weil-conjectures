## Worker report

`Sheaf.Paper.PbcConeIndependence` states `prop-weil-pbc-cone-independence`.
It defines `CategoryTheory.StageSystem.transportedCone`, the explicit triangle after
an extension of stages, and `CategoryTheory.StageSystem.ConeIndependenceSpec`, a Prop
with the four clauses in the node.  The theorem
`AlgebraicGeometry.Scheme.pbcConeIndependence` applies that specification to
`pbcScalarSystem l Ω T hDim.out hInv.out`; its proof is `sorry`.

The theorem hypotheses are rendered literally by
`(l : ℕ) [Fact l.Prime]`, `(Ω : Type c) [Field Ω]`,
`[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]`,
`(T : Scheme.{u}) [IsNoetherian T]`,
`[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and
`[hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`.  The conclusion is
`StageSystem.ConeIndependenceSpec (pbcScalarSystem l Ω T hDim.out hInv.out)`.
The coefficient and scheme universes are independent.

The four fields of `ConeIndependenceSpec` match the four sentences of the node.
`scalarExtension` quantifies a representative `r`, an extension `hr`, a cone object
`Z`, arrows `g,h`, and the distinguishedness premise for
`Triangle.mk r.u g h`.  It asserts distinguishedness of `transportedCone` and an
isomorphism from the mapped triangle whose first two components are the two
associator components and whose third component is an identity.  The helper's
arrows are `S.tr hr r.u`, `(S.assoc r.hY hr).inv.app Y.obj ≫ (S.T hr).map g`, and
`(S.T hr).map h ≫ (S.T hr).commShiftIso 1).hom.app _ ≫
(shiftFunctor (C N) 1).map ((S.assoc r.hX hr).hom.app X.obj)`.

`representatives` assumes literal equality of the two `PairCategory.mkHom` classes,
quantifies arbitrary distinguished cone data for both representatives, and produces
an agreement field `Q`, both inclusions, equality of transported first arrows, and an
isomorphism of transported triangles fixing the first two components.  `finiteStage`
quantifies arbitrary objects, one arrow, two cone choices, and both distinguishedness
premises at one stage; it produces an isomorphism with components one and two equal to
identities.  `witnesses` has the same representative equality and cone hypotheses,
then compares the two exact `commonStageCone` triangles by an isomorphism fixing the
pair endpoints and asserts, for every pair triangle `D`, the equivalence of the two
`Nonempty (D ≅ cone)` witness propositions.  Thus all representative, common-field,
and cone-choice clauses are present, with no uniqueness or functoriality assertion.

The statement dependencies and declarations used are:

* `Sheaf.Paper.PbcCommonStageCones`: `AlgebraicGeometry.Scheme.pbcCommonStageDistinguished`, `qbarStagePretriangulated`, and `CategoryTheory.StageSystem.commonStageCone` through its public imports.
* `Sheaf.Paper.FiniteStagePairCategory`: `AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory`, `pbcStageCategory`, `pbcScalarExtension`, `pbcScalarAssociator`, and `pbcScalarSystem`.
* `Sheaf.Paper.PbcScalarExtension`: the recorded coherent scalar-extension package `AlgebraicGeometry.Scheme.pbcCoherentScalarExtension` and its exactness/shift declarations, imported directly for the proof plan.
* `Sheaf.Paper.CommonStageCalculus`: `AlgebraicGeometry.Scheme.commonStageCalculus` and the concrete pair/stage shift and finite-equality interfaces.
* `CategoryTheory.Pretriangulated`: the Mathlib pre-triangulated structure and distinguished triangles.
* `CategoryTheory.Pretriangulated.Triangle`: Mathlib `Triangle`, triangle morphisms, and `Triangle.isoMk`.

I checked equal coefficient fields and repeated extensions, zero arrows and zero cone
objects, equal representatives with different cone choices, and empty schemes.  No
strict field inclusion, nonzero object, nonempty scheme, positive dimension, or
canonical cone choice is imposed.  The `≤` extension binders allow identity stages.

Searches for an existing declaration used `msearch.py ND prop-weil-pbc-cone-independence`
with LeanSearch, LeanFinder, and Loogle queries for common-stage cone independence,
filtered exact functors, and isomorphisms of distinguished triangles; all returned
only generic fixed-category ingredients.  `rg`/grep searches over Mathlib,
`WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json` found no
common-stage PBC cone-independence declaration.  The node's blueprint source and proof
are `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/prop-weil-pbc-cone-independence.md` and its proof file; the Stacks inputs are Tags 014B and 014A.

No new nodes, dependency modules, statement correction, or `STATEMENT-DISPUTED` flag
is needed.  All variables and universes are explicit, the theorem proof is the only
`sorry`, and the declarations have source/blueprint docstrings.

## Validation

The resumed worker read the current main-20261015 statement and proof, all statement
dependency records and their source declarations, and the two Stacks lemmas in the
local source. The upstream StageSystem.Basic module, absent in the older local
checkout, was read using `scompile.py --source`.

The initial local mandatory overlay failed to resolve `ProEtale.lowerStar` and
`upperStar`, before elaborating this item. The wrapper's server confirmation then
compiled every dependency and `PbcConeIndependence.lean` with exit code 0, including
the latter in 2.3 seconds. The older report's stale duplicate-name rationale was
removed: the current scalar-extension module is imported directly for the proof plan.
A second `scompile.py` invocation also passed locally in both sandbox and library
locations (3.8 and 4.0 seconds). After restoring the direct scalar-extension proof
import, the final file passed again in both locations (3.9 and 4.2 seconds), with
exit code 0 and no warnings. The required readiness gate is
`deliver2.py ND prop-weil-pbc-cone-independence --no-push`, with no delivery push
by this worker.

The inherited second-reading text was removed; the independent second reading is
recorded below.
No shared source, tool, or compiler overlay was edited by this worker.

## Second reading by ND

I reread the node statement, its source place, all six statement dependencies,
and `PbcConeIndependence.lean` declaration by declaration.  The node's objects
and clauses are rendered as follows.

* The finite-stage system, pair category, representatives, transitions and
  shift are the generic `StageSystem` variables `I`, `C`, `S`, `PairCategory.Rep`,
  `S.tr`, and `HasShift`; the concrete theorem uses
  `pbcScalarSystem l Ω T hDim.out hInv.out`.
* The first clause (for `M ≤ N`) is `ConeIndependenceSpec.scalarExtension`.
  It quantifies `r`, `hr`, `Z`, `g`, and `h`, assumes
  `Triangle.mk r.u g h ∈ distTriang (C r.k)`, and gives distinguishedness of
  `transportedCone` plus an isomorphism from the mapped triangle whose endpoint
  components are the two associators and whose cone component is an identity.
  `transportedCone` expands the transported first arrow, second arrow, and
  shift comparison in the required order.
* The second clause (equal representatives) is
  `ConeIndependenceSpec.representatives`: equality of the two
  `PairCategory.mkHom` classes, arbitrary distinguished cone data on both
  representatives, a common stage `Q` and equality of transported arrows, then
  an isomorphism of transported cones fixing the first two components.
* The third clause (two cones for one finite-stage arrow) is
  `ConeIndependenceSpec.finiteStage`: arbitrary `M`, `f`, two pairs of cone
  arrows, both distinguishedness premises, and an isomorphism of triangles with
  identity first and second components.
* The final independence clause is
  `ConeIndependenceSpec.witnesses`: the same representative and cone data,
  an endpoint-fixing isomorphism of the two `commonStageCone`s, and for every
  pair-category triangle `D` the equivalence of the two `Nonempty` witness
  propositions.  This is exactly the existential/isomorphism meaning of
  distinguishedness in `def-weil-pbc-common-stage-cones`, including common
  field and cone-choice independence.
* The concrete hypotheses are exactly `(l : ℕ) [Fact l.Prime]`, an arbitrary
  coefficient type `Ω` with `[Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`, a scheme `T : Scheme.{u}` with
  `[IsNoetherian T]`, finite-dimensionality as
  `[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and invertibility as
  `[hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`.  I found no
  extra strict inclusion, positivity, nonzero object, nonempty scheme, or
  characteristic assumption; coefficient and scheme universes remain
  independent.

Edge cases checked were identity extensions (`M = N`), equal representatives,
zero arrows and zero cone objects, different cone choices, and the empty
scheme.  The quantified types permit all of them, and no nonemptiness of an
index or scheme is added.  The finite coefficient index has its existing
directed/base-field instances from `FiniteStagePairCategory`.

I repeated the concept searches with `msearch.py` (LeanFinder queries for
`ConeIndependenceSpec`, transported/common-stage cones, and distinguished cone
independence), and with `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json`; only generic triangle and projectivization
notions were found.  The Stacks source tags 014B and 014A were checked against
the node's source note.  No mismatch was found, so no Lean or node repair was
needed.  The apparent use of `Pretriangulated` rather than a separate
`IsTriangulated` binder is intentional: every stated clause uses the
pre-triangulated distinguished-triangle/TR3 interface, while the Verdier/TR4
theorem is downstream and must not be imported circularly.

The final `scompile.py` run compiled both sandbox and library copies in about
4.5 seconds each with no warnings beyond the permitted theorem `sorry`.
