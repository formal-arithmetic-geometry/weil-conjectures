## Worker report

The delivery states `AlgebraicGeometry.exists_reductive_nodal_equivariant_torsor_extension`
in `Sheaf.AlgebraicGeometry.ReductiveNodalEquivariantTorsorExtension`. Its proof is `sorry`.
The item's natural-language statement is unchanged. Two missing definition nodes supply
its specified nodal torus chart and equivariant represented right torsors.

Hypothesis and clause correspondence:

- Arbitrary DVR A: `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. This is the recorded Mathlib definition, including
  exclusion of fields. The uniformizer is `(π : A) (hπ : Irreducible π)`;
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this with generation
  of the maximal ideal. No completeness instance appears.
- The residue field k=A/(π) is determined by these data, not an extra input or
  hypothesis. The omitted closed locus is literally V(s,t); its coordinate algebra
  is A/(π), since setting both coordinates to zero leaves precisely the relation π=0.
  No residue-field structure is chosen or restricted in the statement.
- An A-group is `H : Grp (Over (Spec (.of A)))`: multiplication, identity and inverse
  are exactly the recorded `CategoryTheory.GrpObj` diagrams with this base.
- Smooth, affine, finite type: `[Smooth H.X.hom] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`. Affineness of the source
  equals affineness over the affine base. The last two classes render finite type.
- Geometric connectedness and absence of a nontrivial smooth connected normal
  unipotent subgroup are `hred`, which uses the existing
  `ReductiveTorusCentralizer.IsReductive` after each field-valued base change b.
  That definition tests the algebraic closure, uses `ConnectedSpace`, the recorded
  normal closed subgroup conditions, and `SolvableGroupStructure.IsUnipotent`.
  The latter requires a faithful closed matrix representation, smoothness, and
  nilpotence of (matrix-1) at every geometric point. Quantifying over all fields
  gives exactly geometric-fibre reductivity: every b lies over one base point,
  and geometric reductivity is stable under field extension. Conversely these
  tests include the algebraic closures of all residue fields. Additional smooth
  affine finite-type conjuncts within this existing field predicate follow from
  the corresponding hypotheses on H by base change; they impose no extra condition.
- X=Spec A[s,t]/(st-π): `NodalTorusChart.chart A π` uses
  `StrictSemistableModel.nodal`, its existing `.scheme` and `.baseMap`, and the
  existing `strictNodalRing`. Its two coordinates use the existing
  `strictNodalCoordinate`. No second coordinate-ring construction is introduced.
- G_m,A: `NodalTorusChart.torus A` uses Spec of Mathlib's LaurentPolynomial A,
  with `instGrpObjSpecAsOverSpec` from its canonical Laurent Hopf algebra. This
  existing Hopf construction works over any commutative ring, so the field-only
  `StandardGroupSchemes.multiplicative` is not incorrectly applied to a DVR.
- The specified action z(s,t)=(zs,z^-1 t) is fixed by `IsStandardAction` on all
  test A-schemes. `standardAction_existsUnique` fixes it uniquely, including
  its complete coordinate formulas. The resulting `standardAction` definition
  selects only this uniquely determined data, as permitted by AGENTS.md §5.
  `openAction_existsUnique` similarly fixes its restriction via the actual open
  immersion. These named postponed verifications are explicitly part of the
  new chart node's statement and have complete construction proofs in docstrings.
- U=D(s) union D(t) is the actual `puncture`, union of scheme basic opens of
  the existing two coordinates. `openChart` carries its structure map over A;
  `inclusion` is its literal open inclusion.
- The input is every `P : EquivariantRepresentedRightTorsor (torus A) H (openChart A π)`.
  It contains the existing `RepresentedRightTorsor`, so the projection is flat,
  surjective, locally finitely presented, quasi-compact and quasi-separated,
  with the specified right action and cartesian torsor square. `leftAction` is
  Mathlib `ModObj`, including unit and multiplication laws. Its `covers` and
  `commutes` equations on all test schemes render exactly the two action conditions.
- The conclusion `∃ Q : EquivariantRepresentedRightTorsor ... (chart A π),
  Nonempty (...RestrictionIso (inclusion A π) P Q)` gives the requested extended
  torsor and equivariant restriction isomorphism. RestrictionIso is a map from
  P to Q with a cartesian base square; by the universal property of pullback
  this is precisely an isomorphism P ≅ Q|_U. Reversing it gives the displayed
  Q|_U ≅ P in the node. `right_equivariant` and `left_equivariant` preserve both
  actions, while cartesianness includes commutation with the projection.
- There is no splitness or perfectness hypothesis, no rank restriction, and no
  specified trivialization of P on either chart.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp` (def-sc-group-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  `irreducible_iff_uniformizer` (def-sc-discrete-valuation-ring, a Mathlib leaf).
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`: `RepresentedRightTorsor`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used through reductivity.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive` (added already-landed dependency).
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`,
  including its GeneralLinearGroup representation and pointwise matrix condition.
- `Sheaf.TraceFormula.StrictSemistableCurve`: `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`.
- `Sheaf.AlgebraicGeometry.OrderedNodalBranchOverlap`: `strictNodalCoordinate`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `ModObj` and its test-point
  action. `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: the canonical base-change
  monoidal functor, `(Over.pullback b).mapGrp`.
- `Mathlib.AlgebraicGeometry.Group.Affine` and
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`: the canonical affine Hopf group
  law on Spec A[z,z^-1]. `Scheme.ΓSpecIso` converts these functions to sections.

The four proof-dependency nodes have no Lean declarations or Mathlib matches on the
read base, so there are no proof-module imports to add for them. Their full proof
plans are retained verbatim in the DAG and rendered step by step in the main docstring.
They are proof dependencies, not missing notions needed to type this statement.

Edge cases checked before writing: a field cannot satisfy the DVR class; 0 and units
cannot satisfy the uniformizer hypothesis. All residue characteristics are allowed,
including imperfect residue fields. Trivial H and arbitrary nontrivial torsors are
included. The puncture includes the entire generic fibre and both non-origin branches
of the special fibre, not just D(st). The chart definition also makes sense over
arbitrary commutative rings and arbitrary parameters, including zero and units; its
substitution construction and invariant-open argument still work. The canonical torus
action has no empty-scheme exception. All test schemes and fields live in the scheme
universe u, avoiding a vacuous independent smaller testing universe. The construction
is polymorphic in u. No theorem besides the named statements has been proved here.

Searches (all Mathlib service searches used msearch.py):

1. LeanFinder: “A reductive group scheme torsor on the punctured nodal surface over
   a discrete valuation ring extends equivariantly”. Eight hits including
   Proj.valuativeCriterion_existence, valuative squares, affine space and rational maps;
   none states the extension theorem.
2. Loogle: `"Torsor"`. Twelve abstract group torsor hits; no scheme torsor extension.
3. Mathlib grep: `Reductive|reductive|Equivariant.*Torsor|Nodal|nodal|Unipotent`
   in AlgebraicGeometry, zero hits. A later full grep
   `Equivariant.*Torsor|Nodal.*Torus|IsStandardAction` also returned zero hits.
4. LeanSearch: “reductive group scheme nodal surface equivariant torsor extension”.
   Eight abstract torsor/group-extension hits, no scheme result.
5. LeanSearch: “nodal surface Spec A s t modulo st minus uniformizer with multiplicative
   group weights one minus one”. Eight valuation, interpolation and weighted-polynomial
   hits, no such chart/action. LeanFinder with the longer action query returned
   unrelated number-field/elliptic actions and affine-space coordinates.
6. LeanSearch: “equivariant represented right group scheme torsor commuting left action”.
   Abstract additive torsors/action homomorphisms only. LeanFinder with the cartesian
   restriction query returned affine-space and representation internal-Hom material.
7. Loogle: `CategoryTheory.ModObj, CategoryTheory.IsModHom`. Found the internal action
   and equivariant-map APIs; these are reused rather than copied.
8. Local rg by declaration and concept in lean/WeilConjectures and lean/Sheaf found
   the represented right torsor, field reductivity and unipotence definitions, and
   the nodal ring/model/coordinate declarations listed above. The exact item id has
   no hit in lean/WeilConjectures. Existing SchemeAction.TorsorObject is a left
   G-torsor with a map to V; it does not encode a right H-torsor with a separate
   commuting left G-action and hence is not the new definition.
9. DAG grep on definition nodes and blueprint_refs.py search for “reductive”, “nodal”,
   “torsor” and “equivariant torsor” found no node for either combined missing notion.
   Existing universal nodal models and strict semistable charts are reused rather
   than redefined. The item's ancestor command reports blueprint.from.node = None.

Source checked: the author-hosted AHLH PDF, Section 2 Claim 2 and Section 3 proof of
Theorem 1.3 (1) implies (2). The latter treats S-completeness for arbitrary DVR tests,
so the main statement's generality is consistent with the source. No statement fault
or STATEMENT-DISPUTED flag was found.

Validation: all three delivered files compile separately through scompile.py against
the published live library, in dependency order, with no errors or unexpected warnings.

## New nodes

`def-sfb-nodal-torus-chart` owns `NodalTorusChart.lean`. It supplies the standard Laurent
Hopf torus over an arbitrary commutative ring, its coordinate-characterized action on
the existing nodal scheme, its actual puncture and inclusion, and its uniquely fixed
restricted action. Source: AHLH Section 2 p.2. Searches 3, 5, 7--9 above and the recorded
Mathlib search results distinguish this from the existing nodal algebra/model and
field-only standard group scheme. Both unique-existence verification theorems are
explicitly included in this node's natural-language statement; their proofs are postponed
and their data are uniquely determined by all displayed equations.

`def-sfb-equivariant-represented-right-torsor` owns `EquivariantRepresentedRightTorsor.lean`.
It supplies only the commuting left action on the existing represented right torsor and
cartesian equivariant restriction maps. Source: AHLH Section 2 Claims 1--2 p.2.
Searches 3, 6--9 above found no duplicate; the right torsor and left action notions are
reused. A cartesian map is used to express an isomorphism with the actual base change,
so it introduces no arbitrary comparison map or stronger triviality requirement.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
