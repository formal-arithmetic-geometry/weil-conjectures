## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PGL2ProperConnectedSubgroupSolvable`
states `AlgebraicGeometry.pgl2_properConnectedSubgroup_smooth_solvable`.
Its only proof is `sorry`; it defines no object and selects no model from an existence theorem.
The informal statement, proof and proof dependencies are unchanged. The statement dependencies
gain the already landed `def-sfb-semisimple-group-scheme`, whose derived-series solvability is
the notion explicitly required by this item.

Hypothesis and clause correspondence:

- Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- The projective matrix group PGL₂ from lem-sfb-projective-matrix-central-cover:
  `P : Grp (Over (Spec (.of F)))`, the maps `π` from the existing GL₂ and `j` from
  the existing μ₂ to SL₂, and
  `hP : ProjectiveMatrixCentralCover.Presentation F 2 (Nat.le_refl 2) P π j`.
  This uses the dependency's complete quotient characterization. Quantifying over any
  presentation is the invariant way to refer to its uniquely characterized quotient;
  π and j expose its recorded interface, not an additional restriction on PGL₂.
  `Nat.le_refl 2` supplies the presentation's fixed degree bound with no extra hypothesis.
- I is an F-group scheme: `(I : Over (Spec (.of F))) [GrpObj I]`.
- I is affine: `[IsAffine I.left]`.
- I is of finite type: `[LocallyOfFiniteType I.hom] [QuasiCompact I.hom]`.
- I is a closed subgroup of PGL₂: `(i : I ⟶ P.X) [IsClosedSubgroupScheme i]`.
  This existing class includes the homomorphism, injectivity on all algebra-valued points,
  and the closed immersion of schemes.
- Strict containment: `hproper : ¬ IsIso i`. For a closed-subgroup inclusion this says
  it is not the whole subgroup scheme. It does not mistake strict containment for the
  scheme-morphism property called Proper, and does not use abstract non-isomorphism of I and P.
- Reducedness: `[IsReduced I.left]`.
- Connectedness: `[ConnectedSpace I.left]`, including nonemptiness.
- Smoothness conclusion: `Smooth I.hom`.
- Solvability conclusion: `IsSolvableGroupScheme I`. By its existing definition this is
  `∃ n : ℕ, GroupSchemeDerivedLength I n`; the zero case is terminality over F and the
  successor case is the smallest closed subgroup containing the scheme commutator morphism.
- No characteristic restriction: there is no characteristic, perfection, invertibility-of-two,
  or smoothness hypothesis on I. Smoothness is one of the conclusions.

Dependency declarations read and reused:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (the algebraic-closure node's match explicitly includes this predicate).
- `CategoryTheory.GrpObj` and `CategoryTheory.Grp`, Mathlib.CategoryTheory.Monoidal.Grp.
  Their specialization to Over(Spec F) is documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.IsClosedSubgroupScheme`, in that same upstream Defs module;
  this extends IsSubgroupScheme and includes IsClosedImmersion of the underlying map.
- `ProjectiveMatrixCentralCover.Presentation`, Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover.
  Its full docstring and signature, including quotient_universal and all geometric clauses,
  were read. The existing GL, SL and roots schemes used in the parameters come through it.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact (the conjunction is the recorded finite-type notion).
- `IsReduced`, Mathlib.AlgebraicGeometry.Properties; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; `Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme` and
  `groupSchemeCommutator`, Sheaf.AlgebraicGeometry.GroupScheme.Semisimple, through the
  added, already landed definition node. These retain all scheme structure.

Statement dependencies are public imports (possibly through another statement dependency).
The module privately imports the stated proof dependencies for identity components,
scheme reduction and smooth geometrically reduced fibres. Properties, closed immersions
and topological dimension are already exposed through the public imports. The proof-only
node `lem-sfb-connected-group-dimension-two-solvable` has neither a Lean record nor a
Mathlib match in the read DAG, so it has no import; its mathematical use is retained
verbatim in the proof docstring. No missing notion is needed to type this item's statement.

Source and edge-case checks:
The Milne PDF was read using pdftotext. Corollary 17.27, printed p.360, gives solvability
in dimension at most two; Theorem 20.16(c) implies (d), printed p.413, explicitly uses
proper subgroups of PGL₂. Our reduced connected version is the precise group-variety
case and adds the smoothness conclusion by the identity-component theorem already
specified in the node's proof. The proof docstring follows all three DAG proof steps.

The identity subgroup is allowed (derived length zero). One- and two-dimensional
connected subgroups, including a maximal torus and a Borel, satisfy the intended conclusion.
The ambient group itself is excluded by `¬ IsIso i`, even if the inclusion is represented
by a nonidentity isomorphism. An empty scheme is excluded by the group identity and
ConnectedSpace. Nonreduced subgroup schemes, such as μ₂ in characteristic two, fail the
reducedness hypothesis; no use of F-points can erase this distinction. Characteristic two
and arbitrary positive characteristic remain included. All field and scheme data use the
same arbitrary universe u, in agreement with the dependency presentations; there is no
independent smaller test-algebra universe and no equality imposed on distinct universes.
No false-statement dispute or source-based correction is needed.

Searches (2026-10-24):

- msearch.py leanfinder, query “Every proper reduced connected closed algebraic subgroup of
  PGL2 over an algebraically closed field is smooth and solvable”: 8 hits, on arithmetic
  subgroups and modular forms; no group-scheme theorem.
- msearch.py loogle, query `"IsSolvable"`: 12 hits on Lie-algebra solvability; no match.
- msearch.py leansearch, query “Every proper reduced connected closed subgroup scheme of
  PGL2 over an algebraically closed field is smooth and solvable”: 8 hits, abstract
  solvability, reducedness and topological closed-subgroup projections; no theorem match.
- msearch.py grep, query `solvab|PGL|ProjectiveGeneralLinear`, subdirectory AlgebraicGeometry:
  3 incidental Gluing matches, no matching theorem.
- rg of WeilConjectures and Sheaf for `pgl2|PGL2|proper_connected|properConnected` found
  only descriptions of matrix-model proof steps in the Borel/reflection modules.
- grep of WeilConjectures for this node id found no declaration. The name chosen for the
  theorem has no upstream, Mathlib-search or Sheaf match.
- rg of Sheaf/AlgebraicGeometry for solvability and derived series located the existing
  Semisimple module; its full definitions were read and used. The alternative
  SolvableGroupStructure.IsSolvable uses a finite series, so the explicitly requested
  scheme-theoretic derived-series interface was preferred.

Validation: scompile.py compiled both its sandbox probe and the actual library module
successfully (7.5 s and 1.5 s), with no errors or warnings.

## Second reading by NI

A second pass by the same worker reopened the node and the complete module. No other
agent was started, as the dispatcher's explicit instruction forbids that; the independent
maintainer review remains separate. This is not represented as an independent second worker.

The comparison checked F/Field/IsAlgClosed; P and its degree-two quotient Presentation;
I/GrpObj/IsAffine/LocallyOfFiniteType/QuasiCompact; the inclusion and existing closed-subgroup
class; non-isomorphism of that inclusion; IsReduced and ConnectedSpace; and both conjuncts
Smooth and IsSolvableGroupScheme. The definition of the latter was reopened to verify
minimal closed commutator factorization and terminality rather than only pointwise abstract
solvability. No mathematical mismatch was found. The one dependency-list omission was
repaired by adding the landed def-sfb-semisimple-group-scheme; no node statement changed.
The proof docstring names all original proof steps and the unstated proof-only node is
explicitly listed above. There are no new nodes or dependency-module repairs to review.
