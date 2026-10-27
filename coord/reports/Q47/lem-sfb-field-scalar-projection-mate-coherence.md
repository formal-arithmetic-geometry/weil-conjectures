## Worker report

Module: `Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence`.
Main declaration: `AlgebraicGeometry.ProEtale.FieldActionTransport.field_scalar_projection_mate_coherence`.
One postponed theorem, with `sorry`; the two instance definitions have real existing data.
No node statement, dependency list, proof or source is changed. No new nodes or dependency repairs.

Sources read: the complete item and its nine proof steps; all statement-dependency records;
the full FieldActionTransportData, FieldActionScalarTransportData,
FieldActionGeometricTransportData and FieldActionCoefficientTransportData modules; relevant
CondensedGaloisGlobalDescent definitions; Mathlib Mod and Scheme.ProEt; the internal
coefficientRing construction, CondensedActionModule and total-derived convention interfaces.
Bhatt--Scholze Example 4.1.10 was read in the supplied PDF via pdftotext. The current
blueprint `latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/sk-prop-scalar-six.proof.md`
fixes ordinary direct-image comparison as the unit/pullback/counit mate, with no flatness
requirement on the ambient comparison. The node supplies the more detailed agent argument.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Field and separable closure | `k ks : Type u`, `Field`, `Algebra k ks`, `IsSepClosure k ks` |
| Spec k, Spec ks, Krull group | `Spec (.of k)`; dependency `geometricScheme` and `ks ≃ₐ[k] ks`, with existing Krull topology |
| Compatible small site and coefficient universes | explicit `u`; `Scheme.{u}`, `Profinite.{u}`, modules in object universe u+2 and morphism universe u+1, derived localization at u+2 |
| Tests T[P] and internal actions | existing `GeometricTransport.tests`, `test_fibres`, and normalized `GeometricData.sections` on every P; ActionAbelian is on the actual sectionwise ActionModule |
| Commutative condensed coefficients and arbitrary map | `R R' : Coefficients.{u}`, `φ : R ⟶ R'`; no topological presentation or flatness binder |
| qcqs k-scheme with named structure map | `X : Scheme.{u}`, `a : X ⟶ Spec (.of k)`, `CompactSpace X`, `QuasiSeparatedSpace X` |
| Xs and its projection | `geometricScheme k ks X a`, `geometricProjection k ks X a` from the recorded dependency |
| Ordinary unbounded derived categories | `DerivedCategory (Modules R.toMon X)` and actual rightDerivedFunctor / derivedExtend, with no boundedness conditions |
| Given normalized field, scalar, geometric data | `e e' : FieldData`, `c : ScalarTransport`, `d d' : OrdinaryData`, `g g' : GeometricTransport` |
| Forgetting and point adjunction structures | existing `ForgetData` and `PointAdjunctionData` binders, precisely the actual functors and their underlying unit/counit normalization required by the dependency specifications |
| Scheme rho is normalized derived composition with identity ordinary sections | `arithmeticRestriction : CoefficientComparison`, whose `unit` field is the total-derived-unit equation, and `arithmetic_identity` |
| Geometric rho has the same normalization and identity sections | `restriction : CoefficientComparison`, and `section_identity` is exactly equality on every original normalized profinite-test section |
| Beta is scalar transpose of K(eta) then rho | component equation for β uses dependency `scalarProjection`; its body is `(adjS.homEquiv ...).symm (F.map (adjX.unit.app M) ≫ rho.hom.app ...)` |
| Field-side chi has displayed geometric adjunct | the returned t has `arithmetic_counit`; its LHS is that same scalarProjection and RHS is `geometricAdjunction.homEquiv` of `pullExtension.extension.hom` followed by derivedExtend of the geometric counit |
| Direct-image conjugacy and scalar/pullback exchange | `t.arithmetic.pullRestriction`, `direct_normalization`, `pullExtension`, `restriction_normalization`: AdjunctionSquare.transpose fixes every Hom transpose and hence counits and both triangles |
| Applying D(E R') takes chi to beta under the specified comparisons | `t.projection`, with exactly g'.derived, c.derived.extension and g.derived, and equalities `t.arithmetic.direct = arithmeticRestriction`, `t.restriction = restriction` preserve the given arrows |
| Restricting to geometric slices and forgetting gives the point projection | `t.forgotten_projection`, using the fixed g.forgotten, g'.forgotten and the geometric scalar exchange; the latter identifies u* S_X with S_Xs u* |
| R'-linear point adjunct is scalar extension of the point counit | dependency `pointProjection` is defined by precisely that pointDerivedAdjunction.homEquiv and the PointScalar.square.extension exchange |
| R-linear form is the point projection mate with tensor argument R' | final forall M equation at H = u*M: take the R-linear point adjunct of the scalar restriction of π followed by pointRestriction inverse. RHS is PointScalar.square.restriction followed by restriction of scalar exchange and scalar extension of the R-linear point counit. This is the displayed symmetric projection mate; the scalar factor is the actual extension functor, not an arbitrary tensor or arbitrary map |
| Object comparisons and projections give coefficient data | `∃ t : CoefficientTransport ...`, which includes all the section, field, forgotten, and scalar restriction equations |
| Natural in input morphisms | χ, β and π are natural transformations, fixed by their components for every M/H; the existing object comparisons are natural isomorphisms |
| Compatible with scalar restriction and normalized cocycle | t.restriction_square and t.forgotten_restriction use the fixed CoefficientComparison unit normalizations, and t.point_identity fixes point rho on underlying abelian sheaves. Uniqueness of normalized derived lifts makes these the composition-cocycle comparisons, not arbitrary isomorphisms |
| All comparisons and projections commute with canonical integer shifts | g.derived_shift, g.forgotten_shift, c.derived_shift, t.restriction_shift; explicit CommShift clauses for arithmetic/geometric/point restrictions and exchanges, and for χ, β, π. In particular β and χ shift M, and π shifts H, not only the scalar argument |
| Exact geometric pullbacks and separably closed presentation suffice | dependency exact pullback instances and the stipulated geometric normalization; scalar extension is only total left derived, never assumed exact |

The helper `fieldScalarProjectionPushAdditive` explicitly names the source and target as
`Modules A.toMon Y` and `Modules A.toMon Z` and returns the existing
`coefficientPushAdditive A f`. This avoids an instance discrimination-tree mismatch between
ModuleObject condensedRingObj and coefficientRing presentations; it neither asserts nor
postpones a new additivity result. `condensedScalarProjectionCommShift` is exactly
`(condensedScalarAdjunction f).leftAdjointCommShift ℤ`, the canonical shift requested by
the node. It is a construction, not a new shift chosen existentially.

Dependency declarations used (module, name):

- `def-weil-size-convention`: `None`, `None`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `lem-weil-pbc-profinite-test-object-functor`: `Sheaf.Paper.ProfiniteTestObjectFunctor`, `AlgebraicGeometry.ProEtale.profinite_test_object_functor`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `def-sfb-condensed-action-module`: `Sheaf.CategoryTheory.CondensedActionModule`, `Profinite.CondensedAction.ActionModule`.
- `def-sfb-field-action-transport-data`: `Sheaf.AlgebraicGeometry.FieldActionTransportData`, `AlgebraicGeometry.ProEtale.FieldActionTransport.FieldData`.
- `def-sfb-field-action-scalar-transport-data`: `Sheaf.AlgebraicGeometry.FieldActionScalarTransportData`, `AlgebraicGeometry.ProEtale.FieldActionTransport.ScalarTransport`.
- `def-sfb-field-action-geometric-transport-data`: `Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData`, `AlgebraicGeometry.ProEtale.FieldActionTransport.GeometricTransport`.
- `def-sfb-field-action-coefficient-transport-data`: `Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData`, `AlgebraicGeometry.ProEtale.FieldActionTransport.CoefficientTransport`.
- `lem-sfb-condensed-galois-global-descent`: `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent`, `AlgebraicGeometry.ProEtale.CondensedGalois.condensed_galois_global_descent`.

The size-convention node is metatheoretic (no declaration); its universe requirements are
rendered explicitly. Dependency imports are public through FieldActionCoefficientTransportData;
all already stated proof-dependency modules are ordinary imports. The free-orbit slice
proof dependency has no recorded module, so its import is omitted and its proof step is
retained in the main theorem docstring. Adjunction-mate is a convention with no module.

Edge cases checked before writing: φ=id, including the scalar unit normalization; a
non-flat map such as condensed Z to Z/n (there is no scalar-exactness hypothesis);
X=Spec k; separably closed k and hence trivial G; M=0; X empty; P empty; arbitrary
unbounded M and negative/zero/positive shifts. The R-linear point equation is imposed at H=u*M for every original M, exactly
the input range of the node. No finite
cohomological dimension, boundedness or projection invertibility is asserted.

Searches (2026-10-24):

- msearch LeanSearch, `extension of scalars pushforward projection formula mate shift derived category`:
  eight hits about ordinary ModuleCat/presheaf/sheaf pushforward and scalar adjunction;
  none states this field geometric coefficient coherence theorem.
- msearch LeanFinder, `Scalar extension projection morphism is the mate of the geometric counit and is compatible with shifts`:
  eight hits on Adjunction.CommShift unit/counit compatibility; useful general shift interface,
  no field/action/forgotten projection theorem.
- msearch Loogle, `Adjunction.homEquiv, NatTrans.CommShift`: unknown short identifier,
  zero hits. Read the actual Mathlib Adjunction/Basic and Shift/Adjunction declarations.
- msearch grep, `scalarProjection|CoefficientTransport|projection.*[Cc]ommShift`, CategoryTheory:
  zero hits in Mathlib.
- rg of WeilConjectures and Sheaf for scalarProjection/CoefficientTransport: the recorded
  FieldAction* definitions exist; InternalScalarMateProjection concerns the general internal
  scalar comparison, not this simultaneous field/point coherence theorem. No exact match.
- rg of WeilConjectures for the item id and proposed declaration names: no match.
  dag/lean_names_upstream.json also has no proposed-name match.

Verification: prescribed scompile.py compiled the final module both in sandbox and library
module modes; no errors or non-sorry warnings. Every universe and variable is explicitly
bound; line lengths are at most 100. No mathematical statement fault was found.

## Second reading by Q47

Self-review, rather than an independent-agent review: the dispatcher explicitly prohibits
starting agents, and the maintainer performs the independent delivery review. Reopened the
item and final file side by side. Checked every row above against the relevant dependency
field. The initial plain existence of CoefficientTransport would not expose the requested
shift equation in M; the final file additionally gives χ/β/π as natural transformations
with the exact prescribed components and CommShift ℤ. The final point equation retains
both scalar restriction and point direct-image comparison with the correct inverse
orientation, so the R-linear mate clause is not merely prose. Both supplied rhos are
retained by equalities; the theorem does not replace them with arbitrary newly chosen
comparisons. Only transparent instance adapters were added during elaboration debugging.
No statement correction, missing notion, hollow definition, proof, or extra mathematical
hypothesis was introduced.
