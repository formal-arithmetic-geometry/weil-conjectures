## Worker report

The delivery states the normalized relative restriction mate and its compatibility with
forgetting a residual action. It uses the already landed relative-invariant interfaces,
adding their two owning nodes to stmt_deps, as authorized by brief-stage2 section 5.
It introduces no second action category, invariant functor, derived functor, beta, or delta.
Every new theorem has proof `sorry`; the three helper constructions have actual data.

Sources read: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
and the item's complete seven-step extracted proof. The current blueprint paragraph
assembles proper and open direct images; it does not itself state this auxiliary lemma.
The node correctly labels the auxiliary argument agent-formulated and its combined
external reference WANTED. Ingredient statements were read in literature/stacks-project/
derived.tex: lemma-derived-adjoint-functors (09T5),
lemma-bounded-below-injectives-K-injective (070J), lemma-K-injective-defined (070Y),
and lemma-derived-shift (05SU). No statement correction is made.

Hypotheses and clauses, including reused declarations:

- Arbitrary commutative condensed R: `A : CondensedBar.Ring.{u}` is exactly the bundled
  commutative monoid object in abelian sheaves on `coherentTopology Profinite.{u}`;
  `A.toMon` is the recorded `Profinite.CondensedRing` with commutativity. No presentation
  by a topological ring or restriction to discrete coefficients is assumed.
- Internal modules and all generalized group sections: `CondensedBar.Modules A` and
  `Equivariant A P` transparently abbreviate `Profinite.CondensedAction.Modules A.toMon`
  and `ActionModule A.toMon P`, respectively. Those definitions quantify over every
  profinite test object and its continuous P-valued maps.
- Profinite G,H: the binders `[Group] [TopologicalSpace] [IsTopologicalGroup]` and
  `[CompactSpace] [T2Space] [TotallyDisconnectedSpace] give exactly profinite groups.
  The reusable projection and forgetting helpers work for a topological second group,
  so they cover both H and the discrete integer group without imposing compactness on Z.
- The discrete cyclic group and u: `Z.{u}` is the already defined
  `Multiplicative (ULift.{u} ℤ)` with discrete topology; `v : Z.{u} →ₜ* H` is u.
  `RelativeCyclic.generator` is +1, hence tau is v applied to that generator. Tau does
  not occur independently in any equation here and needs no redundant binder.
- Trivial-J inflation L: `inflate (ContinuousMonoidHom.fst G J)`.
  Its normalized right adjoint is `(RelativeCyclic.invariants A G J).functor`,
  including the actual invariant-submodule inclusion and both adjunction transposes.
  `projectionAdjunction` abbreviates its canonical derived adjunction.
- Restriction V: `inflate (productMap (G := G) v)`, where productMap is id_G times v.
  `projectionRestriction` has identity underlying internal-module maps in both
  directions, and `projectionRestrictionDerived` is its exact-localization image.
  It is a construction, not an arbitrary assumed square or an unspecified isomorphism.
- Bounded-below normalization: `projectionAdjunction_plus` states agreement of BOTH
  unit and counit with `Adjunction.derivedPlus`, using the fixed exact-functor and
  `rightDerivedFunctorPlusCompatibility` comparisons. Instantiate K by H and Z.
  This supplies the precise identification used to interpret the ambient derived
  functors on D-plus. The primary `beta_mate` quantifies over `DerivedCategory.Plus`.
- Canonical derived mate beta: `beta_mate` is the unit, localized inflation-square,
  and restricted-counit formula of `def-weil-pbc-adjunction-mate` with its identity
  horizontal functor. It identifies the existing canonical rightDerivedPullback beta;
  it does not choose a new natural transformation or postulate an arbitrary mate.
- Q and alpha: `DerivedCategory.Q` and `RelativeCyclic.unit` are the actual localization
  and `rightDerivedFunctorUnitQ`. The existing `RelativeCyclic.betaNormalization`
  reads `unit P ≫ beta(QP) ≫ RGamma_Z(V.mapDerivedCategoryFactors.hom P) =
  Q(invariantRestriction_P) ≫ unit(VP)`. This is precisely the displayed node equation
  with its suppressed exact-localization identification written explicitly. It holds
  for every complex, hence in particular every bounded-below P, and has no injectivity
  hypothesis on VP. It is not restated in this module.
- The underived inclusion iota: `RelativeCyclic.invariantRestriction v` is the unique
  transformation commuting with the fixed-section inclusions. Its termwise map is
  `NatTrans.mapHomologicalComplex ... (.up ℤ)` in betaNormalization.
- H-zero on modules: the existing `RelativeCyclic.betaDegreeZero`, with
  `RelativeCyclic.degreeZeroIso` fixed by `degreeZeroUnit`, says exactly that the
  conjugated zeroth-homology map is `invariantRestriction v`.
- U_J and U_0: `RelativeCyclic.forgetResidual A G J` is restriction along j ↦ (1,j),
  definitionally the `ProductForgetting.forgetFirst` functor, and `CondensedBar.forgetAction`
  forgets G. The existing `forgetInvariants` is uniquely fixed by the identical actual
  inclusions, as stated in `forgetInvariantsExist`.
- Delta_J: the existing `forgetDerived A G (J := J)` is a natural ISOMORPHISM
  `derived A G J ⋙ D(U_0) ≅ D(U_J) ⋙ scalarDerivedInvariants`.
  `forgetDerivedExist` gives its computation-unit equation for EVERY complex. In
  particular it fixes it on every bounded-below injective complex, exactly as requested.
- Equality with scalar restriction: `beta_forget_natTrans` is an actual equality of
  natural transformations. Its left side is D(U_0)(beta) followed by delta_Z; the
  right side is delta_H, the scalar `CondensedDerivedRestriction.groupMap A v`, and
  the localization of the identity-underlying U/V commutation comparison
  `forgetRestrictionDerived`. Existing `forgetBeta` already states its components;
  no equality only after applying cohomology is substituted here.
- Shifts: the existing `RelativeCyclic.betaShift` and `forgetDerivedShift` use the
  fixed canonical `CommShift ℤ` structures. No transported arbitrary shift is assumed.
- Triangle boundaries: `beta_boundary` and `forgetDerived_boundary` write the last
  triangle-arrow squares including every canonical shift comparison. The first two
  squares are ordinary naturality of the existing natural transformations.
  The latter theorem applies to K=H and K=Z. The ambient formulas restrict to D-plus;
  the existing functors carry distinguished triangles to distinguished triangles.
- The warning in the final sentence is respected: no new theorem takes
  `PreservesInjectiveObjects V`, injectivity of VP, or injectivity of a restricted
  injective complex as a hypothesis. The proof cancels only the original source unit.

Dependency declarations used/read (modules are the recorded ones):

- Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing`.
- Mathlib.CategoryTheory.Monoidal.Mod: `CategoryTheory.Mod`, `ModObj` and its module laws.
- Sheaf.CategoryTheory.CondensedActionModule: `ActionModule`, `Modules`, `inflate`,
  `ProductInvariants`, `Invariants` and their inclusion/transpose fields.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic: `Injective`; its resolution API
  is Mathlib.CategoryTheory.Preadditive.Injective.Resolution, `InjectiveResolution`.
- Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus: the scalar calculus,
  `restrictionDegreeZero`, `boundedBelowComputation`; its definition module
  CondensedDerivedInvariants supplies `groupMap` and `groupMapNormalization`.
- Sheaf.CategoryTheory.ProductActionExactForgetting: `ProductForgetting.Datum`,
  `ExactForgetting`, and `exists_datum`; this is a proof-only import.
- Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus:
  `rightDerivedFunctorPlus`, `rightDerivedFunctorPlusUnit` and universal property.
- Mathlib.CategoryTheory.Adjunction.Mates: `mateEquiv` and its unit/counit formula.
- Mathlib.Algebra.Homology.DerivedCategory.TStructure: `DerivedCategory.Plus`.
- Sheaf.CategoryTheory.RelativeDerivedInvariants: `invariants`, `derived`, `unit`,
  `beta`, `productMap`, `invariantRestriction`, `betaNormalization`, `betaDegreeZero`,
  `degreeZeroIso`, `betaShift`, `forgetResidual`, and the small-Hom localization instances.
- Sheaf.CategoryTheory.RelativeInvariantForgetting: `forgetInvariants`,
  `forgetDerivedExist`, `forgetDerived`, `forgetRestrictionDerived`, `forgetBeta`,
  `forgetDerivedShift`.
- Proof interfaces are imported from BoundedBelowDerivedMateModel, RightDerivedSingleH0,
  CondensedRestrictionMateNormalization, RightDerivedFunctorOfQuasiIsoResolutions,
  CanonicalRightDerivedAdjunctionShift, and the recorded Mathlib derived adjunction,
  K-injective and injective-resolution modules. The Grothendieck K-injective and
  triangulated derived-functor modules are already publicly imported by the relative
  definitions. The infrastructure proof node currently has no Lean binding and so has
  no separately recorded module to import.

Size and edge checks: u is explicit and autoImplicit is false. The same u contains
both parameter groups; the already published size convention puts abelian section
sets and derived Hom sets in u+1. No site-object/morphism universe equality is added.
G=1, H=1, the zero ring, and v=0 all satisfy the binders. For G=1 the forgetting square
reduces to the scalar square. For H=1 the fixed-section inclusion is still the correct
restriction map. The zero complex and all lower bounds are admitted: no degree-zero
or nonnegative truncation is substituted. For arbitrary restricted injective I,
unit(VI) occurs without being inverted. Negative and positive shifts are included
in the existing CommShift statements; the triangle square uses the signed +1 comparison.

Searches actually run via msearch.py, group Q66, this item:

- leanfinder: "Derived mate of restriction commutes with forgetting a residual condensed
  group action". Eight hits, principally ContAction.resComp/mapContActionComp and condensed
  discrete-module adjunctions; none states this relative derived mate.
- loogle: "CategoryTheory.mateEquiv, CategoryTheory.Functor.rightDerivedFunctorPlus".
  OK, zero hits for the joint query; the separate recorded generic APIs are used.
- grep, CategoryTheory: "mateEquiv|rightDerivedFunctorUnitQ". Twenty hits, including
  CategoryTheory/Adjunction/Mates and bicategorical mate APIs; no specialized result.
- rg in lean/WeilConjectures and lean/Sheaf for relativeRestriction, relative.*mate,
  ProductInvariants and the exact item id. This found the already published
  RelativeDerivedInvariants and RelativeInvariantForgetting interfaces reused above;
  no existing explicit relative beta mate theorem was found. Further direct source
  search for rightDerivedPullback/mate found the generic normalization API.

No new nodes, dependency repair, statement dispute, or statement correction is needed.
The two stmt_deps additions refer to already published nodes and prevent a private copy
of their definitions. Clean scompile.py validation succeeded for both sandbox and
library module names (5.9 s and 5.4 s), with no warnings or errors after shortening
exactly the two long lines reported by the first compile.

## Second reading by Q66

A separate rereading pass checked the module against the node and the imported interfaces.
The dispatcher explicitly forbids starting another agent, so this records a self-check,
not a claim that an independent reviewer has approved the mathematics. The maintainer's
independent review remains the delivery review.

The mate orientation is L_Z → V L_H, giving RGamma_H → RGamma_Z D(V), not the reverse.
Both arrows of projectionRestriction have the identity underlying map. The mate formula
retains the localized projection comparison; omitting it would identify nondefinitional
localization choices. The unit and counit agreement formula uses the plus-to-ambient
comparisons in the same orientation as the scalar normalization module.

The delta orientation is D(U_0) RGamma_relative → RGamma_scalar D(U_J); in Lean's
left-to-right functor notation this is `derived ⋙ D(U_0) ≅ D(U_J) ⋙ scalarDerived`.
The forgetting square ends in `D(V) ⋙ D(U_Z) ⋙ scalarDerived`, and its rightmost
comparison maps `D(U_H) ⋙ D(v*)` to that functor in the correct direction.
Its components are exactly the existing forgetBeta formula. The H-zero and unit
clauses are already recorded under their owning nodes and were not duplicated.
The original source unit is the only one cancelled in the proof; there is no hidden
injectivity assumption on V(I). The boundary equations use each composite functor's
canonical commShiftIso at +1. The two line-length faults were corrected and the final
source compiles cleanly. No mathematical mismatch was found in this rereading.
