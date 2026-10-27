## Worker report

Item: `lem-sfb-closed-test-unit-evaluation`, group Q114, stage 2.
Module: `Sheaf.Paper.ClosedTestUnitEvaluation`.
Primary declaration: `AlgebraicGeometry.ProEtale.ClosedTest.closed_test_unit_evaluation`.
The only postponed proof is this named theorem. Its docstring gives the seven-step
DAG proof, with its sources and dependency names. The six helpers have real data.
No statement correction or dependency module is needed. This repair adds one existing:true definition owner for the already-published K-injective-preservation class.

### Hypotheses and conventions

- An arbitrary commutative condensed ring is the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is precisely the unbundled form of the recorded
  `Profinite.CondensedRing`, not a ring presented by a topological ring.
- `condensedRingObj Λ Y` is the recorded `p_Y^* Λ`, underlying `coefficientRing Y`.
  `Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)` is exactly
  the internal module category. The module imports the recorded ordinary total-derived
  functors from `CondensedModuleDerivedPushpull`; there is no alternative derived image.
- Schemes and rings have universe `u`; site objects have universe `u + 1` and
  site morphisms have universe `u`. Set, abelian and ring section values have universe
  `u + 1`. Explicit reconstruction universe arguments retain this distinction.
- `A : Type u`, `[CommRing A]`, `I : Ideal A` introduce all affine-base data.
  `immersion A I` is exactly `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`;
  hence U and Z are the specified spectra, with no arbitrary closed immersion added.
- `V : (Spec (.of (A ⧸ I))).AffineProEt` supplies affineness and ind-etaleness.
  Its lift is the recorded `(closedSiteLift A I).obj V`, denoted B in the node.
  The two `IsWContractibleRing Γ(..., ⊤)` binders are precisely geometric
  w-contractibility of the coordinate rings of V and B. Neither a merely categorical
  projectivity assumption nor a nonemptiness assumption replaces these binders.

### Clause-by-clause translation

1. R_Y and E_Y are the existing `InternalModuleOperations.ring Λ Y` and
   `InternalModuleOperations.equivalence Λ Y`; these abbreviate the recorded
   `sectionRingSheaf` and `sectionModuleEquivalence`. Their actual construction
   preserves underlying abelian sections and restriction maps. No equivalence is chosen
   afresh. The first conjunct states additivity in both directions, homology preservation
   in both directions, homology preservation by both termwise cochain functors,
   K-injective preservation in both directions, and the explicit forward quasi-isomorphism
   implication. The inverse implication follows from the inverse functor's homology
   preservation by the same `QuasiIso` API. Homology preservation expresses exactness
   of sequences in these abelian categories.
2. For every scheme morphism `b`, the second conjunct asserts exactness of internal
   pullback and an isomorphism of its underlying abelian-sheaf functor with ordinary
   abelian inverse image. `upperComparison` and `lowerComparison` are the recorded
   ordinary-module comparisons. The next two displayed equalities are their actual
   adjunction-unit and adjunction-counit equations, respectively.
3. The existential natural isomorphism `q` additionally compares the canonical ordinary
   module inverse image over the inverse-image ring with the internal pullback after
   forgetting modules. Its displayed equation sends the recorded
   `ProEtaleTensorComparison.inverseSection` to the component of the actual internal
   module unit. This is coefficient transport by the specified alpha map, not an
   unrelated module adjunction. Thus the definition dependency for the actual unit
   section is used explicitly.
4. The remaining formula in that conjunct is `(b_* N)(W) = N(X times_Y W)` as an
   equality of underlying `AddCommGrpCat` objects, using the actual `siteMap b`.
   The module action is the existing restriction along `coefficientMap Λ b`.
5. The five consecutive `∀ P Q f, Epi f → Function.Surjective ...` clauses give
   epimorphism surjectivity on V and B in their ambient full sites, V and B in their
   affine basis sites, and the identity object in the basis site of B. In the last
   clause `AffineProEt.mk (𝟙 B.left) (proAffineEtale.of_isAffine _)` is that identity.
6. The next two `SheafOfModules.evaluation ... .PreservesHomology` clauses are ordinary
   section-module evaluation at B and V. The following two composites through
   `Mod.forget`, `sheafToPresheaf` and evaluation assert the same for internal modules.
   These homology-preserving functors apply termwise to unbounded complexes.
7. `IsClosedImmersion (closedSiteLiftInclusion A I V)` and the following `IsPullback`
   give precisely the closed inclusion and V = B times_U Z. `fiberIso` is its canonical
   isomorphism in the full site, extracted from this recorded square.
8. `∀ x, ∃ z, Specializes x (closedSiteLiftInclusion ... z)` is the stated
   specialization property. The subsequent counit clause is LOCAL over B: its ring
   is `Γ(B.left, ⊤)` and its ideal is the kernel of the actual closed-inclusion map
   on global sections. The canonical affine identification B = Spec Γ(B) and the
   quotient identification recover V. The counit is evaluated at the identity over
   Spec Γ(B), not at B as an object of the original U-site. Its invertibility is
   independent of the representation of the canonical adjunction, so the clause is
   expressed for every adjunction of these fixed local lift/base-change functors.
9. `unitSection` is an additive homomorphism made from the GIVEN internal module-unit
   component at B followed by restriction along `fiberIso.hom`. Its source is F(B)
   and its target is (s^*F)(V). The existential additive equivalence `e` is required
   pointwise to equal this homomorphism; it cannot be an arbitrary section equivalence.
   The scalar equation is exactly Lambda_U(B)-linearity. Its right-hand action uses
   `ModuleCat.smul` on the recorded E_Z(s^*F) at V, through `scalarSection`.
   `scalarSection` is the coefficient adjunct at B followed by the SAME fibre
   restriction. Thus it is precisely Lambda_U(B) -> Lambda_Z(V).
   An additive bijection with this equation is equivalently the stated linear
   isomorphism after restriction of scalars; its inverse is automatically linear.
10. `liftSections` is the presheaf V -> F(v(V)) with restriction along v(a).
    `inverseBasis` is the actual internal s^* followed by underlying abelian sheaf
    and restriction to the affine basis. The natural isomorphism `c` identifies the
    sheafification of the former with the latter. Its equation with `toSheafify`
    fixes the comparison on the actual adjunction unit. This is the canonical
    closed-evaluation construction of Stacks 09BL (1), with its normalization retained.
    The equation for `e.symm` states that applying the canonical sheafification map
    to the inverse image of a section equals `c.inv` applied to that section.
    Consequently e's inverse IS the closed-evaluation identification of 09BL (2).
    In particular the map from F(v(V)) to its sheafification is bijective at the
    indicated tests: its composite with c is e. This does not redefine closed
    evaluation as an arbitrary inverse of the unit.
11. The last two conjuncts give naturality under every F -> G and under every
    test map `a : V ⟶ W`, respectively. Both have the same two geometric
    w-contractibility hypotheses for each test involved. The right restriction is
    `liftSections.map a.op`, hence restriction along the specified v(a).
    Since e is the actual unit and is bijective, these equations give naturality
    of its inverse as well.

### Dependency declarations used

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`,
  `isIso_condensedPullbackHom` and `condensedPushforwardHom` in
  `AlgebraicGeometry.ProEtale`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.forget`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`
  and the publicly retained total-derived and K-injective interfaces.
- `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `Scheme.AffineProEt.closedSiteLift` and `closedSiteBaseChange`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, and `IsPullback.isoPullback` for its identification.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf` and
  `sectionModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `AlgebraicGeometry.ProEtaleTensorComparison.inverse`, `inverseRing`, `inverseSection`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
  `InternalModuleOperations.ring`, `equivalence`, `siteMap`, `coefficientMap`,
  `upperStar`, `lowerStar`, `adjunction`, `upperComparison`, `lowerComparison`,
  owned by `def-sfb-section-module-operations`. The transport theorem remains a proof dependency only.
- `WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`:
  `Scheme.AffineProEt.closedSiteLiftInclusion` and `affine_closed_site_functor_properties`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  `CategoryTheory.Functor.PreservesKInjectiveComplexes` and
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes`.

Statement dependencies cite `def-sfb-section-module-operations` for the nine operations
and `def-sfb-preserves-kinjective-complexes` for the preservation class. The geometric
`lem-weil-pbc-affine-closed-site-functor-properties` remains a statement dependency:
`fiberIso` genuinely uses its pullback conclusion. The two normalization theorems remain
proof dependencies. No dependency node is changed. The existing basis and ordinary
abelian inverse-image definition owners are also cited explicitly. Other proof imports correspond to the source's geometric contractibility,
dense-basis comparison, exact evaluation, local counit, specialization-unit and
closed-evaluation proof steps. The statement imports their recorded modules.

### Edge cases checked before and after writing

- I = 0: the quotient closed immersion is the identity up to the canonical affine
  isomorphism; the normalized unit and closed evaluation give the identity comparison.
- I = top: Z and V are empty. The closed lift of the empty affine object is empty
  (the zero algebra is the left-adjoint lift). Evaluation on the empty object is
  the terminal, zero module; the section maps and their inverses remain bijective.
  The specialization assertion over B is vacuous in this case.
- A the zero ring: the same empty-scheme case applies, without a nontriviality binder.
- F = 0 and zero coefficients: all the displayed section modules are zero; the
  additive equivalence and scalar equations still make sense.
- No finite-type, finite-coefficient, torsion, integrality, lisseness, boundedness or
  K-injective-preservation-by-forgetting hypothesis is imposed. The K-injective
  preservation assertion concerns the actual equivalence between module categories.
- Test naturality includes identities and arbitrary maps between the stated tests;
  no surjectivity condition is imposed on the test arrow.

### Searches and source inspection

The following actual wrapper searches are recorded in `searches.jsonl`:

- leanfinder: "Internal modules over condensed coefficients exact closed pro etale
  inverse image unit evaluation on weakly contractible lifted tests". Eight hits,
  including `CondensedMod.IsSolid`, `Condensed.profiniteSolid`,
  `LightCondensed.ihomPoints` and discrete/light-condensed constructions. None states
  the closed-affine geometric actual-unit normalization.
- loogle: `"Sheaf", "IsWeaklyContractible"`. Zero hits.
- grep of Mathlib: `(closedSiteLift|IsWeaklyContractible).*(unit|eval)|(unit|eval).*(closedSiteLift|IsWeaklyContractible)`.
  Zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for closed-test-unit names,
  closed/evaluation and internal operations, and exact item-id `grep -rn` over
  `lean/WeilConjectures`: no exact existing declaration. Related existing results
  include InternalModuleOperationsTransport, AffineClosedInverseImageEvaluation,
  ProEtaleModuleSpecializationUnit, ClosedLiftedTestIsomorphismCriterion and
  SectionDerivedPushpullNormalization. They supply parts or downstream applications,
  not the entire statement with the actual-unit closed-evaluation equation.
- Read the full item, all statement-dependency statements and Lean records, and the
  signatures/docstrings of their recorded source declarations. Read Stacks
  `proetale.tex` at `lemma-closed-immersion-affines` and
  `lemma-closed-immersion-affines-apply`, including the proof of (2).

No STATEMENT-DISPUTED issue was found. The imported CompactObject example is now a
withdrawn empty module, so the header and module-mode conventions follow the current
standing brief and the active dependency modules instead.

## Second reading by Q114

I reopened the node and the final module and checked each clause against the list above.
This is the dispatch worker's own second pass; the maintainer performs the independent
review. The fixes from this pass were to make the ordinary inverseSection comparison
explicit, include internal as well as ordinary homology evaluation at both tests, retain
the original site universes in the reconstruction, and restrict the two final naturality
clauses to the node's stated test family. The local counit is over Spec Γ(B), and does
not conflate the lift over B with the original lift over U. I checked that the c-equation
uses the sheafification unit, and that e's scalar action is through the actual coefficient
map, rather than merely postulating an unrelated additive equivalence. Every helper has
real data; only the named main theorem has `sorry`.

## Validation

All compilation uses the prescribed `scompile.py` server wrapper. Both the sandbox and
named-library mode compiled within the 60-second per-file limit. The final delivery
is also checked by `deliver2.py --no-push`, including its server preflight and compile.

## New nodes

`def-sfb-preserves-kinjective-complexes` owns the existing upstream class
`CategoryTheory.Functor.PreservesKInjectiveComplexes` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, lines 77--84.
Its sole field says exactly that every K-injective cochain complex has K-injective
termwise image. Abelian categories, additivity, integer-indexed cochain complexes and
the null-homotopy K-injectivity convention are cited through their existing nodes.
The object and morphism universes of C and D are independently quantified upstream.
The source is Stacks derived.tex, 070H and the conclusion of 08BJ. This is an
existing:true owner, with no copied definition or new Lean module.

Searches are embedded verbatim as wrapper result records in the new node: LeanSearch
returned IsKInjective and preservation of injective objects, LeanFinder returned exact
derived functors and shift stability, Loogle found no preservation class, and Mathlib
grep found no occurrence. DAG definition grep found only two search-log occurrences;
source grep found the class in upstream Comp.lean:82, and no duplicate class in Sheaf.
The blueprint search returned 77 related nodes, none owning the preservation class;
blueprint_refs ancestor returned None. Edge cases: the zero complex is included,
complexes are unbounded, and no right-adjoint or exactness assumption belongs in this
definition. These are sufficient criteria in the separate theorem, not part of the property.

## Returned-head repair

Returned immutable head: a7850939ee86. The initial retained-packet dry run passed as
7bdd516a026. Comparing with current main found differences only in lean and stmt_deps.

1. Replaced stmt_dep lem-sfb-internal-module-operations-transport by the live
   def-sfb-section-module-operations, whose declarations list owns ring, equivalence,
   siteMap, coefficientMap, upperStar, lowerStar, adjunction, upperComparison and
   lowerComparison. The theorem stays in proof_deps and its module stays imported.
2. Replaced stmt_dep lem-weil-pbc-right-adjoint-preserves-kinjective by the new
   existing:true definition owner def-sfb-preserves-kinjective-complexes. Its exact
   published class and sole field were read in full. The criterion theorem stays
   in proof_deps. The Lean statement is retained byte for byte.
3. Retained lem-weil-pbc-affine-closed-site-functor-properties: fiberIso uses its
   IsPullback conclusion and isoPullback.

The advisory owners def-weil-pbc-ind-etale-basis (AffineProEt/topology) and
def-sfb-finite-upper-star (ordinary abelian upperStar) are now cited explicitly.
The bare underlying-abelian-sheaf iso remains as accepted in the returned review;
the stronger coefficient-sensitive q is already pinned to the actual internal unit.
No mathematical hypothesis or conclusion changed.

### Second reading of the repair by Q114

Reopened the main signature and all new ownership records. The two preservation
conjuncts use precisely the class in the new node; its field is exactly termwise
K-injectivity preservation, with no exactness or adjunction assumption. All nine
section-module operation names are in the landed definition owner's declarations.
The source square still determines fiberIso, so its theorem dependency is genuine.
Only ownership records and this report changed in the repair; the accepted clause-by-clause
translation and edge-case checks above still apply. No statement correction is needed.

### Repair validation

The retained Lean module compiled cleanly through scompile.py in sandbox mode
(24.7 seconds) and its library name (26.0 seconds). The first repaired-packet dry run
reported one field error: the current server requires import_flags on new nodes
(tools/stage2_delivery.py, updated 2026-10-23). Added import_flags: [] as requested.
Its theorem-stmt_dep warning for affine-closed-site-functor-properties is retained
because the independent returned review explicitly passed the genuine IsPullback use.
