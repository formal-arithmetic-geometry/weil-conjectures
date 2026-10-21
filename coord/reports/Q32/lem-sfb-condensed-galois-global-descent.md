## Worker report

Stage 2, Q32, lem-sfb-condensed-galois-global-descent. The prior worker's block concerned the already-reviewed O2 stage-1 split, not a stage-2 statement. The live node has reviewed.result=pass and no lean record. Its stage-1 statement, eleven proof steps, proof dependencies and review record are preserved. This delivery supplies its first Lean statement, in Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent. The primary theorem is AlgebraicGeometry.ProEtale.CondensedGalois.condensed_galois_global_descent. All theorem proofs are sorry; definitions and structure/instance data contain no sorry.

The signature is `theorem condensed_galois_global_descent [CompactSpace X] [QuasiSeparatedSpace X] : Assertion k ks X a`, in the explicitly bound context `(k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks] (X : Scheme.{u}) (a : X ⟶ Spec (.of k))`. The helper specifications make every part of Assertion inspectable. No unspecified existence choice defines a geometric map: twist is chosen from a unique-morphism theorem with a fibrewise formula, and delta is explicitly constructed from the normalized underived gamma and the existing derived-composition isomorphisms.

Hypothesis and clause matching:

| Node clause | Lean rendering |
| --- | --- |
| k a field, ks/k a separable closure | Field k, Field ks, Algebra k ks, IsSepClosure k ks |
| G=Aut_k(ks), with Krull topology | ks ≃ₐ[k] ks throughout; Mathlib's Krull topology instance, publicly imported via Galois.Profinite |
| X qcqs over k | X : Scheme, a : X ⟶ Spec (.of k), CompactSpace X, QuasiSeparatedSpace X |
| Xs=X times_k ks | geometricScheme is the actual scheme pullback; geometricProjection is its first projection |
| Arbitrary commutative condensed R, RX=pX*R | Coefficients is the existing CondensedBar.Ring, i.e. CommMon of profinite abelian sheaves; Modules uses the existing coefficientRing X R.toMon and Mathlib Mod |
| Internal action category AG(R) | Existing Profinite.CondensedAction.ActionModule, with its original preadditive structure, not ordinary/discrete representations |
| All profinite tests Xs[P] and restrictions | test, testMap and tests are built from profiniteToProEtOf (geometricScheme ...); geometricPresheaf restricts the ORIGINAL module on X to these objects |
| Equivariant geometric sections on P | GeometricData.sections is a natural isomorphism of presheaf-valued functors, so it includes every test restriction and every module map |
| The pulled-back R action, not an unrelated module | GeometricData.underlying identifies the actual internal module functor geometricSections, built using CondensedRing.upperStar and the point direct-image unit scalar map; GeometricData.normalization ties sections to this same module identification through geometricRestriction, the actual pullback unit followed by its graph restriction |
| The action induced by k-descent | GeometricData.action is equality with M.X.obj.map (twist ... g).op for EVERY P and continuous g:P→Gal(ks/k); twist_existsUnique specifies the X-map on every geometric fibre by the actual Spec.map of g(p) |
| Grothendieck abelian action category | Assertion existentially supplies existing CondensedBar.ActionAbelian and IsGrothendieckAbelian for EVERY R; these are conclusions, not hypotheses |
| Ordinary invariant-submodule functor | OrdinaryData.invariants is the recorded Invariants specification, including the actual invariant inclusion, image FixedAll, and normalized trivial-inflation adjunction |
| Ordinary total derived K_R and RΓG | derivedGeometric and derivedInvariants use Functor.rightDerivedFunctor on these Grothendieck categories; no boundedness restriction or bar model |
| ev_* at the singleton and forget scalars; exact | pointEvaluation is Mod.forget, sheafToPresheaf, then evaluation at Profinite.of PUnit; pointEvaluation_exact states both finite-limit and finite-colimit preservation |
| Canonical underived comparison | OrdinaryData.gamma and normalization: after inclusion into geometric sections and GeometricData.sections, it is exactly restriction along terminalMap, the structural map Xs[*]→X |
| Canonical natural isomorphism δ in D(Ab) | delta is rightDerivedFunctorNatIso gamma, rightDerivedFunctorCompIso for the geometric functor, then the exact-right-factor comparison for invariants followed by pointEvaluation.mapDerivedCategory |
| No missing derived-existence hypothesis | Standard localizations are named global instances; ordinary modules are Grothendieck from the published module-object framework; action Grothendieck structures are existential outputs. Assertion supplies geometric preservation of K-injectives, from its exact left adjoint in the source proof |
| Every coefficient map R→R' | Assertion quantifies over every morphism of the existing commutative condensed ring category, without flatness, injectivity or topological presentation |
| Actual scalar restriction | restrictX is Mod.comap of (upperStarFromPoint X).map φ.hom.hom; restrictCondensed is Mod.comap φ.hom.hom; the existing CondensedBar.ScalarAction fixes the residual action and underlying scalar restriction |
| Canonical geometric and invariant derived comparisons | CoefficientComparison.ordinary and .derived are tied by the total-right-derived UNIT equation; ScalarData.sections fixes the geometric ordinary comparison on every original section, and .inclusion fixes the invariant comparison under the invariant inclusion |
| Corresponding global and final invariant morphisms | ScalarData.global_unit uses the actual global-section derived unit; invariant_formula writes the final arrow as geometric comparison, invariant comparison, and the exact scalar/evaluation comparison |
| Every M→Res M' | ScalarAssertion quantifies over arbitrary objects of both UNBOUNDED derived categories and every f:M→(restrictX φ X).mapDerivedCategory.obj M'; it writes the equality of the two delta-square composites explicitly |
| Shifts and distinguished triangles | Assertion requires NatTrans.CommShift delta.hom ℤ and invariantSide.IsTriangulated, with the canonical right-derived and exact-functor shift structures. Global sections' right-derived functor is triangulated by the published instance. Thus mapTriangleIso is a morphism of distinguished triangles, including the connecting arrow |
| Ordinary derived categories, no cochain replacement or finite cd | All inputs are DerivedCategory of the recorded internal categories, and all derivation is ordinary right derivation on unbounded ℤ-cochain complexes. There is no cohomological-dimension, boundedness, admissibility, discreteness, K-flatness or bar-cochain hypothesis |

Dependency declarations read and used:

- Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing, the full arbitrary ring-object type.
- Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, Mod.forget, Mod.comap and their actual actions/maps.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: Functor.rightDerivedFunctorOfQuasiIsoResolutions, its universal pair and unit. This recorded convention is imported; on the Grothendieck module categories here the published Functor.rightDerivedFunctor gives the same ordinary total derivation with its public canonical unit/composition API.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing, coefficientRing_X, upperStarFromPoint, pointUpperStarLowerStarAdjunction, profiniteToProEtOf. The full signatures and formulas were read.
- Sheaf.CategoryTheory.CondensedActionModule: Modules, sectionModule, ActionModule, forgetAction, Invariants, FixedAll; the action is indexed by C(S,G), not G alone.
- Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses: ringedSiteZerothHypercohomologyOfUniverses, the existing H0-after-RΓ convention on section modules. Here globalSections uses the same actual underlying terminal sections, and total RΓ stays in D(Ab) as required, rather than passing to H0.
- WeilConjectures.Mathlib.FieldTheory.IsSepClosed: IsSepClosure.exists_intermediateField_mem and Mathlib IsSepClosure.
- def-weil-size-convention is a convention node without a declaration; universes u and u+1 on sites/coefficients and standard u+2 localizations implement it.
- Sheaf.Paper.ProfiniteTestObjectFunctor: profinite_test_object_functor, with finite coproduct, finite-limit, inverse-limit and cover clauses, using the same profiniteToProEtOf.
- Sheaf.AlgebraicGeometry.ProEtalePointPullback: sfbPullbackFromPointRightAdjoint, sfbPullbackFromPoint and sfbPullbackFromPoint_spec. The point adjunction and scalar action are their actual published composites.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs: CondensedRing.upperStar; geometricSections uses its actual coefficient-compatible pullback.
- Sheaf.CategoryTheory.CondensedEquivariantBarData: CondensedBar.Ring, ActionAbelian, actionAbelian, ScalarAction, ScalarAction.additive and ringComm. Only these existing categorical specifications are used, not Assertion(G), a nonnegative injective resolution, or the bar computation. This existing definition node is added to stmt_deps instead of duplicating its notions.
- The declared, already-stated proof dependencies are imported as prescribed. The still-unstated field-site, dense-subsite, action-topos, locally-surjective-epi and forget-exactness nodes have no modules to import. No proof prerequisite is treated as an assumed conclusion of this theorem.

Three already-landed statement nodes are added to stmt_deps because the statement's constructions use them: sk-def-sfb-pullback-from-point, sk-def-sfb-module-pushforward-pullback, def-sfb-condensed-equivariant-bar-data. This is the allowed addition of existing landed definition interfaces; no source statement, proof, review or target is changed. No dependency repair or independent new notion/node was needed. GeometricData, OrdinaryData, CoefficientComparison, ScalarData and Assertion are the specifications belonging to this owning theorem, and all their declarations are listed in lean.declarations.

All postponed helpers are named theorems in this same owning module, with source and complete proof docstrings: pointUnit_isMonHom, geometricProjection_weaklyEtale, singleton_isIso, automorphism_condition, twist_existsUnique, testMap_laws, sections_additive, pointEvaluation_exact, restrictX_exact, restrictCondensed_exact, and the primary theorem. Their names are in the owning DAG lean.declarations record. There is no sorry data, axiom, arbitrary geometric map, or arbitrary chosen derived comparison. The one choice, twist, is from ExistsUnique and is fixed by its explicit fibre formula.

Edge cases checked before writing and again on the complete statement:

- Empty X and zero R: all relevant section modules are zero; no Nonempty X, Nontrivial R or choice of a point of X is required.
- Empty P: test is the empty scheme, the variable action map is uniquely the empty map, and twist's fibre specification correctly determines that map. Test-map restrictions still include maps from the empty test.
- Trivial G (k separably closed): fixed sections are all sections, the canonical geometric restriction is the identity up to the recorded terminal/test identifications.
- Nonperfect k is allowed: IsSepClosure, not an algebraic closure, is used; there is no characteristic restriction.
- Arbitrarily negative and positive cohomology: every input is in the ordinary unbounded DerivedCategory; geometric preservation of K-injectives comes from the exact left adjoint, never finite cd.
- Nonflat coefficient maps, e.g. Z→Z/n: the coefficient comparisons use total-derived UNIT equations and ringed-composition existence; no restriction functor is assumed to preserve K-injectives.
- Identity coefficient maps and arbitrary f:M→Res M': both occur in ScalarAssertion with no exclusions. Naturality in M is already part of delta as a natural isomorphism; the explicit square covers every derived f.
- Size: schemes and separable-closure fields share the small u bound; the pro-etale site retains object universe u+1 and morphism universe u. Coefficients are Ab.{u+1}; derived localizations use u+2. No equality of site object and arrow universes is imposed.

Searches actually run with the prescribed wrapper are retained in searches.jsonl:

1. LeanFinder: "Global sections on the pro-etale site of a field are invariants of geometric sections with condensed Galois action in unbounded derived categories". Eight hits: condensed free/solid/lifted sheaf constructions and InfiniteGalois.asProfiniteGaloisGroupFunctor, not this comparison.
2. LeanSearch: "unbounded derived Galois descent for condensed sheaves on a field". Eight hits: Condensed/LightCondensed definitions, ofSheafProfinite constructors and discreteUnderlyingAdj, none the equivariant ordinary-unbounded descent assertion.
3. Loogle: "CategoryTheory.Action, DerivedCategory, IsSepClosure" was invalid (unknown CategoryTheory.Action), and is not evidence of absence. The replacement query "DerivedCategory" succeeded with twelve standard derived-category definitions, not Galois descent.
4. Wrapper grep: "galois.*descent|[Gg]alois.*[Ii]nvariant|[Cc]ondensed.*[Gg]alois". Five Mathlib hits concern IsGaloisGroup invariant ring actions and unrelated Galois order correspondences; none has the geometric/condensed derived statement.
5. rg on lean/WeilConjectures and lean/Sheaf for Galois descent and geometric sections found lisse-Galois sections, finite/discrete descent, algebraic Brauer descent and clopen geometric sections. Their scopes do not give this theorem. Exact item-id search in WeilConjectures found no declaration. Read the recorded action/invariant and ringed-comparison APIs rather than introducing a new action category.

The precise external literature proof remains WANTED as the existing source and O2 split report say. This delivery preserves that honest provenance and follows the reviewed eleven-step proof, stated in the theorem docstring. No STATEMENT-DISPUTED or node correction is needed.

## Second reading by Q32

This is a separate in-thread source/signature rereading by the dispatched worker; no other agents were started. The maintainer will independently review the delivery. I reopened the live node, the dependency signatures and the final module. The table above records every hypothesis and conclusion clause.

The rereading checked in particular that (1) the statement supplies action Grothendieck/abelian structures instead of assuming them; (2) the geometric functor is identified with the original sections on EVERY profinite test, with action by every continuous generalized Galois element; (3) delta is an actual natural isomorphism of ordinary derived functors; (4) geometric/invariant scalar comparisons are pinned by underived section/inclusion identities and total-derived unit equations, so an arbitrary commuting isomorphism cannot satisfy the specification merely by being chosen; (5) the final coefficient arrow is explicitly their composite; (6) ScalarAssertion includes every f:M→Res M'; and (7) CommShift and IsTriangulated use the canonical shifts, giving the connecting-arrow square of distinguished triangles. The source's no-finite-cd and no-underived-cochain requirements survive literally as absence of such hypotheses or substitutions.

A first complete dry run passed. A further rereading found that the presheaf section isomorphism should explicitly agree with the R-module identification. Added testGraph and geometricRestriction, built from the actual module pullback unit, and GeometricData.normalization equating that canonical map with the underlying internal-module isomorphism. This makes the scalar identification explicit instead of merely giving two unrelated natural isomorphisms. No mathematical hypothesis or conclusion changed.

The generic site universes, arbitrary coefficients, zero/empty/trivial-group cases, sorry-only theorem bodies, real definition data, source/blueprint docstrings, declaration list, and 100-column limit were checked. No statement correction was made. Compilation succeeded in both wrapper modes before delivery preparation; the prescribed dry run will check the final exact file and record again.
