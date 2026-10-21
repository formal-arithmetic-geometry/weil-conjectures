# NM: coordinate faces of the unpunctured full root tower

## Worker report

This is stage 2. The Q02 report and maintainer review on the live node concern stage 1;
they supply the accepted nine-step proof split, not a Lean declaration. The earlier
worker's stale-dispatch diagnosis was incorrect. The live item has no Lean record.
I retain its statement, source, proof, proof dependencies and all review metadata.
This packet repairs the H2/H3 return of head ae952e25753c; no statement correction is needed.

The delivery has one module, `Sheaf.Paper.RootTowerCoordinateFace`, in namespace
`AlgebraicGeometry.ProEtale.RootCoordinateFace`. Its main theorem is `coordinateFace`.
All constructions have explicit bodies. Every theorem has proof `sorry`; its docstring
states its source, node, and complete intended proof. No theorem is proved here.
The helper statements are the equations and geometry already asserted by this node,
or the mate formulas rendering its compatibility clauses. They belong to this node's
canonical comparison, rather than introducing an independent mathematical input.
Every declaration is listed in `lean.declarations`.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Distinct primes p and ell | `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)` |
| Field k of characteristic p | `(k : Type u) [Field k] [CharP k p]` |
| Finite norm-topological E/Q_ell | `E`, `NormedField E`, `NormedAlgebra ℚ_[ℓ] E`, `FiniteDimensional ℚ_[ℓ] E` |
| Algebraic closure with extended norm | `Ω`, `NormedField Ω`, `NormedAlgebra E Ω`, `IsAlgClosure E Ω`; the normed field embedding is isometric |
| Both F = E and F = Omega | The two conjuncts `Assertion p ... E` and `Assertion p ... Ω` |
| All continuous F-valued functions | `Profinite.continuousCoefficientRingObj F`, whose sections are lifted `C(P,F)` with pointwise operations; no completeness or finite-image restriction |
| Pulled-back coefficient ring | `condensedRingObj Λ X`, i.e. `(upperStarFromPoint X).obj Λ` |
| Internal modules on the small pro-etale site | `Modules Λ X = Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ X)` |
| Ordinary unbounded derived direct image | `lower Λ f = CondensedRing.moduleObjectDerivedPushforward Λ f`, the recorded full composite's total right derived functor |
| Exact inverse image | `upper Λ f = (CondensedRing.upperStar Λ f).mapDerivedCategory` and its actual derived adjunction |
| Regular separated finite-type Y/k | `y`, `LocallyOfFiniteType y`, `QuasiCompact y`, `IsSeparated y`, `hY : IsRegularScheme Y` |
| Affine etale chart B/Y | `(A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]` |
| Reduced SNC boundary with the given branches | `hH`, `hproduct` and `hbranches`: the Cartier radical ideal is the product ideal, and the parameter zero loci are precisely its irreducible components, in the same interface as the landed sibling |
| Affine pro-etale Spec R/B | `R`, `CommRing R`, `a : A →+* R` and `WeaklyEtale (Spec.map (CommRingCat.ofHom a))` |
| Full prime-to-p tower and power transitions | Existing `tameRootAlgebra p (fun i ↦ a (s i))`: its relations include every positive prime-to-p root and every divisibility power transition |
| Finite-rank lisse N | `Assertion` quantifies `N` and the recorded `IsLisseCoefficientModule ... N`; this uses a pro-etale cover and `Mod.IsFree`, with finite local ranks |
| T[P], N_P and N_P[0] | `test X P` is `(profiniteToProEtOf X).obj P`; `testModuleComplex` pulls N back by its structural map and applies `DerivedCategory.singleFunctor _ 0` |
| q_P | `towerProjection`, structural test projection followed by `Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t)))` |
| U_J and g_J | `Spec (.of (R ⧸ baseIdeal t J))` and `baseInclusion`; `baseIdeal` is the span of exactly the selected parameters |
| T_J and e_J | `faceRing` and `inclusion`: quotient the existing full root algebra by exactly all selected root coordinates |
| q_(J,P), e_(J,P) | `faceProjection` and `testMap (inclusion ...) P`; `square` states the structural equation |

The face presentation is the displayed presentation in the node: eliminating the J-root
variables in the full root presentation sets the corresponding t_j to zero, leaves the
remaining root equations over R/(t_j), and leaves their divisibility transitions unchanged.
It is not the cartesian fibre with nonzero nilpotent roots. No arbitrary maps or object
existence choices replace these quotients. `baseIdeal_le` makes the actual structural
quotient homomorphism well-defined; its proof argument affects no chosen data.
The site object/morphism size convention remains the published Scheme/ProEt convention;
coefficient and scheme carriers are in u and module sections are in u+1. There is no
restriction on an index type that could omit empty or infinite profinite tests.

### Every conclusion and compatibility

| Node clause | Lean rendering |
| --- | --- |
| Beta is adjunct of pulled-back q-counit | `squareUpper`, `adjunction`, and `exchange` define the canonical mate; `beta` specializes it to the actual face square. The first conjunct of `exchange_adjuncts` is the exact transpose formula. |
| Displayed derived isomorphism | `Assertion` is `IsIso (beta ... .app (testModuleComplex ... N P))`, for every J and P; its right-hand object is exactly R(q_(J,P))_* e_(J,P)^* N_P[0]. |
| Cartesian exchange followed by restriction | `fibreInclusion` is the canonical map to the cartesian fibre; `exchange_horizontal_pasting` identifies the composite of its closed-unit restriction and the cartesian mate with beta. All square maps and composite direct-image identifications occur in the formula. |
| Surjective closed immersion killing nilpotent roots | `fibreInclusion_properties` includes its closed-immersion and surjectivity predicates, as well as the two original closed inclusions. Its proof docstring distinguishes a nil ideal from a uniformly nilpotent ideal. |
| Adjunct back on U equals Rq_* of closed unit | The second conjunct of `exchange_adjuncts` writes this equality with the actual e-unit, q-direct image, square equality transport, and normalized `lowerComp`. |
| Successive J contained in J' restrictions | `ideals_mono`, `nestedBase`, `nestedFace`, `nested_square` give the canonical quotient maps and composition equations; `exchange_vertical_pasting` writes the equality of the successive and composite comparisons. |
| Restriction to opens | `exchange_cube` is equality on a commuting geometric cube; take its base map to be an open immersion and its other maps to be the actual base-change projections. `exchange_proetale` supplies the localization identification used on those sides. |
| Pro-etale base change of U | The same cube equation applies for arbitrary pro-etale base map. `exchange_proetale` states that the cartesian comparison is the localization isomorphism, with the defining mate unchanged. |
| Naturality in P | `profinite_square` gives the two test-map triangles and face square for every actual morphism P' -> P. Instantiating `exchange_cube` with these maps gives equality of the comparison paths. |
| Naturality in supplied lisse module maps | `exchange_naturality` explicitly states the commuting square for any derived module map, hence for the pullback of a supplied module map placed in degree zero. |
| Face-preserving tower automorphisms and module actions | `exchange_cube` quantifies the geometric maps and the four structural square equations; an automorphism preserving a face supplies exactly these data. Combine with `exchange_naturality` for its supplied linear action. No action is assumed to be trivial. |
| Profinite family Q | P ranges over every profinite test, including P times Q. `profinite_square` and `exchange_cube` are equalities on the entire parametrized schemes, and `exchange_naturality` applies to an action map there. They do not assert only equality after evaluation at points of Q. |
| Empty and zero cases | All finite subsets J, r = 0, empty spectra, empty P, and all local ranks including zero are admitted by the actual binders. No Nonempty, Nontrivial, connectedness or positive-rank assumption is imposed. |
| No puncture or outer/inner partition | The statement uses the full `tameRootAlgebra` and its root ideals throughout. No localization by the parameter product or partition occurs in any asserted object. |

The generic mate identities are written in the same module so their formulas can be read
and specialized to these canonical maps, without encoding compatibility as an arbitrary
isomorphism or as an untyped prose promise. They give the corresponding clauses for any
commuting diagram on which the same comparison is defined; they impose no additional
hypothesis on the geometric theorem.

### Dependencies read and used

* `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingSheafOfUniverse` and its underlying ring object. The
  existing scheme-universe `continuousCoefficientRingObj` has definitionally identical
  underlying sheaf at coefficient universe u; a server-compiled `rfl` probe checks this.
* `sk-def-sfb-pulled-back-coefficients` and `def-sfb-profinite-test-objects`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `condensedRingObj`, and `profiniteToProEtOf`; their bodies and docstrings were read.
* `sk-def-sfb-module-objects`: Mathlib `CategoryTheory.Mod`, `ModObj` and module morphisms.
* `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `CondensedRing.moduleObjectDerivedPushforward`; exact pullback and adjunction are the
  existing `upperStar` and `Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
* `def-weil-pbc-proetale-site`: Mathlib `Scheme.ProEt`, `ProEt.topology` and weakly etale
  objects. `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`.
* `def-trf-strict-normal-crossings-boundary`:
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`; it includes the radical Cartier
  condition and regular expected-codimension intersections.
* `def-sfb-lisse-coefficient-module`: `Sheaf.Paper.CoefficientHeartStratificationDefs`,
  `IsLisseCoefficientModule`. Its `Mod.IsFree` definition explicitly quantifies a finite
  natural-number rank, as read in `WeilConjectures.CategoryTheory.ModuleObjects.Free`.
* `lem-weil-pbc-proetale-ringed-open-closed`:
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, `Scheme.proEtale_ringed_open_closed`;
  the internal adjunctions used in the statement are the specified upstream ones.

Two existing landed definition nodes are added to stmt_deps under brief-stage2 section 5:
`def-sfb-strict-local-kummer-tame-module` supplies `TameRootOrder`, `tameRootRelations`
and `tameRootAlgebra`; `def-weil-pbc-condensed-e-module-category` supplies the commutative
`continuousCoefficientRingObj` interface. Their statements, Lean records, signatures
and construction docstrings were read. The root generator in `rootIdeal` is written
as `Ideal.Quotient.mk (Ideal.span (tameRootRelations p t)) (MvPolynomial.X (j, n))`.
The projection in `towerProjection` is written as `Spec.map` of `algebraMap`.
These are expressions in the recorded root algebra, not new definitions of a notion.
Neither the universal residual-chart theorem nor lisse-morphism extension is needed
to state the item: both theorem stmt_deps and both imports have been removed.
A graph walk found no return path from the two definition nodes to this item.

Every already recorded proof-dependency module is imported. The three proof dependencies
with no current Lean module are `sk-thm-pe-indetale-refinement`,
`lem-sfb-indfinite-contractible-base-wstrict`, and
`lem-sfb-wstrict-lisse-component-cohomology`; their content remains the original proof
obligations, described in the main docstring. They are not missing statement notions.
No dependency interface is replaced and there are no dependency modules or new nodes.

### Edge cases and mathematical checks

With J empty both ideals are zero; the quotient identifications and triangle identity
give the identity comparison. With J full, eliminating all root variables gives R/(t),
including the zero ring. With r = 0 there is only the empty face and no root variables.
The order-one root is available for every p, so baseIdeal_le does not require a hidden
nonempty choice of root orders. Infinite root ideals are only nil in the cartesian
fibre: finite sums of multiples of finitely many nilpotents are nilpotent, with no
common exponent claimed. Empty P and empty base charts have their actual empty test
schemes. Rank zero is allowed in Mod.IsFree, and the derived zero module is included.
The test set P need not be extremally disconnected. No field completion of Omega is
used. No statement dispute or source error was found.

### Searches and source

The current blueprint paragraph (3) was opened in full; it gives the open-direct-image
route and references, not a verbatim coordinate-face theorem. The node and its Q02
report correctly mark this as an agent-extracted input with its proof and exact
all-continuous reference WANTED. This delivery formalizes that accepted input.

All seven `msearch.py` calls are recorded by the tool itself in `searches.jsonl`:

1. LeanFinder, "Coordinate-face base change for the full prime-to-characteristic root
   tower with lisse condensed coefficients": eight unrelated Weierstrass or cotangent
   base-change results; no coordinate-face theorem.
2. Loogle, `tameRootAlgebra, upperStarComp`: unknown identifier `tameRootAlgebra`;
   inconclusive, not treated as a valid negative result.
3. Mathlib grep, `rootTower|coordinateFace|tameRootAlgebra`, AlgebraicGeometry:
   zero hits.
4. LeanSearch, "Canonical coordinate face of an infinite tame parameter root algebra
   quotient setting selected roots equal to zero": eight Lie root-space/quadratic
   algebra hits; no root-tower coordinate face.
5. LeanFinder, "Quotient of a compatible prime-to-characteristic root algebra by
   selected root coordinates and the adjunction counit base change map": eight
   single-polynomial AdjoinRoot or cotangent-space hits, not this tower or comparison.
6. Loogle, `"Ideal.Quotient.lift"`: seven actual quotient-lift declarations; these
   implement ordinary quotient maps, not the comparison theorem.
7. Mathlib grep, `coordinateFace|faceIdeal|tameRoot`, RingTheory: zero hits.

Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`
and the node files found the existing root algebra and root-coordinate/projection
helpers used above, but no theorem with this coordinate-face statement or the new
namespace. The exact node-id search in `lean/WeilConjectures` found no existing binding.
`tools/blueprint_refs.py search 'coordinate face'` returned zero blueprint matches.
The existing sibling morphism theorem concerns the punctured open and Hom bijectivity;
it is not a duplicate of this derived closed comparison.

### Validation

All compiles use `scompile.py`, individually against the live published server build.
The module compiled both in sandbox and library-artifact form without errors or warnings
before the final delivery dry run. The separate coefficient-equality probe was also
submitted through `scompile.py`. Final dry-run and delivery outputs are authoritative.
No direct git command, global build, shared-repository edit, launcher-script edit, or
sub-agent was used.

## Repair of returned head ae952e25753c

The saved packet first passed `deliver2.py --no-push` at 0b78b16ee94. That mechanical
pass did not discharge the independent H2/H3 return. I then inlined both one-line
expressions as explicitly permitted by the return, removed imports of
`Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts` and
`Sheaf.Paper.RootTowerLisseMorphismExtension`, and removed their two theorem IDs from
stmt_deps. Direct imports now expose the used definition nodes and Mathlib structures.
There is no new declaration or definition node, and no theorem signature, mathematical
hypothesis, compatibility clause, proof plan or source statement has changed.

For the advisory concerning `CondensedRing.condensedAmbientExchange`: the local
`exchange` extends the same mate construction to any commuting square. On a chosen
cartesian square, its `squareUpper` uses the exact-pullback derived presentation
`mapDerivedCategory`, whereas the ambient comparison uses `leftDerivedFunctor`.
The canonical exact-functor/left-derived identification transports between those
presentations; both square comparisons come from the ordinary `upperStarComp`, and
both exchanges are their mates under the derived pullback/direct-image adjunctions.
The existing ambient-exchange proof import is retained. No arbitrary comparison is
chosen and no additional equality theorem is assumed for the statement.

## Second reading by NM

Self-check of this repair, performed in this worker because the dispatcher prohibits
starting another agent: opened the saved module and node and compared their changed
fields with the current read-only main copy. The only non-lean field delta is the
addition of the two definition-node stmt_deps just listed. The two rejected theorem
edges are absent. The inline root generator is exactly the previous quotient-generator
body and has type `tameRootAlgebra p t`; the inline structural map is exactly the
previous `Spec.map algebraMap` body. Thus rootIdeal, faceRing, towerProjection, beta
and every assertion retain the same mathematical objects. The complete hypothesis
and clause tables above still apply, including both coefficient fields, both adjunct
identities, all tests, all finite faces, naturality and the empty/zero cases. All
variables and universes remain explicitly bound and all theorem proofs remain sorry.
Final server compilation and dry run below validate the repaired packet.
