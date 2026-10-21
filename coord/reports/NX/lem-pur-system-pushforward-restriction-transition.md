## Worker report

The module `Sheaf.Paper.SystemPushforwardRestrictionTransition` states
`WeilConjectures.SemilinearSections.Geometry.systemPushforwardRestrictionTransition`.
Its only postponed proof is that named theorem. Three real helper definitions expose
the canonical comparison in the coordinates of the existing system calculus:
`systemRestrictionPullback`, `systemOrdinaryRestrictionPushforward`, and
`systemRestrictionComparison`. No new mathematical notion, dependency module,
statement correction, arbitrary map, or choice from Nonempty is introduced.

Sources read: Stacks `sites-cohomology.tex`, labels
`lemma-derived-pushforward-composition` (0D6E) and
`lemma-derived-pullback-composition` (0D6D), and the node's complete six-step proof.
The current blueprint ancestor proof is
`main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/lem-weil-compact-support-representative-independence.proof.md`.

Hypothesis and clause correspondence:

- Arbitrary schemes and their morphism are `{V W : Scheme.{u}} (u : V ⟶ W)`.
  Both actual pro-etale topologies are `Scheme.ProEt.topology`. Object and morphism
  universes stay `u+1` and `u`. The `EssentiallySmall.{u+1}` instances for the sites
  and their countable sequence sites explicitly implement the prescribed size
  convention. Countable products of these sites satisfy the same bound; these are
  size witnesses, not assumptions on the morphism or coefficient maps.
- The arbitrary strict tower is `B` together with adjacent maps `τ`. Its iterated
  map is the dependency's `coefficientMap ... h`; indices are `ℕ`, allowing a
  harmless shift from the written sequence starting at 1.
- `A : Data ... B τ` and `G : Geometry ... A ...` specify the ordinary-derived
  calculus already supplied by `semilinearDerivedSections`. These are choices of
  the dependency's normalized operations, not additional properties imposed on
  schemes, tower maps, or inputs. In particular the geometric morphism in `G`
  is fixed to `proEtaleSheafInverseImage u (Type (u+1))`, its actual direct image,
  and `proEtaleSheafAdjunction`. `G.coefficients` and
  `G.coefficientTransition` are their inverse-image ring tower: the existing
  `inverseImage.ringUnderlying` and `coefficient_compatibility` fields specify this.
- `DS` is the actual ordinary unbounded derived category of strict semilinear
  systems, not diagrams in derived categories. `G.push.rightDerivedFunctor` is
  simultaneous derived direct image; `(G.levelPush n).rightDerivedFunctor` is
  its level analogue. `e` and `G.pushEvaluation` supply exactly the canonical
  natural evaluation comparisons named by the node.
- `resD (coefficientMap ... h)` is the dependency's exact, termwise restriction
  of scalars. `systemRestrictionPullback` localizes the specified
  identity-on-underlying-sheaves `G.restrictionPullback`.
- `systemRestrictionComparison` is delta: conjugation of the normalized coefficient
  pullback under the two composite adjunctions, with source `q ⋙ G_m` and target
  `G_n ⋙ p`. This is a real construction by Mathlib's `conjugateIsoEquiv`.
  The FIRST conjunct identifies its inverse with the derived mate of the localized
  restriction pullback. This is the canonical ring-change d in the existing
  system category coordinates; it is not an uncharacterized natural isomorphism.
  The recorded pro-etale ring-change module uses its AsSmall module presentation,
  whereas the system calculus uses module sheaves on the actual site. Rather
  than identifying those two presentations definitionally, this equation gives
  the canonical adjunction characterization in the latter presentation.
- The SECOND conjunct is the displayed restriction transition identity for every
  `N : DS ... G.coefficients G.coefficientTransition`. Both transitions are
  `derivedTransition ... h`, so the maps are actual localized strict transitions.
  Written without suppressing identifications, the equation is
  `a^(GN) ≫ p(e_n) = e_m ≫ G_m(a^N) ≫ delta`. It uses no faithfulness assertion
  for evaluation and no replacement of an arbitrary system by a normalized one.
- The THIRD conjunct quantifies over every K-injective complex `I` at level n,
  K-injective complex `H` at level m, and quasi-isomorphism `j : qI ⟶ H`.
  It asserts that direct image of j is a quasi-isomorphism and gives the
  resolution square for `delta.inv`. The right-hand path is restriction of
  `rightDerivedFunctorObjQIso I`, the exact restriction localization factor,
  the ordinary coefficient comparison, `Q(u_*j)`, then the inverse comparison
  `rightDerivedFunctorObjQIso H`. The left-hand path is `delta.inv` followed
  by `G_m` of the exact restriction localization factor and `Q(j)`. Cancelling
  these isomorphisms is precisely the node's assertion that delta is the inverse
  class of `u_*qI = p u_*I ⟶ u_*H`. The ordinary equality is written using
  `systemOrdinaryRestrictionPushforward`, the canonical ordinary mate of the
  identity-on-underlying-sheaves comparison. No preservation of K-injectives
  by q is used or assumed.
- The FOURTH conjunct quantifies over arbitrary `M`, `L`, and `a : M ⟶ qL`.
  It states the displayed scalar-transpose identity. Both sharps are explicitly
  `(adjunction.homEquiv _ _).symm`: the first is `A.scalar h` and the second
  `G.target.scalar h`. Its right-hand side uses the existing, specified
  `G.coefficientMate`, followed by `G_n.map` of the other transpose.
- All level maps are natural transformations or natural isomorphisms. The
  transition identity quantifies over every system and uses those transformations,
  so it is natural in N. The binder `h : n ≤ m` includes equality, with no
  strict-inequality premise. There are no flatness, boundedness, cartesian-input,
  or evaluated-K-injectivity assumptions.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, and
  `proEtaleSheafAdjunction`, with their actual signatures and source docstrings.
- `Sheaf.Paper.SemilinearDerivedSections`: `semilinearDerivedSections`,
  `SemilinearDerivedSectionsData`, and their exported normalized `Data`, `Geometry`,
  `DS`, `D`, `Mod`, `e`, `derivedTransition`, `coefficientMap`, `res`, `resD`,
  and `Geometry.coefficientMate` interfaces. Their definitions were read in
  SemilinearSystemModels, SemilinearDerivedCalculus, SemilinearGeometryCore,
  SemilinearGeometryDerived, and SemilinearGeometryOps.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by the dependency's `res`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictionDerivedPullback`,
  `proEtaleRingRestrictionDerivedDirectImage`, its existence/uniqueness
  normalization, and `proEtaleRingSheafChangeAdjunction` provide the proof plan
  and canonical mate characterization instantiated in the first conjunct.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, supplying the
  resolution normalization used by the third conjunct.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, fixing the two scalar
  adjunction normalizations already retained by `ScalarData`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
- `Sheaf.Paper.SemilinearGeometryDerived`: `Geometry`, including
  `coefficientPullback_transpose` and canonical derived adjunction equations.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateIsoEquiv`,
  and the mate-pasting lemmas named by the proof dependency records.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`, supplying explicit representative isomorphisms.

Edge cases checked before writing: m=n (identity restriction under the standard
localization identifications), the identity scheme morphism, the zero system,
empty schemes, zero rings, and a non-flat coefficient map Z/4 to Z/2. None is
excluded by a binder. Arbitrary replacement j is quantified; restriction need
not preserve K-injectives. The scalar formula allows every a, including zero
and the adjunction unit. The chosen coefficient universe accommodates the
prescribed small site without identifying its object and morphism universes.

Searches run through the prescribed msearch wrapper:

- leanfinder: “Derived direct image of semilinear sheaf module systems has
  restriction transitions equal to inverse ring change comparison composed
  with pushforward of transitions”. Eight ordinary pushforward/congruence hits,
  including `SheafOfModules.pushforwardCongr` and `pushforwardComp_inv_app_val_app`;
  no system-derived transition with its scalar and resolution normalization.
- loogle: `SheafOfModules.pushforward, CategoryTheory.Adjunction`. Six ordinary
  sheaf adjunction results; none is this theorem.
- grep: `derived.*[Tt]ransition|[Tt]ransition.*derived|semilinear.*system`.
  One unrelated semilinear typeclass comment in Algebra/Ring/CompTypeclasses.
- leansearch: “Restriction of scalars comparison for derived sheaf direct image
  is compatible with semilinear system transitions and scalar adjunction
  transposes”. Eight restriction-of-scalars definitions, no exact theorem.
- Direct rg searches in `lean/WeilConjectures` and `lean/Sheaf` for restriction
  transitions, semilinear systems, and conjugate comparisons found the recorded
  calculus and other specialized comparisons, but no exact statement. The
  literal node-id grep in WeilConjectures found no attachment. The four proposed
  declaration names were searched in both roots, Mathlib, and the upstream name
  index; no clash was found.

No node fault or STATEMENT-DISPUTED issue remains. The statement, dependencies,
proof, and all other original node fields are unchanged.

## Second reading by NX

Separate rereading of the node against the completed module: checked the direction
of delta (G_m q to p G_n), d=delta inverse, both evaluation comparisons in the
transition square, and the coefficient hom-equivalence directions. Checked the
representative square from its common source p G_n QI to its common target G_m QH:
its ordinary comparison points from p u_*I to u_*qI, and the final K-injective
comparison is inverted. This avoids the incorrect inference that qI is K-injective.
Checked that the final mate is exactly the existing coefficientMate, with its
inverse coefficient-pullback orientation. Equality levels and arbitrary unnormalized
systems remain in the statement. Definitions have real data and the sole theorem
has sorry. Universe inference repairs retain the original site universes and only
make the prescribed smallness witnesses explicit. No statement correction or
new/dependency node is needed. This is the dispatcher's single worker rereading;
the maintainer's independent delivery review remains the independent review.
