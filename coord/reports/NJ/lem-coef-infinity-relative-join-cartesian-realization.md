## Worker report

The module `Sheaf.CategoryTheory.InfinityRelativeJoinCartesianRealization` states the
relative-join realization in the common simplicial-set universe `u`.  It imports the
recorded declarations `SSet.Enhanced.coneCategory` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.Enhanced.cartesianFibration` and
`SSet.Enhanced.IsCartesianEdge` from `Sheaf.CategoryTheory.InfinityFibrations`,
`SSet.Enhanced.relativeJoin`, `relativeJoinMap`, `relativeJoinIdentityIso`,
`relativeJoinInl`, `relativeJoinInr`, and `relativeJoinEndpoint` from
`Sheaf.CategoryTheory.RelativeJoin`, and
`SSet.Enhanced.mapping_composition`, `mappingSpace`, and `mappingSpaceMap` from
`Sheaf.CategoryTheory.InfinityMappingComposition` (the latter also imports the
recorded enhanced-diagram and pinch-comparison foundations).

The helper `relativeJoinCartesianTotal R` is exactly
`relativeJoin (𝟙 Y) R`.  The helper
`relativeJoinCartesianProjection R` is the second relative-join projection followed by
the first projection of `Δ[1] ⊗ Y`, hence it is the interval projection.  The helper
`relativeJoinCartesianTransport R` is the inverse of
`relativeJoinIdentityIso X` followed by `relativeJoinMap`; its commuting maps are
`R : X ⟶ Y`, `𝟙 X`, and `R`, so it uses `R` on the base and first factor and the
identity on the second factor.  `relativeJoinCartesianEdge R x` evaluates this map on
`Δ[1] × {x}` at the identity 1-simplex.  The Y and X vertex helpers are the two pure
factor inclusions.

`standardInterval_quasicategory` records the quasicategory assertion for `Δ[1]` as a
named postponed theorem.  `RelativeJoinCartesianStatement R` renders the clauses as
follows.

* `total_quasicategory` is `Quasicategory (relativeJoinCartesianTotal R)`.
* `cartesian_fibration` installs that instance and the named interval instance, then
  states `cartesianFibration relativeJoinCartesianProjection` exactly, including its
  inner-fibration and target-lift clauses through the dependency definition.
* `fiber_zero` and `fiber_one` are isomorphisms from the strict fibers over the
  standard vertices `0` and `1` to `Y` and `X`, respectively; the fibers are the
  degreewise pullbacks from `def-coef-infinity-fibrations`.
* `transport_zero` says that restriction of the cylinder map to the constant-zero
  endpoint is `R` followed by `relativeJoinInl (𝟙 Y) R`.  `transport_one` says that
  restriction to the constant-one endpoint is `relativeJoinInr (𝟙 Y) R`.
* `cartesian_edges` says every `relativeJoinCartesianEdge R x` is
  `IsCartesianEdge` for the interval projection.
* `RelativeJoinMappingData` supplies the four displayed right-pinched mapping-space
  isomorphisms: Y-to-Y, X-to-X, Y-to-X identified with
  `mappingSpace Y y (R.app _ x)`, and X-to-Y having no simplices in every degree via
  `IsEmpty`.
* The composition representative is selected directly from the recorded
  `mapping_composition` package, whose characterization determines its homotopy
  class. `composition_transport` states the coherent
  precomposition formula: for a mixed arrow `f : y → x`, the composite on the total
  relative join, transported by the Y-to-X mapping isomorphism, is homotopic to first
  applying `R` to the X-to-X input and then composing with the image of `f` in
  `mappingSpace Y y (R x)`.  The two maps are written explicitly with `lift`, the
  selected canonical composition maps, and `SSet.Homotopy`.

The theorem `relative_join_cartesian_realization` returns
`Nonempty (RelativeJoinCartesianStatement R)`, so the statement asserts existence of
all the data and does not introduce an arbitrary map or a hollow definition.  Every
postponed fact is named (`standardInterval_quasicategory` and the main theorem) and
has its source and blueprint in its docstring.

Edge cases checked: the formulas remain well-typed for empty `X` or `Y`; no vertex
binder is assumed inhabited.  For point simplicial sets, the total is the interval
relative join and the two fiber isomorphisms have the expected point fibers.  For
ordinary nerves and groupoid nerves, the mixed mapping space has the stated direction
and the reverse mapping space is degreewise empty.  The endpoint formulas use the
constant interval maps, so they also cover the degenerate endpoint cases.

Searches made before writing: `msearch.py ... leanfinder "The relative join for a
functor of quasicategories gives a cartesian fibration over the interval with that
functor as contravariant transport"` (no match; only ordinary fibered categories and
model-category cylinders); `msearch.py ... leansearch "A functor of infinity
categories has a mapping cylinder which is a cartesian fibration over Delta one"`
(no match); `msearch.py ... loogle '"Quasicategory", "horn"'` (only the primitive
horn-filling declarations); `msearch.py ... grep 'relativeJoin|relative.join|cartesian.*transport'
AlgebraicTopology` (zero hits); and repository `rg` searches for
`relativeJoin`, `cartesianFibration`, and `mappingCylinder` (only the recorded
project declarations).  The dependency declarations were read in full and no exact
existing declaration for this node was found.


Additional clause checks completed on resumption:

* The theorem binders `{X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]`
  and `(R : X ⟶ Y)` express precisely the functor between quasicategories in a
  common containing universe. There is no inhabitedness or finiteness hypothesis.
* `fiber_zero_canonical` and `fiber_one_canonical` fix the fiber isomorphisms by
  requiring their inverses followed by `pullback.snd` to be the prescribed
  relative-join inclusions. Fullness follows from the interval parameter: a
  monotone simplex all of whose vertices have one endpoint label is constant.
* `yy_canonical` and `xx_canonical` fix the mapping isomorphisms by their inverses,
  which are the mapping maps induced by those same inclusions. `yx_canonical`
  fixes its underlying simplex in every degree to the image under
  `relativeJoinProjection (𝟙 Y) R`, so the edge corresponding to `f` is exactly
  its projected edge `u`, including degree zero.
* `composition_coherence` states the comparison homotopy on the entire product
  of mapping spaces, varying both inputs simplicially. `composition_transport`
  specializes the comparison to each mixed vertex `f`, with the other input
  first transported by `mapping.xx` and then mapped by `R`. Associativity and
  units are those of `mapping_composition`, not separately chosen operations.

The three proof-only imports are
`Sheaf.CategoryTheory.EquivalenceOuterHornFilling`, with
`SSet.Enhanced.equivalence_iff_outer_horn_filling`,
`Sheaf.CategoryTheory.InnerFibrationEquivalenceOuterHornLift`, with
`SSet.Enhanced.inner_fibration_equivalence_outer_horn_lift`, and
`Sheaf.CategoryTheory.RightPinchComparison`, with
`SSet.Enhanced.right_pinch_comparison`. Their source signatures and docstrings
were read. The first two supply exactly the absolute and relative final-horn
fillers used in steps 3 and 4; the third supplies the pinch comparison used in
step 6. The standard-interval obligation is the auxiliary assertion explicitly
contained in this item's proof step 2, recorded under this item's declarations.
No new definition node, dependency repair, or statement correction is needed.

Fresh searches on resumption: LeanFinder query “The relative join of a
quasicategory functor defines a cartesian fibration over the standard interval”
returned eight hits, including ordinary nerves, strict Segal right Kan
extensions, and the Kan model structure, none stating this theorem. Loogle
`"Quasicategory", "stdSimplex"` returned zero hits. Mathlib grep
`relativeJoin|relative.join|cartesian.*transport` in AlgebraicTopology returned
zero hits. LeanSearch “Relative join of infinity categories cartesian fibration
over the interval with canonical right pinched mapping spaces” returned eight
ordinary categorical join declarations, whose signatures are not simplicial
quasicategory assertions. Direct `rg` searches of upstream WeilConjectures and
project Sheaf sources found the recorded foundations and distinct consumers,
but no existing declaration of this item. Searches for all delivered full names
in `dag/lean_names_upstream.json` and upstream WeilConjectures found no collision.
Mathlib's quasicategory/strict-Segal sources and standard-simplex sources have
no direct standard-interval instance matching the helper.

Source verification: Kerodon [024F](https://kerodon.net/tag/024F) was read online
and confirms all four mapping-space cases, including their pinched versions.
After the web tool failed to fetch the other two pages, direct HTTPS retrieval
succeeded. [024K](https://kerodon.net/tag/024K), Variant the project server, states the
cartesian fibration and the specified cylinder map witnessing contravariant
transport, for an arbitrary quasicategory functor. [0242](https://kerodon.net/tag/0242)
defines the same relative join by its pullback along the canonical splitting
map. Their specialization has the exact orientation `Y ⋆_Y X`. No source-based
statement change was made. No STATEMENT-DISPUTED or node fault was found.

Validation on resumption: the prescribed `scompile.py` compiled both the sandbox
and library-path checks cleanly (2.9 and 4.8 seconds). The module's complete
six-step proof docstring matches the node. Every universe and variable is bound,
all definition data are explicit, and the two named theorem proofs remain
`sorry` as required. The inherited second-reading section was removed so that
the dispatcher can obtain a fresh independent reading of this completion.


## Second reading by NJ

Independent second reader, 2026-10-17. I read the shared node in full, the sandbox
module, all four statement-dependency node statements and recorded signatures,
the actual dependency sources, and the three proof-only imports. There is no
repair note for this item. The sandbox differs from the current node only in
`lean`; no `statement_change`, new node, or dependency module is present.

Source check: I independently read Kerodon Variant the project server (024K),
Construction the project server (0242), and Remark the project server (024F). The latter was available
through the web reader; direct HTTPS retrieval supplied 024K and 0242 after the
web reader failed on those pages. These are Kerodon sources, not Stacks tags.
024K assumes only a functor G:D→C of infinity categories, states that
C ⋆_C D→Δ¹ is cartesian, and specifies the cylinder h as its contravariant
transport witness. 0242 gives the actual pullback used by `relativeJoin`.
024F gives all four mapping cases and explicitly includes right-pinched spaces.
No standing Noetherian, finiteness, nonemptiness, or coefficient hypothesis is
present. The node has the same orientation with D=X, C=Y, G=R.

Object, hypothesis, and conclusion inventory with Lean correspondence:

1. Two quasicategories in a common containing universe, and a coherent functor
   R:X→Y: `{X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (R : X ⟶ Y)`.
   The imported foundations use simplicial maps as coherent functors. Verdict:
   exact; no additional instance or hypothesis is imposed on R.
2. E_R=Y ⋆_Y X for (id_Y,R): `relativeJoinCartesianTotal R` unfolds to
   `relativeJoin (𝟙 Y) R`. Its dependency is the actual subcomplex of pairs
   satisfying the degreewise pullback equation, with real simplicial operators.
   Verdict: same object, no private replacement or mere existence choice.
3. Interval projection p: `relativeJoinCartesianProjection R` is
   `relativeJoinSnd (𝟙 Y) R ≫ fst _ _`. It retains the interval coordinate,
   whereas `relativeJoinProjection` retains Y. Verdict: correct projection.
4. E_R is a quasicategory: `total_quasicategory` in
   `RelativeJoinCartesianStatement`. Verdict: exact.
5. p is cartesian: `cartesian_fibration` uses the dependency's
   `cartesianFibration` with the preceding total instance and named interval
   instance. That definition includes `InnerFibration p` and cartesian lifts of
   every base edge at every prescribed target; its edge test is the final
   outer-horn lifting condition. Verdict: exact, not an arbitrary fibration.
6. Full fibers over 0 and 1 identify with Y and X: `fiber_zero`, `fiber_one`
   are isomorphisms for the recorded strict fibers at
   `stdSimplex.obj₀Equiv.symm 0` and `... 1`. The fields
   `fiber_zero_canonical`, `fiber_one_canonical` fix their inverse inclusions
   after `pullback.snd` to `relativeJoinInl`, `relativeJoinInr`. Fullness needs
   no extra hypothesis or unspecified full-subcategory structure: any simplex
   of Δ¹ whose vertices are all one endpoint is constant, so the strict fiber
   already contains every simplex on those vertices. Verdict: exact canonical
   identifications of full fibers.
7. The specified cylinder h uses R on base and first factor and id_X on the
   second: `relativeJoinCartesianTransport R` is
   `(relativeJoinIdentityIso X).inv ≫ relativeJoinMap (𝟙 X) (𝟙 X)
   (𝟙 Y) R R (𝟙 X) R ...`. I checked the argument order against the actual
   `relativeJoinMap` signature and its `(z,(t,s))` formula. The identity
   isomorphism has its explicitly constructed inverse. Verdict: exact h;
   in particular its interval coordinate is preserved.
8. Its endpoints are R and id_X inside the two fibers: `transport_zero` and
   `transport_one` restrict h using `relativeJoinEndpoint X 0/1` and conclude
   R followed by the left inclusion / the right inclusion. Verdict: exact.
9. Each h restricted to Δ¹×{x} is p-cartesian: `relativeJoinCartesianEdge`
   evaluates the actual cylinder at the identity interval simplex with
   constant x; `cartesian_edges` applies `IsCartesianEdge` to it for every
   vertex x. Verdict: exact, including the edge's specified orientation.
10. For all y,y' in Y, Map_E(y,y') ≅ Map_Y(y,y'):
    `RelativeJoinMappingData.yy`; `yy_canonical` fixes its inverse to the
    mapping map of the left inclusion. Verdict: exact canonical isomorphism.
11. For all x,x' in X, Map_E(x,x') ≅ Map_X(x,x'):
    `xx` and `xx_canonical`, using the right inclusion. Verdict: exact.
12. For all y in Y and x in X, Map_E(y,x) ≅ Map_Y(y,Rx):
    `yx`; `yx_canonical` specifies the underlying (n+1)-simplex in every degree
    to be its image under the projection to Y. This is exactly the node's
    right-pinched mapping model (`mappingSpace` in EnhancedDiagramsCones),
    with constant initial face and prescribed final vertex. Verdict: exact.
13. Map_E(x,y) is empty for every x,y: `xy` gives `IsEmpty` in every simplex
    degree. Degreewise emptiness is equivalent to an isomorphism to the empty
    simplicial set, including its unique operators. Verdict: exact.
14. A mixed edge f corresponds to u:y→Rx: the vertices of the imported
    `mappingSpace` are exactly such edges; `yx_canonical` in degree zero
    requires u=q(f), not an unspecified equivalence or component. Verdict:
    exact, retaining the particular edge.
15. Precomposition by f on maps x→z agrees with v↦R(v)∘u, with composition
    homotopies: `composition_coherence` compares the two maps on the entire
    product Map_E(x,z)×Map_E(y,x). The tensor factors agree with the
    dependency's order (edge 12, then edge 01). `composition_transport`
    restricts the second input to f via `lift (𝟙 _) (SSet.const f)`, and the
    other side first applies `mapping.xx`, then `mappingSpaceMap R`, and
    composes with the image of f under `mapping.yx`. Both comparisons are
    actual `SSet.Homotopy`, not just equalities on components. Composition
    representatives are selected from `mapping_composition` after its fixed
    right-pinch characterization; that determines the homotopy class used
    here and supplies the associativity and unit homotopies. Verdict: exact;
    no arbitrary operation or stronger functoriality hypothesis was added.
16. All of these clauses are conclusions for every R: the theorem returns
    `Nonempty (RelativeJoinCartesianStatement R)`. The structures merely
    package simultaneous data; they do not assume any conclusion. Verdict:
    correct quantifier order and existential packaging.

Edge cases: X empty gives just the Y endpoint and no transport edges; a
cartesian fibration may have empty target fiber, so this is allowed. If Y is
empty then the existence of R forces X empty; the empty total is still covered.
Both empty and point/discrete examples have the claimed mapping spaces. For
ordinary category nerves the mixed edges have orientation y→Rx, while the
reverse mapping spaces are empty; composition is R(v)∘u in that order. Degree
zero of the mapping spaces is explicitly covered by `yx_canonical`; no horn
or simplex degree is excluded by an extra binder. There is no index type,
ring, characteristic, or scheme parameter to restrict. Universe u is bound,
and is exactly the common containing universe of the node. No implicit
nonempty, finite, small-category equality, or field assumption was found.

Independent duplicate searches used different terms: LeanFinder
“Simplicial mapping cylinder of a quasicategory functor has cartesian lifts and
mixed right mapping spaces” returned the ordinary nerve quasicategory theorem,
hypercover cylinders, model-category cylinders and Kan horn lifting; their
reported signatures do not give this realization. Loogle
`"Quasicategory", "stdSimplex"` returned zero hits. Mathlib grep
`relativeJoin|cartesian.*realization|mappingCylinder` in AlgebraicTopology
returned zero hits. Direct rg on upstream WeilConjectures, Mathlib's
AlgebraicTopology, and project Sheaf/CategoryTheory for mapping-cylinder,
relative-join, cartesian-transport and interval-quasicategory terms found the
recorded relative join and distinct consumer/fiberwise/cocartesian results,
not this statement. Full-name searches in upstream sources, Mathlib, and
`dag/lean_names_upstream.json` found no collision. I also read Mathlib's
`CategoryTheory.Nerve.quasicategory` and `stdSimplex.isoNerve`: these concern
nerves and a simplex/nerve isomorphism, rather than an already recorded
interval instance or this realization. The interval helper is precisely the
auxiliary assertion in this node's proof step 2, not a new notion.

H5–H9 check: all six map/object helpers have explicit data from the recorded
relative join. The two structures contain specified data and assertions, not
`sorry` data. The only postponed theorems are
`standardInterval_quasicategory` and `relative_join_cartesian_realization`;
both have source/blueprint docstrings and their full respective proof plans.
The main docstring contains all six node steps. The three ordinary imports
supply the two final outer-horn clauses and right-pinch comparison used in
those steps; public imports supply all four statement dependencies. All lines
are at most 100 characters, every variable and universe is bound, and there
is no private notation, local instance, hidden statement `let`, or proof of a
theorem in this stage-2 module.

Mismatches found and changes made: none. The Lean module and node record were
left unchanged; this section records the independent reading. No source-based
statement correction or dependency repair was needed. The node's
`lean.statement` was checked byte-for-byte against the theorem signature.

Validation: the prescribed scompile.py invocation compiled the sole delivered
module cleanly in the sandbox (3.0 seconds) and at its library path
(5.2 seconds), with no errors or warnings. Delivery preflight is recorded below.

The prescribed deliver2.py --no-push completed successfully: `OK (dry run): commit ca5217818c passes the preflight and compiles; nothing pushed`.
