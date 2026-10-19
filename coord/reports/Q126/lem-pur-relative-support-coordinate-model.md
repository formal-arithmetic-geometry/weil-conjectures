## Worker report

Q126 states `lem-pur-relative-support-coordinate-model` in
`lean/Sheaf/Paper/RelativeSupportCoordinateModel.lean`. All theorems have `sorry`
proofs. Every definition has actual data, and each proof needed by a construction
is a separately named theorem with a source and natural-language proof. No
statement correction or disputed statement is proposed.

The comparison is **canonical pullback in the reverse direction** to the displayed
isomorphism, not an existential choice of an unrelated equivalence. The normal
map retains the last b coordinates, in their given order. The underived
transformation `coordinateGlobalToStalk` is uniquely characterized by its equation
with the supported-kernel inclusion and the ordinary global-section germ map.
`coordinateDerivedGlobalToStalk` derives this specified transformation. The
principal theorem says its transported component is invertible; its inverse is
the isomorphism in the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
|---|---|
| Fixed finite datum, all n ≥ 1 | `P : PurityFiniteSetting.{u}`; `P.level_pos`; coefficients `P.Coefficient`, the recorded ULift of `P.Ring`. No divisibility condition on `P.level` is introduced. |
| Arbitrary k-scheme S | `RelativeSupportCoordinates.S` and `.base : S ⟶ Spec (.of P.field.k)`. No finite-type, noetherian, reducedness, separation or dimension assumption on S. |
| X and Y smooth over S | fields `.pX`, `.pY`, `[.smoothX]`, `[.smoothY]`. |
| Closed immersion over S | `.i`, `[.closed]`, `.overBase : i ≫ pX = pY`. |
| Etale T → X | `.e` and `[.etale]`. |
| Y_T = Y ×_X T | actual categorical `pullback C.i C.e`, with closed inclusion `pullback.snd C.i C.e`. |
| a,b nonnegative integers | `.a .b : ℕ`. |
| Etale S-map h | `.h`, `[.etaleCoordinates]` and `.coordinatesOver`. |
| Scheme-theoretic inverse image of the first a coordinates | `.supportCoordinates` and `.cartesian : IsPullback ... (AffineSpace.zeroLastCoordinates S a b) h`. Supplying the support map is exactly the data of this cartesian square, not an additional geometric hypothesis. The coordinate inclusion is the published construction, not a new copy. |
| Ordinary small etale site | `Scheme.smallEtaleTopology` throughout; no pro-etale support functor is substituted. |
| Underived sections supported on Y_T | `Etale.coordinateSupportSheaf` is the actual kernel of the open-complement adjunction unit. On each etale W this is exactly ker(F(W) → F(W minus Y_W)), since sheaf limits and open direct-image evaluation compute this kernel. |
| Right derived sheaf support and then geometric stalk | The target of `.comparison` is explicitly `(pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus.obj ((coordinateSupportSheaf ...).rightDerivedFunctorPlus.obj (singleFunctor ... 0).obj A(r))`. The named `coordinateSupportedStalkDerivationIso` identifies deriving the supported stalk with this target, using exactness of stalks and preservation of injectives by the support kernel. |
| Every integer r, including negative twists | `r : ℤ`; `Scheme.finiteEtaleTateSheaf` is the published signed roots/dual construction. The canonical annihilator is `ringChar P.Coefficient`, and the named characteristic positivity/unit theorems follow from the finite datum. |
| A(r) on the chart, not just its unidentified pullback | `.twistPullback r` uses the unique root/generator/unit/positive-power/evaluation-normalized signed family in `coordinateTatePullback_existsUnique`, whose existence and uniqueness reduce to `Scheme.etaleFiniteTwistPullback`; this is the same family and retains its identity/composition laws; `.comparison` transports to the actual finite Tate sheaf on C.T. |
| Every geometric point on Y_T | arbitrary `{Ω : Type u} [Field Ω] [IsSepClosed Ω]`, `t : Spec Ω ⟶ C.T`, and `ht : Set.range t.base ⊆ Set.range (pullback.snd C.i C.e).base`. This is equivalent to lying on the closed support. |
| Ordinary supported cohomology on A^b_k | `.normalSpace` is exactly `AffineSpace (ULift (Fin b)) (Spec k)`; `.origin` is its actual zero section. The source of `.comparison` is the recorded generic `Sheaf.supportedSectionsFunctor` right-derived at `.normalTwistComplex r`. |
| Coordinate-induced isomorphism of complexes of A-modules | `IsIso (C.comparison t r)`, in `DerivedCategory.Plus (ModuleCat P.Coefficient)`. Taking `asIso` and inverting gives the displayed direction. No arbitrary orientation, support map or Nonempty isomorphism replaces the canonical construction. The Tate-data choices are from uniquely normalized data, with all proof obligations stated separately. |
| Further etale restriction | `Etale.coordinateDerivedGlobalToStalk_restriction` is the explicit composition square of natural transformations for every further etale e. The restriction map is independently fixed by its inclusion into ordinary germs. Its hypotheses hf, he, hef are only the inverse-image support equalities; on chart restrictions they are supplied by the pullback squares. Exact pullback composition and the normalized Tate composition comparisons transport this same square to `.comparison`. |
| Twist identity A(r)=A(b) tensor A(r-b) | `.twistProduct r` is the unique unit/concatenation/associativity/symmetry/evaluation-normalized p-family (`coordinateTateProduct_existsUnique`) of the recorded signed Tate theorem, with its integer index transported by b+(r-b)=r. `.comparison_twist_identification` states the commuting square with this actual product identification, evaluated on the tensor coefficient sheaf and on A(r). The underlying transformation is natural on all coefficient complexes, and its germ maps are A-linear; hence the same square respects tensoring with the constant finite free line A(r-b), without choosing a basis. |
| Fixed c ≥ 0 and local Krull dimension equality at every point of Y | the second conjunct quantifies `c : ℕ` and every `y : C.Y`; it uses `ringKrullDim (C.X.presheaf.stalk (C.i.base y)) = ringKrullDim (C.Y.presheaf.stalk y) + (c : WithBot ℕ∞)`. These are supremum-of-prime-chain Krull dimensions, allowing infinity. |
| Nonempty support implies b=c | `Nonempty (pullback C.i C.e : Scheme.{u}) → C.b = c`. No cancellation of infinite dimensions is assumed. The nine-step proof selects a point over a minimal base prime, with finite local dimensions b and zero. |

The geometric data are bundled in `RelativeSupportCoordinates` solely to avoid
repeating all of these binders. They are not an added existence or regularity
assumption. The support-kernel, its normalized germ maps and the chart bundle
belong to the objects explicitly introduced by this node. The one new definition node, `def-pur-etale-coordinate-support`, supplies the
missing ordinary-etale sheaf-support notion and its canonical germ maps in its
own module. It is the only added statement dependency. No existing dependency
node is changed. The coordinate-subspace helper and finite signed Tate interfaces
are reused from their published modules.

Dependency declarations read and used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-sbc-affine-space`: its recorded Mathlib match `{'declaration': 'AlgebraicGeometry.AffineSpace', 'file': 'Mathlib/AlgebraicGeometry/AffineSpace.lean', 'line': 44, 'how': 'specializes in one line: take coordinate type ULift (Fin n). AffineSpace (line 44) is exactly the alternative base-change definition in Stacks 01M0/01LZ; over (line 66) is the first projection. SpecIso (line 228) and SpecIso_inv_over (line 255) give the polynomial spectrum and constants inclusion on affine bases; isPullback_map (line 325) applies to each affine-open inclusion to identify its restriction. The instance at line 442 (AlgebraicGeometry.AffineSpace.instIsIsoSchemeOverInferInstanceOverClassOfIsEmpty) makes the projection an isomorphism for an empty coordinate type, including ULift (Fin 0). No affineness assumption on S is required.'}`.
- `def-weil-pbc-geometric-stalks`: `Sheaf.AlgebraicGeometry.PointedEtaleStalk`, `AlgebraicGeometry.pointedEtaleStalk`.
- `def-pur-support-cohomology`: `Sheaf.AlgebraicGeometry.SupportCohomology`, `AlgebraicGeometry.Etale.supportSections`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwists`, `WeilConjectures.intrinsicQbarComplexTwistFunctor`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-pur-etale-coordinate-support`: `Sheaf.AlgebraicGeometry.EtaleCoordinateSupport`, `AlgebraicGeometry.Etale.coordinateSupportSheaf`.

The compact normalized Tate-data interfaces avoid repeatedly elaborating the
large global existence/coherence theorem inside each chart. The new normalization
predicates retain root restriction, scalar generators, unit, positive powers and
negative evaluation for pullback; product retains units, positive concatenation,
associativity, symmetry and evaluation. The named existsUnique obligations have
complete proof docstrings reducing them to the published all-index theorem.
Consequently the choices determine these maps uniquely and agree with its
composition/tensor-normalized families; they are not bare existence choices.

The ordinary finite Tate sheaf is the roots-of-unity realization of the finite
part of the coefficient-twist convention; its published pullback/tensor theorem
supplies the signed identifications. This avoids the restricted exponent-based
`P.twistEtale` interface, which asks for an unnecessary ramification divisibility
hypothesis. `AffineSpace.zeroLastCoordinates` comes from the already landed
smooth-pair-coordinate module. The generic supported-sections functor and
`supportRestrictionArrow` come from the support-cohomology dependency. All stated
proof-dependency modules are imported; the three proof dependencies without a
published declaration remain the existing DAG proof obligations, not replacement
axioms or newly invented hypotheses.

Edge cases checked against the statement and its nine-step proof:

- b=0: the support is all of T, the punctured open is empty, the zero-section
  origin is A^0_k, and the comparison is the unit/constant-line identification.
- a=0: the support subspace is the zero section over S; no positive tangential
  dimension is required.
- Empty T or empty support: no supported geometric point occurs and the b=c
  implication has a false nonemptiness premise.
- Arbitrary positive levels, including levels smaller than the ramification
  index: use the actual quotient characteristic, not an exponent requiring a
  divisibility assumption.
- Negative r and r-b: the published signed sheaf uses dual tensor powers, and
  the tensor/pullback family preserves evaluation.
- Arbitrary nonreduced, reducible, non-noetherian and infinite-dimensional S:
  no additional hypothesis occurs; the dimension equation retains infinite
  values and the proof uses a minimal-base point rather than infinite cancellation.
- The separably closed field and scheme share universe u, while coefficient
  modules are in u+1, as in the recorded geometric-stalk and coefficient interfaces.

Searches for an existing statement or support-kernel interface:

- `msearch.py ... leanfinder "geometric stalk of derived sections with closed support for an etale coordinate chart equals supported cohomology of affine normal space"`: eight unrelated structure-sheaf stalk/germ results; no match.
- `msearch.py ... loogle "AlgebraicGeometry.AffineSpace, CategoryTheory.GrothendieckTopology.Point.sheafFiber"`: no results.
- `msearch.py ... grep "sectionsWithSupport|supportedSheaf|supportSheaf|coordinateModel"`: no Mathlib results.
- `msearch.py ... leansearch "The subsheaf of sections supported on a closed subscheme of the ordinary etale site is the kernel of the adjunction unit to the open complement"`: unrelated ideal-sheaf kernel results; no match.
- `msearch.py ... leanfinder "kernel of restriction unit of sheaves on the small etale site sections supported on a closed subscheme"`: unrelated ideal-sheaf kernel results; no match.
- `rg` in upstream WeilConjectures and published Sheaf sources for the item id,
  sectionsWithSupport/supportedSheaf/supportSheaf/coordinateModel, relative
  support, normal slices and supported stalks: existing pro-etale support Q and
  ordinary global support/cohomology constructions, but no ordinary sheaf kernel
  or this coordinate-stalk comparison. The ordinary global functor is reused.
- Exact-name `rg` over Mathlib, WeilConjectures, published Sheaf and
  dag/lean_names_upstream.json for coordinateSupportSheaf,
  RelativeSupportCoordinates, coordinateGlobalToStalk and
  coordinateCoefficientCharacteristic, CoordinateTatePullbackData, coordinateTatePullback, coordinateTateProduct, their existsUnique theorems and IsNormalizedCoordinateTateProduct: no collisions.
- Source reads: Stacks more-morphisms.tex, Tag 0FUE; etale-cohomology.tex,
  Tag 09XP; the node's full nine-step argument; the recorded dependency modules
  and the already published simultaneous-coordinate and signed-Tate interfaces.

Validation: the prescribed scompile.py command for both delivered files completed
with exit code zero and no warnings. The support file and coordinate file were
checked separately in dependency order, including their library-module names.
Compilation uses only that wrapper and its unchanged per-file limit. The final
server dry run and delivery output record the per-file compiler and preflight
results. Only the expected sorry declarations are permitted warnings.

## New nodes

`def-pur-etale-coordinate-support` (module
`Sheaf.AlgebraicGeometry.EtaleCoordinateSupport`) defines the ordinary-etale
sheaf support kernel, its supported-stalk functor, the canonical inclusion-normalized
global-to-stalk and further-restriction maps, and their derived transformations.
Source: Stacks Tag 09XP and steps 1, 5, 7 of the parent item's proof. It reuses
`CategoryTheory.Sheaf.supportedSectionsFunctor`,
`AlgebraicGeometry.Etale.supportRestrictionArrow`, the geometric sheaf-fibre
functor and the existing derived base-change/composition APIs. The existing
`def-pur-support-cohomology` node supplies global support, not the sheaf-valued
kernel; the formal closed-support nodes concern the pro-etale site and different
coefficient encoding. The blueprint/node scan, LeanSearch, Loogle, Mathlib grep,
and source/Sheaf grep found no existing ordinary-etale sheaf support or normalized
supported germ map. Their tool output is copied into the new node's
`mathlib_searches`. The support kernel's additive and injective-preservation
obligations, kernel factorization obligations and restriction square are named
sorry theorems with full proof docstrings; no data are postponed.

The new module is also needed to keep each file within the unchanged 60-second
compiler limit. The main module imports it and adds the geometric chart, the
actual normal-coordinate map, the normalized signed Tate comparisons, the
invertibility assertion, and the dimension conclusion. Both delivered files are
compiled separately, in dependency order, through scompile.py.

## Second reading by Q126

Independent maintainer second reading, 2026-10-18, of immutable delivery
6714686386c8bf070baca61942aebac0a8e18cc1. This section replaces the delivered
placeholder; it does not claim that the worker performed an independent reading.
The packet, item node, all thirteen statement dependencies, both complete Lean
modules and their docstrings, the new definition node, and the worker report were
read against the source and the exact dependency interfaces.

Hypothesis and conclusion audit:

- `PurityFiniteSetting` retains the fixed finite-field/coefficient datum and every
  positive level. Its quotient and ULift coefficient are the published ones.
  The characteristic positivity/unit helpers derive properties of that datum;
  they introduce no extra hypotheses or divisibility restriction.
- `RelativeSupportCoordinates` has an arbitrary k-scheme S, the two smooth maps,
  the closed S-immersion, and the etale map T to X. `overBase` expresses the
  smooth closed pair over S in Stacks 0FUE. No finite-type, noetherian,
  separation, regularity, or finite-dimension assumption on S was introduced.
- The natural numbers a and b include zero. The actual categorical pullback is
  Y_T. The chart is etale over S, and the cartesian square with the existing
  `zeroLastCoordinates` states scheme-theoretic inverse image. Its support map
  is the uniquely determined map of that square, not extra geometric structure.
- `coordinateSupportSheaf` is the kernel of the open-complement adjunction unit
  in the sheaf functor category. Pointwise evaluation gives exactly the stated
  kernel on every etale W. `coordinateSupportedStalk` composes it with the
  published pointed-neighbourhood colimit functor. The derivation isomorphism
  uses actual derived-composition and exact-stalk comparison isomorphisms.
- Every separably closed geometric point on the support and every integer r
  occur in the main theorem. The range-containment hypothesis says the point
  lies on Y_T. Coefficients and modules are in u+1, schemes and geometric fields
  in u, consistently with the published site and stalk interfaces. There is no
  equality imposed between independently sized site universes.
- `normalSpace`, `origin`, and `normalMap` are actual affine space, zero section,
  and the ordered last-b-coordinate map over k. `normal_support` states their
  inverse-image closed-set equality. The comparison source is ordinary etale
  global supported cohomology of this space; its target is literally the stalk
  of derived sheaf support of `chartTwist r`.
- The global-to-stalk and restriction maps are fixed by unique factorization
  through monic supported-kernel inclusions. The definitions derive those maps,
  rather than choosing unrelated maps or isomorphisms. The asserted `IsIso`
  gives the displayed isomorphism after inversion in D+ of A-modules. Working
  in D+ loses no case of these right-derived functors on degree-zero sheaves.
- Signed twists reuse `finiteEtaleTateSheaf`, including its internal-Hom
  negative powers. The compact pullback and product choices have full unique
  normalization predicates: roots/generators, unit, positive recursion and
  negative evaluation; products also have associativity and symmetry. The
  exact published `etaleFiniteTwistPullback` statement supplies these families
  and their composition/product/exponent-change properties. Thus these are
  determined data, not hollow existence choices or new Tate notions.
- Further etale restriction is the explicit natural-transformation composition
  square in `coordinateDerivedGlobalToStalk_restriction`. Specializing to the
  chart and transporting by the normalized Tate and stalk isomorphisms gives
  restriction for the delivered comparison. `comparison_twist_identification`
  is the naturality square at the actual normalized tensor identification;
  transporting its coefficients gives the stated A(r)=A(b) tensor A(r-b)
  compatibility. Both are properties of the same comparison.
- The second conjunct quantifies c and every point of Y, with Krull dimension
  in `WithBot ENat`, retaining infinite dimensions. It concludes b=c only for
  nonempty Y_T. The proof's minimal-base-prime argument produces finite local
  dimensions b and zero, and does not cancel infinite cardinals.

Sources and dependencies checked:

- Stacks `more-morphisms.tex`, Tag 0FUE, label
  `lemma-etale-local-structure`, lines 4861 ff.; arbitrary base S and the
  scheme-theoretic coordinate square.
- Stacks `etale-cohomology.tex`, Tag 09XP, label
  `section-cohomology-support`, lines 13966 ff., including the supported-sheaf
  definition, injectivity lemma, and support triangle. Tag 0EYM at lines
  7567 ff. supplies the continuity used in the proof.
- Milne, Lectures on Etale Cohomology, printed pp. 111-112, Theorem 16.7
  and Lemma 16.8. These provide the field smooth-pair case; the delivery
  correctly labels the arbitrary-base assertion as its auxiliary argument.
- Exact Mathlib declarations for schemes, smoothness, closed immersions,
  etaleness, affine spaces and the small etale topology; the recorded base
  change conventions and derived-category module were also read through
  `scompile.py --source` because those modules are absent from the old clone.
- The published support-cohomology, pointed-etale-stalk, purity finite-setting,
  coefficient-twist, simultaneous-coordinate, finite signed Tate sheaf and
  finite Tate pullback modules. In particular `Point.sheafFiber` is the same
  colimit diagram as the recorded `pointedEtaleStalk`, for module coefficients
  where the former is available. No private stalk or global-support notion
  was introduced.
- Additional searches for support functors, support kernels, supported stalks,
  and normal slices in Mathlib, upstream WeilConjectures and side Sheaf sources
  found global supported sections, complex-level support triangles and
  pro-etale support, but no duplicate of this ordinary-etale support functor
  with its normalized germ comparisons. The worker's three kinds of search
  and the new node's search/source/blueprint records were checked.

Edge cases checked: a=0, b=0 (whole support and empty product), empty T and
empty support (vacuous point assertion), all positive coefficient levels,
negative r and r-b, nonreduced/reducible/non-noetherian/infinite-dimensional
bases, and infinite local Krull dimensions. The new support node is in the
item's chapter/unit, is cited by it, has the required fields, and states the
actual kernel construction and its normalized maps. No statement correction
or dependency-module repair is required. Both `lean.statement` strings occur
verbatim in their delivered modules; declarations are recorded, variables and
universes are bound, and no line exceeds 100 characters. All local theorem
proofs are `sorry`; data definitions are concrete constructions or choices
from genuinely unique normalization statements. Source/blueprint docstrings
are present and the main theorem retains all nine proof steps.

Route-pivot check: no direct statement/proof dependency is in the current
`coord/route-pivot-dropped.txt`, no item repair note exists at the inspected
`origin/newtargets-dag` ref, and the delivery introduces no infinity/dg/model
machinery. Its comparison is ordinary etale; imported pro-etale comparison
results used in the proof do not replace the statement by a pro-etale one.

Reproduction: ran the prescribed command on the two immutable snapshot paths
in dependency order:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q126 lem-pur-relative-support-coordinate-model snapshot/lean/Sheaf/AlgebraicGeometry/EtaleCoordinateSupport.lean snapshot/lean/Sheaf/Paper/RelativeSupportCoordinateModel.lean
```

It exited 0 with no errors or warnings. The wrapper compiled the private
support overlay, preliminary support file, both sandbox statements, and both
library module names. Reported support library time was 6.4 s; the main sandbox
and library elapsed times were 61.1 s and 65.4 s respectively, with no timeout
reported. These are the wrapper's elapsed times, not a claim about CPU time.
The installed wrapper currently runs the server side overlay and confirmation;
no compiler limit was altered. No global build or direct ssh was run, no live
Lean file or clone was edited, and no Git mutation or delivery command was used.

Finding and correction: H11 (and the user's real-second-reading gate): the
original section consisted solely of a process disclaimer and contained no
reading. Replaced it with this audit. No mathematical or Lean changes were
needed. The complete replacement report is supplied as the review fix.
