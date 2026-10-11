## Worker report

The item is stated by `AlgebraicGeometry.torIndependent_perfect_pullback_comparison`
in `lean/Sheaf/AlgebraicGeometry/TorIndependentPerfectPullbackComparison.lean`.
Its only proof is `sorry`. The original mathematical statement is unchanged.
The item's `stmt_deps` gains one definition node,
`def-pc-pullback-stalk-tensor-comparison`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The schemes X, S, S' and arbitrary morphisms f and g are `{X S T : Scheme.{u₁}}`,
  `(f : X ⟶ S)`, `(g : T ⟶ S)`; T denotes S'. There is no finite-type, flat,
  separated, quasi-compact, or nonempty hypothesis.
- X' is the actual chosen fibre product `Limits.pullback f g`, not an arbitrary
  scheme equipped with maps. Its g_X and f' are `pullback.fst f g` and
  `pullback.snd f g`. This uses exactly the fibre-product convention of the
  recorded `def-pc-base-change`, not its module-base-change declaration, which
  concerns a different clause of that bundle.
- Stalkwise Tor independence is `hTor : PullbackStalkTensor.IsTorIndependent f g`.
  Unfolding this definition quantifies over EVERY x in X, t in T and equality
  f x = g t, and every positive natural degree i. The actual stalk maps specify
  the two scalar structures. The right map first transports the base stalk
  using `S.presheaf.stalkCongr (.of_eq h)`. `CategoryTheory.Tor'` derives in the
  first variable, exactly the projective-resolution definition of the recorded
  `def-weil-pbc-tor-modules`. Its result is a module, so vanishing is `IsZero`.
- P belongs to D(O_X) as `P : schemeDerivedCategory X`, and perfectness is the
  existing `hP : Scheme.IsPerfect X P`. The common HasDerivedCategory binders
  specify the localization used by the recorded definitions. The binders on
  opens are precisely those required by `Scheme.IsPerfect`; they add no
  geometric condition. They do not choose a different Abelian structure.
- Every x' is `∀ z : ↥(Limits.pullback f g)`. There is no restriction on its
  image, residue field, or any chosen affine neighbourhood. `R`, `A`, `B`, `C`
  in the new module are the actual four local rings at the points in the node.
- The conclusion is `PullbackStalkTensor.IsComparisonIso f g P z`. It quantifies
  over `i : ℤ`, so includes negative degrees and degree zero.
- To express P_x as a genuine complex, this predicate quantifies over all K-flat
  representatives K with `Nonempty (DerivedCategory.Q.obj K ≅ P)` and uses
  `stalkComplex f g z K`, the recorded stalk functor applied termwise. These
  are coordinates for the SAME P, not a restriction to strictly perfect global
  models (which need not exist). K-flat representatives exist for every P.
- The source H^i(P_x tensor-derived-over-R B) is the cohomology object of the
  existing `ModuleCat.baseDerivedTensorCohomologyModel`, applied to that stalk
  complex. Its E = A tensor-over-R B action is fixed by the model's
  `cohomologyIso_smul`, not an arbitrary module structure. Tensoring with C is
  `extendScalars (algebraMap E C)` in `localizedComparison`.
- The map is the existing model's `localizedComparison i`. Its defining
  `comparison_eq`, `ordinaryToLocalized_tmul`, and `localized_eq` equations
  specify the derived-to-ordinary map and its localization; it is not an
  existential unconstrained map between two modules.
- The algebra E -> C is `tensorToStalk`. The named existence theorem requires
  its restrictions to A and B to equal the actual two projection stalk maps.
  The tensor universal property makes it unique. Its A -> C composite is
  exactly g_X's stalk map, so `stalkTensorComplex` is Q tensor-over-A C.
- The target is the actual module stalk of
  `(DerivedCategory.homologyFunctor _ i).obj ((derivedPullback g_X).obj P)`.
  Exactness of stalks identifies this with H^i((Lg_X^*P)_z).
- The predicate first requires an isomorphism e from the ordinary tensor
  cohomology to that target. For every such e it asserts
  `IsIso (localizedComparison i ≫ e.hom)`. This states precisely invertibility
  of the specified canonical comparison under the natural K-flat
  pullback-stalk identification. It does not assert that every e itself is
  that canonical identification, nor does it need to: composition with an
  isomorphism preserves and reflects IsIso. Thus the canonical identification
  is among the tested e's, and proving invertibility with it proves the same
  assertion for all e's. The requirement of an identification prevents this
  last universal condition from being vacuous. This change of target
  coordinates neither weakens nor strengthens the canonical-map assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Scheme.Hom.stalkMap`, and the actual structure presheaf stalks.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its module docstring and
  conventions use `Limits.pullback` with `pullback.fst`, `pullback.snd`.
  No second module-base-change definition is introduced or imported unused.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, with exactly
  the shared derived categories and local strictly-perfect-model condition.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback` and its
  `exists_derivedPullback` universal-property/K-flat-counit specification.
- `Sheaf.Algebra.Homology.DerivedTensor`: the recorded `Scheme.derivedTensor`
  and `derivedTensorRing` were read in full. They are specifically for the
  pro-etale constant coefficient site stated by their node. They cannot be
  applied to local-ring modules; their record is correct for that dependency
  node, so replacing it by a ring-module definition would be an H13 fault.
  Instead the already-landed ring-module model below is reused by the new node.
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`:
  `ModuleCat.BaseDerivedTensorCohomologyModel`, `baseDerivedTensorCohomologyModel`.
  Its full signature, scalar-action conditions, and map equations were read.
- `Sheaf.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, preserving zero maps; this is applied
  degreewise with `mapHomologicalComplex`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, the recorded
  Mathlib match of `def-weil-pbc-tor-modules`; ModuleCat monoidal and projective
  resolution instances were read in Mathlib's Monoidal/Basic and Projective.

The natural-language proof follows all three original proof steps, naming all
six original proof dependencies. Its last sentences explain the transport from
an affine bounded projective model to any K-flat representative. No proof was
implemented. The new module's only deferred proofs are `point_eq` and
`exists_tensorToStalk`, both named, with complete source/proof docstrings;
the new definition node records both. Ring-map data are chosen from the latter
existence theorem; no definition has data written as `sorry`.

Edge cases checked before writing:

- Empty X, T or fibre product: the respective point quantifiers are empty,
  precisely as in the mathematical statement. No Nonempty hypothesis occurs.
- Zero P and arbitrary shifts: any K-flat representative is permitted and i
  ranges over all integers. The fixed comparison between zero cohomology
  modules is an isomorphism, including outside the support of a perfect model.
- g or f the identity: the canonical scalar structures and tensor map reduce
  to the usual stalk extension maps; no spurious flatness hypothesis appears.
- Failure of Tor independence: e.g. R = k[e]/(e^2), A = B = k has nonzero
  Tor_1. The quantified hTor excludes this square; it is not an always-true
  identity-morphism hypothesis.
- A perfect object need only be locally strictly perfect. We do not require
  a global bounded complex of finite free modules; global K-flat coordinates
  exist without such a hypothesis.
- Both stalk ring and module universes are u, and the module derived category
  uses HasDerivedCategory.standard. No smaller independent test universe or
  restricted family of schemes occurs. Schemes can be taken in any u.

Searches (executed by msearch.py; searches.jsonl contains the receipts):

- LeanFinder: `Tor independent scheme square perfect complex stalk derived
  pullback tensor comparison` returned eight scheme fibre-product/residue
  tensor declarations, none a derived perfect-stalk comparison.
- Loogle: `ModuleCat.Tor` returned zero hits and an unknown-identifier message.
  The actual recorded general match `CategoryTheory.Tor'` was then read directly.
- Mathlib grep: `TorIndependent|torIndependent|derivedStalk|stalkDerived`
  returned zero hits.
- LeanSearch: `canonical derived tensor comparison at a scheme pullback stalk`
  was unavailable (Internal Server Error); no mathematical verdict was inferred.
- Mathlib grep: `stalk.*[Tt]ensor|[Tt]ensor.*stalk`, restricted to AlgebraicGeometry,
  returned an unrelated surjective-on-stalks tensor embedding lemma.
- LeanFinder: `scheme pullback stalk canonical tensor comparison cohomology K
  flat representative` returned eight ordinary scheme pullback/residue tensor
  declarations, no definition of this condition.
- Mathlib grep: `PullbackStalkTensor|stalkTorIndependent|pullbackStalkTensorComparison`
  returned zero hits. The same pattern against WeilConjectures, lean/Sheaf and
  dag/nodes returned zero hits before writing.
- Project grep for `TorIndependent|torIndependent|stalk.*[Cc]omparison|derivedStalk|
  stalkDerived|perfect.*pullback|baseDerived` located the existing algebraic
  `BaseDerivedTensorCohomologyModel` and projective-complex tensor lemma, which
  are reused instead of copied. The other matches concerned etale sheaves.
- The specified item-id grep of WeilConjectures returned zero hits.
- `blueprint_refs.py search 'stalk tensor square'` and
  `blueprint_refs.py search 'pullback stalk tensor comparison'` returned no nodes.
  `blueprint_refs.py ancestor` returns `lem-sc-finite-duality`.

Source reading: literature/stacks-project/perfect.tex is not present in this
remote clone. The raw Stacks master perfect.tex was read at
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
label lemma-compare-base-change, including its entire local affine proof.
The Stacks tag webpage returned 503; the raw official source succeeded.
The node's local comparison is the algebraic stalk step, not the global
Rf_* base-change lemma, so the latter's qcqs hypotheses are not added here.
The module-pullback stalk and K-flat-computation dependency modules and their
source/proof docstrings were also read.

Validation: both delivery modules compile together on the server in dependency
order, in 3.2 seconds, with no errors and no warnings. Only the expected named
`sorry` proofs remain. No local Lean build and no direct git command was run.
No STATEMENT-DISPUTED issue or mathematical statement correction was needed.

## New nodes

`def-pc-pullback-stalk-tensor-comparison` records the actual four stalk rings,
their canonical scalar maps, stalkwise Tor independence, and a representation
independent condition for invertibility of the canonical comparison in K-flat
coordinates. Its module is
`lean/Sheaf/AlgebraicGeometry/PullbackStalkTensorComparison.lean` and its main
declaration is `AlgebraicGeometry.PullbackStalkTensor.IsComparisonIso`.
The source is Stacks 08IB's affine derived-tensor comparison, with the K-flat
pullback and stalk computations of 06YJ and 0098. The three kinds of searches
above and DAG/project searches found no such existing definition. The existing
module-stalk, K-flat and algebraic tensor-cohomology notions are imported and
cited; this node only supplies their scheme-square coordinates and the
coordinate-invariant IsIso condition. Its scalar-map existence theorem assumes
neither perfectness nor Tor independence and supplies no invertibility of the
derived comparison, so it does not defer the item's conclusion into a definition.


## Second reading by F1

I independently opened the item node, both delivery modules, every statement
 dependency's node and recorded declarations, and the new definition's dependencies.
The following is my inventory of the mathematical statement and its Lean rendering.

| Object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Arbitrary schemes X, S, S' | `{X S T : Scheme.{u₁}}`; T is S'. Same schemes, PASS. |
| Arbitrary morphisms f:X -> S and g:S' -> S | `(f : X ⟶ S) (g : T ⟶ S)`. No geometric assumptions added, PASS. |
| Cartesian X' and its projections g_X, f' | `Limits.pullback f g`, `pullback.fst f g`, `pullback.snd f g`. Actual scheme fibre product, PASS. |
| Every pair x,s' lying over the same s | `IsTorIndependent` quantifies `∀ (x : X) (t : T) (h : f x = g t)`. Not restricted to chosen pullback points, PASS. |
| Vanishing Tor_i over the base stalk, for every i>0 | `∀ i : ℕ, 0 < i → IsZero ...`; `CategoryTheory.Tor'` resolves the first module. Stalk maps give the scalar structures, with `stalkCongr` transporting the right base stalk, PASS. |
| P an object of D(O_X) | `(P : schemeDerivedCategory X)`, the recorded all-module derived category, PASS. |
| P perfect, locally rather than globally | `(hP : Scheme.IsPerfect X P)`; this means open-local strictly perfect representatives, PASS. |
| Every x' with x=g_X(x'), s'=f'(x'), s=f(x) | `∀ z : ↥(Limits.pullback f g)`; `A`, `B`, `R` substitute exactly these projected points, PASS. |
| Four rings O_S,s, O_X,x, O_S',s', O_X',x' | `R`, `A`, `B`, `C` are the actual structure-presheaf stalks; no residue-field replacement, PASS. |
| Tensor algebra O_X,x tensor_O_S,s O_S',s' -> O_X',x' | `tensorToStalk`, chosen from `exists_tensorToStalk`, with both restrictions equal to the projection stalk maps. The universal property fixes this map uniquely, PASS. |
| Every integer cohomology degree | `∀ i : ℤ` inside `IsComparisonIso`; includes zero and negative degrees, PASS. |
| Source H^i(P_x tensor-derived_R B) tensor_E C | `(cohomologyModel ...).cohomology i` and its `localizedComparison i` source. The imported model fixes derived extension, E-action and scalar extension to C, PASS. |
| Target H^i((Lg_X^*P)_x') | `moduleStalkFunctor ... z` applied to `homologyFunctor ... i` of `(derivedPullback (pullback.fst f g)).obj P`. Stalk exactness gives the displayed target, PASS. |
| The canonical map is an isomorphism | `IsIso (localizedComparison i ≫ e.hom)` for every target identification e, together with `Nonempty` of such identifications. The map is specified, not an arbitrary existential morphism, PASS. |

The K-flat-coordinate quantification is equivalent to the node's assertion:
K-flat representatives of P exist; by Tag 06YB their stalks are K-flat over A.
Tag 06YJ computes the derived pullback on these representatives, and Tag 0098
identifies its stalk with ordinary extension from A to C. Thus the target
identification required in the predicate always exists independently of Tor
independence or perfectness. Postcomposition by any isomorphism preserves and
reflects invertibility. Since stalks and restriction of scalars are exact,
derived tensor over R depends only on P_x, including when K is not R-flat.
The predicate's universal choice of K adds no mathematical hypothesis or clause.
The `letI` expressions occur in definitions to fix scalar/category structures;
there are no obstructive let binders in the theorem signature.

Dependency audit: I read `Scheme` and `Scheme.Hom.stalkMap` in pinned Mathlib;
`BaseChangeConventions` uses the same chosen fibre product and projections.
I read `schemeDerivedCategory`, `Scheme.IsPerfect`, `derivedPullback` and its
existence theorem in full. Their shared HasDerivedCategory binders specify
presentations of the localizations, with Mathlib's shared Abelian structures;
they impose no flatness, finiteness, Noetherian or separatedness condition.
The over-open binders are exactly those needed by the recorded perfect predicate.
`def-weil-derived-tensor` is genuinely pro-etale constant-coefficient tensor,
not tensor of local-ring modules; its declaration is therefore not misused.
The existing `BaseDerivedTensorCohomologyModel` supplies the needed ring-module
notion without copying or changing that dependency. I read its `universal`,
`ordinaryIso_tmul`, `cohomologyIso_smul`, `comparison_eq`,
`ordinaryToLocalized_tmul` and `localized_eq` fields: they specify the actual
canonical comparison and do not assume it is invertible.
I also read the module stalk functor, K-flat predicate, and Mathlib Tor' definition.

Source audit: the remote literature tree lacks perfect.tex. I read the official
[Stacks perfect.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex),
label `lemma-compare-base-change`, including its proof and chapter conventions.
Its global Rf_* assertion assumes qcqs, but the local affine Tor tensor argument
used by this node does not. No qcqs hypothesis belongs in this local stalk lemma.
I separately opened [0098](https://stacks.math.columbia.edu/tag/0098),
[06YJ](https://stacks.math.columbia.edu/tag/06YJ), and
[06YB](https://stacks.math.columbia.edu/tag/06YB) for the pullback-stalk and
K-flat identifications above. No statement correction or citer re-review is needed.

New-node audit (H12): `def-pc-pullback-stalk-tensor-comparison` introduces only the
scheme-square coordinates and the comparison invertibility predicate missing
from the DAG. Its self-contained statement introduces all rings and maps,
cites its eight definition dependencies, and matches the definitions in its
module clause by clause. Its chapter/unit, created record, empty proof lists,
null match, absent audit states, source and Lean record follow section 5.
The item cites it. Neither `point_eq` nor `exists_tensorToStalk` asserts
Tor independence, perfectness, a localization, or comparison invertibility;
they are the elementary square identity and tensor universal property.
Their deferred proofs are named and documented. All data definitions are
explicit constructions or choice from a named existence theorem, with no
hollow data. No dependency module was added or needed (H13).

Edge cases: empty X or S' or X' gives the correct empty point quantifiers.
The zero perfect complex and every shift are included; no global strictly
perfect representative is required. Degree i=0 is in the conclusion while
Tor_0 is correctly excluded from the vanishing hypothesis. Negative i are
included. No characteristic or field restriction occurs. All schemes and
stalk modules live in arbitrary u₁; w₁ only presents the sheaf-derived
categories. Tests do not quantify over a smaller independent universe.
Identity morphisms give the usual scalar-extension comparison; nonzero Tor
(e.g. the dual-number quotient with itself) fails the actual hypothesis.
There is no index set or nonemptiness premise to exclude an edge case.

Independent searches, with receipts in searches.jsonl:

- LeanFinder `homology of derived extension of scalars Tor vanishing local rings
  perfect objects`: eight hits, chiefly abstract projective-Tor vanishing;
  none states the scheme-perfect stalk comparison.
- LeanFinder `localization of cohomology derived tensor and pullback of perfect
  sheaves`: eight ordinary sheaf pullback/free-object hits, no matching notion.
- Loogle `CategoryTheory.Tor'`: five hits, confirming the recorded Tor definition
  and projective vanishing facts, no matching scheme statement. A preliminary
  escaped query was malformed and was replaced by this successful literal query.
- LeanSearch `stalk of derived inverse image of a complex of modules under a
  cartesian scheme square`: service Internal Server Error; no verdict inferred.
- Direct rg in Mathlib AlgebraicGeometry, upstream WeilConjectures, lean/Sheaf
  and DAG nodes using `TorIndependent`, `torIndependent`, `stalkComparison`,
  `stalkTensor`, and perfect/pullback combinations: no duplicate definition.
  The upstream `Etale.stalkComparison` concerns geometric etale stalks of Gm,
  a different object. The project's `derivedPullback_torIndependent_flat_complex`
  was opened: it assumes a bounded-above base-flat quasi-coherent complex and
  concludes ordinary tensor comparison, so is not this perfect-object statement.
  The shared algebraic tensor model is already reused.

Mismatch/change verdict: no mathematical or Lean-signature mismatch found.
I left both modules and node records unchanged and appended this independent
reading. All declarations have source/blueprint docstrings; the theorem's
proof docstring carries all three node proof steps and six proof dependencies.
No theorem is proved: the three delivery theorems have only `sorry` proofs.
The two modules compiled together using scompile.py, in dependency order,
in 3.3 seconds, with exit code 0 and no warnings. Variables and universes
are explicitly bound; both recorded signatures match their files.
