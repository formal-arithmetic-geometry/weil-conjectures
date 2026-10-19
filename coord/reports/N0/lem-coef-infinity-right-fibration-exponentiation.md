## Worker report

The delivery states the right-handed assertion of Kerodon Proposition the project server,
[Tag 0154](https://kerodon.net/tag/0154), in
`lean/Sheaf/CategoryTheory/RightFibrationExponentiation.lean`. The only postponed theorem is
`SSet.rightFibration_exponentiation`, whose proof is `sorry`. The helper
`SSet.rightFibrationExponentiationMap` constructs the actual canonical relative internal hom
map with real data. Its commutativity proof is naturality, with no postponed theorem.

Hypothesis and clause correspondence:

* Arbitrary small simplicial sets `A`, `B`, `E`, and `S` are the explicit binders
  `{A B E S : SSet.{u}}`, with an explicitly declared universe `u`.
* The map `q : E ⟶ S` is the node's right fibration. The hypothesis
  `hq : ∀ (m : ℕ) (j : Fin (m + 1)), 1 ≤ m → 0 < j →
  HasLiftingProperty (horn m j).ι q` spells out precisely its horn lifting property.
  `Fin (m + 1)` already imposes `j ≤ m`; the final horn is included.
* The map `i : A ⟶ B` is the node's right-anodyne inclusion, with the hypothesis
  `hi : rightAnodyneExtensions i`. This uses the already landed definition of the smallest
  class containing right horns and all isomorphisms, closed under pushouts, transfinite
  compositions and retracts. Such maps are monomorphisms; no independent monomorphism
  hypothesis is necessary.
* `Fun(B,E)` is Mathlib's internal hom `(ihom B).obj E`, the exact internal functor
  simplicial set used by `def-cbc-enhanced-diagrams-cones`.
* The codomain of the helper is
  `pullback ((MonoidalClosed.pre i).app S) ((ihom A).map q)`, which is
  `Fun(B,S) ×_{Fun(A,S)} Fun(A,E)`. The two maps into `Fun(A,S)` are restriction and
  postcomposition, respectively. Simplicial limits are computed degree by degree.
* The helper is `pullback.lift ((ihom B).map q) ((MonoidalClosed.pre i).app E) ...`.
  Thus its first component sends `u` to `q ∘ u`, and its second sends `u` to `u ∘ i`.
  Naturality of `MonoidalClosed.pre i` gives their compatibility over `Fun(A,S)`.
* The conclusion `modelCategoryQuillen.I.rlp (rightFibrationExponentiationMap i q)` is
  exactly the Mathlib match recorded for `def-weil-pbc-trivial-kan-fibration`: right
  lifting against every boundary inclusion, including dimension zero.
* There is no quasicategory assumption on either `E` or `S`.

Dependency declarations and source inspection:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the recorded declaration
  `SSet.Enhanced.coneCategory` and its surrounding definitions. This module explicitly
  uses Mathlib's internal hom `(ihom K).obj C`; the present statement uses that same object.
  The primary cone declaration itself is not needed by this particular theorem.
* `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.I` is the family `ofHoms (fun n ↦ ∂Δ[n].ι)`.
  `Mathlib.AlgebraicTopology.SimplicialSet.Boundary` defines `SSet.boundary` by
  nonsurjective monotone maps and proves `SSet.boundary_zero = ⊥`.
  `CategoryTheory.MorphismProperty.rlp` is the universal right lifting property.
  These are the recorded Mathlib declarations for the trivial-Kan dependency.
* `Sheaf.CategoryTheory.RightAnodyne`: read the entire signature and body of
  `SSet.rightAnodyneExtensions`. Its `sInf` definition is precisely the stated smallest
  closure class. Added its already landed node `def-coef-infinity-right-anodyne` to
  `stmt_deps`, as authorized for a landed notion needed by the statement.
* The stated proof dependencies are imported through
  `Mathlib.CategoryTheory.Limits.HasLimits` (`CategoryTheory.Limits.colimit`),
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
  (`CategoryTheory.MorphismProperty.llp_isStableUnderRetracts` and the pushout and identity
  closure instances), and
  `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`
  (`CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`).
  `lem-coef-infinity-right-anodyne-product` has no Lean declaration yet, so no import can
  be supplied for it. Its mathematical use is retained in the proof docstring.

Edge cases checked: `m = 1` includes the horn `j = 1`; `j = m` is included in all positive
dimensions; `j = 0` is excluded. Empty simplicial sets are allowed throughout, and a
right-anodyne isomorphism, including the identity of the empty set, is included.
The conclusion uses all boundaries, including the empty boundary of `Δ[0]`, hence retains
surjectivity on vertices. No finiteness, inhabitance, fibrancy or quasicategory restriction
is imposed. All universe and term variables are explicitly bound.

Searches performed with the prescribed search wrapper and direct source searches:

* LeanFinder query: `Exponentiating a right fibration against a right anodyne simplicial
  inclusion gives a trivial Kan fibration`. Eight hits, including
  `SSet.modelCategoryQuillen.J`, `.I`, the all-horn fibration lifting instance, and the
  general model-category Joyal trick. None states the one-sided exponentiation result.
* Loogle query: `"anodyne", "fibration"`. Zero hits.
* Mathlib grep query: `right.?anodyne|right.?[Ff]ibration|exponent.*[Ff]ibration`, in
  `AlgebraicTopology`. Zero hits.
* LeanSearch query: `Right fibrations of simplicial sets have the right lifting property
  against horns with positive missing vertex`. Eight hits, including all-horn Quillen
  fibration declarations, `SSet.KanComplex`, and `MorphismProperty.rlp`. No right-fibration
  definition or exact exponentiation result.
* Loogle query: `"rightFibration"`. Zero hits.
* LeanFinder query: `Right anodyne maps are the closure of positive vertex horn inclusions
  under pushouts transfinite compositions and retracts`. Eight hits, including all-horn
  `J`, boundary `I`, and inner-horn quasicategory declarations. No exact right-horn closure.
* `rg` for right-fibration/right-anodyne names in upstream `WeilConjectures` and the
  upstream declaration index found no matching declaration. Searching the item id in
  upstream `WeilConjectures` likewise found none.
* A refreshed `rg` search of the project's `lean/Sheaf` found the newly landed
  `SSet.rightAnodyneExtensions` in `Sheaf.CategoryTheory.RightAnodyne`; the delivery now
  imports and uses it. The corresponding DAG node is already stated and was read in full.
* `tools/blueprint_refs.py search 'right anodyne'` returned zero blueprint nodes; the DAG
  search and recorded Lean node identify the landed definition just described.

The source theorem agrees with the node. No statement correction or disputed assertion is
needed. This report is the author's check; the independent second reading remains for the
next worker. No new nodes or dependency modules are delivered.

Validation: the final module is compiled through `scompile.py` and the required
`deliver2.py --no-push` dry run is performed before handoff.

## Earlier second reading (a previous round; superseded)

I independently read the node, the sandbox module, the statement-dependency records and
actual declarations, and the source before changing the file. The source is Kerodon
[Proposition the project server, Tag 0154](https://kerodon.net/tag/0154), not a Stacks theorem with
that tag. Its right-handed assertion has precisely the node's hypotheses, with arbitrary
simplicial sets and no ambient quasicategory assumption. I also read Kerodon
[Variant the project server, Tag 014U](https://kerodon.net/tag/014U) for the right-anodyne generators,
[Proposition the project server, Tag 0153](https://kerodon.net/tag/0153) for the Cartesian
pushout-product, and Stacks `simplicial.tex`, label `definition-trivial-kan`, with the
boundary discussion immediately preceding it. The source agrees with the node; no
statement correction, new node, or dependency module is needed.

My object/hypothesis/conclusion checklist, matched against the final Lean:

1. **Four arbitrary small simplicial sets.** The binders `{A B E S : SSet.{u}}` introduce
   all four, with explicit `universe u`. They use the same Mathlib simplicial sets,
   standard simplices and horns as `def-cbc-enhanced-diagrams-cones`. Verdict: exact;
   no category structure, fibrancy, finite-dimensionality, or inhabitance is assumed.
2. **A map from the total space to the base.** `(q : E ⟶ S)` is exactly the map in the
   node. Verdict: exact; neither `E` nor `S` has a `Quasicategory` or `KanComplex` instance
   binder.
3. **Right-fibration hypothesis.** `hq` quantifies over every `m : ℕ` and
   `j : Fin (m + 1)`, assumes `1 ≤ m` and `0 < j`, and requires
   `HasLiftingProperty (horn m j).ι q`. The finite index already gives `j ≤ m`.
   I read Mathlib's `horn` definition: it is the subcomplex of simplices whose image
   misses a vertex different from `j`, exactly the prescribed horn. Verdict: exact,
   including the final horn and excluding the zero-index horn.
4. **Right-anodyne inclusion.** `(i : A ⟶ B)` with
   `(hi : rightAnodyneExtensions i)` uses the existing node
   `def-coef-infinity-right-anodyne` and module `Sheaf.CategoryTheory.RightAnodyne`.
   I read its complete definition: the infimum of morphism properties containing
   isomorphisms and positive-index horns and closed under pushouts, small transfinite
   compositions and retracts. The missing `1 ≤ n` in that definition is redundant:
   a positive element of `Fin (n+1)` forces `n ≥ 1`. This is exactly the node's class.
   Its members are monomorphisms since all generators and closure operations preserve
   monomorphisms; a separate `Mono i` assumption would be redundant. Verdict: exact.
5. **Internal functor simplicial sets.** The map in the conclusion has source
   `(ihom B).obj E`. I read `Sheaf.CategoryTheory.EnhancedDiagramsCones`, which uses
   this exact Mathlib internal hom, and Mathlib's `FunctorToTypes.rightAdj`,
   `functorHomEquiv` and `MonoidalClosed.internalHom`. They give the internal hom with
   simplices `Hom(B × Δ[n], E)`, not an ordinary functor category. Verdict: exact.
6. **Canonical relative internal hom map and displayed target.** The final expression
   uses `((MonoidalCategory.Arrow.pullbackHom.obj (Opposite.op (Arrow.mk i))).obj
   (Arrow.mk q)).hom`, then composes with
   `(pullbackSymmetry ((ihom A).map q) ((MonoidalClosed.pre i).app S)).hom`.
   I traced `pullbackHom` through `MonoidalClosed.internalHom.leibnizPullback` to
   `Functor.PullbackObjObj.ofHasPullback`: before symmetry its target is
   `pullback ((ihom A).map q) ((MonoidalClosed.pre i).app S)` and its components are
   restriction along `i` and postcomposition by `q`. Symmetry reverses these two
   factors. The final target is therefore exactly
   `Fun(B,S) ×_{Fun(A,S)} Fun(A,E)`, with components `(q ∘ u, u ∘ i)` in that order.
   No arbitrary comparison map is supplied as a hypothesis. Verdict: exact.
7. **Trivial Kan fibration, including vertices.** The conclusion is
   `modelCategoryQuillen.I.rlp` applied to the canonical map just described. I read
   the dependency `def-weil-pbc-trivial-kan-fibration` and its recorded Mathlib match:
   `I` is `.ofHoms (fun n ↦ ∂Δ[n].ι)` for every natural number, and `rlp` means lifting
   against every member. `boundary` consists of nonsurjective simplices and
   `boundary_zero` identifies the zero boundary with the empty subcomplex. Thus the
   conclusion gives all positive-dimensional boundary fillers and surjectivity on
   vertices. Verdict: all clauses present, with no additional conclusion.
8. **Quantifier order and scope.** The sets and maps are universally quantified,
   followed by exactly the two lifting/closure hypotheses and the conclusion about
   their induced map. All term variables and universes are explicitly bound and
   `autoImplicit` is false. Verdict: exact.

Edge cases: `m = 0` imposes no horn condition; `m = 1, j = 1` is included, and
`j = m` remains included in every positive dimension. The conclusion includes `n = 0`
and does not discard vertex surjectivity. Empty `A`, `B`, `E` or `S` are allowed wherever
the maps and hypotheses exist; in particular the identity of the empty simplicial set
is allowed among right-anodyne isomorphisms. There is no hidden nonemptiness condition.
The terminal simplicial set and identities are covered. A zero object, characteristic,
or scheme condition is not part of this simplicial-set statement. The common arbitrary
universe is the category of small simplicial sets used by the source; no extra equality
between independent site/coefficient universes is being imposed.

Independent H4 searches used different wording from the author. Through `msearch.py`:

* LeanFinder: `For simplicial sets the pullback exponential comparison has boundary
  fillers when one map lifts all positive indexed horns and the other is in their weak
  saturation`. Eight hits: all-horn Kan filling, `J`, inner-horn quasicategory filling,
  and low-dimensional horn colimits. I inspected the all-horn declarations in
  `CategoryWithFibrations.lean`; they are not the one-sided theorem here.
* Loogle: `"ihom", "HasLiftingProperty"` returned no hits. `"pullbackHom"` returned
  twelve unrelated sheaf/topological/scheme declarations, not the canonical arrow
  construction; this was not accepted as evidence of its absence.
* Wrapped grep: `pullbackHom|pullback.*ihom|ihom.*pullback|right[Ff]ibration|right_anodyne`
  under `AlgebraicTopology` returned no hits. I expanded the direct `rg` search to
  Mathlib's `CategoryTheory/Monoidal`, the upstream `WeilConjectures` tree and the
  project's `lean/Sheaf`. This found the generic canonical map in Mathlib, plus the
  already landed project right-anodyne definition, but no exact exponentiation theorem.
* The follow-up wrapped grep `pullbackHom|leibnizPullback` under
  `CategoryTheory/Monoidal` returned six hits, including
  `Mathlib/CategoryTheory/Monoidal/PushoutProduct.lean:90`. I opened that declaration
  and its implementation in `Limits/Shapes/Pullback/PullbackObjObj.lean`. Its real
  construction is precisely the helper's notion, with the two pullback factors reversed.
* A direct search for both proposed full declaration names in upstream and project
  Lean found no collision or existing exponentiation theorem. The only exact notion
  reuse needed beyond Mathlib is the already recorded `rightAnodyneExtensions` node.

**Mismatch and repair:** H4 applied to the author's helper
`SSet.rightFibrationExponentiationMap`: the same canonical pullback-hom construction
already exists in Mathlib. I removed that helper, imported
`Mathlib.CategoryTheory.Monoidal.PushoutProduct`, and wrote the theorem directly using
`MonoidalCategory.Arrow.pullbackHom` followed by the existing `pullbackSymmetry`, retaining
the exact displayed target order. The theorem's mathematical statement is unchanged.
I updated `lean.declarations`, `lean.statement`, and `lean.note` accordingly, and documented
the map expression in its docstring. The worker report above is retained as requested;
its references to the removed helper describe the pre-review version and are superseded
by this section. I found no other statement mismatch.

H5/H6/H8/H9: the final file has no new definition or auxiliary theorem. Its sole theorem,
`SSet.rightFibration_exponentiation`, has proof `sorry`. Both canonical maps used in its
statement are real Mathlib constructions. The module and theorem docstrings cite the
source and the exact blueprint id. The proof docstring retains all four node steps:
transpose the lifting square and glue by the pushout, use the right-anodyne Cartesian
pushout-product, use the two lifting-class closure dependencies and minimality, and
specialize to every boundary including dimension zero. I opened those proof dependency
records and their recorded Mathlib declarations. The right-anodyne-product node has no
Lean record, so it has no available module to import; all stated proof dependencies have
the required imports. There are no new nodes or dependency modules to audit under H12/H13,
no `statement_change`, no local notation/instances, no unbound variables, and all lines
are at most 100 characters. The recorded signature was checked verbatim against the file.

Validation: after the repair, the only delivered module compiled cleanly through the
prescribed `scompile.py` wrapper, both in its sandbox check and as the library module
(37.0 s and 37.7 s respectively, within the unchanged 60 s limit). The pre-review version
also compiled cleanly, so the repair addresses the duplicate notion rather than a type
error. The required delivery dry run and final delivery follow this reading.

## Second reading by N0

I reread the node record, Kerodon source tag 0154, every recorded statement dependency,
and the current Lean file. The source says: for maps `q : E ⟶ S` and `i : A ⟶ B` of
simplicial sets, if `q` is a right fibration and `i` is right anodyne, the induced
map from `Fun(B,E)` to the pullback of `Fun(B,S)` and `Fun(A,E)` over `Fun(A,S)` is a
trivial Kan fibration. The right-handed assertion is explicitly the second clause of
Proposition the project server; no quasicategory hypotheses occur.

Object and hypothesis checklist:

1. The Lean binders `{A B E S : SSet.{u}}` introduce exactly the four arbitrary
   small simplicial sets from the node, in one common but unrestricted universe.
   `(q : E ⟶ S)` is the source-to-base map. No fibrancy, nonemptiness, finiteness,
   characteristic, or quasicategory instance is added.
2. The hypothesis `hq` quantifies over every `m : ℕ` and `j : Fin (m + 1)`, with
   `1 ≤ m`, `0 < j`, and `HasLiftingProperty (horn m j).ι q`. Since `Fin` supplies
   `j ≤ m`, this is exactly all right horns `0 < j ≤ m` in dimensions `m ≥ 1`.
   The zero-dimensional horn is correctly absent.
3. The hypothesis `hi : rightAnodyneExtensions i` is the recorded
   `SSet.rightAnodyneExtensions` definition from
   `Sheaf.CategoryTheory.RightAnodyne`. I read that definition: it is the infimum
   of properties containing isomorphisms and positive-index horns and closed under
   pushouts, transfinite compositions, and retracts. Thus the Lean uses the same
   right-anodyne notion as the node and does not add a separate monomorphism or
   generation assumption.
4. The conclusion has the exact canonical relative internal-hom map. Its source is
   `(ihom B).obj E`, while the displayed composite is Mathlib's
   `MonoidalCategory.Arrow.pullbackHom` for `i` and `q`, followed by
   `pullbackSymmetry ((ihom A).map q) ((MonoidalClosed.pre i).app S)`. The symmetry
   puts the factors in the node's order `Fun(B,S) ×_{Fun(A,S)} Fun(A,E)`; the two
   components are postcomposition by `q` and restriction along `i`. The conclusion
   `modelCategoryQuillen.I.rlp` is the recorded Mathlib encoding of a trivial Kan
   fibration, with `I` containing every boundary inclusion.
5. Quantifier order is preserved: four sets, `q`, `i`, the right-horn hypothesis,
   the right-anodyne hypothesis, then the lifting conclusion. The theorem has no
   unbound variables under `autoImplicit false`.

Edge cases are covered. Right horns with `m = 1, j = 1` and `j = m` are included;
`j = 0` is excluded. The boundary family includes `n = 0`, whose empty boundary
ensures vertex surjectivity. Empty simplicial sets and identity/isomorphism maps,
including the empty identity, remain admissible. There are no zero-object,
characteristic, or scheme assumptions, and no universe restriction beyond the
arbitrary `SSet.{u}` universe used by the category.

For H4 I searched Mathlib's simplicial-set, monoidal, and pushout-product files,
the upstream `WeilConjectures` tree, and the project `lean/Sheaf` tree for
right-fibration, right-anodyne, exponentiation, `pullbackHom`, and
`pullbackSymmetry` declarations. The exact exponentiation theorem is absent. The
right-anodyne notion is already supplied by the landed dependency module, and the
canonical relative map is already Mathlib's `Arrow.pullbackHom`; no private helper
is permitted.

The mismatch found in the previous worker version was the duplicate helper
`SSet.rightFibrationExponentiationMap`, which repeated Mathlib's canonical
`pullbackHom` construction. I verified the current file has removed that helper,
imports `Mathlib.CategoryTheory.Monoidal.PushoutProduct`, and states the theorem
using the existing canonical map and `pullbackSymmetry`. The node's Lean signature
is verbatim equal to the theorem signature. No statement correction, dependency
repair, new node, or disputed assertion is needed. The theorem remains postponed
with the required `sorry` proof and carries the Kerodon source and blueprint proof
steps in its docstring.

The current module compiles cleanly through the required `scompile.py` wrapper for
both the sandbox and library checks.
