## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus` states
`AlgebraicGeometry.Scheme.exists_perfectLowestCohomologyLocus`, with its proof `sorry`.
It realizes the specified part of Stacks Project, Derived Categories of Schemes,
Lemma 36.31.4, [Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL), read in full online
because `literature/stacks-project/perfect.tex` is absent on this machine.
No statement correction, disputed statement, dependency replacement, or new definition
is needed. The optional additional conclusions of the full Stacks lemma (the closed
immersion under the fibre-rank bound and its rank-one criterion) are outside this node.

Hypotheses and clauses, individually:

- The scheme `S` is the binder `(S : Scheme.{u})`, using Mathlib's actual scheme and
  morphism category. No separation, compactness, or Noetherian condition is imposed.
- The object of the derived category is `(E : schemeDerivedCategory S)`, the shared
  `SheafOfModules (moduleRings S.toRingedSpace)` carrier, not a derived category with
  an independently chosen abelian instance.
- Perfection is `(hE : IsPerfect S E)`, exactly the recorded open-local strictly
  perfect complex definition.
- The two integer endpoints are `(a b : ℤ)`. Tor amplitude in `[a,b]` is the binder
  `hamp`: for every O_S-module `F` and every integer `i` with `i < a ∨ b < i`,
  `schemeDerivedTensorCohomologyVanishes S E F i`. This is the existing K-flat
  derived-tensor vanishing predicate, against all modules, not only quasi-coherent
  ones. The statement adds no `a ≤ b` premise.
- The nonnegative integer rank is `(r : ℕ)`, covering zero and every finite rank.
- Existence of the subscheme morphism is `∃ (Z : Scheme.{u}) (j : Z ⟶ S)`.
  `IsImmersion j` is Mathlib's scheme immersion, including locally closed range and
  stalk surjectivity, rather than just a topological embedding.
- Finite presentation is `LocallyOfFinitePresentation j ∧ QuasiCompact j`.
  Mathlib's FinitePresentation module explicitly uses these two predicates together
  for finite presentation. Immersions are separated, so there is no missing
  quasi-separatedness condition.
- For every morphism `h : T ⟶ S`, factorization is exactly
  `(∃ g : T ⟶ Z, g ≫ j = h)`.
- The equivalent universal test quantifies over every `T' : Scheme.{u}` and
  `u' : T' ⟶ T`, and requires `IsFiniteLocallyFreeOfRank.{u,u,u} ... r` of
  `H^a((derivedPullback (u' ≫ h)).obj E)`. Category-theoretic composition is in the
  order `u' ≫ h`, i.e. the source's `h ∘ u`. The degree is `a`, not literal zero.
- The next conjunct states finite local freeness of rank `r` of
  `H^a((derivedPullback j).obj E)` on `Z` itself.
- The final conjunct, for every `g : T ⟶ Z`, renders the source's identification
  `g^*H^a(Lj^*E) = H^a(L(g ≫ j)^*E)` as an isomorphism of O_T-modules, using the
  existing `Modules.tensorPullback g` on the left and the existing derived pullback
  along `g ≫ j` on the right. `Nonempty ( ... ≅ ... )` is the Prop-valued expression
  of this identification; no equality of implementation-specific chosen objects is
  asserted. The proof docstring records its construction from the same local model.

The `∀ T, HasDerivedCategory` binder supplies the localizations needed to type all
scheme pullbacks; it restricts no geometric case. The open-local derived-category
binder on `S` is required by the existing `IsPerfect` declaration. Every scheme and
module carrier uses the same universe `u`, with localization morphisms in `w`.
In particular the universal tests do not live in an independent smaller universe.
All universes and variables are explicit, with `autoImplicit false`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  imported through PerfectComplex and DerivedPullback.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, including its local-generator definition
  and the explicit universe parameters (necessary for general scheme universes).
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  imported by DerivedPullback; it is the tensor pullback required by the contract.
- `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`:
  `AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes`.

The last three existing landed definition nodes were added to `stmt_deps` so the
explicit derived pullback, underived pullback, and Tor-vanishing notions have DAG edges.
No copied or privately redefined notion is introduced.

Edge cases checked: `r = 0` means vanishing and includes the empty locus when
appropriate; on the empty scheme all ranks are vacuous and every map from an empty
scheme factors. The zero perfect complex has the whole locus at rank zero and empty
locus at positive rank. Negative `a`, `a = b`, and a reversed interval remain typable;
in the latter case the Tor test forces the zero complex, so no extraneous endpoint
hypothesis is needed. All maps (including nonflat and nilpotent base changes) occur
in the universal test. There is no characteristic restriction or finite-base
hypothesis. `h = j`, `u' = id`, and `g = id` recover the expected on-locus cases.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “perfect complex lowest cohomology locally free rank locally
  closed locus universal base change”. Eight hits: free loci, rank at stalk, and
  `DerivedCategory.isGE_Q_obj_iff`; none is the derived universal rank-locus theorem.
- `msearch.py loogle`: `DerivedCategory.homologyFunctor, Immersion`. Zero hits;
  `Immersion` is unknown (the actual Mathlib predicate is `IsImmersion`).
- `msearch.py grep`: `torAmplitude|TorAmplitude|locally.closed.*cohomology` in
  `AlgebraicGeometry`. Zero hits.
- `msearch.py leansearch`: same natural-language query. Service unavailable,
  `Internal Server Error`; the failure is recorded in `searches.jsonl`.
- `rg` of `WeilConjectures/AlgebraicGeometry`, `lean/Sheaf/AlgebraicGeometry` and DAG:
  Tor-amplitude and pullback/cohomology searches locate the existing derived pullback
  and tensor vanishing declarations, but no exact locus statement. Source
  DirectImage has finite-free model base-change results for proper pushforwards,
  which have different hypotheses and do not state this arbitrary-perfect-complex
  theorem. Search for the item id in `WeilConjectures` finds no declaration.
- Declaration-name search for `exists_perfectLowestCohomologyLocus` in the Mathlib
  source, upstream-name index, source repository and project finds no collision.

Server compilation: the first pass identified a universe inference problem in the
rank predicate; explicit `.{u,u,u}` was added. The subsequent server check is recorded
below after completion. No proof other than `sorry` is supplied.

Final single-file server compile: exit code 0, 3.4 seconds, no errors or warnings.

## Second reading by E1

I reread the node statement against Stacks Project Tag 0BDL and matched every introduced
object, hypothesis, and conclusion to the Lean declaration.

- `S` is `(S : Scheme.{u})`, and `E` is `(E : schemeDerivedCategory S)` with
  `(hE : IsPerfect S E)`; these are the scheme and perfect derived object in the node.
- The Tor-amplitude interval is represented by `(a b : ℤ)` and `hamp`, which quantifies
  every `S`-module `F` and every `i : ℤ` satisfying `i < a ∨ b < i`, exactly the
  outside-`[a,b]` vanishing condition. No endpoint ordering or other hypothesis is added.
- The rank is `(r : ℕ)`, equivalent to the source's `r ≥ 0`.
- The witness is `∃ (Z : Scheme.{u}) (j : Z ⟶ S)` with `IsImmersion j` and
  `LocallyOfFinitePresentation j ∧ QuasiCompact j`, rendering a finite-presentation
  locally closed immersion.
- For each `(T : Scheme.{u})` and `h : T ⟶ S`, the factorization condition is
  `(∃ g : T ⟶ Z, g ≫ j = h)`. Its equivalent universal condition quantifies every
  `(T' : Scheme.{u})` and `u' : T' ⟶ T`, and states finite local freeness of rank `r`
  for degree-`a` cohomology of `derivedPullback (u' ≫ h)`, preserving the source's
  composition order and its quantifier order.
- The on-locus clause states the same finite local freeness for degree `a` of
  `derivedPullback j` on `Z`.
- Pullback compatibility is the final `∀ T g`, with an isomorphism between
  `Modules.tensorPullback g` of the degree-`a` cohomology on `Z` and degree-`a`
  cohomology after `derivedPullback (g ≫ j)`. `Nonempty` expresses existence of the
  source's canonical module isomorphism without asserting equality of chosen carriers.

Edge cases checked: `r = 0`, positive rank, zero perfect complex, empty schemes, negative
or equal endpoints, and reversed endpoints are all typable; no characteristic, finiteness,
or separation hypothesis is introduced. The universal test uses the same universe `u` for
schemes and modules, so it does not omit base changes in another universe. Identity maps
recover the on-locus clauses, and arbitrary nonflat or nilpotent base changes remain covered.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and the declaration-name index with
LeanFinder/Loogle/grep-style searches and the natural-language LeanSearch query recorded in
the worker report. No existing declaration states this theorem; the only search failure was
LeanSearch's service error. The dependency declarations were opened and match the notions
used (`IsPerfect`, `schemeDerivedCategory`, `derivedPullback`, `tensorPullback`,
`schemeDerivedTensorCohomologyVanishes`, and `IsFiniteLocallyFreeOfRank`).

No mismatch was found, so no source, node, dependency, or Lean statement was changed. The
single-file server compilation completed successfully with only the permitted `sorry`.
