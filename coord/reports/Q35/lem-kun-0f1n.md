## Worker report

Recorded `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap` from
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` as `existing: true`,
branch `slopmaster2`. No Lean module is delivered. The published theorem's docstring
explicitly identifies it as blueprint `lem-kun-0f1n`. I read its complete signature,
section parameters, docstring, and the definition of `tensorBaseChangeMap` using
`scompile.py --source`; the older local checkout lacks this module.

The previous run confused Q87's accepted stage-1 split with a completed stage-2
statement. The current node has `reviewed` by Q87 but no `lean` or `reviewed_lean`.
This delivery preserves that split and changes only `lean`.

Hypothesis and conclusion correspondence:

- The field is `{K : Type u} [Field K]`; the base is `Spec (.of K)`.
- For the node's integer `n ≥ 1`, specialize the section parameter
  `(Λ : Type (u + 1)) [CommRing Λ]` to `ULift.{u + 1} (ZMod n)`.
  The lift preserves the ring and its module theory and implements the recorded
  coefficient-size convention, without bounding the complexes. Positivity gives
  `NeZero n`, hence `[Finite Λ]`. Invertibility of `n` in `K` gives
  `[HasInvertibleExponent Λ (Spec (.of K))]`: use exponent `n`, its zero image in
  `ZMod n`, and `IsUnit (n : K)` transported by `(Scheme.ΓSpecIso (.of K)).inv.hom`.
  These generic coefficient hypotheses therefore add no assumption to the node.
  Conversely, for this coefficient ring any positive annihilating exponent is a
  multiple of `n`, so its invertibility implies that of `n`.
- The schemes `X X' S' T Y : Scheme.{u}` are exactly the five schemes in the diagram.
  The structure arrows are `a`, `b`, `t`; finite type is
  `[LocallyOfFiniteType a] [QuasiCompact a]` and the corresponding pairs for `b,t`.
  The omitted explicit finite-type hypotheses for `X'` and `Y` are consequences:
  the first square makes `f'` a base change of `a`, and the second makes `e` a base
  change of `f'`; compose with `b` and `t`. Conversely the source's diagram of
  finite-type K-schemes supplies these three pairs. No separatedness is imposed.
- The five arrows `p,f',h,e,g` have exactly the displayed sources and targets.
  `_hg : g ≫ b = t` expresses that `g` is a K-morphism.
  `_sq₁ : IsPullback p f' a b` identifies `X'` with `X ×_{Spec K} S'`.
  `sq₂ : IsPullback h e f' g` identifies `Y` with `X' ×_{S'} T`.
  Their `.w` equations supply the two commutativities. The upper schemes inherit
  their K-structures along these squares; no additional compatibility is needed.
- `E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
  and the analogous `F` on `T` are exactly the unrestricted, unbounded objects
  of `D(X_et, Λ)` and `D(T_et, Λ)`. There are no constructibility, Tor-amplitude,
  boundedness, or flatness hypotheses.
- The conclusion is `IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ)
  h e f' g sq₂.w ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F)`.
  Its source is `p⁻¹E ⊗ᴸ f'⁻¹ Rg_*F` and its target is
  `Rh_*(h⁻¹p⁻¹E ⊗ᴸ e⁻¹F)`, as seen by unfolding the map's signature.
  The map is the actual h-adjoint of the monoidal inverse-image comparison,
  the inverse-image composition comparison for `h ≫ f' = e ≫ g`, and
  `1 ⊗ e⁻¹ ε_g`; it is not a chosen isomorphism between these objects.

Dependency declarations read and used:

- `def-kun-unbounded-exchange`: `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`,
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso` and
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`. Its square is descended
  termwise, and its exchange is the canonical derived-adjunction mate.
  The existing theorem expresses the same exact inverse image through `L(u^*)`;
  `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` is its canonical
  identification with `D(u^*)`. The module also defines the canonical adjunction
  `derivedUpperStarLowerStarAdjunction`. Thus the theorem uses the recorded
  notion under its canonical comparison, without a duplicate definition.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`. This is exactly the derived tensor
  used in `tensorBaseChangeMap`, on the full unbounded category.
- `def-weil-pbc-derived-categories`: the mixed record in
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` expressly uses
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. Its abbreviation is
  precisely the expanded category in the theorem. The torsion-cohomology
  predicate and the bounded subcategories in that record are not assumptions
  of this node and do not occur here.
- `def-weil-pbc-scheme-conventions` fixes no declaration of its own. Its named
  Mathlib notions `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, and fibre
  products are used directly. I read the class signatures/docstrings in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

Source checked: Stacks, `etale-cohomology.tex`,
`lemma-punctual-base-change-upgrade-unbounded` (Tag 0F1N), and the node's current
`blueprint_update` for main-20261015. Its statement agrees exactly. The correction
in that blueprint update concerns the proof's placement of the flat replacement
on E, not the statement. The existing theorem is still a `sorry` statement; no
claim of a completed proof is made.

Edge cases checked: `n = 1` gives the zero coefficient ring and is retained;
`n = 0` is excluded by the node's own positivity requirement. Composite `n` is
allowed, with no field assumption on the coefficients. Zero complexes and empty
schemes are allowed by the binders; no nonempty scheme assumption occurs.
Unbounded E and F and non-separated finite-type schemes remain allowed. Arbitrary
cartesian models are covered by `IsPullback`, not just chosen fibre products.
The universe lift covers the prescribed coefficient category for every `u`.

Searches made (all under Q35 / lem-kun-0f1n):

- `msearch.py leanfinder`, query: “For finite type schemes over a field, derived
  etale pushforward base change tensored with any unbounded Z/n complex is an
  isomorphism”. Eight hits, concerning algebraic étaleness and its stability
  under base change; none is this cohomological comparison.
- `msearch.py leansearch`, query: “Etale derived tensor base change with unbounded
  complexes over a field”. Eight hits, algebraic étaleness, Kähler differentials
  and cotangent base change; no exact hit.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Etale.derivedTensor, AlgebraicGeometry.Etale.derivedBaseChangeMap`.
  No hits; the remote index does not know `derivedTensor`.
- `msearch.py grep`, query: `kunneth|punctual.base.change|isIso.*[Tt]ensor`,
  subdirectory `AlgebraicGeometry`: no Mathlib hit.
- `rg` over upstream `WeilConjectures/SixFunctors` for `lem-kun-0f1n`, `0F1N`,
  `punctual`, and Kunneth vocabulary found related Kunneth modules. The local
  `Relative` theorem requires constructible finite Tor amplitude and separated
  schemes, so it is not a match. `rg` over `lean/Sheaf` found related comparisons
  but no declaration for this node. The upstream name inventory has no hit for
  `isIso_tensorBaseChangeMap`; it predates the published source.
- Following `Sheaf.AlgebraicGeometry.KunnethGlobalSections`'s import of
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`, I used the
  prescribed `scompile.py --source` lookup. The current published source contains
  `tensorBaseChangeMap` and the exact tagged theorem `isIso_tensorBaseChangeMap`.
  This exact match is used; no replacement declaration is written.

Validation: a scratch-only specialization probe, compiled through `scompile.py`,
checks the complete existing declaration and applies it at
`ULift.{u + 1} (ZMod n)` with only the node's positivity, invertibility, geometry,
and unbounded-complex hypotheses. It is not a delivered module. The required
`deliver2.py --no-push` also compiles its own existing-declaration check.
No statement correction, new node, dependency repair, or mathematical dispute.

## Second reading by Q35

I independently read the sandbox node, its complete eight-step proof, Stacks
`etale-cohomology.tex`, label
`lemma-punctual-base-change-upgrade-unbounded` (Tag 0F1N, starting at line 20879),
and the preceding bounded lemma's description of the canonical map. The source
introduces all its hypotheses in this lemma; no separatedness, algebraic closure,
or boundedness convention is inherited. I fetched the current `Ordinary` module
with `scompile.py --source` and read the theorem, section variables, and the actual
body and type of `tensorBaseChangeMap`. I also opened the four dependency nodes
and their declaration sources. No repair note exists for this item.

Here is my object/hypothesis/conclusion checklist, in source order. In this list
`Λₙ` means the explanatory specialization `ULift.{u + 1} (ZMod n)`, not a new
Lean definition.

1. Field K: `{K : Type u} [Field K]`; base `Spec (.of K)`. Exact, including
   positive characteristic; K is not assumed separably closed or algebraically
   closed.
2. Positive integer n and invertibility in K: specialize the existing theorem's
   `(Λ : Type (u + 1)) [CommRing Λ]` to Λₙ. `hn : 0 < n` gives `NeZero n` and
   hence `Finite Λₙ`; `IsUnit (n : K)` gives `HasInvertibleExponent Λₙ (Spec K)`
   by the exponent witness n, `ZMod.natCast_self`, and
   `IsUnit.map (Scheme.ΓSpecIso (.of K)).inv.hom`. I read the class: its only
   field is a positive annihilating integer which is a unit in global sections.
   Thus these instances impose nothing beyond the node for this specialization.
   `ULift.ringEquiv` identifies the coefficient ring with Z/n. The existing
   declaration is more general in coefficients; the record explicitly binds
   its Z/n specialization, rather than asserting that arbitrary finite rings
   are literally Z/n. This is an existing generic interface, not a new stronger
   statement being delivered.
3. The five schemes X, X', S', T, Y: `{X X' S' T Y : Scheme.{u}}`. Exact.
   Structure arrows are `a`, `b`, `t`, and the induced arrows `f' ≫ b` and
   `e ≫ t`. Both upper schemes are arbitrary cartesian models, not fixed
   chosen pullback objects.
4. Every scheme finite type over K: the pairs `[LocallyOfFiniteType a]`
   `[QuasiCompact a]`, and similarly for b and t, are exactly finite type as
   fixed by `def-weil-pbc-scheme-conventions`. I read both Mathlib class
   signatures. `f'` is a base change of a via sq₁, and e a base change of f'
   via sq₂, so X' and Y are finite type by base change and composition. No
   additional finiteness, properness, smoothness or separatedness is present.
5. The diagram's five horizontal/vertical arrows: `p : X' ⟶ X`,
   `f' : X' ⟶ S'`, `h : Y ⟶ X'`, `e : Y ⟶ T`, `g : T ⟶ S'`, with
   `_hg : g ≫ b = t`. These are the arrows of the node with the same directions.
   `_sq₁ : IsPullback p f' a b` and `sq₂ : IsPullback h e f' g` supply both
   commutativity equations and the two fibre-product properties. Exact.
6. Arbitrary E in D(X_et,Z/n) and F in D(T_et,Z/n): the two binders use
   `DerivedCategory (Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   I checked `DerivedCategoryModule` in `Derived.Coefficients`: this is its
   defining abbreviation, as required by `def-weil-pbc-derived-categories`.
   No Plus/Bounded subcategory, torsion predicate, constructibility, flatness,
   or Tor-amplitude assumption occurs. The quantifier order allows every pair
   E,F independently after the geometry and coefficients are fixed. Exact.
7. The source of the comparison is p⁻¹E tensorᴸ f'⁻¹Rg_*F: expanding the
   `tensorBaseChangeMap` type gives `derivedTensor` on X' at
   `((L((p)^*[ModuleCat Λ])).obj E)` and `L(f'^*) (R(g_*) F)`.
   I opened `Derived.Tensor`: `derivedTensor` is the curried tensor on the
   unbounded K-flat-derived monoidal category, the recorded
   `def-kun-derived-tensor`, not an underived tensor or a bounded replacement.
8. The target is Rh_*(h⁻¹p⁻¹E tensorᴸ e⁻¹F): the map's target is literally
   `R(h_*)` of `derivedTensor` on Y at `L(h^*) (L(p^*) E)` and `L(e^*) F`.
   I checked `leftDerivedUpperStarIsoMapDerivedCategory` and
   `leftDerivedUpperStarComp`: these use the exact termwise inverse image and
   its descended composition comparison. They identify the L notation with
   the inverse image of `def-kun-unbounded-exchange` without changing objects.
9. It is the canonical map and it is an isomorphism: the conclusion is
   `IsIso (tensorBaseChangeMap ... sq₂.w (L(p^*) E) F)`. I read its construction:
   `derivedUpperStarLowerStarAdjunction.homEquiv` takes the h-adjoint of the
   monoidal pullback comparison, the two inverse-image composition comparisons,
   and e-pullback of the g-counit. These are precisely the map in the node's
   Step 3. It is neither a freely chosen arrow nor a mere existence of an iso.
   The exact-exchange dependency uses the same canonical descended square and
   adjunction mate through the canonical L-to-D comparison. Exact.

Edge cases: n=1 is included (the zero ring), n=0 is excluded only by the source's
own n≥1 condition, and composite n is included. In characteristic p only the
source's requirement that n be a unit excludes p-divisible n. Empty X, S', T,
and the resulting empty cartesian objects remain allowed; there is no Nonempty
hypothesis. Zero complexes and complexes unbounded in either direction are
allowed. Non-separated finite-type schemes are included. There is no index set
in this statement; in particular no nonempty-index condition is introduced.
The explicit universe u is arbitrary, the category uses the recorded u+1
coefficient-size convention, and the canonical lift permits the small ring Z/n
at every u. Different originally sized schemes can be placed in a common
universe; no site object/morphism universe equality is imposed. I checked the
complete section variables: Λ, its CommRing instance, and u are bound.

Independent H4 searches used different wording from the worker:

- LeanFinder: `Projection formula for tensoring a pullback with an unbounded
  derived direct image of torsion etale sheaves over a field`. Eight hits, all
  ordinary scheme pullback residue-field tensor declarations; no match.
- Loogle: `"tensorBaseChangeMap"`. Zero hits.
- LeanSearch: `Unbounded etale derived projection map after product base change
  over a field with finite torsion coefficients`. Eight hits on ordinary
  algebraic etaleness and tensor base change; no matching cohomological result.
- Direct rg of Mathlib sites, upstream SixFunctors, and project `lean/Sheaf`
  using `tensorBaseChange`, `pushforward tensored`,
  `punctual-base-change-upgrade-unbounded`, and projection-formula vocabulary.
  Related compact-support or bounded/constructible projection formulas do not
  give this statement. The current published `Ordinary` theorem does, by the
  specialization above; I verified it through the required source wrapper.

No mathematical mismatch was found, and I preserved the existing binding,
statement, dependencies, and worker report. Only `lean` differs from the base
node, and I mechanically compared `lean.statement` to the source signature:
verbatim equality holds. There are no new nodes, dependency modules, delivered
Lean files, statement corrections, or citer audits to perform. The published
statement still has `sorry`; this is a stage-2 attachment, not a completed proof.
Its published docstring identifies the exact blueprint; the eight-step proof
remains fully documented in the unchanged DAG node. No definition is added,
no hollow data is introduced, and nothing is proved in this delivery.

The worker's scratch specialization is independently recompiled through
`scompile.py`; the wrapper's existing-declaration check is also required by
`deliver2.py --no-push` below. Scratch files are not part of this delivery.

Validation correction during the second reading: the worker's original scratch
probe omitted rewriting natural casts after `IsUnit.map`. The smaller independent
`CoefficientCheck.lean` exposed this type mismatch. I repaired the scratch proof
with `simpa only [map_natCast] using hu.map ...`; the coefficient probe now compiles
cleanly in both sandbox and library modes (4.9 s and 4.8 s). This is an
elaboration correction in the validation experiment, not a missing mathematical
hypothesis or a change to the existing declaration. The original complete probe
timed out at 60 s before exposing that error; its corrected version is rechecked
separately. No scratch file is delivered.

Final independent interface check: `SpecializedInterface.lean` checks the
coefficient witness and then elaborates
`isIso_tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) (K := K)` under `NeZero n`
and the coefficient exponent instance. It compiles cleanly in both modes
(5.1 s each). The resulting signature quantifies over all the original geometry
and arbitrary E,F and contains no residual coefficient instance requirement.
Together with the compiled witness this verifies the claimed specialization
without repeating the large target type of the original full probe. The dry
run passed preflight and the existing-declaration compile, printing OK for
commit `5c18dac394` (nothing pushed). The delivery will rerun these checks with
this final report.
The corrected original full probe also timed out locally and on the server at
60 s; it is not counted as a successful validation. The two smaller checks
above and the delivery's existing-declaration check are the successful checks.
