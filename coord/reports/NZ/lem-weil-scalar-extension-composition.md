## Worker report

The module `lean/Sheaf/Paper/SfScalarExtensionComposition.lean` states composition,
identity normalization and coherence for the current intrinsic rational coefficient
categories. The item's mathematical statement is unchanged. All six theorem proofs
are `sorry`; the five definitions select objects determined uniquely by their named
characterization theorems. No definition chooses an arbitrary isomorphism.

Source read: the complete item and its proof in
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/lem-weil-scalar-extension-composition.md`,
and the current statement and separate proof in
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-scalar-extension-composition.md`
and `.proof.md`, order 1828. The statements agree. The source proof explicitly includes
the unit and pentagon equations. Also read the item's full DAG proof, its maintenance
invalidation, the sole statement dependency's full statement and active Lean record,
and the declaration signatures and docstrings in `SfRationalizationKaroubi.lean`.
There is no separate `coord/repair-notes/lem-weil-scalar-extension-composition.json`.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The dependency's scalar transitions take
  `(p : ℕ) (hl : l ≠ p)`, retaining the source's coefficient-prime convention.
  Neither p nor hl imposes any property or structure morphism on Y. The API works for
  any such p, including the characteristic of an independently fixed global datum.
- Finite extensions E, L, M of Q_l are the binders `(E L M : Type u)`, with separate
  `Field`, `Algebra (Padic l)` and `FiniteDimensional (Padic l)` instances for each.
  The inclusions E into L and L into M are `ι : E →ₐ[Padic l] L` and
  `j : L →ₐ[Padic l] M`. Field algebra homomorphisms are injective, so no extra
  injectivity hypothesis is required. Their direct inclusion is `j.comp ι`.
- An arbitrary scheme is `(Y : AlgebraicGeometry.Scheme.{u})`, with no Noetherian,
  finite-dimensional, finite-type, or finite-field-base hypothesis. The shared size
  convention is exactly the recorded rationalization dependency's convention; the
  pro-etale site's distinct object and morphism universes are not equated.
- The category D^b_c(Y,E) is exactly `sfRationalConstructibleCategory l E Y` from the
  active dependency. Its objects remain integral representatives; no Karoubi objects
  or discrete E-sheaf derived category is substituted.
- The source `(K tensor_E L) tensor_L M` is the object of
  `sfRationalScalarExtension l E Y p hl L ι ⋙
   sfRationalScalarExtension l L Y p hl M j`. The target is the object of
  `sfRationalScalarExtension l E Y p hl M (j.comp ι)`.
  `sfRationalScalarComp` is a natural isomorphism between precisely those functors.
  Hence its component at every K is the displayed isomorphism in D^b_c(Y,M), and
  naturality is part of its type, including rational morphisms rather than just
  integral chain maps.
- Canonicity is expressed by `sfRationalScalarComp_existsUnique`: every component is
  the localization of `sfIntegralScalarComp` on `K.obj`. Its `HEq` only accommodates
  the published functors' propositionally specified object maps; it is equality of
  these actual morphisms, not merely an isomorphism of endpoints.
- The integral comparison is itself uniquely specified. Its ambient morphism is
  ordinary tensor associativity conjugated by `sfIntegralOrdinaryComparison` at the
  three stages. The latter's theorem fixes its value on every good representative
  using `integralScalarCompletionChain` and the resolving comparison. That chain
  map has every quotient tensor coordinate prescribed and shifted coordinate zero.
  The ordinary associator is the existing sectionwise balanced map sending
  c tensor (b tensor x) to c*j(b) tensor x. Thus no unnormalized natural isomorphism
  or arbitrary cone lift is introduced.
- Compatibility with identity extension is `sfRationalScalarUnit`, localized from
  the completed integral unit; that unit is the inverse completion comparison
  followed by the existing ordinary multiplication unit s tensor x to s*x.
  The first conjunct of `sfRationalScalar_coherence` is the source-unit equation;
  the second is the target-unit equation. Both include the actual identity algebra
  embedding, and neither drops the coincident-field case.
- Compatibility with further composition is the third conjunct of
  `sfRationalScalar_coherence`, quantified over a fourth finite extension N and its
  inclusion k. It equates the two paths from three successive extensions to the
  direct extension. This is the source proof's pentagon/coefficient-pseudofunctor
  equation, not an additional assumption supplied by the caller.

Proof plan correspondence: the ordinary-to-completed comparison and intrinsic integral
associator implement DAG steps 1 and 2 (finite-free comparison, K-flat resolutions,
balanced chain maps and descent through roofs). The rational associator's theorem
implements step 3 by linear naturality on all tensor generators. The integral and
rational unit theorems and coherence theorem implement step 4 by multiplication on
pure tensors followed by cancellation of the normalized completion comparisons.
Each postponed theorem carries the relevant complete natural-language argument.

Dependency declarations and reusable interfaces:

- `Sheaf.Paper.SfRationalizationKaroubi` (sole statement dependency
  `def-weil-rationalization-karoubi`): `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, and `sfRationalScalarExtension` with its
  uniquely prescribed objects and tensor-Hom maps. This was confirmed against the
  current source using `scompile.py --source Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible` and `sfIntegralConstructibleCategory`, the active
  intrinsic completeness and uniformly bounded constructible-reduction predicate.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`:
  `sfConstructibleIntegralScalarExtension`, the full-subcategory restriction of the
  actual completed scalar extension, with intrinsic preservation.
- `Sheaf.Paper.IntegralScalarExtension`:
  `integralScalarExtension`, `integralScalarExtensionComparison`,
  `integralOrdinaryScalar` and `integralOrdinaryDerivedScalar`.
- `Sheaf.Paper.ScalarExtensionComposition`: reuse only the normalized ordinary
  `integralOrdinaryDerivedScalarComp` and `integralOrdinaryDerivedScalarUnit`.
  Their underlying `integralOrdinaryScalarComp_existsUnique` and
  `integralOrdinaryScalarUnit_existsUnique` specify all tensor generators. The
  old completed/rational comparisons in that module are not used for intrinsic
  stages. This import preserves existing callers and avoids a second ordinary
  tensor construction.
- `Sheaf.Paper.IntegralScalarExtensionConstructible`:
  `integralScalarCompletionChain`, whose theorem specifies the quotient cone map.
  Its chain construction does not use the old constructibility predicate; the
  new comparison restricts it to the recorded intrinsic predicate.
- The stated proof-dependency modules are imported: `FiniteFreeCompletedScalarComparison`,
  `KFlatResolutionIndependentCoefficients`, `DerivedChangeOfRingsIndependentCoefficients`,
  `PbcActualScalarPullback` (reexporting the generic ringed-topos comparison), and
  `TensorProductOfUniverses`. Intrinsic integral constructibility and its preservation
  also have direct public imports because their declarations occur in signatures.

Edge cases checked against the statement and formulas: identity first inclusion,
identity second inclusion, E=L=M, and three successive inclusions (pentagon). The
coherence theorem explicitly typechecks these endpoints. Equal fields with arbitrary
algebra embeddings are permitted, not replaced by equality cases. The zero complex
and empty scheme need no nonzero or nonempty hypothesis. Ramified finite extensions
are included: no unramifiedness or chosen integral basis enters the signature.
The proof uses the finite-free comparison and cofinal uniformizer powers, not a
false flatness assertion for matching finite quotients. There is no geometric
hypothesis on Y or relation between Y and any finite field. No statement dispute or
statement correction was needed.

Searches actually run (all msearch queries use group NZ and this item):

- `leanfinder`: “Composition of scalar extension functors on rationalized constructible
  l-adic derived categories with unit and pentagon coherence”. Eight hits, including
  `ModuleCat.extendScalars_assoc'`, `extendScalars_id_comp_assoc`,
  `CommRingCat.moduleCatExtendScalarsPseudofunctor_mapComp`, and derived exact-functor
  interfaces. None states the completed intrinsic rational-stage comparison.
- `loogle`: `ModuleCat.extendScalarsComp, Functor.mapDerivedCategoryCompIso`.
  Service returned zero hits and reported the second identifier unknown.
- `grep`: `extendScalarsComp|mapDerivedCategoryCompIso`. Six Mathlib hits in
  `ModuleCat/Pseudofunctor.lean` and `ModuleCat/ChangeOfRings.lean`; these concern
  ordinary modules. The project already supplies the needed sheaf/derived ordinary
  associator, which this delivery reuses.
- `leansearch`: “Composition of extension of scalars for complexes of sheaves with
  unit and associativity coherence”. Eight hits: ordinary module extension,
  its pseudofunctor and associativity/unit equations, and a cochain scalar lemma.
  No intrinsic completed rational statement.
- `rg` in the project Lean and upstream WeilConjectures trees for
  `sfRationalScalarExtension`, `sfRationalConstructibleCategory`,
  `sf.*ScalarComp|sf.*ScalarUnit|sf.*ScalarComparison`, and scalar-composition names:
  the landed intrinsic rationalization and preservation definitions were found,
  and the old `ScalarExtensionComposition` was found and read completely.
  There was no current intrinsic associator/unit declaration. Exact searches for all
  eleven proposed declaration names in Mathlib, upstream, the upstream-name index and
  the project Lean tree also returned no hits. The upstream node-id
  search `rg -n 'lem-weil-scalar-extension-composition'` had no hits.

Maintenance repair: the previous attempt's absent prerequisite is now active as
`Sheaf.Paper.SfRationalizationKaroubi`, landed by NS. The Q22 invalidation of this
item requires normalization and coherence on these intrinsic stages; this delivery
adds exactly that interface without rebinding the archived legacy specialization.
The new category and scalar functor are not defined again, no other DAG node is
stated or edited, and no dependency record is changed. Consumer validation consists
of elaborating the natural isomorphism, both actual identity-extension equations,
and the fourth-stage coherence equation entirely on `sfRationalConstructibleCategory`;
these are the endpoints required by later finite-stage and compact-support consumers.

Validation: the final per-file `scompile.py NZ lem-weil-scalar-extension-composition`
run completed with exit 0 after the final direct imports were added. Both the sandbox
check and emitted library module compiled under the default 60-second limit, with no
errors or warnings. An earlier run also rebuilt the repaired rationalization overlay
successfully. The delivery dry run separately passed compilation before its preflight.
The second reader supplies the independent reading; this worker does not deliver.

Resumed worker audit (2026-10-16): the active prerequisite now has the landed
`Sheaf.Paper.SfRationalizationKaroubi` record. I reread its complete source, the current
blueprint statement and proof, the intrinsic integral predicate and restriction, and the
ordinary balanced tensor comparison signatures and characterizations. The retained draft
uses those exact intrinsic categories and transitions. Fresh LeanFinder, Loogle and Mathlib
grep searches found derived-functor and ordinary-module scalar-extension APIs, but no
intrinsic rational associator. Exact declaration-name searches in Mathlib, upstream,
`lean/Sheaf`, and the upstream index found no duplicate. The sandbox node differs from the
current shared node only in `lean`. The second-reading section below is retained from the
prior sandbox work; this resumed worker has not performed or claimed a new independent
second reading. The fresh prescribed `scompile.py` run passed with exit 0 after server confirmation:
the item compiled in 5.1 seconds, with no errors or warnings. The local attempt
hit its 60-second limit; the wrapper automatically confirmed against current server
sources, where every dependency also compiled within its own 60-second limit.
The fresh `deliver2.py NZ lem-weil-scalar-extension-composition --no-push`
run printed `OK (dry run)`: commit `b796385cb8` passes preflight and compilation.
It staged only this item's module, node, and report. Nothing was pushed.

## Earlier second reading (a previous round; superseded)

I independently read the active node `dag/nodes/sec-smooth-purity/lem-weil-scalar-extension-composition.json`,
the master source place (order 1469), the current snapshot source place (order 1828),
and `lean/Sheaf/Paper/SfScalarExtensionComposition.lean`. The node has one hypothesis-free
setup clause introducing finite coefficient fields and a scheme, then one object clause for
`K`, one displayed composition isomorphism, naturality, and identity-extension compatibility.
The Lean rendering is as follows.

- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`; `E`, `L`, and `M` are each
  `Type u` with `Field`, `Algebra (Padic l)`, and `FiniteDimensional (Padic l)` instances.
  The parameter `p : ℕ` and `hl : l ≠ p` are the global characteristic convention required
  by the recorded intrinsic scalar-transition interface; they impose no condition on `Y`.
- The finite inclusions are the actual algebra homomorphisms
  `ι : E →ₐ[Padic l] L` and `j : L →ₐ[Padic l] M`; the direct inclusion is `j.comp ι`.
  Field algebra maps are injective, so this introduces no extra injectivity hypothesis.
- `Y : AlgebraicGeometry.Scheme.{u}` is arbitrary. No finite-type, Noetherian,
  separated, proper, field-of-definition, or characteristic hypothesis on `Y` appears.
- The rational stage is exactly `sfRationalConstructibleCategory l E Y`, supplied by
  `def-weil-rationalization-karoubi`; its transition is exactly
  `sfRationalScalarExtension l E Y p hl L ι` (and analogously for `L → M` and `E → M`).
  This is the dependency's intrinsic raw scalar localization, with unchanged integral
  representatives, rather than a Karoubi envelope or a discrete coefficient category.
- For every object `K`, the source object and target object are rendered by the component
  of the natural isomorphism
  `sfRationalScalarComp l E L ι Y p hl M j`, whose type is the composite of the
  `E → L` and `L → M` transitions isomorphic to the direct `E → M` transition
  (with the displayed parameters in the file); its component at `K` is an isomorphism in the target
  `sfRationalConstructibleCategory l M Y`. Naturality in `K` is part of `NatIso`.
- Canonicity is fixed by `sfRationalScalarComp_existsUnique`: each component is HEq to
  the localization of `sfIntegralScalarComp`, whose component is the ordinary balanced
  tensor associator conjugated by the three normalized completion comparisons. Thus the
  isomorphism is not an arbitrary endpoint isomorphism.
- Identity-extension compatibility is rendered by `sfRationalScalarUnit` and the first
  two conjuncts of `sfRationalScalar_coherence`: the first identifies the source identity
  extension with the whiskered unit, and the second identifies the target identity
  extension with the unit at the extended object. The third conjunct gives the pentagon
  for a fourth finite extension `N` and `k : M →ₐ[Padic l] N`, which is the coherence
  required by the source proof's associator package.

The dependency declaration was read in `SfRationalizationKaroubi.lean`: the category and
transition are the exact active intrinsic declarations, including their `p, hl` interface.
The reusable ordinary comparison declarations were read in `ScalarExtensionComposition.lean`;
no private replacement is present. The intrinsic restriction and preservation declarations
were read in `SfIntegralConstructible.lean` and
`IntegralScalarExtensionConstructibleIntrinsic.lean`.

Edge cases checked: `ι` or `j` the identity, `E = L = M`, equal fields with non-definitional
algebra embeddings, a fourth extension for the pentagon, zero objects, and an empty scheme.
All are covered because no nonzero or nonempty assumptions occur. Ramified finite extensions
are allowed; no unramifiedness or chosen basis is assumed. The `l ≠ p` convention is retained,
and no condition is imposed on an independent characteristic of `Y`.

The duplicate searches were rerun. `msearch.py` LeanFinder and Loogle returned only ordinary
`ModuleCat.extendScalars*` results; grep in Mathlib found only ordinary module pseudofunctor and
change-of-rings declarations. `rg` in `lean/Sheaf`, `WeilConjectures`, and the upstream-name
index found the intrinsic rationalization and preservation declarations but no intrinsic
associator, unit, or coherence declaration. The existing `ScalarExtensionComposition` module
was read and its ordinary comparisons are reused. No exact declaration for this node exists.
An independent LeanFinder query, "Coherent transitivity of completed coefficient base change
after inverting a uniformizer", found `IsBaseChange.comp`, `IsBaseChange.of_comp`, and ordinary
adic-completion results; none concerns the intrinsic rational categories. The alternative grep
`rational.*[Aa]ssoc|[Cc]omplet.*[Cc]omp|[Bb]ase[Cc]hange.*[Aa]ssoc` likewise found no match.

One documentation mismatch was found: the module header cited only the current snapshot's
order 1828, while the node's active source is master order 1469. I repaired the header to cite
both source places. No hypothesis, object, quantifier, conclusion clause, dependency, or
construction was changed. The corrected module was recompiled with the prescribed
`scompile.py` wrapper and passed with exit 0; only the six named postponed theorem proofs use
`sorry`.

Delivery-tool note: the first completed dry run staged unrelated files in its temporary
worktree (including other groups' reports and deleted modules) and preflight rejected that
scope. The sandbox itself contains only this item's node, module, and report. This was a
wrapper bookkeeping failure; no unrelated files were edited by this reader. The prescribed
wrapper is retried without any Git workaround.


## Second reading by NZ

Independent reading in this session: I opened the current shared node, its sandbox
copy, the entire delivered Lean file, the master source (order 1469), and the current
main statement and separate proof (order 1828). This item cites the blueprint, not a
Stacks tag; both source places give the same statement and the unit/pentagon proof.
I also read the active rationalization node and its module, the intrinsic integral
predicate and scalar-preservation/restriction module, the ordinary tensor associator
and multiplication unit in ScalarExtensionComposition, the quotient-completion chain
characterization, and the finite-free comparison and its identity normalization.
The Q22 owning-node invalidation is present in the node; there is no separate repair
note for this item. The draft repairs that invalidation using the current intrinsic
categories and preserves the legacy constructions by import.

Object, hypothesis, and conclusion checklist (H3):

1. Q_l and finite extensions E, L, M: `l : ℕ`, `[Fact l.Prime]`, and each
   `E L M : Type u` with `Field`, `Algebra (Padic l)`, and `FiniteDimensional`
   instances. Verdict: exact finite coefficient fields; no algebraic-closure choice,
   unramifiedness, or basis is imposed.
2. The inclusions E into L into M: `ι : E →ₐ[Padic l] L` and
   `j : L →ₐ[Padic l] M`, with direct inclusion `j.comp ι`. Verdict: exact;
   field algebra maps are injective automatically, and arbitrary embeddings are allowed.
3. An arbitrary scheme Y: `Y : AlgebraicGeometry.Scheme.{u}`. Verdict: exact;
   no Noetherian, separated, finite-dimensional, finite-type, or base-field hypothesis.
4. The ambient prime convention inherited from def-weil-rationalization-karoubi:
   `p : ℕ`, `hl : l ≠ p`. Verdict: the active dependency explicitly takes these
   parameters on its scalar transition. They impose no condition on Y, and the
   comparison is provided for every such choice. No finite-field structure is
   substituted for an arbitrary scheme.
5. Every K in D^b_c(Y,E): `K : sfRationalConstructibleCategory l E Y` in the
   component characterizations and coherence theorem. Verdict: this is precisely
   the active dependency's raw scalar localization of sfIntegralConstructibleCategory,
   with unchanged integral objects and Hom tensor E; no Karoubi or discrete-coefficient
   category is substituted.
6. The displayed isomorphism in D^b_c(Y,M): `sfRationalScalarComp` has source
   `sfRationalScalarExtension l E Y p hl L ι ⋙
    sfRationalScalarExtension l L Y p hl M j` and target
   `sfRationalScalarExtension l E Y p hl M (j.comp ι)`. Verdict: exact orientation,
   coefficient ring, and endpoint; evaluation at K gives the required isomorphism.
7. Naturality in K: the output is a natural isomorphism of those actual functors.
   Verdict: all rational morphisms are covered, not just integral chain maps.
8. Canonicity: sfRationalScalarComp_existsUnique prescribes its hom component as
   HEq to the localized sfIntegralScalarComp component. The latter is prescribed as
   the ordinary balanced tensor associator conjugated by the three uniquely normalized
   sfIntegralOrdinaryComparison maps. That comparison is prescribed on good complexes
   by integralScalarCompletionChain, with quotient coordinates and zero shifted
   coordinate. Verdict: actual tensor normalization, not an arbitrary natural iso.
   The HEq accommodates propositionally fixed endpoints without weakening map equality.
9. Identity compatibility: sfRationalScalarUnit is the localization of the integral
   multiplication unit conjugated by the identity completion comparison. The first
   and second conjuncts of sfRationalScalar_coherence are respectively the source
   and target identity laws. Verdict: both required identity cases, with the actual
   AlgHom.id, are retained.
10. Further composition: the third conjunct quantifies over a fourth finite field N,
    its algebra map k, and every K, and equates both paths to direct extension.
    Verdict: the source proof's pentagon equation, with the same quantifier order and
    no coherence premise assumed from the caller.

Edge cases: either inclusion an identity; E=L=M; equal fields with arbitrary
algebra embeddings; three successive extensions; ramified extensions; zero objects;
and empty schemes all remain allowed. There is no index-set or cohomological-degree
parameter in this node, hence no empty-index or n=0 exclusion. The prime assumption
is precisely that needed for Padic l, and l≠p is inherited as above. The common u
is the active coefficient/scheme dependency convention; it can be enlarged to contain
any finite list of fields and a scheme. No equality of the pro-etale site's distinct
object and morphism universes is added. The file declares u and autoImplicit is false;
no implicit unbound variable or universe remains.

Independent searches (H4): I ran msearch LeanFinder with the new query
“Transitivity and unit coherence for scalar localization of completed constructible
coefficient sheaves”; its hits were ordinary localization/structure-sheaf results,
not this comparison. Loogle `ModuleCat.extendScalarsComp` returned the ordinary
module associator and unit/coherence equations; I checked its type, whose category
is ModuleCat rather than these completed rational stages. The msearch grep query
`completed.*tensor.*associ|rationalConstructibleScalarComp|sfRationalScalarComp`
returned zero Mathlib hits. Separate rg searches of Mathlib, upstream WeilConjectures,
and the shared lean/Sheaf tree for sfRationalScalarComp,
sfIntegralOrdinaryComparison, rational transitivity, and completed associativity found
no current intrinsic comparison. The project's legacy ScalarExtensionComposition
was read: its ordinary balanced tensor comparisons are correctly reused; its legacy
constructible comparisons use the withdrawn predicate and cannot serve as an existing
match. Thus no duplicate current notion or statement is introduced.

H5/H6/H8/H9: the six postponed theorems each have exactly a sorry proof and a
source/blueprint docstring with the corresponding full proof argument. All five
new definitions select data from named unique-characterization theorems; their data
are determined up to equality of the natural isomorphism. There is no arbitrary
existence choice, private replacement, file-local notation or local instance.
The DAG proof's four steps appear in order across the comparison, integral associator,
rational associator, and unit/coherence docstrings. Every line is at most 100 columns.
The imports reuse the active statement dependencies and supply the stated proof plan.
No new node or dependency module is delivered, so H12/H13 introduce no additional
review obligations. The sandbox node differs from the shared node only in lean, and
lean.statement is verbatim the main definition signature in the file.

Mismatches and changes: none in the mathematical statement, Lean signature,
normalization, proof plan, or node. The earlier second-reading text is explicitly
historical; this section records this session's independent reading. I appended
this review only and left all correct Lean unchanged. No statement_change or citer
correction audit is needed. Consumer validation is the elaboration, on the exact
active sfRationalConstructibleCategory and scalar transitions, of the normalized
associator, both identity equations, and the fourth-stage coherence equation.

Fresh validation in this independent session: prescribed scompile.py completed
with exit 0 locally for both sandbox (38.5 s) and library module (35.6 s),
under the unchanged 60-second per-file limit, with no errors or warnings.
