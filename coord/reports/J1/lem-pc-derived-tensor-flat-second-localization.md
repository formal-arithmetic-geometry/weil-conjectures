## Worker report

The module `lean/Sheaf/Algebra/Homology/DerivedTensorFlatSecondLocalization.lean` states
`RingTensorCohomology.derivedTensor_flat_second_localization`, with proof `sorry`.
The additional module `lean/Sheaf/Algebra/Homology/RingTensorCohomology.lean` defines
concrete cohomology models and the canonical comparison and base-change maps. Its data
uses upstream functorial K-flat resolutions, extension/restriction of scalars, cohomology,
and the exact-functor cohomology isomorphism. No data is `sorry`. Two named obligations,
`spanLeft_isIso` and `extend_preservesHomology`, have `sorry` proofs and complete proof
docstrings; both belong to the new node and are named in its `lean.declarations`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings are `(R A B C : Type v)` with their four `CommRing` instances.
  The maps R -> A and R -> B are the two `Algebra` instances. The compatible R -> C
  and B -> C maps are `Algebra R C`, `Algebra B C`, and `IsScalarTower R B C`.
  These name the induced map to the localization; they impose no extra mathematical
  assumption. The ambient universe is arbitrary, and complexes are unbounded.
- The multiplicative set is `S : Submonoid B`; C = S^-1 B is `[IsLocalization S C]`.
  This uses the universal-property notion of localization, allowing any isomorphic model.
- Flatness is exactly `(hflat : (algebraMap B C).Flat)`, the recorded dependency's
  `RingHom.Flat`. No flatness of R -> A or R -> B is assumed.
- M is quantified as `CochainComplex (ModuleCat.{v} A) ℤ`; `i : ℤ` is arbitrary.
  This uses the recorded dependency declaration `CochainComplex` directly, specialized
  to ordinary modules. Its full signature allows any category of terms.
- `source R A B i` is H^i(M tensor-derived-over-R B), computed as the cohomology of
  B tensor-over-R F_R(UM), with F_R an upstream functorial K-flat resolution.
  It is a B-module, with the genuine second-factor B-action.
- `baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i`
  is the canonical map in the statement. Mathlib writes extension of scalars as
  C tensor-over-B H; tensor symmetry identifies it with H tensor-over-B C.
  Its definition is the standard cohomology comparison for exact scalar extension,
  followed by associativity C tensor-over-B (B tensor-over-R K) = C tensor-over-R K.
  Thus it is the map x tensor c |-> c times H(M tensor-derived-over-R (B -> C))(x),
  rather than an arbitrary isomorphism between isomorphic objects.
- The first conjunct asserts `IsIso` for this canonical map, for every M.
- The second conjunct is naturality for every complex morphism f : M -> N, using
  the functors `source R A B i` and `source R A C i`. These functors invert
  quasi-isomorphisms by their K-flat construction, so this is also naturality on
  the derived category; no choice of a chain representative is an assumption.
- Every arrow is a morphism of `ModuleCat C`, so C-linearity and compatibility with
  the B-action through B -> C are built into its type. The third conjunct explicitly
  intertwines the A-action: multiplication by a is the chain map `a • 𝟙 M`, and
  its source/target cohomology action is the corresponding functor image.
  C-linearity together with this equation is precisely A tensor-over-R C-linearity,
  since the two actions commute and are R-balanced. It expresses the tensor-algebra
  module statement by the equivalent pair of scalar conditions, without inventing
  another module structure on the same cohomology carrier.
- `target R A B i` is H^i(M tensor-derived-over-A (A tensor-over-R B)), computed as
  B tensor-over-R U(F_A M), canonically the same as
  F_A M tensor-over-A (A tensor-over-R B).
- `comparison R A B i` is H^i of the canonical comparison in the question. The
  common model is B tensor-over-R F_R(U(F_A M)); its left arrow to the source is
  a quasi-isomorphism, and its right arrow to the target is induced by the
  R-resolution augmentation. Inverting the left cohomology arrow and following
  the right gives the usual derived-to-underived comparison on the A-K-flat model.
- The last conjunct states exactly the requested square: first extend H^i(c_B)
  to C and then use target base change, or first use source base change and then
  H^i(c_C). Its target base-change map is `baseChangeMap` applied to U(F_A M).

Dependency declarations read and used:

- `CochainComplex`, `Mathlib.Algebra.Homology.HomologicalComplex`; its underlying
  `HomologicalComplex` data is X, d, shape, and d_comp_d. The category morphisms
  commute with the differentials. This is the `mathlib_match` of
  `def-pc-cochain-complex-modules`, which is a Mathlib leaf without a `lean` record.
- `RingHom.Flat`, `Mathlib.RingTheory.RingHom.Flat`, defined as `Module.Flat R S`
  for the algebra of the ring map. `Module.Flat` and its injectivity characterization
  were read in `Mathlib.RingTheory.Flat.Basic`. These are the `mathlib_match` of
  `def-weil-pbc-flat-ring-map`, likewise a Mathlib leaf.
- `RingTensorCohomology.source`, `target`, `comparison`, `baseChangeMap` from the new
  node/module. The new definitions specialize upstream
  `CategoryTheory.Abelian.LeftResolution.resolutionFunctor` and `resolutionNatTrans`
  (`WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex`), using
  `LeftResolution.reduced`, `ModuleCat.hasFunctorialFlatResolution`
  (`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`),
  and the K-flat construction in
  `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`.
  Extension/restriction and their associativity are `ModuleCat.extendScalars`,
  `restrictScalars`, `extendScalarsComp` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
  Additivity is inherited, without a new theorem, from
  `Adjunction.left_adjoint_additive` in `Mathlib.CategoryTheory.Adjunction.Additive`.
  Exact cohomology comparison is `ShortComplex.mapHomologyIso` in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

Edge cases checked before writing: S may contain zero (then C is the zero ring and both
base-changed cohomologies vanish); S = {1} gives the identity localization; R, A, B may
be zero rings; M may be zero or unbounded in both directions; i may be negative, zero,
or positive; no characteristic, nonzeroness, boundedness, or flatness over R is required.
The resolutions are K-flat over the ring where each is taken. In particular the proof
obligation never assumes that an A-K-flat resolution remains K-flat over R.

Searches for the item (run using `/home/ubuntu/weil-launcher/msearch.py`):

- LeanSearch, `derived tensor cohomology commutes with flat localization in second factor`:
  unavailable, Internal Server Error; no mathematical verdict inferred.
- LeanFinder, `derived tensor cohomology flat localization second factor comparison map`:
  eight hits, cotangent-localization and flat exactness/Tor lemmas; no matching statement.
- Loogle, `Module.Flat, IsLocalization`: four hits, including `IsLocalization.flat`;
  none states derived tensor cohomology or the comparison square.
- Mathlib grep, `derivedTensor|derived_tensor` in `Algebra/Homology`: zero hits.
- Direct rg of `WeilConjectures` for derived tensor names found sheaf/site-derived
  tensors and the general monoidal derived-category infrastructure, not this ring
  comparison theorem. Searching the item ID in the source returned no hits.
  Direct rg of `lean/Sheaf` found K-flat and tensor closure modules, not this statement.
  The proposed namespace and theorem name were checked against both repositories and
  `dag/lean_names_upstream.json`, with no clash.

Source: the Stacks tag was read online because this read-only clone has only the literature
lists, not `literature/stacks-project/more-algebra.tex`:
https://stacks.math.columbia.edu/tag/06Y6 and the surrounding Derived change of rings section.
The concrete comparison uses the same derived-to-underived construction as the source.
No statement correction and no STATEMENT-DISPUTED finding.

Validation: both modules compile together cleanly on the server with automatic implicits disabled.
The delivery dry run is required to pass all worker checks; the independent second-reading
section is intentionally left for the second worker. The new node records the complete
created.item ancestry calculated by blueprint_refs.chain, including intermediate nodes
beyond the shorter stored via field of the item.

## New nodes

`def-pc-ring-tensor-cohomology` defines the missing ring-specific cohomology functors,
comparison span, and canonical flat scalar-extension cohomology map. Source: Stacks
Tag 06Y6, the derived change-of-rings construction and comparison-map equation.
This reuses the general upstream K-flat resolution and Mathlib change-of-rings data.
The DAG's `def-weil-derived-tensor` is a definition for sheaves on a pro-etale site;
it does not provide these ordinary-ring cohomology and comparison maps. The statement
nodes about balanced models and second-factor functoriality do not give declarations
for these maps. No private version of their sheaf notions is introduced.

Searches for this new notion were run and are copied into its `mathlib_searches`:
LeanSearch query `cohomology functors for derived tensor of complexes over two commutative
rings canonical comparison via K-flat resolutions` was unavailable (Internal Server Error).
LeanFinder query `canonical comparison map M derived tensor over R B to M derived tensor
over A A tensor over R B K-flat resolutions` returned eight flatness/exactness lemmas,
none defining the comparison functors. Mathlib grep
`derived.*tensor.*compar|tensor.*cohomology|sourceComplex|middleComplex` returned one
unrelated comment in faithfully flat algebra. Direct rg for `RingTensorCohomology`,
`sourceComplex`, `middleComplex` in upstream and `lean/Sheaf` returned no hits.
`tools/blueprint_refs.py search 'ring tensor cohomology'` found zero blueprint nodes;
DAG grep for `ring tensor cohomology|comparison span` found no existing definition node.
`tools/blueprint_refs.py ancestor` identifies `lem-pc-rf-perfect-base-change` as the
ancestor, used in `blueprint.from` with the item's path prefixed to its `via` list.


## Second reading by J1

Independent verdict: the main signature states the node exactly. I opened the item,
its new definition node, both modules, both original statement-dependency nodes,
and the upstream declarations used in their implementations. No item statement
correction is needed, and there is no `statement_change` in this delivery.
The worker report above describes the initial version; the changes below supersede
its reference to the removed `extend_preservesHomology` obligation.

Object, hypothesis, and conclusion checklist (node order):

1. R, A, B are arbitrary commutative rings and R -> A, R -> B arbitrary ring maps:
   `(R A B C : Type v)` with four `CommRing` instances and `Algebra R A`,
   `Algebra R B`. Verdict: exact. No field, Noetherian, finite-generation, nonzero,
   or flatness-over-R hypothesis is introduced.
2. A multiplicative subset S of B and C = S^-1 B: `(S : Submonoid B)` and
   `[IsLocalization S C]`, with `[Algebra B C]`. Verdict: exact up to the usual
   canonical identification of localization models. `Algebra R C` and
   `IsScalarTower R B C` specify the composite structure induced by R -> B -> C;
   every node datum supplies these, so they are not additional assumptions.
3. Flatness of B -> C: `(hflat : (algebraMap B C).Flat)`. Verdict: exact. I read
   `RingHom.Flat` (RingHom/Flat.lean:27), `flat_algebraMap_iff`, and the original
   flat-ring-map node; the property is precisely flatness of C as a B-module.
4. M is a cochain complex of A-modules, and the degree is any integer:
   each `∀ M : CochainComplex (ModuleCat.{v} A) ℤ` and `(i : ℤ)`.
   Verdict: exact, unbounded in both directions. `CochainComplex` is the general
   Mathlib abbreviation for `HomologicalComplex` of shape `.up ℤ` (line 157),
   with module-linear differentials squaring to zero and chain maps commuting
   with differentials. The dependency's sheaf application does not constrain
   this general declaration to sheaves: it is usable directly for ModuleCat.
5. H^i(M tensor-derived-over-R B): `(source R A B i).obj M`, definitionally
   homology of `extend R B` applied to `resolution R` of `restrict R A` of M.
   Verdict: correct derived scalar-extension cohomology with the second-factor
   B-action, not the underived tensor of M. The corresponding C term is
   `(source R A C i).obj M`.
6. Canonical map after tensoring cohomology with C:
   `baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i`.
   Its domain is `extendScalars (algebraMap B C)` of the B-cohomology, hence
   C tensor_B H, identified with H tensor_B C by symmetry. Its definition is
   inverse exact-functor homology comparison followed by extension associativity.
   I checked `ShortComplex.mapHomologyIso` (PreservesHomology.lean:455): its
   direction is H(FK) -> F(HK), so `.inv` is the required direction. I checked
   `extendScalarsComp`: its direction is direct extension -> iterated extension,
   so the `.symm` in `extendCompIso` gives the required iterated -> direct map.
   Verdict: the canonical map, not just existence of an unspecified isomorphism.
7. Isomorphism of A tensor_R C-modules: first conjunct `IsIso` of that map,
   and third conjunct commuting with `(source ...).map (a • 𝟙 M)` for every a.
   Every arrow is already C-linear in ModuleCat C. These are precisely the
   commuting A and C scalar conditions for tensor-algebra linearity. The A-action
   is the image of multiplication on M under derived restriction/extension;
   although the chosen resolution is not assumed additive on chains, its
   cohomology is the additive derived extension functor. Consequently these
   endomorphisms are the genuine derived A-action. Verdict: exact scalar
   condition with no chosen arbitrary action and no omitted B compatibility;
   B acts through B -> C, already enforced by C-linearity.
8. Naturality in M: second conjunct quantifies arbitrary complexes M,N and
   arbitrary chain maps f and gives the naturality equation. Verdict: exact.
   Source cohomology inverts quasi-isomorphisms: restriction preserves them,
   the resolution augmentation identifies its R-resolution with the original,
   and extension preserves quasi-isomorphisms between R-K-flat complexes.
   Thus the displayed naturality also descends to derived morphisms (roofs).
   Moving universal integer i ahead of universal M changes no quantifier scope.
9. Comparison at B: `(comparison R A B i).app M` goes from source cohomology
   to `(target R A B i).obj M`, the cohomology of
   `extend R B` of `restrict R A` of `resolution A` of M. The latter is
   M tensor-derived-over-A (A tensor_R B) by ordinary tensor associativity.
   The comparison uses the common R-K-flat resolution of the restricted
   A-resolution. `spanLeft` is induced by the A-augmentation and is inverted
   on cohomology; `spanRight` is induced by the R-augmentation.
   Verdict: exactly the canonical comparison of equation comparison-map.
   In particular no false claim that an A-K-flat complex is R-K-flat is used.
10. Compatibility square: last conjunct extends the B comparison to C and then
    applies `baseChangeMap` to `restrict R A` of `resolution A` of M on the
    target side; the other composite applies source base change then
    `(comparison R A C i).app M`. Verdict: all four maps and their order agree
    with the node. The target vertical map is ordinary cohomology base change
    on the A-K-flat model, which computes the required A-derived tensor.

Source reading: the local clone does not hold the Stacks .tex. I read the actual
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex),
section-derived-base-change (lines 13475 onward), lemma-derived-base-change
[Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6), and the beginning of
section-tor-independence, including equation-comparison-map (lines 13721-13762).
The former assumes only a ring map and unbounded complexes; the latter constructs
comparison by first taking an A-K-flat representative and then an R-K-flat
resolution of its restriction, exactly the delivered span. No Tor-independence
hypothesis is needed for existence of comparison, and the delivered theorem
correctly does not assert that comparison itself is an isomorphism. Flatness
makes scalar extension exact; kernels, images and cokernels then give the
cohomology base-change isomorphism. These sections do not impose any hidden
Noetherian, characteristic or boundedness restriction.

New node reading (H12): `def-pc-ring-tensor-cohomology` introduces its own R,A,B,
resolutions, restriction, models L,T,V, cohomology, comparison, actions, and the
compatible flat extension B -> C. Each is rendered by the definitions described
above; its two cited notions have exactly the two `stmt_deps`. Its proof fields
are empty, kind is definition, status split, searches have the required three
kinds, created identifies this item and group, and its chapter/unit match the
item. The ancestry begins at lem-pc-rf-perfect-base-change and carries the full
intermediate path. No maintainer-only review fields are added. Its data are
concrete upstream resolutions and Mathlib scalar-extension/cohomology data.
The remaining `spanLeft_isIso` named theorem has a complete natural-language
proof: restrict the A-augmentation, apply the R-resolution, then tensor a
quasi-isomorphism between K-flat complexes with B. This is the proof obligation
explicitly contained in the new node's comparison span. There are no dependency
replacement modules, no private sheaf definitions, and no hollow data.
I read upstream `LeftResolution.resolutionFunctor`, `resolutionNatTrans`,
`quasiIso_resolutionNatTrans_app`, `kFlat_resolutionFunctor_obj`, and
`ModuleCat.hasFunctorialFlatResolution`: reduced flat resolutions have the
required zero-map condition and yield K-flat resolutions for arbitrary complexes.

Independent searches (H4):

- LeanSearch via msearch, `canonical natural comparison between derived extension
  of scalars over two commutative rings`: unavailable (Internal Server Error),
  recorded as unavailable without inferring absence from the failure.
- LeanFinder via msearch, `homology extension of scalars flat ring map derived base
  change natural comparison`: eight hits. They include
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, `extendScalarsComp`,
  base-change flatness and faithfully-flat reflection; none states this theorem
  or defines this ring-specific comparison span/cohomology pair.
- Loogle via msearch, `ShortComplex.mapHomologyIso`: remote index reports unknown
  identifier, no absence verdict. I opened the actual declaration locally instead.
- Direct rg, `tensor.*[Cc]ohomology|[Cc]ohomology.*tensor|derived.*[Bb]ase.*[Cc]hange|
  [Cc]omparison.*[Ss]calar`, on upstream algebra, Mathlib homology and Sheaf algebra:
  no matching ring localization theorem or ring comparison-functor definition.
  A wider derived-tensor search found the already landed
  `TermwiseTorAcyclicDerivedTensor.lean`; I opened it. It is a bounded,
  termwise-Tor-acyclic comparison theorem, not these unbounded cohomology functors
  or the localization square. Upstream Mod/Tensor.lean defines ordinary internal
  tensor over a commutative monoid, not these cross-ring derived comparisons.
- DAG rg for `ring tensor cohomology|comparison span`, plus blueprint_refs search
  `ring tensor cohomology`: no existing notion node. I opened
  `def-weil-derived-tensor`; its pro-etale sheaf tensor cannot supply these ring
  maps. General derived monoidal infrastructure supplies ingredients only.
  Exact names `RingTensorCohomology|derivedTensor_flat_second_localization` were
  absent from upstream, existing Sheaf files and dag/lean_names_upstream.json.

Edge cases: S = {1}, S containing zero, zero rings and zero or acyclic M are all
allowed. No Nontrivial or regular-element hypothesis occurs. A submonoid contains
1, so an empty S is outside the node as well as Lean; there is no other index-set
parameter or scheme parameter (the empty scheme is irrelevant here). Integer
indices include i = 0 and negative i. All characteristics and unbounded complexes
are permitted. Universe v is arbitrary and is a common ambient universe for the
rings and module carriers; choosing a common universe (and lifts if necessary)
covers every set-sized datum, rather than fixing rings or modules to Type 0.
No implicit universe, variable, finiteness or boundedness instance remains.

Mismatches and repairs:

- The new node's source place incorrectly put equation comparison-map in Section
  15.61. The .tex places it in Tor independence. Corrected the new node source
  attribution and its module header; the item's mathematical statement and
  original source record are untouched.
- The auxiliary `extend_preservesHomology` sorry repeated an exactness fact already
  available from Mathlib. Replaced it in `flatHomologyMap` by the existing
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat h`, with finite-colimit
  preservation from the scalar-extension adjunction and the existing
  `Functor.preservesHomologyOfExact` instance. Imported ModuleCat.Descent and
  removed the redundant theorem and its `lean.declarations` entry. This uses
  existing proofs; no theorem was proved in stage 2 and no data is hollow.
- No mismatch in the main statement signature, models, map directions or square
  was found. I did not rewrite them. The two remaining theorem proofs (the main
  item and `spanLeft_isIso`) are `sorry`, each with source, blueprint marker and
  complete natural-language proof. The new node's recorded source signature
  `def source (i : ℤ)` and the item's full signature remain verbatim equal to
  their declarations.

Validation after repair: scompile compiled both delivered modules together in
order RingTensorCohomology then DerivedTensorFlatSecondLocalization, with exit
code 0 in 2.8 seconds, no errors or warnings. Automatic implicits are disabled.
