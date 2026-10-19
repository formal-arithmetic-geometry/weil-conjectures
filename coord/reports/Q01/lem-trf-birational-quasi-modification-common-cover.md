## Worker report

The module [BirationalQuasiModificationCommonCover.lean](lean/Sheaf/AlgebraicGeometry/BirationalQuasiModificationCommonCover.lean) states `AlgebraicGeometry.exists_common_reduced_modification_cover` with proof `sorry`, and also states the finite affine reindexing form `AlgebraicGeometry.exists_common_reduced_modification_affine_cover` with proof `sorry`. The definitions required by the statement are in `BirationalQuasiModification.lean` and `CenteredValuation.lean`; each definition has real data and no `sorry`. The modification notion is the landed `AlgebraicGeometry.SchemeModification` from `Sheaf.TraceFormula.Modification` (node `def-trf-modification`).

For the main theorem, `(X : Scheme.{u}) [IsReduced X] [CompactSpace X] [QuasiSeparatedSpace X]` renders the reduced qcqs base. `n : ℕ`, `Y : Fin n → Scheme.{u}` with `[∀ i, IsIntegral (Y i)]`, and `f : ∀ i, Y i ⟶ X` render the finite family of integral schemes and its maps. `hY` requires `IsBirationalQuasiModification (f i)` for every index. `hcomponents : Set.Finite (irreducibleComponents X)` is the finite-component hypothesis. `hvaluation` ranges over every point `η : X` whose closure is an irreducible component, every valuation subring `V : ValuationSubring (X.residueField η)`, and every `v : Spec (.of V) ⟶ X`; `IsCenteredValuation η V v` is the exact canonical generic-point equation, and the conclusion of this hypothesis supplies an index `i` and `l : Spec (.of V) ⟶ Y i` with `l ≫ f i = v`. The conclusion supplies `X₁`, `p : X₁ ⟶ X`, `IsReduced X₁`, and `SchemeModification p`; it then supplies opens `W : Fin n → X₁.Opens` with `(⨆ i, W i) = ⊤`, and for every `i` a map `a : (W i).toScheme ⟶ Y i` such that `SchemeModification a` and `a ≫ f i = (W i).ι ≫ p`.

The second theorem repeats those hypotheses and adds a finite dependent family of specified affine opens `A i j`, the hypotheses `IsAffineOpen (A i j)` and `(⨆ j, A i j) = ⊤` for each `i`. Its conclusion uses `W : (Σ i : Fin n, Fin (m i)) → X₁.Opens`, has `(⨆ j, W j) = ⊤`, and gives a modification to each `(A j.1 j.2).toScheme` with the displayed composite equation. This is the node's clause that an index may be repeated after finite affine covers.

`IsBirationalQuasiModification` (module `Sheaf.AlgebraicGeometry.BirationalQuasiModification`, declaration `AlgebraicGeometry.IsBirationalQuasiModification`) renders the source integral and target reduced typeclasses, separatedness, quasi-compactness, locally finite type, component closure of the source generic image, and the actual residue-field map being an isomorphism. `IsCenteredValuation` (module `Sheaf.AlgebraicGeometry.CenteredValuation`, declaration `AlgebraicGeometry.IsCenteredValuation`) renders a valuation subring of the residue field together with the equation `Spec.map (CommRingCat.ofHom V.toSubring.subtype) ≫ v = Z.fromSpecResidueField η`. `SchemeModification` (module `Sheaf.TraceFormula.Modification`, declaration `AlgebraicGeometry.SchemeModification`) renders properness and an open `U` of the target such that `SchematicallyDenseOpen U`, `SchematicallyDenseOpen (f ⁻¹ᵁ U)`, and `IsIso (f ∣_ U)`. Schematic density is the landed `AlgebraicGeometry.SchematicallyDenseOpen`, meaning injectivity of restriction to the intersection on every ambient open. The restriction is the actual induced map, so the required square commutes canonically. This gives the node's isomorphism between schematically dense opens. The same landed module defines `AlgebraicGeometry.EtaModification`, using the actual induced generic base-change map, for the explanatory generic-fibre clause.

The original statement dependencies are retained: `def-pc-integral-scheme`, `def-pc-reduced-scheme`, `def-weil-finite-type-morphism`, `def-weil-irreducible-components`, and `def-weil-proper-morphism`. The two added definition nodes and the existing `def-trf-modification` are used through the modules and declarations above. Proof-only imports are present for the recorded compactification, reduced closed subscheme, dense component coproduct, affine birational, valuation, and valuative-criterion dependencies; they are not hypotheses of the statement.

Edge cases checked were the empty base and `n = 0` (the valuation hypothesis then forces the vacuous component situation), an integral one-point scheme with its trivial valuation subring, a reduced scheme with crossing irreducible components, repeated affine indices, empty affine pieces, non-Noetherian valuation rings, and the Frobenius map on the affine line in positive characteristic. The last case rejects replacing the induced residue-field map by an arbitrary abstract field isomorphism. The canonical morphism equation in `IsCenteredValuation` likewise rejects a morphism that merely has the same topological generic point. Schematic density is checked through sheaf restriction injectivity, so nilpotent or disjoint extra components cannot be hidden.

Historical searches from the retained packet, run on 2026-10-17, were saved in `search-results.json`. For the common-cover notion, `msearch.py ... leanfinder` queried “Finite birational quasi modifications with every centred valuation lifting have a common proper refinement with a finite open cover”, `leansearch` queried “A finite family of birational quasi modifications covering all centred valuations admits a common proper modification”, and grep queried `IsModification|QuasiModification|CenteredValuation|CentredValuation|common.*modification`; the returned constituent declarations did not state this theorem. For the birational predicate, LeanSearch, LeanFinder, and grep queried respectively “A separated finite type integral scheme morphism induces an isomorphism of function fields onto an irreducible component”, “Birational quasi modification scheme morphism finite type separated residue field isomorphism at generic point”, and `QuasiModification|quasi.?modification`; no exact declaration was found. For centred valuations, the queries were “Valuation subring of the function field of an irreducible component and a morphism of its spectrum agreeing with the canonical generic point morphism”, “Centred valuation on a scheme is a valuation subring of its function field with a compatible spectrum morphism”, and `CenteredValuation|CentredValuation|centered.?valuation|centred.?valuation`; no exact declaration was found. For modifications, the queries were “Proper morphism inducing an isomorphism between schematically dense open subschemes modification”, “A modification is a proper morphism inducing an isomorphism between schematically dense opens”, and `IsModification|def Modification|class Modification`; no exact declaration was found. `rg` over `WeilConjectures` and the shared `lean/Sheaf` tree found only the narrower Orgogozo modification predicate, which assumes a Noetherian compact target and does not state this qcqs notion. `tools/blueprint_refs.py search` then found no existing node for these three notions. The repair rechecked the current base and found the subsequently landed `def-trf-modification`; it reuses that declaration, superseding the earlier negative modification search.

## New nodes

`def-trf-birational-quasi-modification` defines the integral separated finite-type map with its actual generic residue-field identification. Its source is Temkin §3, and its node records the LeanSearch, LeanFinder, and grep results above; none gave the notion. Its module is imported directly by the item.

`def-trf-centred-valuation` defines the valuation-subring spectrum morphism with the exact canonical generic-point equation. Its source is Temkin §3.2 preceding Corollary 3.2.5, and its node records the LeanSearch, LeanFinder, and grep results above; none gave this notion. Its module is imported directly by the item.

`def-trf-modification` is already on the current base and is reused; it is not a new node of this repaired delivery.

## Dependency modules

No recorded dependency required a §1(B) repair: all original dependency declarations were usable for their stated notions. The two added definition modules are §1(A) nodes. The usable landed modification interface is imported without modification or a dependency-node copy.

No statement correction or `STATEMENT-DISPUTED` marker is needed. The retained four-module packet compiled, but its dry run rejected the duplicate `def-trf-modification` as a dependency repair without `lean.note`. This repair removes that duplicate instead of overriding the usable landed interface. The final three-module packet is checked again through `scompile.py` and `deliver2.py`.

## Returned-delivery repair

L returned immutable head `000001384048` because `def-trf-modification` now exists on `newtargets-dag`. Read the current node and the full live module with `scompile.py --source Sheaf.TraceFormula.Modification`. Removed the packet's `def-trf-modification.json` and `Sheaf.AlgebraicGeometry.Modification` module; the item now imports `Sheaf.TraceFormula.Modification` and uses `AlgebraicGeometry.SchemeModification` in both theorem conclusions. The item still cites the existing node in `stmt_deps`. No existing node is overwritten. The item signature record is updated verbatim.

Self-check: both theorem binders and valuation equations are unchanged. The main cover is still indexed by `Fin n`, and the affine refinement by the dependent finite pair. Every map to a model is still over `X` and a modification; `p` remains a reduced modification. The landed definition uses the whole inverse image of a dense target open. This is the source convention, and the node's retained proof supplies it: the integral component maps have single generic fibres, and the finite-component assembly chooses the target open inside the componentwise isomorphism loci. Its whole preimage is therefore the chosen isomorphism open and schematically dense. Empty bases and empty families remain included. No statement correction is required.

## Second reading by Q01

Independent maintainer second reading of immutable delivery
`c04a6364eb7728a36c906efd6dd792a59223a8ab`, performed 2026-10-18. This section
replaces the worker's placeholder; it does not assert that a worker performed a
previous independent reading. I read the item, all eight statement dependency
records, both new definition modules, both theorem declarations, and the exact
landed modification and schematic-density declarations.

Clause-by-clause check:

1. The base is `X : Scheme.{u}` with `[IsReduced X]`, `[CompactSpace X]`, and
   `[QuasiSeparatedSpace X]`. These say reduced and qcqs in the node's explicit
   topological sense; no Noetherian, normality, excellence, separated-base,
   characteristic, or finite-presentation hypothesis is added. PASS.
2. `hcomponents : Set.Finite (irreducibleComponents X)` is exactly the finite
   component assumption. Mathlib's `irreducibleComponents` is the set of maximal
   nonempty irreducible subsets, so the closure condition on `η` ranges over all
   component generic points of a scheme. PASS.
3. `n : ℕ`, `Y : Fin n → Scheme.{u}`, `[∀ i, IsIntegral (Y i)]`, and
   `f : ∀ i, Y i ⟶ X` express an arbitrary finite family of integral models and
   its given structural morphisms, including the empty family. Finite indexing
   by `Fin n` loses no finite-family case. PASS.
4. `hY` uses `IsBirationalQuasiModification (f i)`. Its definition is precisely
   separatedness, locally finite type and quasi-compactness, the component
   condition on the image of the source generic point, and invertibility of
   `f.residueFieldMap (genericPoint Y)`. The latter is the actual contravariant
   field map, not an unrelated field isomorphism. At component generic points of
   reduced schemes, the local ring is a field (Mathlib Properties, line 220),
   so the residue-field formulation is canonically the function-field one.
   Integral source and reduced target are required by the definition's binders.
   PASS.
5. `hvaluation` quantifies over every component generic point `η`, every
   `ValuationSubring (X.residueField η)`, and every spectrum morphism `v`.
   `IsCenteredValuation η V v` requires equality of the full generic morphisms
   `Spec.map (CommRingCat.ofHom V.toSubring.subtype) ≫ v` and
   `X.fromSpecResidueField η`. The lift supplies an actual `l` and the equation
   `l ≫ f i = v`, with the index chosen separately for each valuation. PASS.
6. The conclusion gives `X₁`, the actual map `p : X₁ ⟶ X`, `IsReduced X₁`, and
   `SchemeModification p`. This reused landed structure requires properness,
   schematic density on target and inverse-image opens, and invertibility of
   the actual restriction of `p`. PASS.
7. `W : Fin n → X₁.Opens` and `(⨆ i, W i) = ⊤` are the finite open cover, with
   the same model indices. Each `a : (W i).toScheme ⟶ Y i` is required to be a
   `SchemeModification`, and `a ≫ f i = (W i).ι ≫ p` is exactly the over-`X`
   equation. Neither properness nor birationality of these local maps is
   omitted. PASS.
8. The second theorem retains all original hypotheses and accepts any specified
   finite affine cover of each model, with `IsAffineOpen` and supremum equal to
   top. Its dependent pair index `(Σ i : Fin n, Fin (m i))` retains repetitions;
   its local targets are the actual open subschemes and its factorization
   includes their inclusions into `Y i`. This realizes the optional affine
   reindexing clause. PASS.
9. The explanatory eta-modification clause is covered by the reused
   `AlgebraicGeometry.EtaModification`, whose second conjunct makes the actual
   pullback functor's map invertible. The node does not require an additional
   eta-modification conclusion for an unspecified base generic fibre. PASS.

Source and proof reading: I opened the primary Temkin PDF at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, especially §1.2,
§3 opening conventions, §3.2 and Proposition 3.2.6 with Corollaries 3.2.5/3.2.7
(pp. 13–17). Its integral qcqs base convention is used on each reduced component
in the node's explicitly identified finite-component extension. The valuation
condition supplies the cover, rather than silently treating the existence of
local opens as a covering assertion. The proof is labelled agent-written in the
node; it does not pretend that the finite-component extension is a verbatim
source statement. Local Stacks sources checked include integral/reduced and
component definitions (01OK/01ON, 01J0/01J1, 004V) and the qcqs Nagata theorem
0F41 (`flat.tex`, lines 9950–9957).

The common-cover docstring carries all thirteen node steps. The reduced closure
of the generic point of the product, rather than the entire product, removes
extraneous components. Properness of its projections gives proper maps from the
model opens. A dominating valuation at a point, followed by separatedness of
the compactification, establishes membership in some model open. Finite
component coproducts give the required reduced source over `X`. The affine
variant documents the final reindexing step and refers to the other twelve
steps, all under this same DAG node.

I checked the apparently stronger full-inverse-image convention in the landed
`SchemeModification`: for each proper birational map in the blueprint, choose
an open source isomorphic to a dense target open. The generic fibre is a single
point. The image of the closed source complement is closed by properness and
misses the target generic point. Remove that image from the target open. The
whole inverse image now lies in the chosen isomorphism open. For finitely many
components do this componentwise before the component-separating open is chosen.
The resulting opens are schematically dense: on integral pieces this follows
from injection into the function field, and on reduced `X` from the zero
nilradical. Thus the reused definition adds no unintended assumption.

Edge cases: if `n = 0`, the full-field valuation at a component generic point
contradicts `hvaluation` unless `X` is empty. The empty source, identity, and
empty cover then satisfy the conclusion. A field base includes the trivial
valuation ring. Crossing components are allowed and handled by the finite
disjoint union, without assuming normality. Empty affine members cause no
false assertion: choose their `W` empty, and the map from empty to empty is a
modification. Nonempty affine members retain integrality; one applies the
construction to those members and reinstates the empty ones. Covers with
repeated indices, positive characteristic (including non-birational Frobenius),
and valuation rings of arbitrary rank are retained. All scheme and residue-field
objects live in the one arbitrary declared universe `u`; no smaller universe of
test valuations or imposed site-universe equality occurs.

Dependencies and duplication: I inspected Mathlib `IsIntegral`, `IsReduced`,
`LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `irreducibleComponents`,
`Hom.residueFieldMap`, and `fromSpecResidueField`, and read the exact current
`Sheaf.TraceFormula.Modification` and `SchematicallyDenseOpen` sources through
`scompile.py --source`. The component dependency has a usable exact
`mathlib_match` even though its snapshot has no `lean` field. No dependency
interface repair is needed. Independent `rg` searches used birational,
Riemann–Zariski, quasi-model, quasi-modification and centred-valuation terminology
in Mathlib, upstream and the Q01 side tree. Mathlib `Scheme.BirationalOver` is an
existence of partial isomorphism between structural maps, not this predicate on
the given morphism. The Riemann–Zariski module's bundled `QuasiModel` and
`ValuationPoint` use specified ambient field maps and are not these unbundled
predicates; its refinement theorem has a different finite-type-base/extension
setting. The strict-curve `CenteredValuation` carries additional base and
closed-centre data. None supplies this exact common-cover theorem. The delivered
modification duplicate was correctly removed in favour of the landed notion.
The report and new nodes retain the worker's three kinds of search records.
Both new definition nodes have the expected source, blueprint ancestry, empty
proof fields, audit fields and owning modules, and are cited by the item.

Mechanical and pilot gates: all three delivered `lean.statement` fields occur
verbatim as their complete signatures in the corresponding immutable modules.
All three modules have source/blueprint docstrings, `autoImplicit false`, bound
`u`, and lines at most 100 characters. Both definitions have explicit predicate
bodies with no `sorry`; both theorems have only `by sorry`, with no local proof.
The actual commit adds only the three modules, two new definition records,
item metadata and report. The item delta is only `lean` and the allowed added
statement dependencies; no statement correction or citer audit is needed.
The exact item/dependency statement and proof dependency ids have empty
intersection with `origin/newtargets-dag:coord/route-pivot-dropped.txt`; no
route-pivot repair note exists for this item, and no dropped machinery or
pro-etale replacement is introduced.

Compilation reproduced on 2026-10-18 with the exact immutable files:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q01 lem-trf-birational-quasi-modification-common-cover \
  snapshot/lean/Sheaf/AlgebraicGeometry/BirationalQuasiModification.lean \
  snapshot/lean/Sheaf/AlgebraicGeometry/CenteredValuation.lean \
  snapshot/lean/Sheaf/AlgebraicGeometry/BirationalQuasiModificationCommonCover.lean
```

All three compiled separately in the wrapper's private side overlay and library
checks. Library times were 2.2 s, 1.8 s, and 2.7 s, respectively; there were no
reported errors or warnings. Preliminary/sandbox checks also passed. An initial
standalone invocation of the final module failed for absent sibling object
files, including its automatic server confirmation; this was an invocation
without the required siblings, not a delivery fault. Supplying all siblings as
the brief directs resolves it. The historical report asserted compilation but
contained no detailed final transcript; the reproducible command and observed
results above supply that evidence. No global build, live Lean write, direct
SSH, delivery operation or repository mutation was performed by this review.

Finding and change: H11, the original second-reading section explicitly said no
reading had occurred. This complete independent section replaces that
placeholder. The Worker report and all other original report sections are
preserved. No Lean, JSON, source statement, definition, or dependency change is
required. Verdict: FIX, report only.
