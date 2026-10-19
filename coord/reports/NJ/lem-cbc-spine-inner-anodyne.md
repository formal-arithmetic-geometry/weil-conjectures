## Worker report

The module `lean/Sheaf/AlgebraicTopology/SimplexSpineInnerAnodyne.lean` defines
`SSet.simplexSpine` and states `SSet.simplexSpine_innerAnodyne` with proof `sorry`.
The module imports the recorded dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones`
and Mathlib's inner-anodyne extension module.  The dependency supplies the simplicial
set, standard simplex, and horn conventions.  Mathlib's
`SSet.innerAnodyneExtensions` is the exact left lifting property against the class
`SSet.innerFibrations`; its recorded definition is `innerFibrations.llp`, and
`SSet.innerFibrations` is the right lifting property against inner horn inclusions.
Thus the theorem's conclusion renders the node's inner-anodyne clause without a
private duplicate of that notion.

The definition `simplexSpine (n : ℕ)` is a subcomplex of `Δ[n]`.  At degree `m`,
its object predicate is
`((SSet.stdSimplex.asOrderHom s) (Fin.last _)).val ≤
 (SSet.stdSimplex.asOrderHom s 0).val + 1`,
which is exactly the node's weakly increasing map condition
`σ(r) ≤ σ(0)+1`; `stdSimplex.asOrderHom` identifies an `m`-simplex with its
weakly increasing map `[m] → [n]`.  The `map` field proves closure under
precomposition: if `g` is the original monotone map and `h` is the ordinal map,
then `g (h (last)) ≤ g (last)` and `g 0 ≤ g (h 0)`, so the original endpoint
inequality implies the pulled-back endpoint inequality.  No additional hypothesis
is introduced.

The theorem is
`theorem simplexSpine_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions.{u} (simplexSpine.{u} n).ι`.
Here `n : ℕ` is the node's arbitrary integer with `n ≥ 0`; there are no omitted
hypotheses.  `innerAnodyneExtensions` unfolds to the LLP against every inner
fibration, and `innerFibrations` unfolds to the RLP against every
`Λ_i^m ⟶ Δ^m` with `0 < i < m`, matching each clause of the node.  The proof is
postponed as the named theorem's `sorry`; its docstring records all five DAG proof
steps, including the normalized pairing, stage equalities, horn intersections,
degreewise pushout gluing, lifting-class closure and identity cases `n = 0,1`.

Dependency declaration read: `SSet.Enhanced.coneCategory` and the module-level
helpers in `Sheaf.CategoryTheory.EnhancedDiagramsCones` (the standard simplex,
horn, and simplicial-set conventions) were read in full.  The Mathlib leaf
`SSet.innerAnodyneExtensions` was read in
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/Basic.lean`:
its docstring explicitly defines inner anodyne extensions as LLP against inner
fibrations, and `innerAnodyneExtensions.horn_ι` supplies the generating horn
case.  The proof dependency `lem-coef-lifting-class-closure` is the Mathlib
lifting-property closure result. Its source module
`Mathlib.CategoryTheory.MorphismProperty.LiftingProperty` is imported privately
for the proof plan. I read `llp`, `rlp`, `llp_isStableUnderRetracts`,
`rlp_isStableUnderRetracts`, `llp_isStableUnderCobaseChange`, and
`llp_isMultiplicative` in that module; no separate project module is needed.

Edge cases checked: for `n = 0` and `n = 1`, every simplex in `Δ[n]` satisfies
the endpoint inequality, so `simplexSpine n` is the full simplex and the inclusion
is an identity (covered by Mathlib's identity closure).  For `n = 2`, the nondegenerate simplices outside the spine are the long edge
`{0,2}` and the triangle `{0,1,2}`. They form one normalized pair attached along
the inner horn `Λ^2_1`; this checks the orientation and the `+1` bound.  Degenerate
simplices are retained because the predicate is stable under all precompositions,
and empty degree components are allowed.  The inequality uses `.val` and ordinary
natural-number addition, avoiding modular `Fin` addition while expressing the
same endpoint inequality.

Searches made:

- `msearch.py ... leanfinder "The inclusion of the union of adjacent edges into the standard n simplex is inner anodyne"`: eight hits (`SSet.horn.ι`, `SSet.face_le_horn`, `SSet.horn`, `SSet.horn.edge`, `SSet.horn.faceι`, `SSet.horn.faceι_ι`, `SSet.boundary`, `SSet.horn_eq_iSup`), with no spine theorem.
- `msearch.py ... loogle "innerAnodyneExtensions, spine"`: zero hits.
- `msearch.py ... grep "innerAnodyneExtensions" AlgebraicTopology`: ten hits in
  `Inner/Basic.lean` and `Inner/PushoutProduct.lean`, giving primitives and product
  closure, with no spine theorem.
- `msearch.py ... leansearch "Every spine inclusion has the left lifting property with respect to all inner fibrations of simplicial sets"`: eight model-category/quasicategory hits, no exact result.
- Direct `rg` over `WeilConjectures`, shared `lean/Sheaf`, Mathlib, and `dag/lean_names_upstream.json` found no declaration of the node's theorem or of an equivalent `simplexSpine` subcomplex.  The only Mathlib `spine` declarations are path/strict-Segal constructions, not this subcomplex.

No `STATEMENT-DISPUTED` issue or node fault was found.  No new definition node or
dependency module is needed.

## Source and validation

Opened Kerodon [00JA](https://kerodon.net/tag/00JA) and
[00J6](https://kerodon.net/tag/00J6) online. The literal spine definition and
assertion (a) agree with the node. WANTED: archived copies of these sources.
The finite-subset proof plan in the docstring is the DAG's directed-line
specialization of the normalized-simplex horn filtration.

The theorem explicitly applies universe `u` to both the spine and inner-anodyne
property; no inferred independent universe or size restriction is introduced.
The auxiliary `simplexSpine` definition is listed in `lean.declarations` as part
of the notion introduced by this item, with real predicate data and a complete
proof of closure under operators. No other DAG node is stated.

## Worker revalidation of the earlier attempt

The dispatched worker reopened the current DAG node, its recorded dependency module,
Mathlib's standard simplex and horn declarations, inner-horn inclusions, inner
fibrations, inner-anodyne extensions, and lifting-class closure declarations. No
repair note exists at `coord/repair-notes/lem-cbc-spine-inner-anodyne.json`.
The earlier module and its statement signature need no change. The only postponed
proof remains `SSet.simplexSpine_innerAnodyne`; the subcomplex has explicit predicate
data and a complete closure proof, with no postponed data or unnamed `sorry`.
The earlier independent reading below is preserved as an earlier reader's record;
this worker does not claim a new independent second reading.

Fresh searches through the prescribed wrapper reproduced no exact match:

- LeanFinder, `The inclusion of the union of adjacent edges into the standard n
  simplex is inner anodyne`: eight hits, including `SSet.horn`, `SSet.horn_eq_iSup`,
  `SSet.horn_obj`, `SSet.S.IsUniquelyCodimOneFace`, `SSet.face_le_horn`,
  `SSet.stdSimplex.face`, `SSet.modelCategoryQuillen.J`, and
  `SSet.Subcomplex.PairingCore.type₂_simplex`; no matching theorem or spine subcomplex.
- Loogle, `"innerAnodyneExtensions", "spine"`: zero hits.
- Mathlib grep, `spine.*(anodyne|Anodyne)|[Aa]nodyne.*[Ss]pine|innerAnodyneExtensions`
  in `AlgebraicTopology`: ten hits, all inner-anodyne primitives or product results.
- LeanSearch, `Every spine inclusion has the left lifting property with respect to
  all inner fibrations of simplicial sets`: eight hits, all Quillen-model-category
  fibrations, Kan complexes or general lifting classes, with no exact match.
- Direct `rg` of `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `simplexSpine`, the node id, and spine/anodyne
  combinations: only a downstream proof-plan citation in
  `Sheaf.CategoryTheory.SimplicialCompositionSpine`. Broader spine searches found
  mapping-space composition helpers in the project and path/strict-Segal
  constructions in Mathlib. They do not supply this simplicial subset or theorem.

Kerodon 00JA and 00J6 were reopened online. The node and the Lean use the same
endpoint predicate and the same unrestricted inner-anodyne conclusion. All objects
are in the explicit arbitrary universe `u`; neither lifting class restricts its
source or target to quasicategories. The edge checks at n=0,1,2 and at degree zero
remain valid. The file compiles cleanly through `scompile.py` as both sandbox and
library module (1.4 seconds each), with no errors or warnings. The system command
`date -u +%F` returns 2026-10-16, which is retained as `lean.date` as required.

## Earlier second reading (a previous round; superseded)

Independent reading completed on 2026-10-17. I opened the node and its Lean
module, the statement and recorded module of `def-cbc-enhanced-diagrams-cones`,
and the Mathlib leaf `lem-coef-lifting-class-closure`. There is no repair note
for this item. I read the actual source at
[Kerodon 00JA](https://kerodon.net/tag/00JA), Example the project server, including its
definition and assertion (a), and the normalized-simplex filtration in
[Kerodon 00J6](https://kerodon.net/tag/00J6), Proposition the project server. The source is
Kerodon, not the unrelated Stacks tag 00JA; there is no Stacks .tex source
for this item. The example assumes only a nonnegative integer n, with no
ambient quasicategory hypothesis for assertion (a).

The following is my object/hypothesis/conclusion checklist, matched to Lean:

1. Small simplicial sets in the fixed universe: `SSet.{u}` is Mathlib's
   `SimplicialObject (Type u)`. The dependency module explicitly uses these
   Mathlib primitives, and the delivered file publicly imports that module.
   Verdict: the same category, with arbitrary bound universe `u`.
2. Every integer n at least zero: `(n : ℕ)` in both declarations ranges over
   exactly those integers. Verdict: no positive-dimension restriction or
   other hypothesis has been added.
3. The standard n-simplex: `(Δ[n] : SSet.{u})` is Mathlib's `uliftYoneda`
   standard simplex. I read `stdSimplex.asOrderHom` and `map_apply` in
   StdSimplex.lean: simplices are the monotone maps of finite ordinals and
   the operators are precomposition. Verdict: the dependency's exact object.
4. Its spine simplicial subset: `simplexSpine n : (Δ[n] : SSet.{u}).Subcomplex`
   has degree-m predicate
   `((stdSimplex.asOrderHom s) (Fin.last _)).val ≤
   (stdSimplex.asOrderHom s 0).val + 1`.
   `Fin.last _` is the last vertex of the degree, and `.val` uses ordinary
   natural-number arithmetic. This is precisely sigma(r) ≤ sigma(0)+1.
   The `map` proof uses monotonicity at both endpoints to verify closure
   under every precomposition. Verdict: exact predicate in all degrees,
   with real construction data and no hollow definition.
5. Inner fibrations: I opened InnerFibration.lean. Its
   `innerHornInclusions` uses all indices `0 < i < Fin.last (n+2)` in
   dimension `n+2`; these are exactly all inner horns, since dimensions
   zero and one have none. `innerFibrations := innerHornInclusions.rlp`.
   I also read `horn` in Horn.lean: its range-union predicate omits a vertex
   other than i, as the dependency requires. Verdict: all inner fibrations,
   without any Kan or quasicategory assumption on source or target.
6. Inner anodyne means LLP against every such fibration:
   `innerAnodyneExtensions.{u} := innerFibrations.llp`. In LiftingProperty.lean,
   `llp` quantifies over arbitrary source, target and map in this category;
   `HasLiftingProperty` in LiftingProperties/Basic.lean requires a lift of
   every commutative square. Verdict: the full diagonal-filler conclusion,
   with the same order of quantification as the node.
7. The specified inclusion is inner anodyne:
   `innerAnodyneExtensions.{u} (simplexSpine.{u} n).ι`.
   I read `Subcomplex.ι := Subfunctor.ι`: this is the canonical inclusion
   of the actual constructed subcomplex. Verdict: precisely the node's
   conclusion, with no extra conjunct or chosen comparison map.

Edge cases: for n=0 and n=1 all monotone maps satisfy the endpoint bound,
so the subcomplex is full; the theorem includes both cases. For n=2 the
excluded nondegenerate simplices are exactly the long edge and triangle,
so the inclusion is the inner horn with missing index one. At degree zero
the bound always holds, including the last vertex n. Degenerate simplices
of arbitrarily high degree are included according to the same predicate.
The ambient simplicial indexing has nonempty ordinals only, as in the
source; no augmented degree -1 is being silently discarded. Empty cell
attachment lists in the proof plan use identity closure. Empty source or
target simplicial sets are not excluded from the lifting quantifiers.
There are no schemes, rings, characteristic restrictions or external index
sets in this statement. Both the spine and the morphism property explicitly
use `u`, so no additional universe equality is imposed.

My independent searches used different wording from the worker's:

- `msearch.py NJ lem-cbc-spine-inner-anodyne leanfinder
  "Every finite string of consecutive one-simplices embeds inner anodynely
  in its ordinal nerve"`: eight hits, including nerve strict-Segal facts,
  `stdSimplex.isoNerve`, and `StrictSegal`; no matching inclusion theorem.
- `msearch.py NJ lem-cbc-spine-inner-anodyne leansearch
  "The subcomplex of the standard simplex generated by consecutive edges
  is inner anodyne"`: eight hits, including `Subcomplex.ofSimplex`,
  `stdSimplex.face`, and `PairingCore.IsInner`; these are construction and
  pairing infrastructure, not the spine or its theorem.
- Direct `rg` for spine, consecutive/adjacent edges, inner anodyne and
  lifting combinations over Mathlib, `WeilConjectures`, shared `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no matching declaration. I opened
  Path.lean's `spine` and `stdSimplex.spineId`, and StrictSegal declarations:
  those give paths or reconstruction in strict Segal sets, not this
  subcomplex or its LLP. The project's `spineRestriction` uses fixed-vertex
  mapping-space products and cites this item as a proof dependency; it does
  not define the inclusion. No duplicate notion or theorem was found.

I checked all five proof steps against the node and source: ordered-image
factorization and span filtration; normalized/unnormalized pairing;
dimension filtration and its endpoint equalities; the exact index-one horn
intersection and degreewise pushout, including empty lists; and finite
pushout/composition/identity closure. The theorem docstring carries each
step. I read the recorded Mathlib closure declarations for retracts,
cobase change and multiplicativity; the private proof import is appropriate.
The helper definition belongs to the notion this item explicitly introduces
and is listed in `lean.declarations`. There are no new definition nodes,
dependency repairs, statement corrections, or citer-audit obligations.

No mathematical or Lean mismatch was found. I left the module and node
unchanged and appended this independent reading. A direct check confirms
`lean.statement` is verbatim the theorem signature, the node differs from
the base only in `lean`, no line of Lean exceeds 100 characters, and the
only `sorry` is the named main theorem. All variables and universes are
explicitly bound. Compilation through `scompile.py` of the delivered file
passed cleanly, both as sandbox and library module (1.3 seconds each),
with no errors or warnings. The first compile invocation used a relative
path from the read-only checkout and failed to locate the sandbox file;
rerunning with the absolute sandbox path produced that clean result.

## Second reading by NJ

I read the node statement, its Kerodon source, the dependency declaration, and the
Lean module item by item. The node introduces: small simplicial sets and the
standard simplex/horn conventions from `def-cbc-enhanced-diagrams-cones`; an
arbitrary integer `n ≥ 0`; the standard simplex `Δⁿ`; its spine sub-simplicial-set;
inner fibrations defined by the right lifting property against every inner horn;
and inner anodyne maps defined by the left lifting property against every inner
fibration. The conclusion is that the canonical spine inclusion is inner anodyne.

The Lean renders these items as follows. `SSet.{u}` and `(Δ[n] : SSet.{u})` are
the recorded Mathlib simplicial-set and standard-simplex objects. `n : ℕ` covers
exactly the nonnegative integers. `simplexSpine n` is a genuine subcomplex with
degree-`m` predicate `σ(last) ≤ σ(0) + 1`, expressed through
`stdSimplex.asOrderHom` and ordinary natural-number values; its `map` field proves
closure under every precomposition. `innerFibrations` and
`innerAnodyneExtensions` are the recorded Mathlib lifting classes, and the theorem
concludes `innerAnodyneExtensions.{u} (simplexSpine.{u} n).ι`. Verdict: every
object, hypothesis, quantifier, and conclusion clause agrees with the node; no
stronger or weaker assumption is present.

The source is Kerodon 00JA, Example the project server(a), and its literal definition and
assertion agree with the node. The proof-plan docstring follows Kerodon 00J6:
ordered-image factorization, span filtration, normalized/non-normalized pairing,
the index-one inner-horn pushout filtration, and closure under pushouts,
composition, and identities. No statement correction, dependency repair, or new
definition node was needed. The dependency declaration
`SSet.Enhanced.coneCategory` was read in its source module; the lifting-class
dependency is the Mathlib `llp`/`rlp` closure interface used by the proof plan.

Edge cases checked: for `n = 0` and `n = 1`, the endpoint inequality includes
every simplex, so the inclusion is an identity; for `n = 2`, the excluded long
edge and triangle are attached through the inner horn `Λ²₁`; degree-zero and
degenerate simplices satisfy the same predicate; empty attachment families use
identity closure. The explicit universe `u` is shared by the simplicial set and
the morphism property, with no unintended universe restriction. There are no
scheme, ring, characteristic, or external-index hypotheses.

I searched Mathlib, `WeilConjectures`, shared `lean/Sheaf`, and
`dag/lean_names_upstream.json` using alternate spine/anodyne/lifting queries and
found no existing equivalent definition or theorem. The only nearby matches are
generic horns, lifting classes, paths, and strict-Segal constructions. The module
compiled via `scompile.py` with no errors or warnings beyond the permitted
postponed theorem proof. No mismatch was found and no Lean or node content was
changed in this second reading.
