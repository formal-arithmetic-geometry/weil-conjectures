## Worker report

The module `Sheaf.AlgebraicTopology.TwistedArrowBoundaryFiltration` states
`SSet.TwistedArrowBoundary.horn_filtration`, with its proof `sorry`. Four fully defined
helpers in the same namespace spell out the notions introduced inline in this node:
`IsBasic`, `priority`, `IsPrioritized`, and `stage`. All five declarations are listed in
`lean.declarations`; all carry this node's source and blueprint tag. There are no new
independent notions, dependency repairs, statement changes, or disputed statements.

Source read: https://kerodon.net/tag/03JW, proof of Proposition the project server, especially the
basic-subset conditions, priority/cardinality ordering, the inverse-image definition of
the attaching intersection, and its deleted-face argument. The node agrees with it.

Hypothesis and clause correspondence:

* `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`.
* The ordered vertex set `{0,...,2n+1}` is `Fin (2 * n + 2)` with its usual order.
  Every subset is represented by a `Finset` of this finite type. Its spanned face is
  Mathlib's `stdSimplex.face`, including its degeneracies.
* The first basic condition is `∀ v ∈ S, v.val ≤ n`. The second is
  `∃ i : Fin (n + 1), ∀ v ∈ S, v.val ≠ i.val ∧ v.val ≠ 2*n+1-i.val`.
  These are joined by `∨` in `IsBasic`, together with `S.Nonempty`, exactly expressing
  the node’s basicness predicate on its nonempty domain.
* The priority is `(S.filter (fun v ↦ n < v.val)).sup (fun v ↦ 2*n+1-v.val)`.
  A nonbasic subset has an upper-block vertex. Reflection sends these vertices exactly
  to the indices `i ∈ {0,...,n}` whose partners belong to `S`, so this supremum is the
  stated maximum. The definition's default zero on empty upper blocks is never used
  for a nonbasic subset and excludes no priority-zero case.
* `IsPrioritized n S` means `S.Nonempty`, `¬ IsBasic n S`, and membership of the
  priority in `S`, expressed by `∃ v ∈ S, v.val = priority n S`.
* `S : Fin m → Finset (Fin (2*n+2))` enumerates the paper's `S_1,...,S_m`, with
  paper index `a.val+1`. `hS : Function.Injective S` excludes repetitions and
  `hEnum` says its range is exactly all prioritized nonbasic subsets, with none omitted
  and no extra sets. Thus these two binders are precisely enumeration data.
* `hPriority : Monotone (fun a ↦ priority n (S a))` is nondecreasing priority.
  `hCard` requires nondecreasing cardinality only for ordered indices of equal priority.
  Nothing restricts ties of equal priority and cardinality.
* `stage n S q` is the union of all basic faces and the faces `S a` with `a.val < q`.
  In particular `stage n S 0` is `K_0`; `stage n S m` is `K_m`; the previous stage
  when attaching `S a = S_(a+1)` is `stage n S a.val`.
* The increasing identification `S_q = {j_0 < ... < j_d}` is quantified as
  `e : Fin (d + 1) ≃o ↥(S a)`. The equation specifying `j_k = pr(S_q)` is
  `(e k).val.val = priority n (S a)`. These binders name the identification and index
  from the node, rather than restricting the class of enumerations. Such an order
  isomorphism exists for every nonempty finite subset, and the priority belongs to
  each listed subset by `hEnum`, so the equality is not vacuous.
* Mathlib's `stdSimplex.faceRepresentableBy (S a) d e`, followed by
  `stdSimplex.isoOfRepresentableBy`, gives the increasing isomorphism from `Δ[d]`
  onto `Δ^(S a)`. Its hom composed with `(stdSimplex.face (S a)).ι` is the canonical
  ambient inclusion. Taking `.preimage` of the previous stage along this composite
  expresses the intersection transported through that isomorphism. The result is
  exactly `horn d k`. This is also the source's formula `L = sigma_q⁻¹ K_(q-1)`.
* `∃ last : Fin m, last.val + 1 = m ∧ S last = Finset.univ` says `S_m = V_n`,
  including the assertion that the list has a final entry. Finally
  `stage n S m = ⊤` says `K_m = Δ^(2n+1)`.

Dependency declarations and imports:

* The only statement/proof dependency, `def-cbc-enhanced-diagrams-cones`, records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` and `SSet.Enhanced.coneCategory`, together
  with its helper declarations. I read its node and the recorded declaration's full
  signature and docstring. Its module explicitly uses Mathlib's simplicial primitives
  directly; this item uses those primitive simplex/horn clauses, not its cone object.
  The recorded module is the sole public import and covers the proof dependency too.
* `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`: `SSet.stdSimplex`,
  `SSet.stdSimplex.face`, `SSet.stdSimplex.faceRepresentableBy`, and
  `SSet.stdSimplex.isoOfRepresentableBy`. I read the full definitions and docstrings.
* `Mathlib.AlgebraicTopology.SimplicialSet.Horn`: `SSet.horn`, with its range-missing
  definition, and `SSet.horn_eq_iSup`, which confirms the union-of-other-faces convention.
* `Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex`: `SSet.Subcomplex.preimage`;
  suprema in its complete lattice express all of the stated unions.

Edge cases checked before finalizing:

* Empty subsets are excluded from `IsBasic` and `IsPrioritized`, exactly as in the source;
  their face is bottom and no empty subset can be listed.
* `m = 0` is not silently excluded by an extra hypothesis: the exact enumeration
  hypotheses already rule it out because the full vertex set is prioritized.
* Priority zero and the possible outer horn `k = 0` are retained. There is no added
  inner-horn assumption or restriction on face dimension. No vertex identification
  is chosen from an unproved existence assertion.
* For `n = 1,...,5`, an executable bitmask enumeration checked every nonempty subface
  at every attachment under three shuffled tie orders, sorted only by priority and
  cardinality. Counts were 4, 13, 40, 121, 364. At every attachment membership in the
  old union equaled omission of some vertex other than the priority, and every final
  face was full with final union all nonempty subsets. This includes the smallest
  allowed `n`, the full face itself, and the missing facet, not just other facets.
* `universe u` is explicit, all simplicial objects use `SSet.{u}`, and
  `set_option autoImplicit false` forbids implicit unbound variables. There is no
  restriction on the simplicial universe. No file-local notation or instance is used.

Searches for an existing statement:

* `msearch.py leanfinder`, query `Prioritized paired subsets of a simplex and horn
  intersection filtration`: eight hits, including `SSet.horn`, `Subcomplex.Pairing`,
  `Subcomplex.PairingCore`, and `SSet.boundary`. None states this priority-specific
  filtration or its intersection identity.
* `msearch.py loogle`, query `SSet.horn_eq_iSup`: the generic horn union identity,
  not the claimed ordering-dependent attaching intersection.
* `msearch.py leansearch`, query `Paired faces of a simplex ordered by priority attach
  along horns`: generic horn faces, inclusions, and `horn_eq_iSup`; no exact match.
* `msearch.py grep`, query `priority|prioritized|boundaryFiltration|pairedFace`, in
  `AlgebraicTopology/SimplicialSet`: zero hits. Direct `rg` in that Mathlib directory
  with these names and `TwistedArrowBoundary|horn_filtration` also found no match.
* `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `pairedFace|boundaryFiltration|prioritized|PairedFace` and the item id found no exact
  statement. The prescribed upstream `grep -rn` for the item id found no hits.
* Declaration-name searches in `dag/lean_names_upstream.json`, upstream and project
  Lean found no collision for `TwistedArrowBoundary`. A broader `horn_filtration`
  search found `twistedArrow_join_horn_filtration` and
  `exists_initial_prism_horn_filtration`. I read both modules: the former concerns a
  different paired-deletion domain (Kerodon 03JT) and existential inner-horn pushouts;
  the latter concerns a product of simplices (Kerodon 01DN). Neither is this statement.

Validation: the prescribed `scompile.py Q123` invocation compiled this module cleanly,
both in its sandbox and at its library module path, within the 60-second limit. The
only postponed proof is the named theorem above; all auxiliary definitions have real
data. The delivery dry run is the final validation step; an independent reader supplies
the second reading before delivery.


## Second reading by Q123

I opened the node, Kerodon Tag 03JW (Proposition the project server), the dependency node
`def-cbc-enhanced-diagrams-cones`, and the complete Lean module. The source introduces
nonempty subsets of `[2n+1]`, calls a subset basic when (a) it lies in the lower block or
(b) misses a paired set, defines `K₀` as the union of their faces, defines priority as the
largest reflected upper-block index, lists all prioritized nonbasic subsets by priority and
cardinality, identifies each attaching intersection with the horn omitting the priority
vertex, and ends with the full subset as `S_m` and `K_m` equal to the full simplex.
The Lean renders these items as follows.

* The objects `n ≥ 1`, `m`, and the ordered vertex set `V_n` are `(n : ℕ)`,
  `hn : 1 ≤ n`, `m : ℕ`, and `Fin (2 * n + 2)` with its native order. A subset is
  `Finset (Fin (2 * n + 2))`, and its face is `stdSimplex.face`.
* `IsBasic n S` is now `S.Nonempty ∧ ((∀ v ∈ S, v.val ≤ n) ∨
  ∃ i : Fin (n + 1), ∀ v ∈ S, v.val ≠ i.val ∧ v.val ≠ 2 * n + 1 - i.val)`, exactly the
  two source alternatives on the nonempty domain. `stage n S q` takes the supremum of
  all such basic faces and all `stdSimplex.face (S a)` with `a.val < q`, rendering `K_q`.
* `priority n S` is the finite supremum of `2 * n + 1 - v.val` over upper-block vertices
  of `S`, which is the source maximum on nonbasic subsets. `IsPrioritized n S` adds
  nonemptiness, nonbasicness, and membership of this priority in `S`.
* `hS : Function.Injective S` and `hEnum : ∀ T, (∃ a, S a = T) ↔ IsPrioritized n T`
  give an exact enumeration of all prioritized nonbasic subsets. `hPriority` is the
  nondecreasing priority condition, and `hCard` is the nondecreasing-cardinality condition
  for ordered equal-priority pairs; no tie-breaking hypothesis beyond the source is added.
* For each `a`, `d`, increasing order equivalence `e : Fin (d + 1) ≃o ↥(S a)`, and
  `k` with `(e k).val.val = priority n (S a)`, the displayed equality uses
  `Subcomplex.preimage` along `stdSimplex.isoOfRepresentableBy ... ≫
  (stdSimplex.face (S a)).ι` and states the source identity
  `σ_q⁻¹ K_(q-1) = Λ^d_k`. The quantification over every such increasing `e` is
  equivalent to the unique vertex-order identification in the source.
* The final conjunct `∃ last : Fin m, last.val + 1 = m ∧ S last = Finset.univ` renders
  `S_m = V_n`, and `stage n S m = ⊤` renders `K_m = Δ^(2n+1)`.

The edge cases are covered. The empty subset is excluded from `IsBasic` and
`IsPrioritized` exactly as in the source; its face would be bottom in any event. `n = 0`
is excluded only by the source hypothesis `hn`, while `n = 1` is allowed. The hypotheses
force `m > 0` because the full subset is prioritized, so the final `Fin m` witness is not
vacuous. Priority zero, outer horns (`k = 0`), and the full subset are not excluded. The
explicit universe `u` is propagated to every simplicial object; no universe equality or
finite-set restriction beyond the source is imposed.

I repeated the existing-definition searches in Mathlib, upstream `WeilConjectures`, and
project `lean/Sheaf` using `TwistedArrowBoundary`, `horn_filtration`, `IsPrioritized`,
`priority`, and `boundary filtration`; only the distinct generic declarations
`twistedArrow_join_horn_filtration` and `exists_initial_prism_horn_filtration` appeared.
LeanSearch, Loogle, and LeanFinder returned only generic `stdSimplex`, face, horn, and
`Subcomplex.preimage` declarations. Neither is this priority-specific statement, so the
module remains necessary and has no duplicate notion.

The only mismatch found was the worker's extension of `IsBasic` to the empty subset. I
changed `IsBasic` to include `S.Nonempty` and made `IsPrioritized` explicitly nonempty;
this makes the helper declarations match the source domain exactly while preserving the
node's theorem signature and all conclusions. The module recompiles cleanly with
`scompile.py`; no other mismatch, extra hypothesis, weakened clause, hollow definition,
or unbound variable remains.

Resumed second reading, 2026-10-17: retained the review above and rechecked the current
module, node, dependency record and source definitions against Kerodon 03JW, proof of
Proposition the project server (https://kerodon.net/tag/03JW), especially the basic conditions,
priority/cardinality ordering, inverse-image intersection, and deleted-facet argument.
The existing nonemptiness repair is present in both predicates; no further Lean or
natural-language statement change was needed. The sandbox node differs from the current
shared node only in its authorized `lean` field. The historical `created.item` names the
parent that introduced this node and is correctly retained.

I independently read `stdSimplex.face` (degreewise image containment),
`faceRepresentableBy` and `isoOfRepresentableBy` (the increasing face inclusion),
`Subcomplex.preimage` (degreewise inverse image), and `horn`/`horn_eq_iSup` (omission of
some vertex other than `k`). These confirm that the displayed equation is equality of
simplicial subcomplexes, including degeneracies, rather than only their vertex sets.
The enhanced-diagrams dependency explicitly delegates these primitives to Mathlib, so
its unrelated cone-category construction introduces no additional hypothesis here.
There are no new nodes, dependency repairs, or statement corrections to audit.

Repeated searches used LeanFinder with "Union of paired simplex faces ordered by
reflected upper vertex maxima intersects next face in a horn" (generic horn declarations
only), Loogle with `SSet.stdSimplex.faceRepresentableBy` (the already used ordered-face
primitive), and LeanSearch with "Finite filtration of a simplex using reflected vertex
pairs with a distinguished missing facet at each stage" (generic face, horn, and finite
simplicial-set declarations only). Direct `rg` over all Mathlib, upstream
`WeilConjectures`, project `lean/Sheaf`, and the upstream name inventory found no
`TwistedArrowBoundary`, `IsPrioritized`, `boundaryFiltration`, or `pairedFace` duplicate.
The other two horn-filtration modules were opened and concern different initial
subcomplexes, so neither supplies this statement. Edge cases remain as checked above;
empty schemes, coefficient characteristics and zero objects do not occur in this purely
finite simplicial statement.

The prescribed `scompile.py Q123` check compiled the unchanged delivered module cleanly
at both sandbox and library paths (1.4 s and 1.5 s). An independent text check confirmed
that `lean.statement` is verbatim the theorem signature and all Lean lines have at most
100 characters. There is exactly one postponed proof, the named `horn_filtration`, and
all four auxiliary definitions have explicit data.
