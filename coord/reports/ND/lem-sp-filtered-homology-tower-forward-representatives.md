## Worker report

Restated `CategoryTheory.filteredHomology_tower_forward_representatives` in
`Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives`, with its proof
`by sorry`. The natural-language statement is unchanged. Its docstring gives all
three proof steps, including the connecting-map calculation and cancellation of I.
No new node and no statement correction is required. The only additional node
file is the lean-only dependency repair described below.

Hypotheses and conclusion, checked against the node:

- An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`;
  object and morphism universes remain independent.
- The finite filtered cochain complex `(K,F)` is `U` in the full subcategory of
  `FilteredObject (CochainComplex C ℤ)` satisfying `W.filtration.IsFinite`.
  Thus `K = U.obj.obj` and `F = U.obj.filtration`; no bound or normalization of
  the finite filtration is added.
- `X` is precisely `filteredHomologyExactCouple K F`. Its canonical tower `T`
  is precisely `X.cycleBoundaryTower`, never an arbitrary tower.
- The families of maps into graded cycles and tower cycles are `j` and `tQ`.
  Their domains are `F.complexCycles p (p+q) (s+1)`. The equations `hj` and
  `ht` respectively assert `j ≫ iCycles = complexCycles.arrow` and
  `tQ ≫ T.Z.arrow ≫ filteredHomologyEIso.hom = j ≫ homologyπ`, for every
  natural `s` and integer `p,q`.
- `I` has exactly the page-D to initial-D types in the node. `hI0` is its
  identity normalization, `hIs` its successor inclusion formula, and `hImono`
  its monicity at all pages and bidegrees. No chosen I is substituted.
- The fixed parameters are `(s : ℕ) (p q : ℤ)`. The printed expressions
  `p + (s+1)` and `q - (s+1) + 1` equal the node's `p' = p+s+1` and
  `q' = q-s`; hence their sum is `p+q+1`. Set `P = 2*p'+q'` and `Q = -p'`.
  There are no implicit let-bound abbreviations in the signature.
- `e` has source `X.D P Q` and target `(X.pageCouple s).D (P-s) (Q+s)`.
  Its only constraint `he` is precisely `e ≫ I s (P-s) (Q+s) = X.alphaIter s P Q`.
- `(A : C)` is arbitrary. The maps `a`, `b`, and `x` have respectively the
  degree-`p+q` filtration-step, degree-`p'+q'` filtration-step cycle, and
  filtered cycle-subobject codomains specified in the node.
- `ha` says `a` followed by the ambient filtration inclusion and the ambient
  differential is `b` followed by its cycle inclusion and ambient filtration
  inclusion. `hx` says `x ≫ complexCycles.arrow` equals `a` followed by the
  graded quotient projection in degree `p+q`. No epimorphism assumption on
  `a`, `b`, or `x` is imposed.
- The left side of the conclusion is exactly `x ≫ tQ ≫ T.projection ≫ page.f`
  followed by equality transport from `(2*p+q+2,-p-1)` to `(P-s,Q+s)`.
  The right side is exactly `b ≫ homologyπ`, equality transport to `X.D P Q`,
  and `e`. The target is the derived D object; no composition with g occurs.
  The transports are proved by integer arithmetic and congruence, without
  supplying an extra object equality as a hypothesis.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `CategoryTheory.DecreasingFiltration`; its `F` and `F_succ_le` fields.
  `WeilConjectures.CategoryTheory.Filtration` supplies `FilteredObject` and
  `DecreasingFiltration.IsFinite`; `Sheaf.CategoryTheory.Filtration` supplies
  the existing `step` and `gradedPiece` compatibility accessors used by the
  recorded subquotient module.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexCycles`, `complexQuotientπ`, and the source
  representative construction. The cycles are subobjects of the graded
  degree term, and projections are genuine cokernel projections.
- `Sheaf.CategoryTheory.FilteredHomologyExactCouple`:
  `filteredHomologyExactCouple`, `filteredHomologyEIso` (repaired here).
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`:
  `BigradedExactCouple.CycleBoundaryTower`, `cycleBoundaryTower`, `alphaIter`;
  the tower's `Z`, `projection`, `cycleLift_comm`, and `projection_succ` fields.
- `WeilConjectures.CategoryTheory.ExactCouple`:
  `BigradedExactCouple`, `pageCouple`, `derivedDInclusion`, and page `f`.
- The proof-only dependency `Sheaf.CategoryTheory.FilteredHomologyCoupleData`
  supplies `filteredHomologyD/E/Alpha/F/G` and `filteredStep_shortExact`.
  The dependency repair additionally uses the named six-clause theorem
  `filteredHomologyCouple_exact` from
  `Sheaf.CategoryTheory.FilteredHomologyCoupleExactness`.

Edge cases checked: `s=0` leaves the target bidegree `(2*p+q+2,-p-1)`;
`p'=p+1`, `q'=q`, and the connecting class has degree `p+q+1`. There is
no division or predecessor of a natural number. Negative `p` and `q` are
allowed, and all degree identities hold for them. A zero complex, zero A,
or zero representatives is permitted. A filtration step that is top or
bottom introduces no excluded case. Finite filtrations need not have any
specified bound. No smallness, countable-coproduct, or element-category
hypothesis is imposed: the construction is degreewise in an arbitrary
abelian category, as in the general part of Stacks Tag 012K.

Searches performed with `msearch.py ND` (full tool records in searches.jsonl):

- LeanFinder: `forward map of a filtered homology derived exact couple on representatives`.
  Eight hits, on homology-sequence input maps and opcycles; none gives the
  normalized filtered forward-map identity into a derived D object.
- Loogle: `CategoryTheory.ShortComplex.ShortExact.δ_eq`.
  Exactly this Mathlib theorem exists; it gives the initial connecting-class
  calculation, not the filtered tower statement with I and e.
- Mathlib grep: `derived.*forward|alphaIter`, subdirectory `Algebra/Homology`.
  No hits.
- LeanSearch: `The forward map in a derived exact couple sends a filtered cycle representative to the homology class of its differential`.
  Eight hits concerning short-complex cycles, homology projection/maps and
  opcycles; none states this theorem.
- `rg` of upstream `WeilConjectures` and the shared `lean/Sheaf` for
  `filteredHomology_tower_forward_representatives`, its blueprint id,
  `filteredHomologyExactCouple`, and `filteredHomologyEIso`, plus the
  upstream name index. The filtered homology definitions occur in the
  recorded side modules; no upstream matching forward theorem exists.
  The only shared reference to the withdrawn forward theorem is the
  differential consumer's proof docstring.

Source read: `literature/stacks-project/homology.tex`, section-filtered-complex
(Tag 012K), the Z/B formulas and representative differential immediately
before Lemma 12.24.2, including the general-category construction; and
lemma-derived-exact-couple (Tag 011R), which defines the forward map by the
restriction of f. Missing/stale local upstream modules were read through
`scompile.py --source` as required. There is no repair-notes file for this item.

Validation: `scompile.py ND lem-sp-filtered-homology-tower-forward-representatives`
compiled both delivery modules separately in dependency order, including their
library imports, with no errors or warnings (each Lean invocation approximately
one second). The repaired dependency is thereby tested in the actual consumer
statement that previously could not elaborate. The item has one named sorry
(the requested theorem). The repaired definition module contains no sorry.

## Dependency modules

`def-sp-filtered-homology-exact-couple`: the current published compiled binding
prints `filteredHomologyExactCouple K F := sorry`, and its `filteredHomologyEIso`
also has sorry data. Consequently the D object cannot reduce to
`H^(P+Q)(F^(-Q)K)`, so the consumer's homology-to-D equality transport cannot be
typed. The archived module uses `BigradedExactCouple.ofShifted`, but that name
is absent from the current compiler API. The current upstream
`BigradedExactCouple` constructor instead takes precisely the two terms, three
maps, and six proof fields required by this node.

The replacement module, at the dependency's existing module path, constructs
that structure directly with the existing `filteredHomologyD`,
`filteredHomologyE`, `filteredHomologyAlpha`, `filteredHomologyF`, and
`filteredHomologyG`. All six proof fields refer to the corresponding clauses
of the already named `filteredHomologyCouple_exact`. Its E isomorphism is the
actual equality isomorphism given by `-(-p)=p` and `2*p+q-p=p+q`. Thus all data
is explicit; no arbitrary couple, isomorphism, map, or existence choice is
introduced. The original namespace, declaration names, signatures, and
mathematical objects are retained. Only this dependency node's lean field
changes; its source, statement, dependency lists, and proofs are unchanged.

## Second reading by ND

Fresh dispatcher-started repair reader, 2026-10-17. I did not author the
retained Lean modules. I opened the saved item and dependency node, both Lean
files, the current base node records, the dependency implementations, and
Stacks `homology.tex` at `lemma-derived-exact-couple` and
`section-filtered-complex`. This is a new reading of the retained packet,
independent of its original author; no additional agent was started.

The current return names immutable head `e3d09cefd4b7`: index transport goals,
a metavariable declaration, and the missing second reading. The saved packet
already contains revised transports and this clause-by-clause reading. I opened
both node statements, both Lean files, the dependency implementations and the
source passages again for this retry. I checked every hypothesis and conclusion
as follows.

| Node hypothesis or clause | Lean rendering and finding |
| --- | --- |
| An arbitrary abelian category C | `(C : Type u) [Category.{v} C] [Abelian C]`; `u` and `v` are independently declared, with no smallness restriction. |
| A finite filtered cochain complex U=(K,F) | `U : ObjectProperty.FullSubcategory (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)`; `K` is `U.obj.obj`, `F` is `U.obj.filtration`. The existing `IsFinite` means `∃ n m : ℤ, F.F n = ⊤ ∧ F.F m = ⊥`, so it adds no normalization at degree zero. |
| X is its homology exact couple | Every occurrence is `filteredHomologyExactCouple U.obj.obj U.obj.filtration`, with the concrete dependency construction inspected below. |
| T is the canonical tower of X | Every tower term is `X.cycleBoundaryTower`, not a new tower parameter. I read its recorded upstream definition and the `CycleBoundaryTower` projection fields using `scompile.py --source`. |
| Families j_s and t_s out of the filtered cycle subobjects | `j` and `tQ` quantify over all natural `s` and integer `p,q`; each source is `F.complexCycles p (p+q) (s+1)`. Their respective targets are graded-complex cycles and `X.cycleBoundaryTower.Z s (2*p+q) (-p)`. |
| j_s followed by iCycles is the subobject inclusion | `hj` is exactly `j s p q ≫ (F.gradedPiece p).iCycles (p+q) = (F.complexCycles p (p+q) (s+1)).arrow`. |
| t_s followed by the tower inclusion and EIso is j_s followed by homology projection | `ht` has exactly this composite with `(filteredHomologyEIso K F p q).hom` on the left and `(F.gradedPiece p).homologyπ (p+q)` on the right. The direction of EIso is initial E to graded homology. |
| The page-D to initial-D maps I_n | `I : ∀ (n : ℕ) (P Q : ℤ), (X.pageCouple n).D P Q ⟶ X.D P Q`. The indices on both D objects agree. |
| I_0=id, the successor inclusion formula, and monicity | `hI0`, `hIs`, and `hImono` assert precisely these three conditions for all pages and bidegrees. `hIs` composes `derivedDInclusion P Q` with `I n P Q` in that order. |
| Fixed natural s, integer p,q, and the shifted indices | `(s : ℕ) (p q : ℤ)` are unrestricted. The expanded terms use `p+(s+1)` and `q-(s+1)+1`, equal to p'=p+s+1 and q'=q-s. Hence n'=p'+q'=p+q+1. No hidden let binder is used. |
| The map e and its equation | Its domain is `X.D P Q` at `P=2*p'+q'`, `Q=-p'`, and its codomain is `(X.pageCouple s).D (P-s) (Q+s)`. `he` is `e ≫ I s (P-s) (Q+s) = X.alphaIter s P Q`. Reading `alphaIter` confirms exactly these endpoints. |
| An arbitrary test object A and representatives a,b,x | `(A : C)` is arbitrary; `a` targets `(F.step p).X (p+q)`, `b` targets `(F.step p').cycles n'`, and `x` targets `F.complexCycles p (p+q) (s+1)`. None is assumed epi or mono. |
| da is the ambient inclusion of b | `ha` first includes `a` in K, then applies `K.d (p+q) n'`; the other side includes `b` through `iCycles n'` and `(F.step p').arrow.f n'`. Since n'=p+q+1, this is the requested differential. |
| x's graded inclusion equals a's graded projection | `hx` uses the cycle-subobject `.arrow` on the left and `(F.complexQuotientπ p (p+1) (by omega)).f (p+q)` on the right. This is the canonical cokernel projection, not an arbitrary map. |
| The left composite in the conclusion | `x ≫ tQ s p q ≫ T.projection s (2*p+q) (-p) ≫ (X.pageCouple s).f (2*p+q) (-p) ≫ eqToHom ...`. The page f has bidegree (+2,-1). Its target `(2*p+q+2,-p-1)` equals `(P-s,Q+s)` by integer arithmetic. |
| The right composite in the conclusion | `b ≫ (F.step p').homologyπ n' ≫ eqToHom ... ≫ e`. Unfolding D gives `H^(P+Q)(F^(-Q)K)`; `-Q=p'` and `P+Q=n'`, exactly the two equalities proved by `congrArg₂` and `omega`. |
| Equality before applying g | The conclusion equates those two morphisms into `(X.pageCouple s).D (P-s) (Q+s)`. There is no final g, so the statement retains the stronger D-valued identity specified by the node. |

Dependency reading: `def-sp-filtered-homology-exact-couple` requires exactly
`filteredHomologyD/E/Alpha/F/G` and six named exactness proofs, plus the
index-equality E isomorphism. I read `FilteredHomologyCoupleData.lean`:
D is `(F.step (-Q)).homology (P+Q)`; E is graded-piece homology at the same
indices; Alpha is homology of the filtration inclusion; F is the successive
short-exact-sequence connecting map; G is homology of the graded projection.
The delivered `filteredHomologyExactCouple` assigns all five fields directly
to these declarations. Its proof fields select, in order, the six clauses of
`filteredHomologyCouple_exact`. I opened that theorem's complete signature:
its three zero composites and three image/kernel equalities have precisely
the fields' types, including the type-zero index transports. Thus the repair
changes the representation, not the mathematical couple, and uses no new
existential choice or sorry data. `filteredHomologyEIso` is the actual
`eqToIso` of `-(-p)=p` and `2*p+q+(-p)=p+q`, as the dependency node specifies.
Both declarations are listed in its Lean record, whose note explains the
unusable old interface. The consumer's D transport exercises the repaired
reducible construction; its clean compile validates that repair in use.

I checked `s=0`: `(P-s,Q+s)=(2*p+q+2,-p-1)`, n'=p+q+1, and he uses the
zero iterate, without natural-number subtraction. Negative p and q remain
valid integers. Zero A, zero K, zero maps, and filtration steps equal to top
or bottom are allowed. There is no countable-coproduct assumption: the
source's general abelian-category construction follows its initial
exposition with exact countable sums. The finite filtration assumption is
exactly the node's, even though this local identity needs no bound in its
signature. Source Tag 011R induces f' from f; source Tag 012K sends a
representative to its differential. These agree with the retained proof
plan and the conclusion's sign and degree.

Findings and changes: the retained theorem renders every hypothesis and the
D-valued conclusion without a mismatch. Its left transport identifies the two
page-D indices by integer arithmetic; its right transport unfolds
`filteredHomologyExactCouple`, `BigradedExactCouple.D`, and `filteredHomologyD`
and applies `congrArg₂` to the filtration-step and homology-degree equalities.
The concrete dependency abbreviation makes that unfolding possible. The initial
E isomorphism rewrites `neg_neg` and the homology-degree equality. These are
index transports, not extra hypotheses or postponed mathematical proofs.
There is exactly one named sorry, the item's theorem, and no sorry data in
either delivered definition. The successful actual-consumer compilation below
checks that no unsolved transport goals or metavariable declaration remains.

## Previous repair validation

This retry first read the retained report and ran the prescribed unchanged-packet
`deliver2.py --no-push`. It compiled both modules separately, passed preflight,
and reported `OK (dry run)` at `e6031c642a`. Following the dispatcher's explicit
instruction for a passing saved packet, the Lean files are retained byte for
byte. The report now addresses the current immutable-head return directly and
retains the independent second reading above.

The node copies were rebased onto the current shared node metadata, retaining
only their saved `lean` records. In particular the obsolete sandbox-only
`blueprint` edit was removed: the current return requests transport and report
repairs, and stage 2 owns neither that protected field nor the base metadata.
No statement, dependency list, source or proof is changed. This packet contains
no metadata correction and no new node.

Final self-check: the recorded signatures match the Lean text verbatim; both
modules bind universes and variables explicitly with `autoImplicit false`; all
Lean lines have at most 100 characters; the definition module uses the existing
five data declarations and all six named exactness clauses. Zero page, negative
integer indices, zero objects and unrestricted finite-filtration bounds remain
covered. Both modules are rechecked with `scompile.py` in dependency order and
the final report/node packet is checked again by the delivery dry run before
pushing.

## Repair of immutable head 6a6552a05f94

The current return is incremental DAG validation:
`blueprint.from.node lem-sp-filtered-homology-tower-differential is not a blueprint node`.
Unlike the previous retries, this repair changes the sandbox blueprint provenance
in direct response to that return. The previous repair-validation section is
historical; its statement that this packet has no metadata correction no longer
applies to this retry.

The corrected `blueprint.from.node` is `thm-sp-spectral-object-yields`.
I opened the current imported blueprint statement and proof, especially Steps
1–3 (the initial connecting map, derived pages, and representative description),
and the complete current parent record. The corrected `via` starts with
`lem-sp-filtered-homology-tower-differential`, then retains every entry of that
parent's `via` in order. Thus the helper stays in the provenance path while the
endpoint is an actual imported blueprint theorem. `is` stays null and `same_as`
stays empty. This changes no mathematical statement, dependency or Lean file.

`blueprint_refs.py search lem-sp-filtered-homology-tower-forward-representatives`
returned zero imported blueprint matches. Its `ancestor` query returns None
because the old `created.item` uses a module name, not a DAG id; I did not change
that unrelated historical field. The source-based parent provenance supplies
the precise existing ancestor and full path. The imported theorem has
`blueprint_kind` and `blueprint.is` equal to its own id.

Tool limitation found during this repair: the prescribed `deliver2.py` reads
existing node copies, but its delivery whitelist consists of `lean` and
`stmt_deps` (plus the mathematical statement-correction fields when applicable).
It excludes `blueprint` even for a returned delivery explicitly requesting its
repair. Its code says differing protected fields are "NOT delivered (not yours
to change)" and retains the base value. Per AGENTS.md §3/§6 and tools/README.md,
I do not patch or bypass shared tooling. The corrected sandbox node remains
available for the maintainer; the next dry run tests whether the wrapper still
discards this authorized repair.

Self-check with both node records and Lean files open: the recorded signatures
are verbatim substrings of the files. Universes u and v and every binder are
explicit, both modules set `autoImplicit false`, and maximum line lengths are
90 and 95. The exact-couple data is concrete and has no sorry; its six proof
fields use the named exactness theorem. The item has its one named theorem
sorry and complete proof docstring. All previously checked zero-page, negative
index, zero-object and unrestricted finite-filtration cases remain admitted.

Repair validation result: the initial saved-packet dry run passed at
`76a3657b0c`. After the sandbox provenance correction, the second dry run
compiled both modules cleanly and passed preflight at `2c85994476`, but printed:

```
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Thus that temporary commit still contains the exact inherited ancestry defect
named in the current return. The authorized correction is complete in the
sandbox but cannot be included by the prescribed tool. Pushing that generated
packet would repeat the unresolved return. No push was attempted, no shared
file or tool was edited, and no direct Git command was run. This is a delivery
wrapper failure to carry the specifically requested metadata repair, requiring
the maintainer to permit this field on the returned item or normalize the base
provenance. BLOCKED is reported with this concrete diagnostic.

## Retained-packet retry on 2026-10-18

I inspected this retained report and first started the required saved-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
The sandbox already contains the source-based blueprint correction requested
by the immutable-head return. I retained both Lean modules and both node copies.
A fresh comparison with the current shared records finds only the two `lean`
changes and the item's corrected `blueprint`; there is no mathematical statement
change or additional metadata change. Both recorded signatures are exact
substrings of their Lean files, whose maximum line lengths are 90 and 95.

I reread the current blueprint theorem `thm-sp-spectral-object-yields` and the
parent `lem-sp-filtered-homology-tower-differential` record. The parent itself
correctly names that imported theorem and supplies the provenance path retained
by the sandbox correction. The published main base still names the non-blueprint
helper as the item's `blueprint.from.node`. The current `deliver2.py` still
excludes `blueprint` from the fields it copies for an existing node (lines
114–117), so the previous tool failure has not been repaired. Editing that shared
wrapper or bypassing its field policy is outside this worker's authorized scope.
The concrete retry log is `dry-run-retry-20261018.log` in the sandbox.

Fresh validation result: the prescribed wrapper compiled both modules cleanly
and passed server preflight at temporary commit `702b59e414`, but again printed
`NOT delivered (not yours to change): ['blueprint']`. Thus the saved provenance
repair is still discarded, and the generated packet retains the exact defect
returned by the maintainer. No push was attempted. The sandbox retains the
complete corrected packet; this retry reports BLOCKED for the unchanged delivery
tool failure, not for a missing Lean declaration or failed mathematical repair.

## Final retry 2026-10-18

The required direct `scompile.py ND lem-sp-filtered-homology-tower-forward-representatives`
run completed for both delivery modules, including the private overlay, preliminary,
sandbox, and library paths, with no errors or warnings. A fresh prescribed
`deliver2.py ... --no-push` retry was then started twice; each remains in its
server SSH compile session waiting for a shared slot (the second remained there
for over eight minutes without producing a compiler diagnostic), so it was
terminated. The previously completed dry run is recorded above. The sandbox
blueprint correction remains the requested source-based provenance repair, but
the current delivery wrapper excludes `blueprint` from its copied fields.


## Dispatcher retry: immutable head 6a6552a05f94

Started by inspecting this saved report, then ran the prescribed unchanged-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It completed successfully at temporary commit `d48dee01a0`: both delivery modules
compiled cleanly and server preflight passed. However, its exact diagnostic was:

```
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
OK (dry run): commit d48dee01a0 passes the preflight and compiles; nothing pushed
```

I inspected the current wrapper: its existing-node whitelist is still `lean`
and `stmt_deps`, plus statement-correction fields when the statement changes.
It does not copy `blueprint`. The base node still names the non-blueprint helper
`lem-sp-filtered-homology-tower-differential`; the sandbox instead names the
imported theorem `thm-sp-spectral-object-yields`, with the helper and its complete
parent provenance path in `via`. I reread that parent and the actual current
main-20261015 imported theorem. The sandbox correction addresses the returned
provenance defect without changing a mathematical statement or dependency.

The required self-check passed: both recorded signatures occur verbatim in
their Lean files; both explicitly disable autoImplicit and declare universes u
and v; maximum line lengths are 90 and 95. The dependency module contains no
sorry data or postponed theorem. The item's single named theorem has its
requested sorry and complete proof docstring. Both modules and node records
are retained unchanged, apart from this report addition.

The dry-run success does not repair the immutable-head return: the wrapper's
explicit field-discard diagnostic establishes that its generated packet still
omits the required correction. No tool or shared source was edited, no direct
Git command was run, and no defective packet was pushed. The corrected sandbox
packet is ready, but delivery remains BLOCKED by the wrapper excluding the
specifically returned blueprint field. The maintainer must allow that repair
through the wrapper or normalize the base provenance.

## Current repair retry: immutable head 9028820e1954

I first inspected the retained packet and ran the prescribed unchanged-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It compiled both delivery modules cleanly and passed server preflight at
`8fad58cbbd`, printing `OK (dry run)`. The wrapper again explicitly reported
that it did not deliver the differing `blueprint` field. The sandbox already
contains the source-based correction to `thm-sp-spectral-object-yields`, with
`lem-sp-filtered-homology-tower-differential` followed by that parent's complete
provenance path in `via`. The current shared record still has the non-blueprint
helper as its endpoint. The wrapper's existing-node field whitelist still
excludes `blueprint`, so this passing preflight does not establish that the
returned ancestry fault has been fixed in the generated commit.

The current dispatch explicitly instructs that a passing saved packet be
retained, self-checked, and pushed. Following that instruction, this retry
retains both Lean modules and both sandbox node copies and proceeds to the
prescribed delivery wrapper; it does not edit or bypass the wrapper. The
maintainer must carry the sandbox provenance correction into the base or
permit its inclusion through the wrapper before incremental DAG validation
can accept that inherited endpoint.

Required self-check completed with both node statements and both modules open:
the saved signatures occur verbatim in their files; universes u and v and all
variables are explicit, and both modules disable autoImplicit. Maximum line
lengths are 90 and 95. The exact-couple definition supplies real data from the
five recorded homology constructions and named exactness proofs, with no sorry
data. The item's one theorem retains its requested sorry and full proof
docstring. The arbitrary abelian category, finite filtration, normalized monic
I maps, representative equations, and equality into the derived D object are
unchanged. Zero page, negative integer indices, zero objects and arbitrary
finite-filtration bounds remain covered. No statement correction or new node
is introduced. Only this report is updated for the current retry.

## Current repair retry: immutable head ead35beb1e97

The required first saved-packet dry run passed at `7a052a6eb0`, compiling
both modules cleanly and passing server preflight. I retained the saved Lean
files and node copies as instructed for a passing packet. Comparison with
the current shared records finds only their two Lean records and the item's
already corrected blueprint provenance. The sandbox endpoint is the genuine
blueprint node `thm-sp-spectral-object-yields`; its via path starts with
`lem-sp-filtered-homology-tower-differential` and retains that parent's full
path. I opened both current parent records and the Stacks source passages.

The self-check confirms verbatim recorded signatures, explicit universes u
and v, `autoImplicit false`, and maximum line lengths of 90 and 95. The
dependency supplies the five concrete homology constructions and six named
exactness proofs; its data contains no sorry. The consumer retains its one
named theorem sorry, full proof docstring, every hypothesis and its identity
into derived D. Zero page, negative indices, zero objects and arbitrary finite
filtration bounds remain admitted. No mathematical statement changed.

The wrapper still prints `NOT delivered (not yours to change): ['blueprint']`.
Consequently preflight success does not resolve the returned ancestry defect
in the generated commit, although the requested correction is present in the
sandbox. Following the dispatcher's explicit instruction to push a passing
retained packet, this retry proceeds through the prescribed delivery wrapper.
The maintainer must apply the recorded sandbox provenance correction to the
base or permit the wrapper to carry it before incremental DAG validation can
accept that endpoint. No shared tool or source is edited or bypassed.

## Current repair retry: immutable head 9de3691091e4

The required first retained-packet dry run passed at `5ffb232b23`, compiling
both delivery modules cleanly and passing server preflight. I opened the two
saved Lean files and their complete node statements and compared the saved
node copies with the current shared records. The dependency differs only in
`lean`; the item differs in `lean` and the previously corrected `blueprint`.
The Lean files and node copies are retained as explicitly instructed for a
passing saved packet.

Self-check: both recorded signatures are verbatim in their Lean files, all
universes and variables are explicit, both files disable autoImplicit, and
the maximum line widths are 90 and 95. The concrete exact couple uses the
five recorded homology data declarations and six named exactness clauses;
its data contains no sorry. The item's named theorem retains its requested
sorry, complete proof docstring, all representative and normalization
hypotheses, and the identity into derived D before applying g. Zero page,
negative indices, zero objects, and unrestricted finite-filtration bounds
remain covered. No mathematical statement, dependency list, or Lean file
is changed in this retry.

The saved provenance endpoint is `thm-sp-spectral-object-yields`, whose
`blueprint.is` is its own id and whose `blueprint_kind` is `theorem`. Its
via path starts with `lem-sp-filtered-homology-tower-differential` followed
by that parent's full current path. The shared item still names the helper
as its endpoint. The wrapper explicitly prints that differing `blueprint`
is NOT delivered. Thus its passing preflight does not resolve the returned
incremental-DAG ancestry defect in the generated commit. Following the
current dispatch's explicit passing-packet instruction, this retry pushes
through the prescribed wrapper. The maintainer must carry the sandbox's
corrected provenance into the base or permit the wrapper to include it.
No shared source or tool is edited or bypassed.

## Current repair retry: immutable head 370e6b5444d7

I inspected the retained packet and ran the required first unchanged-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It compiled both modules cleanly and passed server preflight at `324f2cab42`.
Following the dispatcher's explicit passing-packet instruction, I retain both
Lean files and node copies and deliver through the prescribed wrapper.

The self-check reopened both modules and both complete node statements.
Both recorded signatures occur verbatim in the files; all universes and
variables are explicit, both modules disable autoImplicit, and maximum line
widths are 90 and 95. The dependency's concrete five data fields and six
named exactness clauses contain no sorry data. The item's one named theorem
retains its full proof docstring, representative equations, monic normalized
I maps, and the D-valued identity before g. Zero page, negative integer
indices, zero objects and arbitrary finite-filtration bounds remain covered.
No mathematical statement, dependency list or Lean file changes in this retry.

Comparison with the current shared records finds only the two Lean records
and the item's retained blueprint correction. I reread Steps 1–3 of the
current main-20261015 blueprint proof of `thm-sp-spectral-object-yields`.
That genuine blueprint node is the corrected endpoint; the via path retains
`lem-sp-filtered-homology-tower-differential` and the parent's complete path.
The current base still names the non-blueprint helper as its endpoint.

The dry run explicitly printed `NOT delivered (not yours to change):
['blueprint']`. Inspection of the current wrapper confirms its existing-node
field whitelist still excludes blueprint. Thus the sandbox repairs the
returned ancestry defect, but preflight success does not establish that this
repair reaches the generated commit. As explicitly instructed for a passing
saved packet, this retry proceeds to delivery. The maintainer must carry the
sandbox correction into the base or permit its inclusion through the wrapper
before incremental DAG validation can accept that endpoint. No shared source
or tool was edited or bypassed, and no direct Git command was run.

## Current repair retry: immutable head 10d05ed7cc79

I first inspected the saved report and ran the prescribed retained-packet dry
run. It compiled both modules cleanly and passed server preflight at temporary
commit `5c49d97586`. As explicitly instructed for a passing saved packet, I
retain the saved Lean files and node copies and proceed through `deliver2.py`.

The self-check opened both Lean files and the item statement. Both recorded
signatures occur verbatim, both modules disable autoImplicit, and universes u
and v and all variables are explicit. Maximum line widths are 90 and 95.
The exact-couple definition has concrete data from the five recorded homology
constructions and the six named exactness clauses, with no sorry data. The
consumer retains its single named theorem sorry, full proof docstring, all
representative equations and normalized monic I hypotheses, and its identity
into derived D. Zero page, negative indices, zero objects, and unrestricted
finite-filtration bounds remain admitted. No mathematical statement or Lean
file changes in this retry.

The comparison with current shared records finds only the two Lean records
and the item's saved blueprint correction. I rechecked the complete parent
provenance: the saved endpoint `thm-sp-spectral-object-yields` is a genuine
blueprint theorem, and the via path is the differential helper followed by
that helper's complete current path. This addresses the returned ancestry
fault in the sandbox. The wrapper nevertheless printed `NOT delivered (not
yours to change): ['blueprint']`, so its passing preflight does not establish
that the correction reaches the generated commit. Following the dispatcher's
explicit passing-packet instruction, delivery proceeds through the prescribed
wrapper; the maintainer must normalize the base provenance or permit that
field through the wrapper for incremental DAG validation to accept it. No
shared source or tool is edited or bypassed, and no direct Git command is run.

## Current repair retry: immutable head 300cb3f4780e

The prescribed first saved-packet dry run passed at `34d040e3cd`, compiling
both modules cleanly and passing server preflight. Following the explicit
passing-packet retry instruction, this attempt retains the saved Lean files
and node copies and delivers through the prescribed wrapper.

Self-check reopened both Lean files and both complete node statements. Both
recorded signatures occur verbatim; universes u and v and all variables are
explicit, both modules disable autoImplicit, and maximum line widths are 90
and 95. The exact-couple definition supplies its five concrete data fields
and six named exactness clauses without sorry data. The consumer retains
its one named theorem sorry and full proof docstring, all representative
and normalized monic I hypotheses, and the equality into derived D before g.
Zero page, negative integer indices, zero objects, and arbitrary finite
filtration bounds remain admitted. No mathematical statement, dependency
list, or Lean file changes in this retry.

Comparison with the current shared records finds only the two Lean records
and the item's saved blueprint correction. The saved endpoint is the genuine
blueprint theorem `thm-sp-spectral-object-yields`. I reopened its complete
record and the differential helper's record; the saved via path is precisely
that helper followed by its complete current provenance path. This repairs
the reported ancestry defect in the sandbox.

The dry run nevertheless prints `NOT delivered (not yours to change):
['blueprint']`. Inspection confirms that the current wrapper's existing-node
field whitelist still excludes blueprint. Thus passing preflight does not
establish that the provenance repair reaches the generated commit. The
maintainer must apply the saved correction to the base or permit the wrapper
to carry it for incremental DAG validation to accept that endpoint. As the
current dispatch explicitly requires delivery of a passing retained packet,
this attempt proceeds through the wrapper. No shared source or tool is
edited or bypassed, and no direct Git command is run.

## Current repair retry: immutable head 72d877d80936

I inspected the saved report first and ran the prescribed unchanged-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It passed server preflight and compiled both modules cleanly at `fc053e814d`.
Following the explicit passing-packet retry instruction, I retain the saved
Lean modules and node copies and deliver through the prescribed wrapper.

Self-check reopened both modules and both full node statements. Both recorded
signatures occur verbatim; universes u and v and all variables are explicit,
both modules disable autoImplicit, and maximum line widths are 90 and 95.
The exact couple supplies concrete data from the five homology constructions
and six named exactness clauses, without sorry data. The consumer has exactly
one named theorem sorry, its complete proof docstring, all representative and
normalized monic I hypotheses, and the identity into derived D before g.
The zero page, negative indices, zero objects, and arbitrary finite-filtration
bounds remain admitted. No mathematical statement or Lean module changes.

Comparison with the current shared records finds only the two Lean records
and the retained blueprint correction. The saved endpoint is the genuine
blueprint theorem `thm-sp-spectral-object-yields`, whose blueprint.is equals
its own id. The saved via list is the differential helper followed by that
helper's complete current provenance path. This addresses the returned
ancestry fault in the sandbox.

The wrapper still explicitly prints that the differing blueprint field is
NOT delivered. Inspection confirms that its existing-node field whitelist
excludes blueprint, so its passing preflight does not establish that the
provenance correction reaches the generated commit. The maintainer must
normalize the base provenance or permit this correction through the wrapper
for incremental DAG validation to accept that endpoint. The current dispatch
explicitly requires pushing a passing retained packet, so this retry proceeds
through deliver2.py. No shared source or tool is edited or bypassed, and no
direct Git command is run.


## Current repair retry: immutable head b7a6bdc7f1eb

I first inspected the saved report and ran the prescribed retained-packet
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It passed server preflight and compiled both modules cleanly at `3123d710ef`.
The current dispatch explicitly instructs retention and delivery when this
first saved-packet dry run passes; both Lean files and node copies are retained.

Self-check reopened both Lean files and both full node statements. Both recorded
signatures occur verbatim; universes u and v and all variables are explicit,
both modules disable autoImplicit, and maximum line widths are 90 and 95.
The exact couple supplies the five concrete homology constructions and six
named exactness clauses, without sorry data. The consumer retains its one
named theorem sorry, full proof docstring, every representative and normalized
monic I hypothesis, and the identity into derived D before g. Zero page,
negative indices, zero objects and arbitrary finite-filtration bounds remain
admitted. No mathematical statement, dependency list or Lean module changed.

Comparison with the current shared records finds only the two Lean records
and the retained blueprint correction. I opened the current main-20261015
blueprint theorem and both provenance records: the saved endpoint is the
genuine blueprint theorem `thm-sp-spectral-object-yields`; the via list is
`lem-sp-filtered-homology-tower-differential` followed by that parent's complete
current path. This corrects the reported ancestry defect in the sandbox.

The dry run nevertheless prints `NOT delivered (not yours to change):
['blueprint']`. Reading deliver2.py confirms its existing-node field whitelist
excludes blueprint. Thus the generated commit still requires the maintainer
to normalize the base provenance or permit this authorized correction through
the wrapper before incremental DAG validation can accept it. Following the
explicit passing-packet instruction, this retry proceeds through deliver2.py.
No shared file or tool was edited or bypassed, and no direct Git command ran.

## Current repair retry: immutable head b209824bd03f

I inspected the retained report and ran the required first saved-packet dry run.
It compiled both delivery modules cleanly and passed server preflight at
`81a7a1bef7`. Following the explicit passing-packet instruction, the saved Lean
modules and node copies are retained and delivered through the prescribed wrapper.

The self-check reopened both modules and node statements. Both recorded signatures
occur verbatim, universes u and v and all variables are explicit, and both modules
disable autoImplicit. Maximum line widths are 90 and 95. The exact-couple module
has concrete data and no sorry; the consumer retains its one named theorem sorry,
complete proof docstring, representative equations, normalized monic I hypotheses,
and equality into derived D. The zero page, negative indices, zero objects and
arbitrary finite-filtration bounds remain covered. No mathematical statement,
dependency list or Lean module changes in this retry.

The dependency node differs from the current shared record only in lean; the
item differs in lean and its retained blueprint correction. I verified that
`thm-sp-spectral-object-yields` is a genuine blueprint node and that the saved
via list equals the differential helper followed by that parent's complete
current via list. This is the correction requested by the immutable-head return.

The wrapper nevertheless explicitly printed `NOT delivered (not yours to change):
['blueprint']`. Its existing-node whitelist still excludes blueprint, so this
passing dry run does not establish that the provenance repair reaches the
commit. The maintainer must normalize the base provenance or permit the wrapper
to include this correction before incremental DAG validation can accept it.
The current dispatch explicitly requires delivery after a passing saved-packet
dry run, so this retry proceeds through deliver2.py. No shared source or tool
was edited or bypassed, and no direct Git command was run.

## Current repair retry: immutable head 5b090b83c023

I first inspected the saved report and ran the required retained-packet dry run.
It passed server preflight and compiled both modules cleanly at `ce54fefa83`.
Following the explicit passing-packet instruction, I retain both saved Lean
modules and node copies and deliver through the prescribed wrapper.

Self-check reopened both modules and both complete node statements. Both recorded
signatures occur verbatim; universes u and v and all variables are explicit,
both modules disable autoImplicit, and maximum line widths are 90 and 95.
The exact couple supplies five concrete homology data fields and six named
exactness clauses, with no sorry data. The consumer retains its single named
theorem sorry, full proof docstring, every representative and normalized monic I
hypothesis, and the equality into derived D before applying g. Zero page,
negative indices, zero objects and arbitrary finite-filtration bounds remain
covered. No mathematical statement, dependency list or Lean module changed.

Comparison with current shared records finds only the two Lean records and the
retained blueprint correction. The saved endpoint `thm-sp-spectral-object-yields`
is a genuine blueprint theorem whose blueprint.is equals its id; the via list
is the differential helper followed by that helper's full current ancestry.
This addresses the returned ancestry fault in the sandbox.

The dry run still explicitly prints that the differing blueprint field is
NOT delivered (not yours to change). Its passing preflight therefore does not
establish that the provenance correction reaches the generated commit. The
maintainer must normalize the base provenance or permit this correction through
the wrapper for incremental DAG validation to accept the endpoint. The current
dispatch explicitly requires delivery of a passing retained packet, so this
retry proceeds through deliver2.py. No shared source or tool is edited or
bypassed, and no direct Git command is run.


## Current repair retry: immutable head 2a40dfc145b9

I inspected the saved report first and ran the prescribed retained-packet dry run.
It compiled both modules cleanly and passed server preflight at `93f3c364e1`.
Following the explicit instruction for a passing saved packet, I retain its
Lean modules and node copies and deliver through the prescribed wrapper.

The self-check reopened both modules and both node statements. Both recorded
signatures occur verbatim, every universe and variable is explicitly bound,
and both modules disable autoImplicit. Maximum line widths are 90 and 95.
The exact-couple construction supplies actual data and named exactness proofs;
the consumer retains its single named theorem sorry, complete proof docstring,
all representative equations and normalized monic I hypotheses, and its
D-valued identity before applying g. Zero page, negative indices, zero objects,
and unrestricted finite-filtration bounds remain admitted.

The saved blueprint endpoint is `thm-sp-spectral-object-yields`, verified to
be a genuine blueprint node. Its via list is exactly the differential helper
followed by that helper's complete current ancestry. This corrects the returned
provenance defect in the sandbox without changing the mathematical statement.

The wrapper still prints `NOT delivered (not yours to change): ['blueprint']`.
Its existing-node whitelist at deliver2.py line 116 excludes that field, so
passing preflight does not certify that this correction reaches the generated
commit. The maintainer must normalize the base provenance or authorize the
wrapper to include the correction for incremental DAG validation to accept it.
The current dispatch explicitly requires pushing a passing saved packet; this
retry follows that instruction. No shared source or tool is edited or bypassed,
and no direct Git command is run.


## Current repair retry: immutable head 7ff31d0b674e

I inspected the retained report and ran the required first saved-packet dry run.
It passed server preflight and compiled both modules cleanly at `4fe6337d3c`.
Following the explicit passing-packet instruction, I retain the saved Lean modules
and node copies and deliver through the prescribed wrapper.

Self-check reopened both modules and both node statements. Both recorded signatures
occur verbatim; universes u and v and all variables are explicit, and both modules
disable autoImplicit. Maximum line widths are 90 and 95. The exact-couple definition
supplies concrete homology data and named exactness proofs without sorry data.
The consumer retains its single named theorem sorry, full proof docstring, every
representative equation and normalized monic I hypothesis, and the equality into
derived D before g. Zero page, negative indices, zero objects and arbitrary
finite-filtration bounds remain covered. No mathematical statement or Lean file
changes in this retry.

Compared with current shared records, only the two Lean records and the saved
blueprint correction differ. The saved endpoint `thm-sp-spectral-object-yields`
is a genuine blueprint node, verified by its blueprint.is field; the saved via
list is exactly the differential helper followed by that parent's complete
current via list. This corrects the returned ancestry defect in the sandbox.

The wrapper explicitly prints `NOT delivered (not yours to change): ['blueprint']`.
Passing preflight therefore does not establish that the provenance correction
reaches the generated commit. The maintainer must normalize the base provenance
or permit the wrapper to carry this correction before incremental DAG validation
can accept it. The current dispatch explicitly requires delivery after a passing
saved-packet dry run, so this attempt proceeds through deliver2.py. No shared
source or tool is edited or bypassed, and no direct Git command is run.


## Current repair retry: immutable head bf7653162193

I inspected the retained report and ran the prescribed saved-packet dry run.
It passed server preflight and compiled both modules cleanly at `a66e3fefde`.
Following the explicit passing-packet instruction, the saved Lean modules and
node copies are retained and delivered through the prescribed wrapper.

The self-check reopened both Lean files and compared both full node records
with current shared records. Both recorded signatures occur verbatim; both
modules disable autoImplicit, and universes u,v and variables are explicit.
Maximum line widths are 90 and 95. The exact-couple construction has concrete
homology data and named exactness proofs; the consumer has only its requested
named theorem sorry and retains all representative equations, normalized monic
I hypotheses, and the identity into derived D before g. Zero page, negative
indices, zero objects and arbitrary finite-filtration bounds remain allowed.
No mathematical statement or Lean module changes are needed in this retry.

The dependency differs from current main only in lean. The item differs only
in lean and the saved blueprint correction. I verified that the corrected
endpoint `thm-sp-spectral-object-yields` has blueprint.is equal to its id,
and that the saved via path is exactly the differential helper followed by
that helper's full current via path. The base still incorrectly names the
non-blueprint differential helper as the endpoint.

The dry run explicitly printed `NOT delivered (not yours to change):
['blueprint']`. The wrapper's existing-node whitelist excludes this field,
so its passing preflight does not establish that the ancestry correction
reaches the generated commit. The maintainer must normalize the base
provenance or permit the wrapper to include this correction before incremental
DAG validation can accept that endpoint. The dispatch explicitly instructs
pushing after a passing saved-packet dry run; this retry follows that instruction.
No shared source or tool was edited or bypassed, and no direct Git command ran.

## Current repair retry: immutable head 411e203db3ad

I inspected the retained report, ran the required saved-packet dry run, and
reopened both complete Lean modules and node statements for the self-check.
Both recorded signatures occur verbatim, both modules disable autoImplicit,
and all universes and variables are bound. Maximum line widths are 90 and 95.
The exact couple has concrete data and named exactness proofs with no sorry;
the consumer retains its sole named theorem sorry, proof docstring, all
representative and normalized monic I hypotheses, and the identity into D.
Zero page, negative indices, zero objects and arbitrary finite bounds remain
admitted. The retained Lean modules and mathematical statements are unchanged.

For the returned provenance fault, the sandbox endpoint is the genuine blueprint
node thm-sp-spectral-object-yields; its via list is the differential helper
followed by that helper's complete current ancestry. The dependency differs
from the shared record only in lean; the item differs in lean and this retained
blueprint correction. The delivery wrapper's existing-node whitelist excludes
blueprint, so a passing dry run alone does not establish that the correction
reaches the commit. This is the same wrapper limitation recorded above; no
shared file or tool was edited or bypassed. The dispatch explicitly requires
retaining and pushing the saved packet if its initial dry run passes.

## Repair retry: immutable head 46cd9b282ad3 (2026-10-18)

Inspected the retained report first, then ran the prescribed saved-packet command
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
Both modules compiled cleanly and server preflight accepted generated commit
`61da7031b2`. However, the same run explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

The required repair is present in the sandbox: blueprint.from.node names the
genuine blueprint node `thm-sp-spectral-object-yields`, and blueprint.from.via
is `lem-sp-filtered-homology-tower-differential` followed by that helper's
complete current ancestry. Compared with the current shared node, the only
item changes are lean and this blueprint correction; the dependency differs
only in lean. Reading deliver2.py confirms that its existing-node whitelist
excludes blueprint and preserves the base's invalid provenance in the generated
commit. Thus its passing preflight does not validate the specific returned fault.

Self-check reopened both complete Lean modules and the item's natural statement.
Both recorded signatures occur verbatim, universes and variables are explicit,
autoImplicit is false, maximum widths are 90 and 95, and the exact-couple
definition contains concrete data without sorry. The consumer retains its named
theorem sorry, proof docstring, representative equations, normalized monic I
hypotheses and D-valued equality. No Lean or mathematical-statement change is
needed for this metadata return.

BLOCKED: the prescribed delivery tool discards the correction requested by the
maintainer. The launcher-files instruction expressly prohibits patching or
bypassing this tool and requires reporting a wrong gate as BLOCKED. No shared
file or launcher tool was edited, no direct Git command ran, and no unchanged
packet was re-pushed as a purported repair. The saved correction is retained
for delivery after the wrapper admits it or the maintainer repairs the base.


## Confirmed tool blocker on retained-packet retry (2026-10-18)

Read this saved report before running the prescribed first dry run. The command
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`
compiled both retained modules and returned dry-run commit `4b8988c492`, but also
explicitly reported that `blueprint` was NOT delivered (not yours to change).
Thus the dry run passes its narrower preflight while omitting the repair for
immutable head `46cd9b282ad3`; this does not resolve the returned DAG diagnostic.

Compared both sandbox node copies against the current shared records: the
dependency differs only in lean; the item differs only in lean and blueprint.
Verified that the corrected endpoint thm-sp-spectral-object-yields has
blueprint.is equal to its id, and that the saved via path is exactly the
non-blueprint differential helper followed by its current full via path.
Both Lean signatures occur verbatim in their records, both modules explicitly
disable autoImplicit, and their maximum line widths remain 90 and 95.

Read the wrapper's existing-node whitelist: it admits lean and stmt_deps,
plus statement-correction fields conditionally, but never blueprint. No
sandbox-only change can make that gate transmit the required provenance
correction. The launcher-files instruction requires reporting this wrong
gate as BLOCKED and forbids patching or bypassing the wrapper. The corrected
packet is retained; no shared file or launcher script was edited, and no
unchanged delivery was pushed as a purported repair. The maintainer must
correct the base provenance or the tool must admit the requested correction.


## Retained-packet repair diagnostic (2026-10-18, dry run 397e249bfe)

Inspected the saved report first and ran the prescribed initial saved-packet
dry run. Both Lean modules compiled and server preflight passed at commit
`397e249bfe`. The wrapper nevertheless explicitly reported:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared the saved node records with the current shared records: the dependency
differs only in lean; the item differs only in lean and the required blueprint
repair. Confirmed that thm-sp-spectral-object-yields is a genuine blueprint
node, and that the saved via path is the differential helper followed by its
complete current ancestry. The base still names that non-blueprint helper
as its endpoint, exactly the fault returned for head 46cd9b282ad3.

Self-check reopened both complete Lean modules and their node statements. Both
recorded signatures occur verbatim, both modules disable autoImplicit, universes
and variables are explicit, and maximum line widths are 90 and 95. The exact
couple has concrete data without sorry; the consumer has its single requested
named theorem sorry and complete proof docstring. No mathematical change is
needed for this provenance repair.

Reading deliver2.py confirms that its existing-node field whitelist excludes
blueprint. The passing dry run therefore omits the repair and cannot resolve
the returned incremental DAG validation failure. Under the launcher-files
instruction, this wrong gate is a tool blocker: no launcher file or shared
source was modified, no tool was bypassed, and no unchanged packet was pushed
as a purported repair. The corrected packet is retained until the wrapper
admits the correction or the maintainer fixes the base provenance.


## Current saved-packet retry (2026-10-18, dry run 64c1802a2c)

Read the saved report and ran the required initial saved-packet dry run before
making any change. Both modules compiled and server preflight passed, but the
wrapper again printed the concrete refusal:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Reopened both complete Lean modules and compared both node copies with the
current shared records. Both signatures occur verbatim, all universes and
variables are explicit, autoImplicit is disabled, and maximum line widths are
90 and 95. The dependency differs only in lean. The item differs in lean and
the required blueprint correction. Verified that the saved endpoint
thm-sp-spectral-object-yields is a genuine blueprint node and its via list
is the differential helper followed by that helper's complete current ancestry.
The shared base still has the returned invalid non-blueprint endpoint.

Read the current deliver2.py existing-node whitelist: blueprint is excluded
and cannot reach the generated commit through any authorized sandbox change.
Thus the dry run's OK certifies compilation and its narrower preflight, while
its explicit refusal leaves the returned incremental DAG defect unresolved.
The instruction to report a wrong launcher gate as BLOCKED applies. No
launcher or shared file was edited, no gate was bypassed, and no unchanged
packet was pushed as a repair. The corrected packet remains in the sandbox;
the tool must transmit the requested blueprint correction or the maintainer
must normalize the base provenance.


## Saved-packet self-check and delivery (2026-10-18)

Read the saved report first and ran the prescribed initial dry run. Commit
`0eafcbd008` passed server preflight and both module compilations. Reopened
both complete Lean modules and both node statements: both recorded signatures
occur verbatim; autoImplicit is disabled, universes and variables are explicit,
and maximum line widths are 90 and 95. The exact couple supplies concrete data
and named exactness proofs; the consumer retains its named theorem sorry, full
proof docstring, representative equations, normalized monic I hypotheses, and
D-valued identity. Zero page, negative indices, zero objects and arbitrary
finite-filtration bounds remain allowed. The retained mathematical statements
and Lean modules need no change.

Compared the node copies with the current shared records. The dependency differs
only in lean; the item differs in lean and the saved provenance correction.
Verified that the corrected endpoint thm-sp-spectral-object-yields is a genuine
blueprint node, and the via path is the differential helper followed by that
helper's complete current ancestry. The current base still names the
non-blueprint differential helper as its endpoint.

The wrapper explicitly reports that blueprint is NOT delivered (not yours to
change); its existing-node whitelist still excludes that field. The returned
provenance fault therefore remains unresolved by the generated packet, despite
its passing compile and preflight. The final dispatcher instruction explicitly
says to retain a saved packet that passes its first dry run, finish the
self-check, then push with deliver2.py. This retry follows that instruction,
with this limitation recorded for independent review. No shared file or
launcher tool was edited or bypassed, and no direct Git command was run.


## Repair diagnostic for immutable head d69fa739b776 (2026-10-18)

Read the retained report first and ran the prescribed saved-packet dry run.
The captured run in dry-run-current-repair.log compiled both modules cleanly
and passed server preflight at commit 0d44fb37cd. It also explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared both saved node copies with the current shared records. The dependency
differs only in lean; the item differs only in lean and the required blueprint
repair. Verified that the saved endpoint thm-sp-spectral-object-yields has
blueprint.is equal to its id, and that the saved via list is the differential
helper followed by that helper's complete current ancestry. The shared base
still names the non-blueprint differential helper as the endpoint, exactly the
returned defect. Reopened both complete Lean modules: both recorded signatures
occur verbatim; autoImplicit is disabled, universes and variables are explicit,
and maximum line widths remain 90 and 95. No mathematical change is needed.

Read the current delivery wrapper: its existing-node whitelist excludes
blueprint, so no authorized sandbox edit can transmit this required correction.
The passing dry run omits the repair and does not resolve the specific returned
incremental DAG validation failure. The launcher-files instruction requires
reporting this wrong gate as BLOCKED and forbids editing or bypassing it. No
launcher file or shared file was edited, no direct Git command ran, and no
unchanged packet was re-pushed as a purported repair. The corrected packet is
retained until the tool admits the blueprint correction or the maintainer
normalizes the base provenance.


## Current repair retry: dry run 0ea81f6c56 (2026-10-18)

Inspected the saved report first and ran the prescribed initial saved-packet
dry run. Both retained modules compiled without errors or unexpected warnings,
and server preflight passed. The wrapper nevertheless explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared both sandbox node copies with the current shared records and reopened
both complete Lean modules. The dependency differs only in lean. The item differs
only in lean and the required blueprint correction. Both recorded signatures
occur verbatim, both modules disable autoImplicit, universes and variables are
explicit, and maximum line widths remain 90 and 95. The exact-couple data are
concrete; the consumer retains its sole named theorem sorry and proof docstring.

Confirmed that the saved blueprint endpoint thm-sp-spectral-object-yields is a
genuine blueprint node and its via list is the differential helper followed by
that helper's complete current ancestry. The shared base still names the
non-blueprint differential helper as its endpoint, exactly the fault returned
for immutable head d69fa739b776. Reading the current delivery wrapper confirms
its existing-node whitelist excludes blueprint. Its successful preflight thus
omits the specific required repair. No authorized sandbox change can transmit
that field through this gate.

BLOCKED under the launcher-files instruction: the prescribed tool refuses the
required metadata correction. No shared file or launcher script was edited,
no gate was bypassed, and no unchanged packet was re-pushed as a repair. The
corrected packet remains saved for the wrapper to admit the field or the
maintainer to normalize the base provenance.


## Retained-packet repair retry: dry run 894244f4ea (2026-10-18)

Read the saved report and ran the prescribed initial saved-packet dry run.
Both modules compiled cleanly and preflight passed at 894244f4ea. The tool
explicitly reported that the differing blueprint field was NOT delivered
(not yours to change). Thus the returned immutable-head d69fa739b776
incremental DAG defect remains in the generated commit.

Compared both sandbox node files with current shared records and reopened both
complete Lean modules. The dependency differs only in lean; the item differs
only in lean and the retained blueprint repair. Both recorded signatures occur
verbatim, all universes and variables are bound, autoImplicit is disabled, and
maximum widths are 90 and 95. The exact couple has concrete data; the theorem
retains its named sorry and complete proof docstring. No Lean change is needed.

Verified that the saved endpoint thm-sp-spectral-object-yields is a genuine
blueprint node. Its via list is the differential helper followed by that
helper's complete current ancestry. The shared base still incorrectly names
the non-blueprint differential helper as its endpoint. Reading deliver2.py
confirms that its existing-node whitelist excludes blueprint; no authorized
sandbox edit can transmit this correction through that gate.

BLOCKED under the launcher-files instruction: the delivery wrapper omits the
required repair despite its narrower successful preflight. No launcher file or
shared file was edited, no gate was bypassed, and no unchanged packet was pushed
as a repair. The corrected packet remains saved pending a tool fix or base
provenance normalization by the maintainer.


## Retained-packet repair retry: dry run 6474c05c8e (2026-10-18)

Read the saved report first and ran the required initial dry run. Both retained
Lean modules compiled and server preflight passed. The wrapper explicitly
reported that the differing blueprint field was NOT delivered (not yours to
change). Its existing-node whitelist at deliver2.py:116 excludes blueprint.
Consequently the generated commit still omits the precise correction requested
for immutable head d69fa739b776.

Reopened both complete modules and compared both saved node copies against the
current shared records. The dependency differs only in lean; the item differs
only in lean and blueprint. Both signatures occur verbatim, autoImplicit is
disabled, variables and universes are explicit, and maximum line widths are
90 and 95. The dependency has concrete data, and the consumer retains its
single named theorem sorry with the complete proof docstring. Verified that
the saved endpoint thm-sp-spectral-object-yields is a genuine blueprint node
and its via list is the differential helper followed by the complete current
ancestry. The current shared node retains the invalid helper endpoint.

BLOCKED: the passing dry run excludes the returned repair, so it is not a
repaired packet. The launcher-files instruction forbids patching or bypassing
this gate and requires reporting a wrong refusal as BLOCKED. No shared file
or launcher script was edited, no direct Git command ran, and no unchanged
packet was pushed as a repair. The corrected packet remains in this sandbox.


## Saved-packet retry after immutable head d69fa739b776 (2026-10-18)

Read the saved report first and ran the required initial dry run. Commit
`defd5a1c80` passed server preflight and compiled both retained Lean modules.
Reopened both complete modules and the item and dependency statements; checked
that both lean.statement signatures occur verbatim, all variables and universes
are explicit, autoImplicit is disabled, and maximum line widths are 90 and 95.
The dependency contains concrete exact-couple data and no sorry; the consumer
retains its single named theorem sorry and complete natural-language proof.
The node's arbitrary abelian category, finite filtration, representative
families, compatibility equations, normalized monic inclusions, lift equation,
and D-valued conclusion remain matched clause by clause in the second reading.
The zero page, negative integer indices, zero representatives, and arbitrary
finite-filtration bounds remain included.

Compared both saved nodes with current shared records: the dependency differs
only in lean; the item differs only in lean and blueprint. The saved blueprint
endpoint thm-sp-spectral-object-yields is a genuine blueprint node, and its via
list is the differential helper followed by its complete current ancestry.
The shared record still names the non-blueprint differential helper directly.
The dry run explicitly reports blueprint as NOT delivered (not yours to change),
and the wrapper's existing-node whitelist excludes it. Consequently the returned
incremental DAG defect is not fixed in the generated commit. No shared source,
launcher script, or delivery gate was edited or bypassed.

The latest dispatcher instruction specifically requires retaining a saved packet
whose first dry run passes, finishing the self-check, then pushing it through
deliver2.py. This retry follows that instruction and preserves this explicit
limitation for the maintainer's independent review. The saved blueprint correction
remains available in the sandbox; transmitting it still needs a wrapper change
or normalization of the base metadata by the maintainer.


## Returned-head b43bc9d1f901 repair diagnostic (2026-10-18)

Read the saved report first and ran the prescribed initial saved-packet dry run.
Commit `72346168d7` compiled both retained modules and passed server preflight,
but the wrapper explicitly reported:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Reopened both complete Lean modules and both node statements. The signatures
are verbatim, autoImplicit is disabled, universes and variables are explicit,
and maximum line widths are 90 and 95. The dependency differs only in lean;
the item differs in lean and the saved blueprint correction. Verified against
the current shared records that thm-sp-spectral-object-yields has blueprint.is
equal to its id, and the saved via path is the differential helper followed
by that helper's complete current ancestry. The base retains the invalid
non-blueprint endpoint named in the current return.

Read deliver2.py lines 112–134: its existing-node field whitelist excludes
blueprint, even for corrected statements. Thus the successful dry run omits
the precise repair requested for immutable head b43bc9d1f901. No authorized
sandbox edit can transmit that correction. Under the launcher-files rule,
this wrong tool refusal is BLOCKED; pushing the generated packet would leave
the returned fault unchanged. No launcher file or shared file was edited,
no gate was bypassed, and no unchanged packet was pushed as a repair.

## Current retained-packet retry: e24a65747f (2026-10-18)

Read the retained report before running the prescribed unchanged-packet dry run.
The current dry run compiled both modules separately and passed server preflight
at commit `e24a65747f`, but printed the decisive diagnostic:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared the saved packet with the current shared records without running Git.
The dependency differs only in `lean`; the item differs only in `lean` and the
saved provenance repair. The current base still sets `blueprint.from.node` to
`lem-sp-filtered-homology-tower-differential`, whose `blueprint.is` is null.
The sandbox instead uses the genuine blueprint node
`thm-sp-spectral-object-yields` and prepends the differential helper to that
helper's complete current `via` list. This directly repairs the returned
immutable-head b43bc9d1f901 diagnostic in the saved node.

Opened both complete Lean modules and rechecked both node statements and
recorded signatures. Both signatures occur verbatim, all universes and variables
are explicit, autoImplicit is disabled, and maximum line lengths are 90 and 95.
The concrete exact-couple definition contains no sorry data. The consumer keeps
its single named theorem sorry, full proof docstring, arbitrary abelian category,
finite filtration, supplied representatives and compatibility equations, monic
normalized inclusions, lift equation, and equality into the derived D object.
The retained clause-by-clause second reading and edge-case checks still apply.
No Lean change is required for the returned metadata defect.

Confirmed in the read-only deliver2.py existing-node update logic that its
allowed fields omit `blueprint`, including the statement-correction branch.
Thus a passing compile/preflight does not transmit the returned repair. Under
the explicit launcher-files instruction, this wrong refusal is a tool failure
and must be reported as BLOCKED. No launcher script, shared file, or delivery
gate was edited or bypassed, and no unchanged defective packet was pushed.

## Blueprint repair

The returned head identified an invalid `blueprint.from.node` reference to the split node `lem-sp-filtered-homology-tower-differential`, which is not itself a blueprint node. The item now records its valid nearest blueprint ancestor `thm-sp-spectral-object-yields`, with the existing via chain and proof place. This metadata repair is retained in the sandbox packet for delivery validation.


## Returned-head 3b95bce890e5 repair diagnostic (2026-10-18)

Read the saved report first and ran the required unchanged-packet dry run.
Commit `efee7709f5` compiled both retained modules and passed server preflight,
but the wrapper explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Reopened both complete Lean modules and compared both sandbox nodes against
current shared records. The dependency differs only in lean; the item differs
only in lean and the saved blueprint correction. Both recorded signatures occur
verbatim, autoImplicit is disabled, universes and variables are explicit, and
maximum line lengths are 90 and 95. The exact couple has concrete data and no
sorry; the consumer retains its single named theorem sorry and proof docstring.
No mathematical change is needed for this metadata return.

Confirmed that the current base still names the non-blueprint differential
helper as blueprint.from.node. The sandbox correctly names the genuine blueprint
node thm-sp-spectral-object-yields, and its via path is the differential helper
followed by that helper's complete current ancestry. Read the current deliver2.py
existing-node update logic: its allowed-field set excludes blueprint. Therefore
the generated commit omits precisely the repair requested for immutable head
3b95bce890e5 despite its narrower successful preflight.

BLOCKED under the launcher-files instruction: the delivery wrapper refuses to
transmit the required provenance correction. No authorized sandbox change can
repair that gate. No shared file or launcher script was edited, no direct Git
command ran, and no unchanged defective packet was pushed as a repair. The
corrected packet is retained pending a wrapper fix or maintainer normalization
of the base provenance.

## Blueprint provenance repair

The returned validation identified `blueprint.from.node` as invalid because
`lem-sp-filtered-homology-tower-differential` is a created DAG node, not an
imported blueprint node. The item is therefore anchored at the imported
blueprint node `thm-sp-spectral-object-yields`; the differential node is listed
in `via` as the intermediate statement whose forward-`f` half this item
specifies. The Lean statement, dependencies, and source are unchanged.


## Returned-head 56a1bdf6a389 repair check (2026-10-18)

Read the retained report first and ran the prescribed initial saved-packet dry
run. Commit `c799f2e4ce` compiled both modules and passed server preflight, but
the wrapper explicitly reported that the differing `blueprint` field was NOT
delivered (not yours to change). Reopened both modules and compared the saved
nodes with current shared records: both recorded signatures occur verbatim,
autoImplicit is disabled, all universes and variables are explicit, and maximum
line lengths are 90 and 95. The dependency differs only in lean; the item
differs only in lean and blueprint. No mathematical change is required.

Refreshed the sandbox provenance repair from the current differential helper:
its endpoint is the genuine blueprint node `thm-sp-spectral-object-yields`,
and its via list now includes the differential helper followed by that helper's
complete six-node ancestry. The shared base still incorrectly names the
non-blueprint differential helper directly.

The current delivery wrapper's existing-node whitelist excludes `blueprint`,
including its statement-correction branch. This is the precise metadata field
required by the return. The initial successful dry run omitted that repair;
the corrected sandbox packet is retained, with a fresh dry run below to check
the gate again. No shared source, launcher file, or gate was edited or bypassed.

The follow-up dry run at `9d9fc4551e` again compiled both retained modules and
passed preflight, but explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

BLOCKED under the launcher-files instruction: deliver2.py omits the exact
provenance repair required by immutable head 56a1bdf6a389. Both the initial
and refreshed-packet dry runs reproduce this wrong refusal. No permitted
sandbox change can transmit the excluded field. The corrected packet is
retained; no launcher/shared file was edited, no gate bypassed, and no
unchanged defective commit was pushed as a repair.

## Retained-packet verification, current retry (2026-10-18)

Ran the requested initial saved-packet dry run before changing anything:
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push`.
It compiled both retained Lean modules, passed server preflight, and produced
commit `1e2e054ab9`, but explicitly reported:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared the sandbox against the current shared records without Git: the
item differs only in `lean` and the required `blueprint` repair; the dependency
differs only in `lean`. The saved valid endpoint is the imported blueprint
node `thm-sp-spectral-object-yields`. Its via list is the differential helper
followed by that helper's complete current ancestry. The current shared item
still uses the non-blueprint differential helper as its endpoint, exactly the
fault returned against immutable head `56a1bdf6a389`.

Reopened both complete Lean files and checked the recorded signatures verbatim,
explicit universes and disabled autoImplicit, maximum line lengths 90 and 95,
concrete definition data with no sorry, and the single named theorem sorry.
No Lean repair is needed for this metadata-only return. The saved correction
already matches the current helper provenance, so no node refresh is needed.

Read the current wrapper's existing-node whitelist: it permits `lean` and
`stmt_deps`, plus the statement-correction fields when applicable, but never
`blueprint`. Consequently its passing dry run omits the returned repair. This
is an actual tool refusal under the launcher's explicit tool-file rule, not a
Lean or dependency blocker. The corrected packet is retained. No launcher file
was patched, no shared file edited, no gate bypassed, and no unchanged defective
packet pushed.


## Current tool diagnostic: dry run 341d3ae102 (2026-10-18)

Read the saved report and ran the required initial dry run without changing the
packet. Both retained modules compiled cleanly and server preflight passed at
`341d3ae102`, but deliver2.py explicitly excluded `blueprint` as “NOT delivered
(not yours to change)”. Its existing-node field whitelist still excludes that
field, including in its statement-correction branch. Thus this dry run does
not include the repair requested for immutable head `56a1bdf6a389`.

Reopened both full modules and compared the sandbox nodes with current shared
records: only lean differs for the dependency; only lean and blueprint differ
for the item. The saved blueprint endpoint is the genuine imported node
`thm-sp-spectral-object-yields`; its via list is the differential helper followed
by the helper’s current complete ancestry. Both signatures occur verbatim,
maximum line widths are 90 and 95, autoImplicit is disabled, the definition has
no sorry, and the theorem has its single requested sorry. No Lean change is
needed for this return.

BLOCKED by the wrapper’s exclusion of the required provenance field. Under the
explicit launcher-files instruction, the wrapper may not be patched or bypassed.
No unchanged defective delivery was pushed; the corrected packet remains here.


## Returned-head 56a1bdf6a389: current saved-packet diagnostic (2026-10-18)

Read the retained report and ran the prescribed initial dry run before changing
anything. The dry run produced `ce73b4f865`, compiled both delivery modules,
and passed server preflight, but explicitly printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Reopened both complete Lean modules and compared both saved node records with
the current shared records without Git. The dependency differs only in lean;
the item differs only in lean and blueprint. Both signatures occur verbatim.
The exact-couple data are concrete; the consumer has its requested named sorry.
The saved provenance names the genuine blueprint node
`thm-sp-spectral-object-yields`, with the differential helper followed by its
complete current ancestry in via. The shared item still directly names the
non-blueprint differential helper, exactly the defect of the returned head.

Read the current delivery wrapper's existing-node field whitelist: blueprint
is excluded even in its statement-correction branch. The successful preflight
therefore does not validate delivery of the requested correction. This is a
reproduced tool refusal, not a missing Lean construction. Under the explicit
launcher-files rule the wrapper may neither be patched nor bypassed. No shared
file or launcher file was edited, no direct Git command was run, and no
unchanged defective packet was pushed. The corrected sandbox packet is retained.


## Current returned-head repair diagnostic (2026-10-18)

Read the retained report and ran the prescribed initial saved-packet dry run.
Commit `5b21549e17` compiled both modules and passed server preflight, but
explicitly reported the required `blueprint` correction as “NOT delivered
(not yours to change)”. The shared item still names the non-blueprint node
`lem-sp-filtered-homology-tower-differential` as its blueprint endpoint.
The saved correction names the genuine blueprint node
`thm-sp-spectral-object-yields`, with the differential helper followed by
its complete current ancestry in `via`. This matches the current helper record.

Reopened both complete Lean files: their recorded signatures are verbatim,
autoImplicit is disabled, universes are explicit, maximum line widths are
90 and 95, the exact-couple data are concrete, and the theorem retains its
named sorry and source/proof docstring. Refreshed the dependency copy from
the current shared node while retaining only its delivered lean record; this
removes stale reviewed_proof metadata from the packet.

The current deliver2.py existing-node whitelist excludes blueprint, even for
a statement correction. Therefore its successful dry run cannot transmit
the repair requested for immutable head 56a1bdf6a389. Under the explicit
launcher-files rule this is a tool failure; no wrapper or shared file was
edited, no gate was bypassed, and no unchanged defective packet was pushed.

## Saved-packet retry for returned head 56a1bdf6a389 (2026-10-18)

The prescribed initial dry run compiled both saved modules and passed server
preflight at `d4310fedbd`, but printed:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Compared the saved nodes with current shared records without Git: the dependency
changes only lean; the item changes only lean and blueprint. Opened both complete
Lean files and verified the recorded signatures verbatim, explicit universes,
disabled autoImplicit, maximum line widths 90 and 95, concrete definition data,
and the consumer's single named theorem sorry. No Lean repair is needed for the
returned metadata diagnostic.

The saved blueprint correction is valid against the current ancestry: its endpoint
is the imported blueprint node thm-sp-spectral-object-yields, and via prepends the
differential helper to that helper's complete current via list. The shared item
still directly names the non-blueprint differential helper as its endpoint.

Read deliver2.py's existing-node update logic: blueprint is excluded from its
allowed fields, including the statement-correction branch. Consequently this
successful dry run omits the precise repair requested by the maintainer. This
is a tool refusal under the launcher's explicit launcher-files rule. No launcher
file or shared file was modified, no gate was bypassed, and no unchanged defective
packet was pushed. The corrected sandbox packet remains available for a wrapper
fix or a maintainer correction of the base provenance.


## Retained-packet dry run 60375d3c1e (2026-10-18)

Read the retained report first and ran the required unchanged-packet dry run.
Both delivery modules compiled and server preflight passed, but the wrapper
explicitly excluded the required repair:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
OK (dry run): commit 60375d3c1e passes the preflight and compiles; nothing pushed
```

Reopened both complete modules and compared both saved nodes with the current
shared records. Only lean differs for the dependency; only lean and blueprint
differ for the item. Verified verbatim recorded signatures, explicit universes,
disabled autoImplicit, widths below 100, concrete exact-couple data, and the
consumer's single named theorem sorry. Verified the saved blueprint endpoint
and via list against the differential helper's complete current ancestry.
The corrected endpoint is the genuine blueprint node thm-sp-spectral-object-yields.

Read the current deliver2.py existing-node field whitelist: blueprint is still
excluded, including for statement corrections. Hence a passing dry run does
not transmit the returned metadata repair. This is the reproduced tool refusal
for immutable head 56a1bdf6a389. The launcher-files instruction prohibits patching
or bypassing that wrapper. No shared file or launcher script was edited, no
direct Git command was run, and no unchanged defective packet was pushed.

## Repair retry (2026-10-18)

The returned blueprint defect is repaired in the retained node copy: `blueprint.from.node` is
`thm-sp-spectral-object-yields`, and `via` is the complete chain beginning with
`lem-sp-filtered-homology-tower-differential`. `tools/blueprint_refs.py` confirms this is the
current blueprint ancestry. `scompile.py` was rerun on both delivery modules and is clean. A
fresh `deliver2.py --no-push` run again compiles and passes preflight, but reports that
`blueprint` is not delivered because the wrapper treats it as maintainer-owned. The launcher
rule forbids editing or bypassing that wrapper, so the corrected blueprint metadata cannot be
transmitted by the prescribed delivery tool.

## Final repair retry (2026-10-18)

The required provenance repair remains in the item copy: `blueprint.from.node` is
`thm-sp-spectral-object-yields`, and its `via` list includes the complete ancestry
through `lem-sp-filtered-homology-tower-differential`. The dependency copy differs
from the current base only in its permitted `lean` record. I reran the prescribed
`deliver2.py ND lem-sp-filtered-homology-tower-forward-representatives --no-push` after
reading the retained packet; both Lean modules compiled and server preflight passed.
The wrapper again emitted:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
```

Thus the dry-run commit contains the Lean repair but cannot contain the returned
blueprint correction. The launcher-file rule forbids patching or bypassing the
wrapper, so this is reported as the prescribed tool failure rather than pushing a
packet that silently omits the requested repair.


## Current repair verification: dry run 6b1f126412

The initial saved-packet dry run on 2026-10-18 compiled both modules and passed
preflight, but explicitly omitted `blueprint` as “NOT delivered (not yours to
change)”. Reopened both complete Lean files and compared both saved node files
against the current shared records without Git. The dependency differs only in
`lean`; the item differs only in `lean` and its required `blueprint` repair.
Both signatures are verbatim, universes are explicit, autoImplicit is disabled,
maximum line widths are 90 and 95, definitions have concrete data, and the theorem
retains its single requested sorry.

The shared item still names the non-blueprint differential helper as its
blueprint endpoint. The saved endpoint is `thm-sp-spectral-object-yields`, whose
`blueprint.is` names itself; saved `via` prepends the differential helper to its
complete current ancestry. This repairs the precise immutable-head return.
Read the current delivery wrapper at lines 115–125: existing-node allowed fields
exclude `blueprint`, including the statement-correction path. Thus dry-run commit
6b1f126412 cannot carry the requested repair despite passing preflight. The
launcher-files instruction forbids modifying or bypassing the wrapper. No
unchanged defective delivery was pushed. BLOCKED is the actual delivery-tool
refusal; the corrected sandbox packet remains intact.


## Returned-head repair verification: dry run 885ed3982c (2026-10-18)

The prescribed initial dry run on the retained packet compiled both modules and
passed server preflight, but explicitly excluded the required correction:

```text
note: lem-sp-filtered-homology-tower-forward-representatives: these fields differed in your copy and were NOT delivered (not yours to change): ['blueprint']
OK (dry run): commit 885ed3982c passes the preflight and compiles; nothing pushed
```

Reopened both complete Lean modules and compared the two sandbox nodes against
current shared records without Git. The dependency differs only in lean; the
item differs only in lean and blueprint. Both recorded signatures are verbatim;
autoImplicit is disabled, universes are explicit, line widths are 90 and 95,
the exact-couple construction has concrete data, and the consumer has its single
named theorem sorry. The saved corrected blueprint endpoint is the genuine
blueprint node thm-sp-spectral-object-yields. Its via list prepends the differential
helper to that helper's complete current ancestry. The current shared item still
has the invalid endpoint named by the immutable-head return 56a1bdf6a389.

Read the current deliver2.py existing-node update logic: its allowed-field set
excludes blueprint, including for statement corrections. This concrete tool
refusal prevents transmitting the already saved repair. The explicit launcher-files
rule prohibits modifying or bypassing that wrapper. No launcher or shared file was
edited and no unchanged defective packet was pushed. The corrected sandbox remains
ready for delivery once the tool permits the required provenance repair.
