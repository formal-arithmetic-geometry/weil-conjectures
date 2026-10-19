## Worker report

Reuse `AlgebraicGeometry.GeometricallyReduced.dense_smoothLocus`, declared in
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`, lines 130–133 of the
read-only slopmaster2 source. No module is added and only the item's `lean` field changes.
The pre-existing attachment record lacked the complete stage-2 fields; this delivery supplies them.

The full signature, copied verbatim into `lean.statement`, is:

```lean
theorem GeometricallyReduced.dense_smoothLocus {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    Dense (f.smoothLocus : Set X) :=
```

Hypothesis and conclusion comparison:

- “K is a field” is `{K : Type u} [Field K]`; no perfectness assumption.
- “Z is a scheme” is `{X : Scheme.{u}}`, with X renaming Z.
- The specified morphism h to Spec K is `(f : X ⟶ Spec (.of K))`.
- “locally finitely presented” is `[LocallyOfFinitePresentation f]`.
- “geometrically reduced over K” is `[GeometricallyReduced f]`.
- The dense smooth locus is `Dense (f.smoothLocus : Set X)`.

The smooth locus definition and the full signatures and surrounding proofs were read in
Mathlib.AlgebraicGeometry.Morphisms.Smooth, lines 260–343.
`Scheme.Hom.smoothLocus` is open. For any open W, `preimage_smoothLocus_eq`
identifies its inverse image with the smooth locus of `W.ι ≫ f`, and
`smoothLocus_eq_top_iff` says that this is all of W precisely when that restricted
morphism is smooth. Consequently an open W has smooth restriction exactly when
it is contained in f.smoothLocus; applying this also to f.smoothLocus itself
shows that it is exactly the union specified by the node. Thus the conclusion
neither drops nor adds a clause.

Dependency declarations read and used by the existing theorem:

- `def-sbc-locally-finite-presentation`: the mathlib_match declaration
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, lines 42–49.
- `def-pc-geometrically-irreducible`: the geometrically reduced clause of its
  mathlib_match uses `AlgebraicGeometry.GeometricallyReduced` in
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`, lines 41–45. Its definition
  tests reducedness after all field-valued base changes, as the node requires.
- `def-sbc-smooth-morphisms`: the recorded `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, lines 59–67, is the predicate
  used in the smooth-locus equivalence. No replacement notion is introduced.

Source checked: Stacks varieties.tex, lemma-geometrically-reduced-dense-smooth-open
(Tag 056V), lines 4693–4730. The geometrically reduced direction constructs a dense
smooth open. The source's reducedness is automatic from geometric reducedness;
locally finite type and locally finite presentation agree over a field. This is
also exactly the existing project's theorem, with no extra hypotheses.
The existing proof passes to the perfect closure in an algebraic closure, uses
perfect-field density there and descends the resulting smooth open. The node's
proof and proof_deps are empty; they are left unchanged.

Edge cases checked: X empty is allowed (density in the empty space is valid);
no nonempty or irreducibility hypothesis, no quasi-compactness, no finite global
presentation, and no characteristic or perfectness restriction is present.
The universe u is arbitrary and shared by K and X, in accordance with Scheme/Spec's
universe convention. No independent lower universe is used for test extensions.

Searches performed using msearch.py, with group NA and this item:

- leanfinder: “A geometrically reduced scheme locally of finite presentation over an
  arbitrary field has dense smooth locus”: eight hits, standard smooth chart results
  and Algebra.smoothLocus_eq_univ; no exact Mathlib statement.
- loogle: `"smoothLocus", Dense`: one hit,
  `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField`, which has the
  extra perfect-field hypothesis and is not the arbitrary-field statement.
- grep: `dense.*smoothLocus|smoothLocus.*dense` in AlgebraicGeometry: three hits,
  only the perfect-field lemma and its use.
- rg of WeilConjectures for `dense_smoothLocus` found the exact theorem in SlicingFlat.
  Searching for the item id there found no tagged declaration; the theorem is untagged.
- rg of project lean/Sheaf for `dense_smoothLocus|geometrically.*reduced.*dense`
  returned no hits. The DAG item's own lean_candidates and attachment record also
  identify the exact SlicingFlat theorem; its signature and docstring were checked
  directly rather than inferred from that record.

No statement correction, new node, dependency module, or disputed statement.
Validation: deliver2.py --no-push checks the existing declaration on the server
through its scompile.py probe and runs the maintainer preflight. The independent
second reading is intentionally reserved for the next worker.

## Successful server validation

2026-10-15 09:50 UTC: resumed the earlier attempt and reread the node, all three statement
dependency records and their Mathlib signatures/docstrings, the exact upstream theorem,
the smooth-locus restriction equivalences, and Stacks Tag 056V. Only the item's `lean`
field differs from the repository. The existing declaration remains exact; no replacement
module or statement correction is needed.

The required `deliver2.py NA lem-pur-geometrically-reduced-dense-smooth-open --no-push`
now prints `OK (dry run)`: the existing-declaration server compile and preflight pass,
except for the independent second reading that the designated next worker supplies.
The previous read-only import collision no longer prevents validation. Nothing was
pushed, and no second-reading section was written by this worker.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node, Stacks varieties.tex Tag 056V
(lemma-geometrically-reduced-dense-smooth-open), the upstream SlicingFlat declaration
and its surrounding proof, all three statement-dependency nodes, and their Mathlib
signatures. The proposed existing declaration says exactly what this node says.

Object, hypothesis and conclusion inventory, matched individually:

1. Arbitrary field K: `{K : Type u} [Field K]`. Exact; no perfectness or
   characteristic assumption.
2. Scheme Z: `{X : Scheme.{u}}`. Exact, with X a harmless renaming of Z.
3. Specified structure morphism h: `(f : X ⟶ Spec (.of K))`. Exact;
   the node explicitly names h, so an explicit morphism is the prescribed convention.
4. Locally finitely presented h: `[LocallyOfFinitePresentation f]`. Exact.
   The dependency def-sbc-locally-finite-presentation matches the class in
   Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation, whose finitePresentation_appLE
   field tests affine pairs. Its pointwise affine-local interpretation is precisely
   the dependency's definition. No global quasi-compactness is assumed.
5. Z geometrically reduced over K: `[GeometricallyReduced f]`. Exact.
   The reduced clause of def-pc-geometrically-irreducible is the class in
   Mathlib.AlgebraicGeometry.Geometrically.Reduced, with field base changes expressed
   by `geometrically IsReduced f`. I also opened geometrically in Geometrically.Basic:
   it quantifies over field-valued base changes and all pullback squares, rather than
   merely testing Z itself. Over Spec K these are precisely field extensions of K.
6. Smooth locus as the union of opens W with smooth restricted structure map:
   `f.smoothLocus`. Exact. In Mathlib.AlgebraicGeometry.Morphisms.Smooth this is an
   open subset, initially expressed by formal smoothness of stalk maps. For W.ι,
   `preimage_smoothLocus_eq` identifies its preimage with the smooth locus of
   `W.ι ≫ f`; `smoothLocus_eq_top_iff` then says that this is all of W exactly
   when `Smooth (W.ι ≫ f)`. Thus W is contained in f.smoothLocus exactly when
   its restriction is smooth. Taking W = f.smoothLocus also proves that the locus
   itself belongs to the union. The Smooth class is the recorded dependency
   def-sbc-smooth-morphisms: its affine-local RingHom.Smooth definition is the
   Stacks notion, equivalent to the dependency's lifting definition by Tag 02H6.
7. Density in Z: `Dense (f.smoothLocus : Set X)`. Exact topological density;
   neither existence of one point nor a nonempty-open hypothesis replaces it.

Source assumptions checked: Tag 056V states the equivalence for reduced schemes
locally of finite type over a field. Here only its geometric-reducedness-to-dense-open
implication is needed. Geometric reducedness supplies reducedness by the identity
field extension. Over a field local finite type equals local finite presentation,
since the field is Noetherian. The lemma has no ambient perfectness, separatedness,
or irreducibility assumption. Its proof reduces locally to integral components;
those reductions are not hypotheses of the result. The node and Lean agree without
requiring a statement correction.

Edge cases: the empty scheme and its empty smooth locus satisfy density; arbitrary
disconnected schemes are allowed. No nonemptiness, quasi-compactness, irreducibility,
finite global presentation, or characteristic restriction appears. There is no index
set, degree n, or zero-module parameter. Universe u is explicitly bound by the
upstream module's `universe u`; K and X use the standard common Scheme/Spec universe,
and geometrically tests fields in that same universe. There is no independent lower
test-field universe and no unbound variable. Every size is covered by arbitrary u.

Independent searches (recorded in searches.jsonl): LeanFinder query
“Over an imperfect field a geometrically reduced locally finite type scheme is
 generically smooth” returned eight standard-smooth chart and ring-geometric-reducedness
hits, none the desired theorem. Loogle `"smoothLocus", Dense` returned only
Scheme.Hom.dense_smoothLocus_of_perfectField, which adds PerfectField and is not exact.
The msearch grep `geometrically.*reduced|reduced.*geometrically` in
AlgebraicGeometry/Geometrically returned definitions and integral implications, not
this density result. LeanSearch “geometrically reduced scheme over a field has dense
smooth locus” was unavailable (Internal Server Error); no mathematical verdict is
inferred from that failure. Direct rg for `dense.*smooth|smooth.*dense` in Mathlib
AlgebraicGeometry, all upstream WeilConjectures, and project lean/Sheaf found the exact
arbitrary-field theorem only in upstream SlicingFlat. I opened its actual signature,
not just its search hit. The project hits concern other statements, so no project
module should replace or duplicate it.

No mismatch found and no Lean or node edits needed. The existing declaration has
real proof data and its docstring describes the perfect-closure argument; the node's
proof and proof_deps are empty. Existing upstream source is read-only: its absent
blueprint tag is not repaired by duplicating the theorem. No new definitions,
dependency modules, hollow definitions, or newly proved statements are delivered.
The recorded lean.statement was checked verbatim against the source signature.
Only this independent review is added to the worker's delivery.

## Returned H10 repaired: clean published import environment

2026-10-15: Rechecked the exact upstream theorem and docstring in SlicingFlat,
all three dependency records and their Mathlib signatures/docstrings, the smooth
locus restriction equivalences, and Stacks varieties.tex Tag 056V. The attachment
and dependency records remain exact; no mathematical change is needed.

The earlier duplicate-instance error in the published QCoh import environment no
longer reproduces. Ran the existing-declaration probe in scratchpad/ExistingChecks.lean
through the prescribed scompile.py command: both its sandbox and library checks passed
without warnings or errors (4.8 and 4.7 seconds). Independently called
scompile.run_server on that same probe to check the published server environment
rather than relying only on the local overlay. This also passed without warnings
or errors, printing the exact type of
AlgebraicGeometry.GeometricallyReduced.dense_smoothLocus in 3.5 seconds, with nice 19,
two threads and the unchanged 60-second limit. It imports SlicingFlat directly,
so the formerly failing transitive imports are checked without an import bypass.

This delivery repairs the stale report of an unresolved blocker with current clean
server evidence. No published sources, compiled artifacts, or tools were modified;
no duplicate theorem, new module, node correction, or dependency repair is needed.
The existing second reading above remains applicable because the mathematical
attachment has not changed. The required deliver2.py --no-push validation follows.

## Second reading by NA

Fresh independent reading on 2026-10-15: opened the sandbox node, the actual
SlicingFlat.lean declaration and surrounding proof (lines 89–133), all three
statement-dependency nodes, and their recorded Mathlib declarations. Read Stacks
varieties.tex, lemma-geometrically-reduced-dense-smooth-open (Tag 056V), including
its complete proof, and more-morphisms.tex, lemma-smooth-formally-smooth (02H6).
No mathematical mismatch was found; the existing attachment is retained.

Object/hypothesis/conclusion inventory and individual verdicts:

1. Field K: `{K : Type u} [Field K]`. Exact arbitrary field, including imperfect
   fields of positive characteristic; no perfectness assumption.
2. Scheme Z: `{X : Scheme.{u}}`. Exact, with X renaming Z.
3. Named structure map h: `(f : X ⟶ Spec (.of K))`. Exact; the node explicitly
   introduces this map, so the explicit morphism convention applies.
4. Local finite presentation: `[LocallyOfFinitePresentation f]`. Exact recorded
   notion from def-sbc-locally-finite-presentation, FinitePresentation.lean:45–49.
   Its all-affine-pairs field is the affine-local presentation condition, with
   no global quasi-compactness or quasi-separatedness assumption.
5. Geometric reducedness over K: `[GeometricallyReduced f]`. Exact reducedness
   clause of def-pc-geometrically-irreducible, Reduced.lean:44–45. Opened
   `geometrically` (Basic.lean:46–49) and `geometrically_iff_of_commRing`
   (129–143): this quantifies over field-valued base changes and says that the
   actual pullback is reduced. Over Spec K these are field extensions of K,
   not just reducedness of X or of its original stalks.
6. Union of all smooth open subschemes: `f.smoothLocus`. Exact. Opened its
   definition and `smoothLocus_eq_top_iff`, `preimage_smoothLocus_eq` in
   Mathlib Morphisms/Smooth.lean. For every open W, the inverse image of this
   locus under W.ι is the locus of W.ι ≫ f, which is all of W if and only if
   `Smooth (W.ι ≫ f)`. Thus such W are precisely the opens contained in the
   locus. Taking W to be the locus itself shows it is the specified union.
   The Smooth class at lines 62–66 is the recorded def-sbc-smooth-morphisms
   interface; Stacks 02H6 identifies its affine-local smoothness with local
   finite presentation plus formal smoothness. No private replacement notion.
7. Density in Z: `Dense (f.smoothLocus : Set X)`. Exact topological density,
   without an added nonemptiness or irreducibility clause.

Source hypotheses: Stacks 056V assumes reducedness and local finite type over a
field. Geometric reducedness supplies reducedness by the identity extension;
over a field local finite type and local finite presentation agree. The desired
implication is geometric reducedness to existence of a dense smooth open.
Density of the whole smooth locus is equivalent by item 6. The proof's local
reductions to quasi-compact and integral schemes are not ambient assumptions.
No statement_change or citer audit is needed.

Edge cases: the empty scheme and its empty locus are allowed and density holds
in the empty space. Disconnected and non-quasi-compact schemes are included.
There is no index set, module, degree n, or characteristic restriction. Universe
u is explicitly declared upstream and arbitrary; K, X, Spec, and test fields
have the standard common scheme universe, with no independent lower test-field
universe. No free variable or universe occurs in the recorded signature.

Independent searches in this reading (searches.jsonl records wrapper calls):
LeanFinder “A geometrically reduced scheme over an imperfect field is generically
smooth” returned eight hits about ring reducedness and standard smooth charts,
not an exact Mathlib density theorem. Loogle `"smoothLocus", Dense` returned
only `Scheme.Hom.dense_smoothLocus_of_perfectField`, whose extra PerfectField
assumption makes it unsuitable. Wrapper grep
`generically.*smooth|dense.*smoothLocus|smoothLocus.*dense` returned only that
perfect-field lemma and its use. LeanSearch “geometrically reduced schemes have
dense smooth locus over a field” was unavailable (Internal Server Error), with
no verdict inferred. Direct rg for `dense.*smooth|smooth.*dense` over Mathlib
AlgebraicGeometry, all upstream WeilConjectures, and project lean/Sheaf found
the exact arbitrary-field theorem in SlicingFlat. Opened that declaration,
not merely its name; no exact project duplicate was found.

The upstream proof uses perfect closure in an algebraic closure, obtains density
there, and descends smoothness along the purely inseparable field extension.
The item's proof/proof_deps are empty. No new theorem, definition, dependency
module, or hollow data is delivered. Existing read-only source has no blueprint
tag; reuse does not authorize editing or duplicating it. The lean.statement is
verified as a verbatim substring of the actual source signature. No Lean/node
change was needed; this fresh second-reading section is the sole report addition.
Validation uses the prescribed scompile.py probe importing SlicingFlat directly,
then deliver2.py --no-push and delivery; results are recorded below.

Fresh validation result: scompile.py passed both sandbox and library probes without
warnings or errors (4.2 s and 4.6 s). deliver2.py --no-push printed OK: the
existing-declaration check, preflight and compilation all pass.
