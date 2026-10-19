## Worker report

The module `lean/Sheaf/AlgebraicTopology/SubdivisionAnodyne.lean` states
`SSet.subdivision_anodyne`. Its sole proof is `by sorry`, as required for stage 2.
It introduces no definitions or auxiliary theorems. The node copy changes only `lean`.
No dependency correction, new node, or statement correction is needed.

The source is [Kerodon Proposition the project server (00Z3)](https://kerodon.net/tag/00Z3),
read online together with [Lemma the project server (00Z9)](https://kerodon.net/tag/00Z9).
The proposition states precisely subdivision preservation of anodyne morphisms.
Its proof uses subdivided horns and two finite-poset pushouts. The module's docstring
contains all seven expanded proof steps of the DAG, including both intersection
calculations and the adjunction transpositions used in place of weak saturation.

Clause-by-clause correspondence:

- Small simplicial sets: `{X Y : SSet.{u}}`, with `universe u` explicitly declared.
  `SSet` is Mathlib's contravariant functor category on `SimplexCategory`, with
  simplex sets in `Type u`. No finiteness or nonemptiness is imposed on X or Y.
- Any morphism `f : X → Y`: `(f : X ⟶ Y)`, a natural transformation.
- The subdivision functor of `lem-coef-subdivision-face-poset-calculus`:
  the same Mathlib `SSet.sd` used by that node, not a replacement construction.
  `sd.map f` has source `sd.obj X` and target `sd.obj Y` by its functor type.
- Kan fibration as right lifting against every horn with n ≥ 1 and every vertex:
  `SSet.modelCategoryQuillen.J` is the supremum of the morphism families
  `Λ[n + 1, i].ι`, where `n : ℕ` and `i : Fin (n + 2)`; its right lifting class
  is the scoped Quillen fibration property. This includes both outer vertices
  and excludes dimension-zero lifting conditions.
- Anodyne as left lifting against every Kan fibration: Mathlib
  `SSet.anodyneExtensions` is definitionally `(fibrations SSet).llp`, and
  `anodyneExtensions_eq_llp_rlp` identifies this with `J.rlp.llp`.
  `MorphismProperty.llp` quantifies `HasLiftingProperty` against every member
  of that class, so it expresses the stated diagonal filler property exactly.
- Hypothesis that f is anodyne: `(hf : anodyneExtensions f)`.
- Conclusion that the induced subdivision map is anodyne:
  `anodyneExtensions (sd.map f)`. This is the whole conclusion.

Dependency interfaces read and used:

- `def-weil-pbc-simplicial-set` has status mathlib and no required Lean record.
  Its `mathlib_match` lists `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`,
  `SSet.Subcomplex`, and `SSet.Finite`. Read their signatures/docstrings in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `.Degenerate`, `.Subcomplex`,
  and `.Finite`; only `SSet` is needed by this signature.
- `lem-coef-subdivision-face-poset-calculus` records
  `Sheaf.AlgebraicTopology.SubdivisionFacePosetCalculus`, declaration
  `SSet.SubdivisionFacePoset.subdivision_face_poset_calculus`. Read its full
  signature, docstring and constructions. It explicitly uses Mathlib `SSet.sd`,
  `SSet.ex`, and `SSet.sdExAdjunction`. Read these definitions in
  `Mathlib.AlgebraicTopology.SimplicialSet.Subdivision` as well.
- `lem-coef-sset-anodyne-pushout-product` is a mathlib leaf, with match
  `SSet.anodyneExtensions_pushoutObjObjι` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`.
  Read its full signature and the anodyne definition in `.AnodyneExtensions.Basic`.
  The same lifting predicate is used here; the theorem is a proof-plan input.
- The additional proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`
  (`SSet.Enhanced.coneCategory`, with ordinary `CategoryTheory.nerve` used by
  the poset argument), `Mathlib.CategoryTheory.Limits.HasLimits`
  (`CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, `colimit.desc`), and
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
  (`llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange`, `llp_isMultiplicative`). They retain the node's
  stated proof plan even though the postponed proof does not yet invoke them.

Edge cases checked before writing:

- Empty source, target, and empty complexes are not excluded by any binder.
  In particular identities of the empty simplicial set remain included.
- Identities and arbitrary isomorphisms satisfy the input predicate; subdivision
  maps them to isomorphisms, consistently with the proposed conclusion.
- The generating class includes all positive dimensions and all vertices.
  For n = 1, both endpoint horns occur. In the proof, J has one element and
  I = J minus {j} is empty: P_-(I) and P_pm(J) are empty, and the pushout
  calculations still apply. There is no false assumption that I is nonempty.
- Dimension-zero horns are not added: doing so would change Kan fibrations.
- No Mono hypothesis, Kan hypothesis on X or Y, finite-complex hypothesis,
  or weak-equivalence hypothesis is added to the theorem. The poset finiteness
  occurs only in the positive-dimensional horn argument of the proof plan.
- The universe `u` is arbitrary, and subdivision and both lifting classes act
  on the same `SSet.{u}`. No universe equality or smallness restriction is added.

Searches (all run through the prescribed tools on 2026-10-17):

- `msearch.py NV lem-coef-subdivision-anodyne leanfinder` with query
  `Subdivision of an anodyne extension of simplicial sets is an anodyne extension`:
  eight results on `SSet.Subcomplex.Pairing`, `PairingCore` and their fields;
  none has the required preservation statement.
- `msearch.py ... leansearch` with query
  `Barycentric subdivision preserves anodyne morphisms of simplicial sets`:
  eight results on nondegenerate simplices, monomorphisms, Quillen generating
  classes and simplex-category factorizations; none states subdivision preservation.
- `msearch.py ... loogle "SSet.sd, SSet.anodyneExtensions"`: zero results.
- `msearch.py ... grep "anodyne.*(sd|subdiv)|(sd|subdiv).*anodyne" AlgebraicTopology`:
  one result, `.AnodyneExtensions.Basic.lean:46`, explicitly listing stability
  under subdivision as TODO. Read the surrounding file and lifting definition.
- `rg -n` with `anodyne.*(sd|subdiv)|(sd|subdiv).*anodyne|lem-coef-subdivision-anodyne`
  over `WeilConjectures/` and `lean/Sheaf/`: only a proof-plan mention in
  `SubdivisionExHomotopyAdjunction.lean:43`, no matching declaration.
- `rg -n 'anodyneExtensions_sd|SubdivisionAnodyne'` over
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures/`, and `lean/Sheaf/`:
  no results. The new declaration name is not already supplied there.

Validation: the prescribed `scompile.py NV lem-coef-subdivision-anodyne` compiled
this module cleanly in both sandbox and library positions. After expanding the
docstring, the final file is checked again by the required `deliver2.py --no-push`.
No `STATEMENT-DISPUTED` issue or node fault was found. No second-reading section
is supplied by the author; that belongs to the independent second reader.

## Second reading by NV

I independently read the sandbox node and Lean module, the three statement
dependency records, their declarations, and the proof-dependency records and
interfaces. No repair note exists for this item. I also read the actual source,
[Kerodon Proposition the project server (00Z3)](https://kerodon.net/tag/00Z3), and
[Lemma the project server (00Z9)](https://kerodon.net/tag/00Z9). These are Kerodon tags;
the identically numbered Stacks tags concern sites and are not this source.
The proposition has no standing finiteness, fibrancy, or nonemptiness hypothesis
on its simplicial sets. Its finite nonempty set occurs only inside its proof.

My object/hypothesis/conclusion checklist, in the node's order:

1. Small simplicial sets X and Y: `{X Y : SSet.{u}}`. I read
   `Mathlib.AlgebraicTopology.SimplicialSet.Basic`: `SSet` is
   `SimplicialObject (Type u)`, hence the contravariant functor category and
   natural transformations specified by `def-weil-pbc-simplicial-set`.
   Verdict: exact; neither set is required finite, nonempty, or Kan.
2. The subdivision functor of `lem-coef-subdivision-face-poset-calculus`:
   `sd`. I read that dependency's full theorem signature and its helpers
   `simplexInclusion` and `subdivisionCocone`. It uses Mathlib's `SSet.sd`,
   `SSet.ex`, and `SSet.sdExAdjunction`. I then read their definitions in
   `Mathlib.AlgebraicTopology.SimplicialSet.Subdivision`: `sd` is the left
   Kan extension from the nonempty-face-poset nerves. Thus the current file
   uses the same functor and its actual `map`, with no alternate construction.
   Verdict: exact; the dependency's finite-poset clauses impose no restriction
   on its general subdivision functor or on the present theorem.
3. Kan fibrations against all horns of positive dimension and every vertex:
   the predicate inside `anodyneExtensions` is the Quillen fibration class.
   I read `CategoryWithFibrations.lean`: its generating class is
   `J := ⨆ n, .ofHoms (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)`, and its
   fibration class is `J.rlp`. Every dimension at least one and both outer
   vertices occur. Verdict: exact; no dimension-zero condition is inserted.
4. Anodyne means left lifting against every such Kan fibration:
   `anodyneExtensions` in `AnodyneExtensions.Basic` is `(fibrations _).llp`;
   `anodyneExtensions_eq_llp_rlp` is definitionally `J.rlp.llp`. I read `llp`,
   `rlp`, and `HasLiftingProperty.sq_hasLift`: they quantify over all right
   maps and all commutative squares and demand diagonal fillers. This is the
   same predicate as the pushout-product dependency uses. Verdict: exact;
   no replacement by inner anodynes or weak equivalences is hidden here.
5. An arbitrary map f with the sole hypothesis that it is anodyne:
   `(f : X ⟶ Y) (hf : anodyneExtensions f)`. Verdict: exact; there is no
   additional Mono instance, coefficient ring, field, or size assumption.
6. The whole conclusion, with the specified source and target:
   `anodyneExtensions (sd.map f)`, where the functor gives
   `sd.map f : sd.obj X ⟶ sd.obj Y`. Verdict: exact, with the same order of
   quantifiers and no omitted or extra conclusion.

Edge cases: the arbitrary universe `u` includes all the node's small simplicial
sets; both functor and lifting classes use that universe, with no extra equality
of universes. Empty X and Y, their identity, and arbitrary isomorphisms are
included. There is no index set or coefficient characteristic in the statement.
For the horn argument, dimension one includes both endpoint inclusions; J then
has one element and I is empty. Its proper-subset poset and P_pm(J) are empty,
and both pushout descriptions still work. Dimension-zero simplices of X and Y
are unrestricted; dimension-zero horns are correctly absent. No additive zero
object or scheme is involved.

I checked the seven proof steps against the node, rather than only the short
signature. The docstring includes the cube product and its union/intersection;
the two faces missing from a horn; the first attachment and its intersection;
the second attachment, cover and intersection; pushout-product and composition;
Ex preservation of Kan fibrations by transposing horn squares; and finally
transposing an arbitrary anodyne square. The latter two steps use the natural
Sd-Ex adjunction, so they do not assume the theorem being stated. The required
pushout-product and lifting-class closure interfaces are the existing Mathlib
ones, which I opened. The imports retain all recorded statement and stated
proof dependencies. There are no new nodes or dependency modules to audit.

Independent searches used different semantic phrasing from the worker:

- LeanFinder, via `msearch.py`, query `Left adjoint Sd sends trivial Kan
  cofibrations to trivial Kan cofibrations`: eight returned types, concerning
  the homotopy-category adjoint, truncation adjoints and generic cofibrant
  objects; no subdivision-preservation theorem.
- LeanSearch, via `msearch.py`, query `The image of an anodyne map under
  barycentric subdivision has the left lifting property against Kan fibrations`:
  eight returned types, including horn lifting, `fibration_iff`, generic model
  lifting and subcomplex images; none states the required conclusion.
- Loogle, via `msearch.py`, query `SSet.sd, SSet.anodyneExtensions`: zero hits.
- Case-insensitive `rg` across the full pinned Mathlib, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `(anodyne|trivialcofibration|acycliccofibration).*(subdiv|sd\.)` and
  its reverse, plus `subdivision_anodyne`: only the explicit subdivision TODO
  in `AnodyneExtensions/Basic.lean:46` and the downstream proof-plan citation
  in `SubdivisionExHomotopyAdjunction.lean:42-43`. I opened the surrounding
  TODO, the definitions, and the pushout-product theorem; none is an existing
  statement of this item.

Mismatches found: none. Changes made by this second reading: this independent
review section only; the correct Lean module and node record are left intact.
There is one named theorem with its entire proof `by sorry`, no definitions,
no hollow data, and no proved theorem. The module and declaration docstrings
identify the source and blueprint; all Lean lines are at most 100 characters;
both implicit-variable options are disabled and `u`, X, Y, f, hf are bound.
I checked programmatically that `lean.statement` is verbatim the file's
signature and that `lean` is the only node field changed from the shared base.
The prescribed `scompile.py` and delivery dry run provide the final compiler
and preflight validation.
