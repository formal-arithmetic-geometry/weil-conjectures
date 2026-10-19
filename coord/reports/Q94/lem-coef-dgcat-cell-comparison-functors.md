## Worker report

The module `Sheaf.CategoryTheory.DgCategoryCellComparisonFunctors` states
`CategoryTheory.Dg.cellComparisonFunctors`. Its only postponed theorem is this
main theorem, with proof `sorry`. The three supporting declarations are a
predicate spelling out the four attaching equations, the relative free
four-generator presentation, and the complete existential proposition for the
comparison functors. They do not choose any construction from an existence
assertion and contain no `sorry` data.

I read the item's complete statement and nine proof steps, both original
statement-dependency nodes and their complete recorded Lean modules, and the
newly landed sibling `lem-coef-dgcat-cone-word-normal-form` with its complete
Lean module. I also read the example CompactObject module and its node record,
the stage-2 brief, stage document, delivery-errors H, worker role, SETUP, GOAL,
STATE, and tools README. No repair note is present for this item.

Source read: Tabuada, https://arxiv.org/pdf/0710.4303, Chapter 1, section 1.3.1,
Lemma 1.10 on printed p. 29 (PDF page index 28), particularly the construction
of L0, L1, L2, L3 and the two functors between M and L3. I also read Proposition
1.7 on printed p. 27 (PDF page index 26), including the shifted cone module,
its differential and contraction matrix. The arbitrary closed-arrow case and
the two minus signs are the explicit generalization already present in the
reviewed node. The paper's displayed unsigned top row is not used to change
the reviewed node's correct cochain signs.

Hypotheses and clauses are rendered as follows.

| Node text | Lean rendering |
| --- | --- |
| R commutative | `(R : Type u) [CommRing R]`; no nontriviality or characteristic hypothesis |
| A a small R-linear cochain dg category | `{A : Cat R}`, the dependency's enrichment in cochain complexes of small R-modules |
| u:x→y closed of degree zero | `(c : ClosedArrow R A)`, with `source`, `target`, `arrow : ...X 0`, and `closed : d 0 1 arrow = 0` |
| Labelled cone enlargement | `(K : FormalConeCalculus R)`, using the exact dependency interface, universally in its realization |
| L full on the representables and the chosen Z=C_u | Existing `coneWordBase R K c`: full Hom complexes pulled back along `coneWordLabel` on `Option A`; `some x` labels the representable and `none` the chosen cone |
| T freely adjoins h of degree -1 with dh=1_Z | `(E : ConeContractingCell R K c)`, the existing abbreviation for the dependency's `ArrowCell`, with `coneWordH R E` its generator |
| T0 full on representable labels, identified with A | Existing `coneWordOldCategory R E`, whose underlying object type is literally A and whose Hom complexes are the full T Hom complexes |
| The four coordinate maps | Existing `coneWordInY`, `coneWordOutY`, `coneWordInX`, `coneWordOutX`, which apply E's attaching functor to K's actual coordinates, of degrees 0,0,-1,1 |
| v_h, a_h, b_h, w_h | Existing `coneWordV`, `coneWordA`, `coneWordB`, `coneWordW`, the exact composites π_x h ι_y, π_x h ι_x, -π_y h ι_y, -π_y h ι_x, with degree transports only |
| B has no new objects | `RelativeInverseCell.objects_bijective` identifies every object with its original label through `inclusion` |
| Four freely adjoined generators | `RelativeInverseCell.v`, `.a`, `.b`, `.w`, with endpoints and degrees 0,-1,-1,-2; `.universal` is the relative free presentation over A, quantifying over every coefficient dg functor and every four arrows satisfying exactly the attaching equations |
| dv=0, da=vu-1, db=uv-1, dw=ua-bu | `InverseCellEquations`, instantiated by `RelativeInverseCell.equations` on `mapClosedArrow R inclusion c`; the four conjuncts are literally these four equations |
| F:B→T0, G:T0→B | The existentially bound `F` and `G` in `CellComparisonFunctors` |
| Identity on labels | The `F_obj` and `G_obj` conjuncts, relative to the label bijection supplied by B's attaching functor |
| Identity on the original A coefficients | the `F_old` clause and the `G_old` clause, in every Hom degree and for every original homogeneous coefficient, using `coneWordOld` and `B.inclusion.map` |
| F(v), F(a), F(b), F(w) | the `F_v` clause, the `F_a` clause, the `F_b` clause, the `F_w` clause set these equal to the four existing coneWord component definitions |
| G(v_h), G(a_h), G(b_h), G(w_h) | the `G_v` clause, the `G_a` clause, the `G_b` clause, the `G_w` clause recover the four generators |
| More precise dg functor T→Cone(B) | The existentially bound `extension : E.category ⟶ (K.cones B.category).category` |
| Restriction on L is the labelled cone extension of j | the `extension_base_obj` clause and the `extension_base_map` clause agree on every label and every homogeneous arrow with `K.extend B.inclusion` restricted along the literal full L inclusion |
| Value on h is [[-b,-w],[v,a]] | The existentially bound `H` is an actual degree -1 endomorphism of the specified C_{j(u)}; the `extension_h` clause identifies it with the image of h; the `H_00` clause, the `H_01` clause, the `H_10` clause, the `H_11` clause fix all four entries under the dependency's matrix equivalence |
| Restriction on T0 is the representable embedding after G | the `extension_old_obj` clause and the `extension_old_map` clause specify the equality on all objects and all homogeneous arrows with `G` followed by `(K.cones B.category).embedding` |

`HEq` is used only at the object-identification boundaries and at the two
numerical degree equalities (-1-1=-2 and -1+1=0). The paired object clauses
make these homogeneous-map comparisons inhabited and precise. In particular,
the restriction clauses quantify over all homogeneous arrows, not just the
four displayed generators. The four entries completely determine H because
`ConeSystem.matrix` is a linear equivalence onto the actual two-by-two matrix
space. H is not an arbitrary contraction chosen without normalization.

The theorem is universal in K, E, and the free presentation B, matching the
node's “let L, T, T0, B be” clauses rather than selecting unrelated objects.
`RelativeInverseCell` merely packages B's specified free presentation. Its
existence is supplied by the successive free-attachment construction of the
original dependency; the theorem does not add a homotopy-equivalence assumption
on the input closed arrow, or assume that a comparison map already exists.

Dependency declarations used:

* `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`: `CategoryTheory.Dg.Cat`,
  `hom`, `mul`, `unit`, `ArrowCell`, `generator`, and their strict dg functor
  category. Its `freeCellCalculus` theorem is the nine-field interface for the
  existing construction; the proof docstring names the successive attachments.
* `Sheaf.CategoryTheory.DgCategoryFormalConeEnlargement`:
  `CategoryTheory.Dg.ClosedArrow`, `mapClosedArrow`, `FormalConeCalculus`, its
  `cones`, `coordinates`, `extend`, and `ConeSystem.matrix` and `embedding`,
  together with `coneEntry00`, `coneEntry01`, `coneEntry10`, `coneEntry11`.
  The interface comes from `formalConeEnlargement`.
* `Sheaf.CategoryTheory.DgCategoryConeWordNormalForm`: the exact `coneWord*`
  definitions and `ConeContractingCell` listed above. I added the landed node
  `lem-coef-dgcat-cone-word-normal-form` to `stmt_deps` under STMT_DEPS MAY GAIN
  LANDED NODES. Its normal-form theorem is not invoked or restated. This imports
  the shared concrete constructions, and introduces no dependency cycle: the
  sibling's dependencies are free-cell calculus, formal-cone enlargement and
  graded-linear categories, none of which depends on this item.

No new independent notion needs a definition node, and no dependency record is
repaired. The relative free presentation and complete comparison proposition are
helpers specific to the constructions in this item's own statement and are
listed in `lean.declarations`.

Edge cases checked by inspecting the formulas and their types:

* R may be the zero ring or have characteristic 2: no cancellation by 2,
  nontriviality, division or characteristic assumption appears.
* x=y and loop arrows, including u=1 and u=0: no distinctness assumption appears;
  the cone remains a distinct label through `Option A` even if the underlying
  module is isomorphic to a representable.
* No invertibility of u is assumed. For u=0 the free construction may make
  original identity arrows boundaries; this is permitted, not excluded.
* Empty A has no ClosedArrow and hence no spurious chosen object; the theorem
  remains universally quantified without a Nonempty hypothesis.
* All homogeneous degrees and all coefficient arrows are quantified in the
  restriction clauses; no boundedness, flatness, finite generation or h²=0
  condition is imposed. The graded coordinate maps are never assumed closed.
* Targets of the relative free universal property may identify old objects.
  This retains the loop and repeated-label cases.
* In degree -1 the matrix differential is (-db+uv,-dw+ua-bu;-dv,vu-da),
  hence the prescribed equations give the identity. Selecting its four entries
  recovers v,a,b,w with exactly the two required minus signs.

Searches actually run for this item:

* `msearch.py ... leanfinder` with “Comparison dg functors between adjoining a
  contraction of a formal cone and freely adjoining coherent inverse data”:
  8 hits, chiefly `CochainComplex.mappingCone.mapHomologicalComplexXIso`, its
  variants, ordinary cone functoriality, and `mappingCone.mapTrianglehIso`.
  None gives these strict dg-category free presentations or comparison functors.
* `msearch.py ... loogle` with `"EnrichedFunctor", "mappingCone"`: 0 hits.
* `msearch.py ... grep` with `CellComparison|dg[Cc]at|DGCategory|Kontsevich`:
  0 Mathlib hits.
* `msearch.py ... leansearch` with “A formal cone contraction determines
  coherent inverse generators and comparison differential graded functors”:
  8 hits about ordinary categorical limits/cones and mapping cones of cochain
  complexes, not this statement.
* Direct `rg` over upstream `WeilConjectures` and the project's `lean/Sheaf`
  for the item id, dg-category keywords and comparison names: no upstream
  item match; the project's landed free-cell and formal-cone modules, parent
  equivalence-cell calculus and sibling normal-form module were found and read.
  The parent treats its universal two-object cell, pushouts and liftings, not
  this arbitrary-relative-category comparison statement. The sibling supplies
  exactly the shared constructions and hence is reused.
* Direct upstream grep by the full item id: no hits. Direct search in
  `dag/lean_names_upstream.json`: no exact item or formal-cone-comparison match.
* Direct `rg` for `RelativeInverseCell`, `InverseCellEquations`,
  `CellComparisonFunctors`, `cellComparisonFunctors` over Mathlib, upstream
  `WeilConjectures`, and project `lean/Sheaf`: no pre-existing declarations.
* Read the Mathlib MappingCone module's header, mapping cone definition and
  coordinate declarations (lines 13--100), and Enriched.Basic's full enriched
  functor signature (lines 295--335). These supply ordinary complex cones and
  enriched functor data; neither is an existing statement of this node.

No statement correction and no STATEMENT-DISPUTED issue. The module docstring
and theorem docstring name the source; the theorem docstring follows all nine
DAG proof steps. Compiler checks and the delivery dry run use only the
prescribed wrappers, with all files in this item's sandbox.

Compilation diagnosis: the first complete record version passed the sandbox
check in 21.8 seconds but timed out while emitting its library artifact. The
wrapper confirmation also timed out rebuilding the already-landed free-cell
dependency. I replaced the final record by an explicit existential proposition
with the identical functor, matrix, object and homogeneous-map clauses. Clause
names are retained as comments for the table above; no mathematical condition
was removed. This avoids generating a large family of record projections.

Validation: the revised module passed scompile.py with no diagnostics: sandbox
37.0 seconds and library artifact 15.5 seconds, both within the unchanged
60-second limit. There is exactly one sorry, on the matching main theorem;
all Lean lines are at most 100 characters, and autoImplicit is disabled. The
node copy changes only lean and the additional landed statement dependency.

## Second reading by Q94

Independent maintainer second reading, 2026-10-17, of immutable delivery
`a1c22310dd219a1c11f14f14bdc524197b7954a9`. This section was supplied by
the independent reviewer; it does not claim that a Q94 worker performed a
second reading. I read the item node, all three statement-dependency nodes,
the delivered module and report, and the dependency modules and exact declarations
in the read-only Q94 clone. The dependency node records there match the snapshot.

Source checked: Tabuada, arXiv:0710.4303, Chapter 1, Definitions 1.3–1.4,
Proposition 1.7, printed pp. 26–27, and Lemma 1.10's construction on printed
p. 29 (PDF index 28), continuing to p. 30. The paper constructs the cone
contraction and the two functors; the node explicitly generalizes to an arbitrary
closed arrow. I checked that generalization from the free relative presentations.
The unsigned top row in the paper's Proposition 1.7 does not satisfy the displayed
cochain differential with its stated generator equations. The node already uses
the correct top row `[-b,-w]`; no source-based statement correction is needed here.

Hypothesis and conclusion checks, independently against the Lean:

* `(R : Type u) [CommRing R]` allows every commutative ring, including the zero
  ring. `Cat R` is the recorded enrichment in cochain complexes of R-modules.
  Its object and module carriers are U-small, exactly the free-cell dependency's
  stated size convention. There is no new equality of independent universes.
* `ClosedArrow R A` supplies both endpoints, a degree-zero arrow and `du=0`.
  There is no assumption that its cohomology class is invertible.
* `FormalConeCalculus R` supplies the labelled full cone category, actual
  coordinates, full Hom-complex embedding and entrywise functor extension.
  Universal quantification over this characterized realization is appropriate.
* `coneWordBase` uses `Option A`, with `some x` the representable and `none`
  the distinct cone label. `ConeContractingCell` is precisely `ArrowCell` for
  degree -1 and differential the cone identity. `coneWordOldCategory` pulls
  back the full Hom complexes to object type A. These existing definitions
  are reused, with the sibling recorded in `stmt_deps`.
* `RelativeInverseCell` has the four generators with exactly the endpoints
  and degrees 0,-1,-1,-2. `InverseCellEquations` gives all four differential
  equations, with right-to-left composition and the correct signs.
  Its object bijection expresses unchanged labels. Its relative universal
  property quantifies over every dg functor out of A, including functors
  identifying objects, and characterizes precisely the successive free
  attachments. It neither assumes comparison functors nor chooses data from
  an uncharacterized existence theorem. This is a local presentation helper,
  not a second copy of the parent node's two-object universal cell.
* `CellComparisonFunctors` existentially supplies F:B→T0 and G:T0→B.
  The two object clauses fix labels; `F_old` and `G_old` fix every homogeneous
  original coefficient. All eight prescribed generator images occur literally,
  using the sibling's four concrete `coneWordV/A/B/W` composites.
* The same existential supplies the dg functor `extension:T→Cone(B)`.
  `extension_base_obj/map` agrees with `K.extend B.inclusion` on every object
  and homogeneous map of L. Its image of h is the degree -1 endomorphism H
  at exactly `C_{j(u)}`. The four `H_00/01/10/11` clauses specify
  `[-b,-w;v,a]` under a linear equivalence onto all matrices, hence pin H
  uniquely. `extension_old_obj/map` agrees with G followed by the full
  representable embedding on every object and homogeneous map of T0.
  The accompanying object equalities justify the `HEq` transports; none is
  an empty-antecedent substitute for a restriction equality.

I checked all nine proof-docstring steps against the cited statements:
1. `FreeCellCalculus.exists_arrowCell` applies successively because the
   attaching expressions are closed, including
   `d(ua-bu)=u(vu-1)-(uv-1)u=0`.
2. The actual cone coordinates give `dι_y=dπ_x=0`, `dι_x=ι_y u` and
   `dπ_y=-uπ_x`, with the graded projection/inclusion identities.
3. Signed Leibniz gives the four stated equations for v_h,a_h,b_h,w_h.
4. The free relative presentation extends the coefficient functor to F.
5. `FormalConeCalculus.extend_obj/extend_matrix` gives J on all labels and
   matrix entries, including each coordinate map.
6. At degree -1 the matrix differential has entries
   `(-db+uv,-dw+ua-bu;-dv,vu-da)`, which are the identity matrix.
7. The free attachment universal property extends J by h↦H.
8. `ConeSystem.embedding_full` is an isomorphism of the full Hom complexes,
   so restriction to representables gives a dg functor G.
9. Selecting H's four entries and the two defining minus signs recovers
   v,a,b,w. No closedness of coordinates or relation h²=0 was used.
The non-elementary extension and full-embedding steps cite the appropriate
nodes; the coordinate and matrix calculations are elementary consequences.

Edge cases: x=y, u=0, u=1 for an endomorphism, characteristic two, zero ring,
all integer degrees and coefficient arrows are retained. Empty A has no
ClosedArrow, so the universal statement is correctly vacuous without a chosen
object. Nothing assumes boundedness, flatness, finite generation, nonzero
identities or distinct objects. The cone label remains separate in all cases.

One-definition checks: I independently searched Mathlib, upstream
WeilConjectures and Q94's lean/Sheaf for the four new declaration names and
for cone/contraction vocabulary. The closest Mathlib declarations in
`Algebra/Homology/HomotopyCategory/MappingCone.lean:13–100` concern cones of
individual complexes; `CategoryTheory/Enriched/Basic.lean:295–335` supplies
ordinary enriched functor data. Neither gives this relative free dg-cell
comparison. I read the existing parent's `IsFreeCell` and
`EquivalenceCellCalculus`; they concern the universal two-object cell and its
realization, pushout and lifting properties, not this arbitrary-relative-A
presentation. The worker's LeanSearch, LeanFinder, Loogle and grep records
are present, with concrete candidates and non-match explanations. Shared
cone/category/component definitions are reused, and there is no dependency
cycle or missing helper requiring repair.

Pilot gates: every declaration has a source/blueprint docstring; the theorem
has all nine proof steps. The sole theorem body is `sorry`; the two predicates
and the presentation structure contain genuine formulas/data, without hollow
definitions. There is exactly one sorry and no line over 100 characters.
`autoImplicit` is false and all variables and universes are bound.
The node's `lean.statement` is verbatim the delivered theorem signature.
Against the read-only base node, only `lean` and the added landed sibling
`stmt_dep` differ. There are no new nodes or dependency-module repairs.

Compiler evidence: on 2026-10-17 I reproduced the delivered file using
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q94
lem-coef-dgcat-cell-comparison-functors
snapshot/lean/Sheaf/CategoryTheory/DgCategoryCellComparisonFunctors.lean`.
Exit code 0; sandbox 7.8 s, library artifact 7.6 s; no diagnostics. The
installed wrapper currently uses the server side overlay with wire confirmation,
so this run supplies server confirmation rather than claiming a local compile.
No global build, direct ssh command, live Lean edit, Git mutation or project
clone edit was performed. Pro-etale substitutes are inapplicable.

Finding repaired: H11 (and the substantive second-reading requirement of H1):
the original section explicitly said no second reading occurred. This complete
replacement report preserves the Worker report and replaces that placeholder
with the independent reading above. No mathematics, Lean file or node record
needed a change. The delivery is suitable to land with this report-only FIX.
