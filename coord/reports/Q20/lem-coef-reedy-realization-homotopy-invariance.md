## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-reedy-realization-homotopy-invariance.json`: item, split; original statement retained verbatim.
- `dag/nodes/sec-six-functors/lem-coef-reedy-realization-prism.json`: statement-only supporting lemma, unsplit, no exact Mathlib match after two semantic phrasings, LeanSearch, Loogle and source searches.
- `citations.json`: literal quotations for every citation of all five proof steps.

Attachments: none. Searching the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, Reedy, prism and realization found no declaration of this item. The upstream master is not used as evidence of completion.

WANTED: an archived copy of Dugger, *A Primer on Homotopy Colimits*, formula (3.2), proof of Theorem 3.5 and Section 19.1, for the item and prism node. I read these online at https://pages.uoregon.edu/ddugger/hocolim.pdf; no document was downloaded or written into the shared repository.

WANTED: an archived copy of Hovey, *Model categories*, Theorem 1.2.10(iv), for the existing localization-detection input. I read it online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf.

The earlier attempt's report, node files and citations are retained in `earlier-attempt/`, and its searches remain in `searches.jsonl`. I started with the required dry run. It rejected new-node searches that were not in the item's msearch log. These queries have now actually run through the prescribed command, with the hits read, and the new prism node records their actual outputs rather than the old summaries. `rerun_searches.log` retains the complete outputs. I initially passed each proposed node id as msearch's item argument, which placed those logs in separate Q20 item directories; I corrected the invocation to the assigned item and reran them so the required delivery log is in this sandbox. No fabricated log entry was added.

Two proposed nodes are withdrawn from this delivery. The left-homotopy endpoint criterion, although matched by Mathlib's `HomotopicalAlgebra.Cylinder.LeftHomotopy.weakEquivalence_iff` (LeftHomotopy.lean:140-145, read), is elementary from the cylinder identities and two-out-of-three, so it is now Step 4. The proposed two-out-of-six lemma is unnecessary: Step 5 uses the existing `lem-coef-model-localization-detects-weak-equivalences`, which states exactly the needed reflection property, and writes the inverse formulas explicitly. The earlier prism node referred to the item for its realization formula; its statement is now independent, with the coend, cylinder identities and endpoint restrictions stated in full. This removes a hidden statement dependency back to the item. It has no proof or proof dependencies.

Nothing remains unfinished in this one-level split. Proving the supporting prism lemma is a later item's work. No Lean file, compiler, Lake command, live project file, maintainer metadata, unit record or chapter record was changed. This item is not a unit key node. The current main-20261015 ancestor proof was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`; paragraph beginning “For K” is the finite mapping-complex adjunction that the pre-existing dependency chain serves. Historical ancestry and the assigned unit are retained; there is no route change or SGA input.

## Review by Q20

For the item and new prism node I read Dugger formula (3.2) on printed p.9, the skeletal pushout in the proof of Theorem 3.5 on printed pp.10-11, and the simplicial tensor/SM7 formulation in Section 19.1 on printed p.90. Theorem 3.5 concerns objectwise weak equivalences of Reedy-cofibrant simplicial spaces. It does not state our combinatorial prism result. In particular, it would be incorrect to claim that Dugger supplies that exact theorem. The item keeps `proof_origin.by = agent`, and the new node's source explains the distinction. I also read Hovey Theorem 1.2.10(iv), printed p.13, which detects weak equivalences in the homotopy category, and verified it agrees with the existing localization-detection node. Neither a Stacks tag nor an SGA trace theorem states the prism fact; none is invented or cited.

I opened and read the statements of `def-coef-simplicial-tensor-cotensor`, `lem-coef-simplicial-model-nerve-localization`, `lem-coef-reedy-model-structure`, `def-weil-pbc-simplicial-set`, `lem-coef-simplicial-extra-degeneracy-prism`, `lem-coef-model-localization-detects-weak-equivalences`, `lem-coef-simplicial-realization-cylinder`, and `lem-coef-resolution-interval-tensor`. The two last statements do not give the required enriched realization theorem and are not used as if they did. I read the model-category definition in `lem-coef-model-infinity-derived-adjunction` to compare the hypotheses of localization detection with the item's own model-category definition; both require complete and cocomplete categories, retract closure, two-out-of-three and the two functorial weak factorization systems. There is no added properness, combinatoriality, fibrancy or nonemptiness hypothesis.

Step 1 uses the chosen tensor's action on morphisms as explicitly stated by `def-coef-simplicial-tensor-cotensor`. A natural transformation acts on the degree-n coend summand by its n-th component tensored with the identity simplex. Its naturality square identifies the two parallel relations. Identity and composition are checked on these summands, giving the exact identities required in Steps 2 and 3. This is an elementary universal-property calculation, not an appeal to a theorem hidden in a definition.

Steps 2 and 3 use only the new prism node's statement: the specified cylinder, its weak-equivalence projection, and the two endpoint equalities. Each is applied with source and target both A, respectively both B; both are Reedy-cofibrant by hypothesis. They use the earlier coend composition calculation to identify |gf| and |fg| with composites. Orientation is handled by retaining the endpoint order; no nonexistent simplicial self-map swapping 0 and 1 is asserted.

Step 4 uses precisely two-out-of-three and the model weak factorization systems in `lem-coef-simplicial-model-nerve-localization`. The cylinder projection p is a weak equivalence by Steps 2 and 3, and p i_j = 1. Thus both inclusions are weak equivalences. One composite H i_j is the identity, making H a weak equivalence, and its other endpoint is then a weak equivalence. Identities lie in the lifting classes and hence in W. This writes the complete short argument instead of creating a node for it. Step 5 uses the exact iff in `lem-coef-model-localization-detects-weak-equivalences`. The images F and G have invertible composites; (GF)^{-1}G and G(FG)^{-1} are left and right inverses of F and are equal by associativity. The reflection half of the cited iff then gives the conclusion. Its unrestricted endpoint hypotheses apply. The localization universe can be enlarged, as the cited statement allows. I checked there is no dependency path from this existing node back to the item.

For the new statement I checked the construction rather than merely renaming the item's assertion. Its domain concerns one homotopy between arbitrary maps u and v, without an inverse or any weak-equivalence conclusion for u. The n-prism is the simplicial set Delta^n times Delta^1, covered by the n+1 chains (0,0),...,(j,0),(j,1),...,(n,1). On chain j use H_j^n tensored with Delta^{n+1} followed by the coend map to |Y|. The internal shared-face relations are exactly d_{j+1}H_{j+1} = d_{j+1}H_j; the other face and degeneracy identities in the cited combinatorial definition identify restrictions along all outer simplicial operators. They therefore descend to the coend of these prisms. Tensor adjunctions identify that coend with |X| tensored with Delta^1 because tensoring with Delta^1 preserves colimits. The all-zero edge is the last prism's final face, hence gives u; the all-one edge is the first prism's initial face, hence gives v. This verifies the asserted order against the precise endpoint conventions of `lem-coef-simplicial-extra-degeneracy-prism`.

For its cofibrancy clause, the skeletal attachment is (L_n X tensor Delta^n) amalgamated along (L_n X tensor boundary Delta^n) with (X_n tensor boundary Delta^n), mapping to X_n tensor Delta^n. This is the pushout product of the latching cofibration with the simplex boundary inclusion. SM7 makes it a cofibration, so successive pushouts, and their sequential composite from the initial object, make |X| cofibrant. For its cylinder clause apply SM7 to initial -> |X| and boundary Delta^1 -> Delta^1, and to initial -> |X| and the trivial cofibration {0} -> Delta^1. The former gives the combined endpoint cofibration and the latter gives one endpoint as a weak equivalence; since projection composed with that endpoint is identity, projection is a weak equivalence. These are the intended proof obligations of the unsplit supporting lemma; I have not put a hidden proof into its statement.

Small cases: an initial constant diagram realizes to the initial object and has the initial cylinder; a constant diagram at a cofibrant object realizes to that object (the simplex coend contracts to Delta^0), with its usual tensor cylinder; for n=0 the sole prism is Delta^1 and the two face equalities give exactly u_0 and v_0; for n=1 the two triangular pieces share the d_1 face. Identity homotopies give coincident endpoints and the projection homotopy. An arbitrary constant noncofibrant object is not a counterexample because Reedy cofibrancy already forces degree zero to be cofibrant. Neither the initial case nor the endpoint calculation requires a terminal object to be inhabited. For Step 5, F=1, G=1 and ordinary isomorphisms yield the expected inverses.

Against delivery-errors B–E: the sole new node is statement-only and self-contained, with all five notion nodes named, no circular reference, and verbatim msearch queries/results. The item statement is unchanged. Every non-elementary step has a cited theorem with the claimed clause; the endpoint and inverse calculations are written out. No theorem is extracted from a cited node's proof. There is no unsupported small-colimit assumption: Delta and all the displayed coproduct indices are small, in the item's enlarged universes. The new node neither restates the item nor proves one of its clauses with no intermediate content: it transfers arbitrary combinatorial homotopies to a specifically described cylinder, while the item's proof handles two supplied homotopies and detects the inverse after localization. Whole-DAG and blueprint searches found no equivalent prism statement. Mathlib Reedy/Basic.lean:22-24 still marks the model structure as TODO; SimplicialObject/Homotopy.lean supplies the degree-raising data only; TopAdj.lean is topological realization of simplicial sets only. No match was upgraded on the basis of a related name alone.

## Not duplicates

- `lem-coef-reedy-realization-prism` vs `lem-coef-simplicial-realization-cylinder`: the former transfers degree-raising maps to enriched tensor realization in an arbitrary simplicial model category; the latter is the topological homeomorphism |K times Delta^1| = |K| times [0,1] for a simplicial set K.
- `lem-coef-reedy-realization-prism` vs `lem-coef-resolution-interval-tensor`: the latter concerns cosimplicial resolutions in a possibly unenriched model category and an interval coend, not realization of simplicial objects or degree-raising homotopies.
- `lem-coef-reedy-realization-prism` vs `lem-coef-simplicial-extra-degeneracy-prism`: the existing node constructs a combinatorial homotopy from extra degeneracies; it does not realize one or provide a model-category cylinder.
- `lem-coef-reedy-realization-prism` vs `lem-coef-reedy-realization-homotopy-invariance`: the new node is the prism-to-cylinder tool for a single pair u,v, with explicit endpoint and cylinder structure. It neither assumes a homotopy inverse nor asserts that a realized map is a weak equivalence; that argument remains in the item.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q20 lem-coef-reedy-realization-homotopy-invariance --no-push .` printed `OK (not pushed)` and `preflight passed` at commit 3c9b390863 on 2026-10-17. After correcting the cited Mathlib line range from 143-148 to the actual 140-145 and adding this validation record, I repeat the same command so the durable handoff receipt covers the final report and node. No push is authorized in this worker turn; the second reader delivers the accepted sandbox.


## Second reading by Q20

The recovery exception does not apply: the assigned item is
`lem-coef-reedy-realization-homotopy-invariance`, its stage-1 JSON is present,
and the named stage-2 sandbox does not exist. This is an independent stage-1
reading, with no compiler, Lean writing, git command in the shared repository,
or other agent. The worker's report, review, and earlier-attempt archive are
preserved. GOAL.md, coord/dag-sync.md, the stage-1 contract, delivery-errors B--E,
the current main-20261015 ancestor proof, and the assigned unit/chapter records
were read. The item is a generic foundational tool below the existing finite
mapping-complex route; no coefficient category, target or unit route changes.

- Item statement: PASS against its live unsplit statement (verbatim unchanged),
  Dugger formula (3.2), the Theorem 3.5 skeletal pushout on printed pp.10--11,
  and Section 19.1 on printed p.90. Dugger's numbered theorem is about objectwise
  weak equivalences of simplicial spaces; it is not misrepresented as this
  combinatorial-homotopy theorem. The general proof remains agent-written.
- Step 1: PASS against the full current statement of
  `def-coef-simplicial-tensor-cotensor`. On the alpha summand, naturality is
  exactly `f_m C(alpha) = D(alpha) f_n`, so the induced maps respect both
  coequalizer arrows. Tensor functoriality and the coequalizer universal
  property give the stated identity and composition laws; elementary.
- Step 2: PASS against the complete new prism statement and the endpoint
  convention in `lem-coef-simplicial-extra-degeneracy-prism`. Apply it to
  X=Y=A, u=gf, v=identity, or to the ordered pair supplied by the reversed
  homotopy. Both Reedy-cofibrancy hypotheses hold. Step 1 gives the composite
  of the realized maps; no reflection of the ordered interval is used.
- Step 3: PASS by a separate application of that same stated theorem with
  X=Y=B and the actual ordered pair fg, identity. The assumed Reedy
  cofibrancy of B supplies both hypotheses. No property of A is substituted
  for a missing property of B.
- Step 4: PASS against the model axioms in the current
  `lem-coef-simplicial-model-nerve-localization` statement and Mathlib's
  Cylinder.LeftHomotopy.weakEquivalence_iff, LeftHomotopy.lean:140--145.
  Identities lie in the left lifting class C intersect W. Two-out-of-three
  applied to p i_j = identity makes both endpoints weak equivalences; applied
  to H i_j = identity makes H a weak equivalence. Composition then gives
  the other endpoint. This is the elementary calculation the text claims.
- Step 5: PASS against the entire current statement of
  `lem-coef-model-localization-detects-weak-equivalences`, its definition of
  model category in `lem-coef-model-infinity-derived-adjunction`, and Hovey
  Theorem 1.2.10(iv), printed p.13. The model axioms coincide. In the localized
  category (GF)^(-1)G is a left inverse and G(FG)^(-1) a right inverse of F;
  associativity makes them equal. Reflection applies without cofibrant or
  fibrant endpoints. Traversal of statement and proof dependencies from this
  existing localization node does not reach the item.
- New node `lem-coef-reedy-realization-prism`: PASS after checking every clause
  against its five notion nodes and the Dugger passages above. Its coend has
  the correct variance: C_n tensor Delta^m for alpha:[m]->[n]. The enriched
  adjunctions identify an iterated tensor with the tensor by the product, and
  make tensoring preserve colimits in both relevant variables. Decompose
  Delta^n times Delta^1 into the n+1 chains
  (0,0),...,(j,0),(j,1),...,(n,1), and use H_j on the j-th piece. The internal
  shared face is d_(j+1)H_j=d_(j+1)H_(j+1); outer faces and degeneracies use
  precisely the other displayed homotopy identities. Thus the pieces agree
  on intersections and on the coend relations. The all-zero face uses
  d_(n+1)H_n=u; the all-one face uses d_0H_0=v. The skeletal attachment is the
  pushout product of L_n X -> X_n with boundary Delta^n -> Delta^n. SM7 and
  closure of the left lifting class under pushout and sequential composite
  give cofibrancy of |X|. Applying SM7 to initial -> |X| and respectively
  boundary Delta^1 -> Delta^1 and {0} -> Delta^1 gives the endpoint
  cofibration and a weak-equivalence endpoint. Its projection is then a weak
  equivalence by two-out-of-three. These are substantive future obligations,
  not a two-line elementary fact, and the statement itself contains no proof.

Small cases checked independently: the initial simplicial object gives the
initial realization and cylinder; the constant diagram at a cofibrant object
realizes to that object; in degree zero the prism is Delta^1 with exactly the
two stated endpoints; in degree one the two triangular pieces share d_1.
A noncofibrant constant object is excluded already in degree zero. These
checks introduce no fibrancy, properness, pointedness or nonempty-object
hypothesis. The inverse formulas in Step 5 also give the identity in the
identity-map case.

Necessity and duplication: the complete current statements of
`lem-coef-simplicial-realization-cylinder` (topological realization of sets),
`lem-coef-resolution-interval-tensor` (cosimplicial resolutions without
simplicial enrichment), and `lem-coef-simplicial-extra-degeneracy-prism`
(combinatorial homotopy data/construction) were compared directly. None gives
the new transfer theorem. Whole-DAG keyword searches and blueprint_refs.py
searches for prism and realization found no equivalent imported blueprint
node. The ancestor command confirms prop-coef-integral-exceptional-adjoint.
Reading/searching the named slopmaster2 and upstream master sources found no
candidate closed declaration. No sorry declaration was treated as a proof.
The new node concerns an arbitrary single homotopy, without an inverse or a
weak-equivalence conclusion for u; the item's two homotopies and localization
argument remain in its own steps. It is not a relabelled clause of the item.

Independent Mathlib searches actually run through msearch.py used a new
coend/weighted-simplex phrasing, the Loogle query `"Homotopy", "tensor"`, and
`Realization|Coend|Reedy` in AlgebraicTopology/SimplicialObject. LeanFinder's
interval vertex, product-simplex and Dold--Kan hits were read against the
required statement. The relevant product-simplex declarations give only
combinatorics; Homotopy.lean gives degree-raising data and operations;
Reedy/Basic.lean:22--25 still lists the model structure as TODO. The Loogle
hit is an unrelated truncated tensor-unit instance. No exact or one-line
specialization was found. Actual query records are appended to the new node
from searches.jsonl, without inventing successful matches.

All five citation quotations were checked verbatim against the current
statements (using the sandbox statement for the new node). They remain true,
so citations.json needs no repair. The new node remains statement-only,
self-contained with its five notion dependencies, single-escaped TeX, an
honest source place, searched blueprint ancestry, and no dependency back to
the item. No SGA source is used.

Changes: appended the independent search evidence to the new prism node and
this second-reading audit to the report. No mathematical repair was needed;
the correct item statement, five proof steps, citations, and one supporting
statement are retained. Backups precede these changes. One new unsplit node,
zero new Mathlib leaves. The final dry run and delivery are performed only
with deliver.py, one invocation at a time.
