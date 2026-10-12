## What changed

Corrected `CategoryTheory.site_injective_cech_acyclic` to use covering indices and
abelian coefficients in universe `max u v`. The old independent-universe
statement is already disputed and mathematically false, as documented by E2.
The correction retains both conclusions of Stacks 03AW and introduces no new
hypothesis beyond the appropriate sizing of the category of abelian sheaves.
No target signature or definition changes.

Proved the corrected theorem using exact sheafification, the split embedding
into `Presheaf.cofree`, positive-degree exactness, and the existing proved
`site_cech_zero_cohomology`. Added proof-only imports of
`SiteCechZeroCohomology`, `SiteCechCofreeExact`, and
`Mathlib.Algebra.Category.Grp.FilteredColimits`. The last import is necessary:
removing it produced missing HasWeakSheafify and PreservesMonomorphisms instances.

Reused the proof of the previous C2 delivery (which was returned at landing),
including its chosen-product contraction. Removed its duplicate private
`projection_ext'`: the face-transport proof now uses the product's recorded
universal property directly, without declaring a duplicate theorem or changing
another module's visibility. This addresses the reported landing failure.
The existing `projection_ext` in SiteCechComplex is private and cannot be used
by a different module. The previously proved degree-zero module is imported,
not copied or delivered again. The new module has only one public theorem.

Both delivery modules and all four original direct callers compiled cleanly
through lcompile.py. The callers were temporarily copied into the sandbox for
this counterfactual check and then removed; none is adapted or delivered.
No forced adaptations are required. The unit sk-thm-p1 realized statements and
steps remain unchanged; this item is below their level.

Repair of the landing return at head 1707f242f: added the missing user
`Sheaf.Topology.DirectedInjectiveDerivedSectionsAcyclic` to the change record
under `## Users`, with its current unclaimed status and universe specialization.
The refreshed downstream scan lists four external declaration users. Compiled
the fourth caller unchanged against the delivery overlay, then removed the
temporary copy; no caller adaptation or additional Lean file is delivered.
The existing second-reading entry below records the earlier three-caller audit;
this repair adds the fourth-caller check without rewriting that reader's entry.
The refreshed dry run also required updating the node's citer list: removed
`lem-weil-pbc-etale-limit-acyclic-replacement`, which no longer cites this node,
and added `lem-sc-injective-cech-total-sections-nat` and
`lem-weil-pbc-etale-limit-injective-colimit-acyclic`, with individual effect notes.
The first retains its explicit sheafification hypothesis and hom-sized
free-representable argument; the second uses aligned small-etale universes.

## Proved and sorry left

Closed the single original hole, `CategoryTheory.site_injective_cech_acyclic`
(node `lem-weil-pbc-site-injective-cech-acyclic`), by proving its explicitly
corrected signature. This does not prove the old false universe-polymorphic
statement; the correction is documented in the node and change record.

Also proved `CategoryTheory.SiteCechComplex.exactAt_cofree`
(node `lem-weil-pbc-site-cech-cofree-exact`) and its private face and differential
helpers. There are no sorries in either delivered module and no new hole or
split-off obligation. The original callers retain their exact signatures and
proofs. This is a proof plus an interface correction, not a decomposition.

## No longer needed

No original import is removed, and no existing dependency module is claimed
pruned from the targets' closure. The old route's explicit free-presheaf complex,
Yoneda identification, and image-factorization construction are unnecessary:
the cofree contraction and splitting implement positive acyclicity directly.
The exact-sheafification dependency remains used, as does the chosen-complex
node. The old proof dependency `def-weil-pbc-sites-and-cohomology` is no longer a direct
proof dependency; it remains in `stmt_deps` and is not claimed pruned from the
targets' import closure. No existing unit
statement or step is bypassed. The original file had no proof-only imports of
separate free-complex nodes to remove.

## Where the brief, the DAG or earlier work was wrong

The independent coefficient universe allows E2's Type 1 / Type 0 counterexample;
we cannot honestly close that signature. This is corrected under the brief's
permission to repair an intermediate statement. The four external declaration users
are already appropriately sized: small etale uses u+1, SmallCategory uses u,
and both Opens X callers use object universe u with hom universe 0. Each original caller
compiles against the correction, so their statements and proofs do not change.
The downstream scan found 762 transitive importers and exactly four external direct
users. The node's statement_change lists all ten current DAG citers individually.
Other DAG uses continue in ordinary appropriately sized abelian categories;
InjectiveCechTotalSections already uses its separate U1 route.

Read Stacks [03AT](https://stacks.math.columbia.edu/tag/03AT),
[03AW](https://stacks.math.columbia.edu/tag/03AW), and
[03F6](https://stacks.math.columbia.edu/tag/03F6), plus upstream CechComplex's
cofree construction and contraction. The local literature TeX is absent;
the official tag pages supply the same source proofs. The insertion operation
uses a genuine universal-property choice determining the inserted map uniquely,
not arbitrary data chosen from an unproved existence theorem.

Edge cases of the new theorem: an empty family has no tuple components, so the
extensionality proof is vacuous; q=0 computes exactness in degree one with the
same Fin.sum_univ_succ sign argument; arbitrary choices of products are handled
by their universal properties. No covering or injectivity is required by the
cofree theorem. For the main theorem, even an empty covering's degree-zero
identification is supplied by the existing sheaf-gluing proof.

Fresh searches: LeanSearch returned Internal Server Error (unavailable, no verdict).
LeanFinder for injective-presheaf Cech exactness found resolution
and Mayer-Vietoris results, not this chosen-complex assertion; Loogle for
Injective.factorThru found the splitting API. msearch grep returned no hit, but
local rg in both library roots identified the upstream cofree theorem for a
different complex, which guided the reused contraction. Search records are
in searches.jsonl and in the new node. No claimed search result is invented.

## New nodes

`lem-weil-pbc-site-cech-cofree-exact` records the completely proved positive-degree
exactness of the chosen complex of a cofree abelian presheaf. The proof evaluates
at maps from an object Z, chooses a lift for each fixed composite Z -> U, and
prepends it to the tuple. Uniqueness of fibre-product maps identifies every face;
the expanded cocycle equation gives the primitive's differential. The node's
source is Stacks 03AT and its only proof dependency is the chosen-complex node.
This reuses C2's unlanded construction, with the duplicate helper removed and
fresh search records and provenance. Change record:
`coord/changes/site-injective-cech-universes.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the repository using diff. Its sole existing
   declaration changes only the two universe annotations documented in
   `coord/changes/site-injective-cech-universes.md`, plus its proof and explanatory
   docstring. The original independent-universe statement remains unproved; this
   delivery proves the explicitly corrected intermediate statement. No target or
   definition changes. The auxiliary module is new. All three direct callers were
   independently compiled as unchanged scratch copies against the delivery overlay;
   they compile without warnings. Verdict: the declared interface correction is
   explicit and its callers retain their signatures.
2. Compiled both modules with lcompile.py. Scratch copies with #print axioms for
   `CategoryTheory.site_injective_cech_acyclic` and
   `CategoryTheory.SiteCechComplex.exactAt_cofree` list exactly propext,
   Classical.choice, Quot.sound, with no sorryAx. There are no sorries or prohibited
   declarations in the delivered sources, and no definition is added. The local
   choice of an index and lift is from the explicitly proved tuple-supplied
   existence, inside a theorem proof; inserted maps are determined uniquely by the
   product universal property. Verdict: both are complete kernel-checked proofs.
3. There are no split-off holes. Read the new cofree theorem and its natural-language
   proof, checked the empty-family case (no components) and q=0 (degree-one cocycles),
   and followed the face transport and alternating-sign calculation. The lift is
   fixed per Z and composite v, so deleting a face does not change it. Fresh
   LeanFinder search for an alternating restriction complex returned Mayer-Vietoris,
   alternating-constant and degreewise-exactness results, no chosen-product theorem.
   Loogle found Adjunction.map_injective, already used. msearch grep returned no hit;
   independent rg found the upstream cofree exactness proof. Its category-of-products
   complex requires HasFiniteProducts (Over U); the present statement only supplies
   the chosen family products, so it is not directly applicable. Verdict: the new
   fully proved theorem is a genuine ingredient, not a restated hole.
4. Read the proof from the target downward: Mathlib transfers injectivity through
   exact sheafification; the cofree monomorphism splits; the contraction supplies a
   primitive; the chain-map retraction transports it back; the existing degree-zero
   theorem supplies the second conclusion. Both original public imports are needed
   by the main signature; all three added main imports are proof-only. Both public
   imports of the new module are needed by its signature, including Presheaf.cofree
   from the upstream CechComplex module. The sk-thm-p1 realized statement and steps
   are untouched; this item is below the unit level. Verdict: no unused import or
   bypassed unit step found. The removed old direct proof dependency is now named
   explicitly under No longer needed; no module pruning is claimed.
5. Compared the old and new node proof plans, proof_deps, proof_origin, lean records,
   and statement_change. The main node records exact sheafification, the chosen
   complex, cofree exactness, and degree-zero identification. The auxiliary node has
   the required source, searches, provenance, blueprint, chapter/unit and Lean record.
   Its only node dependency is the chosen-complex construction; the upstream cofree
   implementation is credited in the source and proof_origin. The new dependency
   list is exactly the union of proof-step uses. Verdict: records agree with Lean.

Second reading changed only the report (explicitly identifying the removed site
proof dependency and recording this audit) and the auxiliary node's proof wording
(fixing the chosen lift once per composite). No Lean edit was needed. Closed original
holes: the corrected `CategoryTheory.site_injective_cech_acyclic` only; added holes:
none. The new `CategoryTheory.SiteCechComplex.exactAt_cofree` is fully proved. This is
an interface correction with a complete proof, not a decomposition and not a proof
of the old disputed universe-polymorphic signature.


## Second reading by X3

1. Compared the existing module and node against the repository with diff. The only
   existing signature changes are T and AddCommGrpCat from w to max u v, exactly
   as recorded in coord/changes/site-injective-cech-universes.md. The theorem retains
   both conclusions and every site hypothesis. No target or definition changes.
   Independently compiled all four unchanged direct users, including
   DirectedInjectiveDerivedSectionsAcyclic, against the delivery overlay; all pass.
   Verdict: the interface correction is explicit and no caller adaptation is needed.
2. Independently compiled both delivered modules and a scratch axiom-check module.
   Both public theorems use exactly propext, Classical.choice and Quot.sound, with
   no sorryAx. Read both source files: no sorry, forbidden declaration or new
   definition. The locally chosen family lift has a proved existence witness;
   the inserted map is uniquely characterized by the recorded universal property.
   Verdict: complete kernel-checked proofs, with no hollow data.
3. No split-off holes remain. Read the fully proved exactAt_cofree statement,
   docstring and node against the contraction. Checked q=0 and the empty family:
   the alternating sum works in degree one, and empty tuples leave no components.
   The lift depends on Z and v, not on the tuple; hb and hv ensure face compatibility.
   Fresh LeanFinder query for exactness of alternating products of sections of a
   coinduced presheaf returned alternatingConst_exactAt and Mayer-Vietoris results,
   with no chosen-product match. Independent rg located the upstream cofree
   contraction, whose categorical-products complex assumes HasFiniteProducts
   (Over U); this delivery instead uses the supplied chosen family products.
   Verdict: a genuine proved ingredient, not a renamed obligation.
4. Followed the main theorem downward: exact sheafification transfers injectivity,
   Injective.factorThru splits toCofree, the cofree contraction gives primitives,
   and the retraction transports them back; the existing degree-zero result closes
   the other conclusion. Read Stacks 03AW, 03F6 and 03AT on the official tag pages.
   All added main imports are proof-only; both public auxiliary imports supply
   signature data. No shorter applicable library result was found. The old direct
   dependency def-weil-pbc-sites-and-cohomology is explicitly named under No longer
   needed; no import-closure module pruning is claimed. Read sk-thm-p1.realized:
   this lower-level ingredient does not replace any realized unit step.
   Verdict: route and pruning records agree with the proof.
5. Compared both nodes with Lean, including proof, proof_deps, proof_origin and
   lean.statement. The main plan records the splitting, positive exactness and
   degree-zero identification. The auxiliary node records the fixed-per-composite
   contraction, source, actual searches, provenance and required new-node fields.
   statement_change lists the updated ten citers and their individual effects;
   the change record lists all four direct Lean users. Verdict: records agree.

This reading changed only the report by adding this current four-caller audit.
No Lean repair was needed. Temporary caller and axiom-check modules were removed
before delivery. Holes closed: CategoryTheory.site_injective_cech_acyclic at its
explicitly corrected signature; holes added: none. The old false independent-universe
signature is not claimed proved. CategoryTheory.SiteCechComplex.exactAt_cofree
is a new fully proved ingredient, not a split-off hole.
