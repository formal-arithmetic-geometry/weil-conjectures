## Worker report

Files written (all under the Q10 sandbox):

- `dag/nodes/sec-six-functors-basics/det-base-field-cd-galois-group.json`: statement, unchanged mathematically and textually; complete six-step split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-separable-closure-algebraic.json`: statement; Mathlib leaf, `IsSepClosure.isAlgClosure_of_perfectField`, with `PerfectField.ofFinite` inferred.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-galois-frobenius.json`: statement; Mathlib leaf with one declaration per clause (Galois instance, Frobenius formula, exact order, bijective power parametrization).
- `dag/nodes/sec-six-functors-basics/lem-sfb-infinite-galois-profinite-limit.json`: statement; Mathlib leaf, `InfiniteGalois.continuousMulEquivToLimit`.
- `citations.json`: a verbatim statement quotation for every node citation of every step.

Attachments: none. Searching the project `WeilConjectures/` by the item's exact blueprint tag and id found no declaration. Concept searches in `WeilConjectures/FieldTheory/` and `WeilConjectures/Mathlib/FieldTheory/`, and for absolute Galois group, finite fields, cyclic groups and Frobenius found only partial interfaces. In particular the project `Mathlib/FieldTheory/Finite/Basic.lean` contains geometric-Frobenius and embedding lemmas, not the unique subextension and profinite identification of this item. The exact id is absent from `dag/lean_names_upstream.json`. None is an attachment for the whole item. No master sorry declaration is treated as a proof.

WANTED: none needed for this split. The already reviewed `lem-weil-unique-subfield-of-closure` records Lang as wanted, but I use its self-contained statement, not an unavailable part of its proof. All sources needed for the present Mathlib leaves and the existing node interfaces were available locally.

The original proof assumed a degree-n extension without establishing that one exists for each n. It also had no cited nodes, no elementary judgments, no definition dependencies and no justification that the final limit map is a homeomorphism or that its cyclic identifications commute with restriction. I filled these gaps without changing the statement. There is no STATEMENT-DISPUTED claim: the statement is true; existence was a proof gap. The earlier sandbox held only an unmodified item copy and search logs, so no previous completed split was discarded.

At the original delivery the imported metadata was incomplete. On the current base, the item has `chapter: sec-six-functors-basics` and `unit: sk-lem-base-field-cd`, and both chapter and unit JSON records now exist; I read both during this repair. I read the current blueprint section `_section.md`, the base-field-cd `_section.md` and its proof instead. This is metadata of the new snapshot, not an invitation to change maintainer-owned fields. The node's route stays exactly finite-field subextensions, cyclic Frobenius groups, and their profinite limit. No chapter/unit record is edited.

Nothing remains unfinished at this split level. Each new node is a statement-only Mathlib leaf: no proof, proof sketch or proof dependency was put into a child. The arithmetic of degree/cardinality and the coordinatewise inverse-limit identification are steps of the item, rather than new nodes.

## Searches and source reading

The full item was searched with LeanSearch and LeanFinder using its combined unique-degree-subextension, Frobenius and profinite-limit statement, Loogle with `"frobenius", "profinite"`, and grep in `FieldTheory/AbsoluteGaloisGroup.lean` for `ZHat|ZMod|frobenius|FiniteField`. The semantic hits were definitions and finite-extension ingredients, not the full result. I read the absolute-Galois-group source: it defines the group and its topological abelianization and does not prove the finite-field identification.

Each new leaf was searched separately with all four msearch kinds. The recorded query text is copied exactly from actual calls in `searches.jsonl`. All searches used here succeeded; no failed service is recorded as an absence. Single-name Loogle queries found the exact declarations, while natural-language searches supplied the alternative formulations. Earlier combined Loogle patterns with several declaration names were not mistaken for evidence of absence.

For the closure leaf I read `Perfect.lean:302-311` and `IsSepClosed.lean:225-247`, including both base-field and top-field perfection instances. The intended instance is the base-field one at line 244, with the finite-field instance at line 308. I also read Stacks `algebra.tex`, Tag 030Z, label `lemma-perfect`, and its proof: characteristic-power surjectivity characterizes perfect fields. This supplies the finite-field input; the precise closure specialization is the Mathlib instance and is named as such, rather than falsely attributing that exact formulation to 030Z.

For the Frobenius leaf I read `Finite/Basic.lean:331-406`: Frobenius is a K-algebra map, becomes an equivalence for algebraic extensions, has order the finite rank (the proof rules out smaller powers by root counting), and its first r powers give a bijection onto all automorphisms. I read `Finite/GaloisField.lean:196-204`, the instance for any extension whose top field is finite, and Stacks `fields.tex`, Tag 09HY (`section-finite`) and Tag 09I1 (`lemma-finite-Galois`). The source record distinguishes the Stacks finite-field/Galois inputs from the blueprint's Frobenius argument and exact Mathlib clauses. This is an arbitrary finite-field-extension lemma, not a new unsplit rewording of the item's conclusion: each clause is already a Mathlib interface, and it says nothing about the subfield inside the given closure or the profinite limit.

For the limit leaf I read Stacks `fields.tex:2977-3051`, Tag 0BU2, label `lemma-infinite-galois-limit`, especially assertion (3), the explicit restriction map, and the topology argument. I read Mathlib `Galois/Profinite.lean:120-141, 278-341`: `algEquivToLimit` is restriction, `continuousMulEquivToLimit` includes continuity of both directions, and `profiniteGalGrpIsoLimit` is the same equivalence packaged categorically. The new statement introduces its index set, maps and topologies, and applies to any Galois extension, including a finite one.

Before writing each new id I searched the entire DAG by concepts, declarations and Stacks tags, not only the target reach. Blueprint searches were `finite field`, `Galois`, `splitting field`, `polynomial`, `perfect`, `Galois.*limit`, `cyclic`, `separable closure`, `Galois group`, `unique subfield`, and `0BU2`. In particular `Galois group` gave the item and unrelated geometric/Galois-cover assertions, while `separable closure` gave definitions and Picard-descent assertions. The DAG search found the already reviewed unique-subfield construction and I reused it. `lem-galois-inverse-limit-surjective` concerns surjectivity for finite sets, not identification of a field automorphism group, and is not substituted for 0BU2. No blueprint node duplicates a new leaf. Every child has the exact ancestor and paragraph location; the item has `same_as: []` and its split report records which paragraphs the six steps realize.

## Not duplicates

lem-sfb-finite-field-separable-closure-algebraic vs lem-weil-pbc-perfect-field-separating-basis: the latter produces a separating transcendence basis for a finitely generated extension of a perfect field; it does not identify a given separable closure as algebraically closed. The shared source input is 030Z.

lem-sfb-finite-field-separable-closure-algebraic vs lem-weil-pbc-algclosed-fg-field-separating-basis: the latter assumes an algebraically closed bottom field and produces a separating basis for a finitely generated extension. The new leaf starts with a finite bottom field and a given separable closure. Neither conclusion specializes to the other.

lem-sfb-finite-field-galois-frobenius vs lem-weil-finite-field-pow-card: the existing node gives x^Q=x inside a finite field; it gives neither Galoisness nor a Frobenius generator over a subfield.

lem-sfb-finite-field-galois-frobenius vs lem-weil-unique-subfield-of-closure: the existing node constructs and counts subfields in an algebraic closure; it gives neither automorphism parametrization nor Galoisness. It is reused in step 1.

lem-sfb-finite-field-galois-frobenius vs def-weil-finite-field-q-elements: the latter introduces finite fields and their cardinality/characteristic, not the Galois group of an arbitrary inclusion.

lem-sfb-finite-field-galois-frobenius vs lem-weil-pbc-finite-galois-fixed-field: the latter assumes a finite Galois extension and identifies its fixed field and automorphism cardinality; it does not establish Galoisness for finite fields or give the Frobenius generator and power bijection.

lem-sfb-finite-field-separable-closure-algebraic vs lem-weil-pbc-field-char-p-h1-cotangent-vanishing: the latter asserts vanishing of the first cotangent homology of a characteristic-p field over its prime field, with no separable closure or algebraic-closure conclusion. I read its full statement; shared use of 030Z does not identify these propositions.

lem-sfb-finite-field-separable-closure-algebraic vs lem-weil-pbc-field-char-p-nilpotent-lifting: the latter lifts a map from a characteristic-p field through a nilpotent ideal of a characteristic-p ring, with no closure assertion. Its source also uses 030Z, but neither statement is a specialization of the other.

No existing node has 0BU2 as a source. The search hits mentioning that tag elsewhere were not source duplicates.

## Review by Q10

I opened the current `main-20261015` item and its two proof paragraphs, as well as the containing base-field-cd proof and section route. I checked the statement clause by clause: the original field is any finite field, n is positive, subextensions are inside the specified separable closure, Frobenius is arithmetic x ↦ x^q, and the last isomorphism is of profinite groups and sends this Frobenius to 1. No hypothesis or conclusion is removed, and no smooth-purity or other prohibited source route is involved. I read the source and Mathlib clauses of all three new leaves as detailed above, not just search-result titles.

Step 1 uses the finite-field definition's converse q=p^a, the new closure leaf's exact conclusion that this given separable closure is an algebraic closure, and clauses 1-3 of `lem-weil-unique-subfield-of-closure`. I checked that this last statement applies to arbitrary k_0 with q elements, not merely a canonically chosen model. Its statement supplies roots, the actual subfield, cardinality, containment of the original field, and uniqueness. It does not supply degree; I did not take degree from it. Its use as a tool is declared in `split_report.tool_uses`.

Step 2 cites the definition of finite-dimensional span and the basis definition of dimension. The finite set K_n spans itself, so the finite-dimensional hypothesis is established. The coordinate map is written out with both injectivity and surjectivity, and the equality q^s=q^n forces s=n because q is at least 2. Conversely a degree-n intermediate field has precisely q^n elements by this same bijection, allowing the uniqueness already proved in step 1. No uncited finite-field classification, embedding theorem or degree multiplication theorem is used here.

Step 3 cites the new finite-field leaf, whose statement explicitly gives all three facts used: Galoisness, order n, and the bijection of the first n powers with all automorphisms. The extension-degree substitution comes from step 2. The residue-class isomorphism is then checked by powers, not asserted as an unidentified cyclic-group isomorphism. The new leaf's exact Mathlib proof is the same root-count obstruction to a smaller order that the blueprint prescribes. It is a Mathlib leaf under B8, not an unsplit child carrying the main argument.

Step 4 cites `def-weil-frobenius-substitution` only for its stated automorphism on an algebraic closure of a finite field, after step 1 verifies that hypothesis. It cites `def-pd-separable-closure` for its stated union/filtered-colimit of finite separable subextensions, not merely for the name of a closure. Preservation of roots and the inclusion for d dividing n are explicit exponent calculations. The reverse implication is proved by division with remainder and the exact order from step 3; it does not silently assume the tower law. All finite intermediate fields are identified using step 2, so the later limit is indexed by all of them. These are elementary steps from the cited statements and the already proved steps, not a hidden new Galois theorem.

Step 5 uses part (2) of `lem-weil-pbc-separable-closure-exists-galois`, with the intermediate field equal to K, to establish exactly the normal separable algebraic hypothesis of the new limit leaf. I read that node's statement: it really asserts Galoisness over every intermediate field. The new leaf really asserts a topological-group isomorphism by restriction, so no continuity or compactness theorem is missing. Step 4 identifies the entire index poset, not just a cofinal subset, and it is a set of subfields of a fixed field; no unjustified large colimit is introduced.

Step 6 takes only the results of steps 3-5. I wrote the restriction on every element x of K_d, so the map on exponents is specifically reduction modulo d. The induced maps on compatible tuples are inverse to each other; their continuity follows coordinatewise from finite discrete factors and the product-subspace topology. The compatible tuple (1 mod n) is computed explicitly from the distinguished Frobenius, including n=1. The notation Z-hat is the inverse limit of residues as in the statement; no unproved universal property of profinite completion is needed.

For B1-B10/C1-C8/D1-D5, I checked that every new child is statement-only and self-contained, has actual logged searches, proper blueprint ancestry, and exact file/line matches. Every use in every proof step has a verbatim quote in `citations.json`. Existing notions and the existing subfield construction were reused. The three new facts are independent generic Mathlib interfaces, rather than unsplit copies of clauses. The item carries all elementary assembly, restriction and topology calculations.

For the mathematical edge cases, I checked n=1 (K_1=K, trivial finite Galois group, residue 1=0 in Z/1), q=2 (the smallest cardinality, with the exponent-count argument still strict), extensions of composite degree (divisibility and reductions use the full positive-divisibility poset), and the finite or trivial extension in the generic limit leaf. In the latter case there is a largest finite intermediate field, and the limit is its automorphism group, as the statement requires. The closure leaf has no restriction excluding characteristic 2. The finite-field leaf assumes the top field finite; it does not assert that an arbitrary finite-dimensional extension over an infinite field has cyclic group.

The repairs made during this reading were the missing existence argument, separating cardinality from degree, using the base-field perfection instance rather than assuming the top field perfect, and explicitly checking both topology and generator compatibility at the last step. No compiler or Lake command was run, no Lean file was written, and no live source or repository file was changed. The next reader receives the sandbox and the required dry-run result, without a push.

The first dry run returned only two missing same-tag comparisons in this report: the characteristic-p cotangent-vanishing and nilpotent-lifting nodes, both already read during source searching. I added the explicit statement distinctions above. I also checked the inferred finite-dimensionality instance at `RingTheory/Finiteness/Basic.lean:241-243` and recorded its name and source in the Frobenius leaf's `how`. The inverse-limit declaration grep was repeated on its directory so its output retained the actual file name. No mathematical statement or proof step changed in these repairs.

The second dry run required chapter and unit on every new node. I filled these on the three new leaves using the exact ids of the current blueprint section and containing unit, `sec-six-functors-basics` and `sk-lem-base-field-cd`, whose `_section.md` files I read. This records their actual location; the chapter and unit JSON records are present on the current base. No existing item metadata or chapter/unit record was changed.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against the blueprint paragraph, `def-weil-finite-field-q-elements`, the separable-closure leaf, and `lem-weil-unique-subfield-of-closure`; verdict: existence, containment, cardinality, and uniqueness are all stated and the arbitrary finite field embedding is handled.
- Step 2 checked against the finite-dimensional-subspace and vector-space-dimension definitions and the $K^s$ coordinate bijection; verdict: the cardinality/degree conversion is elementary and valid for every $q\geq2$.
- Step 3 checked against the finite-field Frobenius Mathlib declarations and the finite extension hypotheses; verdict: Galoisness, order $n$, and the complete power parametrization are exactly the cited clauses.
- Step 4 checked against the Frobenius-substitution and separable-closure definitions plus steps 2–3; verdict: divisibility/inclusion, reverse divisibility, finite-subextension coverage, and the union are explicitly justified.
- Step 5 checked against `lem-weil-pbc-separable-closure-exists-galois` and the infinite-Galois-limit leaf; verdict: the extension and the full finite-Galois index set meet the limit theorem's hypotheses.
- Step 6 checked by direct restriction calculations and the product-subspace topology; verdict: transition maps are reductions, the compatible tuple map is an inverse in both directions, and Frobenius maps to $(1\bmod n)_n$, including $n=1$.
- `lem-sfb-finite-field-separable-closure-algebraic` checked against Stacks Tag 030Z (`lemma-perfect`) and Mathlib `IsSepClosure.isAlgClosure_of_perfectField` (with `PerfectField.ofFinite`); verdict: exact Mathlib leaf.
- `lem-sfb-finite-field-galois-frobenius` checked against Stacks Tags 09HY (`section-finite`) and 09I1 (`lemma-finite-Galois`) and Mathlib finite-field Frobenius declarations; verdict: each Galois, order, and bijection clause is covered by named declarations.
- `lem-sfb-infinite-galois-profinite-limit` checked against Stacks Tag 0BU2 (`lemma-infinite-galois-limit`) and Mathlib `InfiniteGalois.continuousMulEquivToLimit`; verdict: the restriction isomorphism and profinite topology are exact.
- Changed no mathematical statement or proof; added explicit Stacks external source entries for Tags 09HY and 09I1 on the finite-field Mathlib leaf so its source is tag-and-label addressable.

## Repair review F1-F4 (2026-10-17)

I repeated the four checks named in the return. For F1 (independent source), I read the
complete imported target and proof in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-base-field-cd/`
and searched the read-only upstream master under `/home/ubuntu/weil-newtargets-master/WeilConjectures`
for the item id, blueprint tag, absolute-Galois wording, and the finite-field/Galois keywords.
The closest master field-theory match is the generic finite-field Frobenius wrapper (`WeilConjectures/Mathlib/FieldTheory/Finite/Basic.lean`); the point-count and zeta-series files also use finite extensions but do not identify the absolute Galois group. There is no declaration of this whole item to attach. I also
read the independent Stacks passages Tag 030Z (perfect fields), Tags 09HY and 09I1 (finite fields
and finite Galois extensions), and Tag 0BU2 (the infinite-Galois inverse limit), and checked the
Mathlib source at `FieldTheory/Perfect.lean:302-311`, `FieldTheory/IsSepClosed.lean:225-247`,
`FieldTheory/Finite/Basic.lean:331-406`, `FieldTheory/Finite/GaloisField.lean:196-204`,
and `FieldTheory/Galois/Profinite.lean:120-141,278-341`.

For F2 (route), I compared each of the six item steps with the two blueprint proof paragraphs.
Steps 1-3 are exactly the finite-subfield existence, degree/cardinality, and finite Frobenius
parts. Steps 4-6 are exactly the divisibility/union, Galois-limit, and compatible restriction
parts. The only route supplement is the explicit existence argument through the already existing
`lem-weil-unique-subfield-of-closure`; that node is declared in `tool_uses` because the imported
paragraph began with an extension that it had not shown to exist. No SGA source or alternate
purity route occurs.

For F3 (cited-definition audit), I reopened every node named in `stmt_deps`, `proof_deps`, and
`citations.json`. In particular, the quotes for the finite-field cardinality, finite-dimensional
span and basis dimension, arithmetic Frobenius, separable-closure filtered union, Galoisness over
intermediate fields, and the profinite restriction isomorphism are verbatim parts of those node
statements. The three new leaves state the complete clauses used by Steps 1, 3, and 5; none is
being used merely as a definition name. The statement quotations were reread against all
six steps, including the elementary calculations in Steps 2, 4, and 6.

For F4 (full-DAG duplicate audit), I searched all `dag/nodes/**/*.json` files by every new
statement's keywords, source tags 030Z/09HY/09I1/0BU2, and the Mathlib declaration names. The
only substantive reuse is the existing unique-subfield node, which Step 1 cites. The three new
leaves have no same-statement duplicate; the distinctions from all tag-sharing nodes
are recorded under `## Not duplicates`. I also ran the blueprint searches for finite field,
Frobenius, cyclic Galois group, separable closure, and inverse limit and found no blueprint node
that states any of the three leaves. These checks found no mathematical statement, hypothesis, or route correction. I added the existing finite-dimensionality definition to the general limit leaf's statement dependencies, which its index set uses, and regenerated its citation quote. The earlier report's assertion that chapter/unit records are missing has been corrected against the current base.

I located and read the actual return review at
`/home/ubuntu/weil-launcher-nt/reviews/Q10__det-base-field-cd-galois-group__9b4071217852/review.md`.
It certifies no mathematical defect, and explicitly withdraws the fixed-model objection. Comparison
with that immutable snapshot confirms that the retained parent statement and six proof steps agree;
only child metadata had changed before this repair. The current base still has the imported parent
and none of the three proposed children, so no live finished split is superseded.

The focused full-DAG search produced 25 candidate nodes, saved with their complete statements in
`work/duplicate-candidates.json`. I read the candidate statements: the finite-Galois fixed-field
node assumes Galoisness and gives automorphism cardinality, not Frobenius; the automorphism-functor
profinite node gives a closed subgroup of a product, not the field restriction limit; the fixing-subgroup
node compares a subgroup with an intermediate-field Galois group, not the inverse limit; the
finite-set inverse-limit-surjectivity lemma supplies nonemptiness and projections, not this
restriction equivalence. The remaining candidates concern etale stalks, torsor descent, cochains,
Tate modules, or separating bases. None specializes to a new leaf. I checked that every recorded
Mathlib search in all four nodes has a matching tool/query entry in `searches.jsonl` (4, 6, 5,
and 5 entries before the fresh item searches); no recorded search was invented.

The unit's first proof paragraph explicitly calls this item for the finite-field Frobenius argument;
its later cochain and inflation steps are outside this item's conclusion. I read the complete
chapter and unit source and records. This is not the unit's key statement, so no `realized` record
is changed. The two coefficient layers and the target base-change morphisms are unrelated to the
field-theoretic statement here; the four archived target signatures remain untouched.

Final repair validation: all 10 step citations are verbatim in the current overlaid statements; the proof-dependency union is exact; a traversal of 63 descendant nodes finds no path back to this item and no missing dependency. Fresh alternative item searches (LeanFinder, Loogle, LeanSearch and grep) still find only ingredients, and the new query/result records are retained in the item and search log.


## Completed return checks by Q10

This continuation completes the return's F1–F4 checks by reading the actual files, not by treating the earlier report as evidence. The immutable returned files are in `/home/ubuntu/weil-launcher-nt/reviews/Q10__det-base-field-cd-galois-group__9b4071217852/snapshot`. `work/base-comparison.txt` records their field differences from the retained sandbox before these final edits. The shared base still has the imported parent and none of the children. The dry-run delivery tool rebases the sandbox-owned fields on its current fetched base and preserves current maintainer metadata.

F1, independent sources: I opened Stacks `algebra.tex:10483–10512` (030Z, `lemma-perfect`) and `fields.tex:2266–2290` (09HY, `section-finite`), `2664–2679` (09I1, `lemma-finite-Galois`), and `2980–3055` (0BU2, `lemma-infinite-galois-limit`, including the complete proof). I checked the four tag-to-label mappings in `tags/tags`. 030Z characterizes perfectness, rather than asserting the closure specialization; Mathlib supplies that specialization. In Mathlib I read `Perfect.lean:302–311`, `IsSepClosed.lean:225–247`, `Finite/Basic.lean:331–416`, `Finite/GaloisField.lean:196–204`, and `Galois/Profinite.lean:1–180,278–341`. The finite-field base is perfect by `PerfectField.ofFinite`; `IsSepClosure.isAlgClosure_of_perfectField` applies to the given extension with no choice of a different closure. The finite-field Frobenius formulas, exact order and Fin-r power bijection occur in the named declarations, with finite-dimensionality supplied by the finite underlying set (`Module.Finite.of_finite`, read at `RingTheory/Finiteness/Basic.lean:241–243`; its finite-dimensional abbreviation was read at `LinearAlgebra/FiniteDimensional/Defs.lean:75–76`). For the limit leaf, `algEquivToLimit` explicitly restricts automorphisms to finite Galois intermediate fields, and `continuousMulEquivToLimit` uses the proved forward and inverse continuity. Its index and topology agree with the new statement, even for finite or trivial Galois extensions.

I repeated the project-source attachment search in both read-only checkouts by the exact id/tag and by absolute-Galois, finite-field/Galois and Frobenius/limit phrases. I read the entire project finite-field wrapper in each checkout and `WeilConjectures/Mathlib/FieldTheory/IsSepClosed.lean` on slopmaster2. The latter proves the finite-subextension union clause used by `def-pd-separable-closure`, but none of these project declarations states this item or any complete new leaf. The master point-count and zeta-series occurrences use finite extensions; they provide no absolute-Galois profinite identification. Thus no attachment is being withheld and no upstream sorry is counted as finished.

F2, route: I read the full current chapter and base-field-cd unit sources and JSON records. Unit step 1 explicitly calls this item for the finite-field group calculation; its later cochain/inflation arguments lie above it. The six steps still follow the two item proof paragraphs: finite roots and existence, degree counting, finite Frobenius, divisibility and the union, restriction limit, and compatible residues. The sole off-unit unclosed theorem is the already split unique-root-subfield construction; its statement is a generic tool completing the omitted existence argument, and is declared in `split_report.tool_uses`. The other off-unit statements used as tools are already Mathlib leaves. The coefficient layers and base-change morphisms are not changed or identified by any step here. No SGA source is used.

F3, cited definitions and clauses: I opened every definition in the parent and child `stmt_deps` as well as every statement in the six steps' `uses`. Step 1 takes precisely prime-power cardinality, the specified closure's algebraic-closure property, and the three numbered root-subfield clauses. The root-subfield statement says “a field with q elements”, so K itself is allowed. Step 2 uses spanning and basis dimension; I added the finite deletion argument establishing a basis rather than hiding basis extraction in the word “choose”. The coefficient map is injective by linear independence and surjective by spanning; q>=2 makes the exponent comparison injective. Step 3 takes precisely Galoisness, the Frobenius formula, exact order, and the full power bijection from its new leaf. Step 4 takes the automorphism clause actually present in the Frobenius definition and the finite-subextension union clause actually present in the separable-closure definition. I added explicitly that every finite intermediate field has positive degree because 1 is nonzero. Inclusions and reverse divisibility use the displayed exponent calculation and division with remainder. Step 5 uses exactly the separable-closure Galois clause at k'=K and the restriction homeomorphism of the general limit theorem. I corrected its source-place description to refer directly to 0BU2 rather than mixing the blueprint paragraph number with the Stacks location. Step 6 uses only previous steps: every coordinate sends a Frobenius power to the same exponent modulo d. Basic open cylinders pull back to open cylinders under each coordinate bijection and its inverse, which verifies the stated product-subspace continuity. There is no additional compactness or extension-of-automorphisms theorem silently used.

F4, duplicates and generalizations: I reran a scan over all 16,567 current DAG files, with no reach or chapter restriction, by finite-field wording, separable/algebraic-closure combinations, Galois with inverse-limit/profinite/Frobenius/cyclic wording, the four source tags and all principal matched declaration names. The 194 broad hits are saved with full statements in `work/current-duplicate-audit.json`; most are geometric Frobenius, coefficients or residue-field assertions and were eliminated by their titles and statements. I read the substantive field/group candidates, including the previous 25 in `work/duplicate-candidates.json`, plus the purely inseparable algebraic-closure lemma, relative separable-closure definition, finite-extension embedding and degree theorems, separably closed finite-extension lemmas, tame DVR sequence, root-of-unity Frobenius lemma and global finite-field/zeta definitions. The purely inseparable results assume the bottom field separably closed and do not make a closure of a finite field algebraically closed. The relative-closure node constructs a separable closure inside an overfield, not an algebraic closure of the specified field. The tame DVR sequence describes a quotient for a different base and does not specialize to a general Galois inverse limit. Finite embedding bounds, degree multiplication, and roots-of-unity actions give none of the new conclusions. The already reused unique-subfield lemma remains the only subfield construction needed. The previously recorded same-tag comparisons remain valid. The whole-blueprint searches were repeated for finite field, separable closure, Galois.*limit and Frobenius; none gives a duplicate new leaf.

I checked the recorded Mathlib searches against the retained JSONL execution log by exact tool/query pairs: all 23 records across the parent and three children have successful matching calls, including their actual grep directories and hit counts. No unavailable response is described as absence. I did not invent or replace a search record. The three children remain statement-only exact Mathlib leaves, not new unsplit copies of the parent's clauses. No new child was added during repair.

For E1–E7, I checked arbitrary finite K and its specified closure throughout, n>=1, q>=2, and finite (not merely algebraic infinite) top field in the Frobenius-order leaf. In degree one the automorphism group and Z/1 are trivial and 1 mod 1=0; for F_4/F_2 the nontrivial squaring automorphism has order two, consistent with both the order and power-bijection clauses. Positive composite degrees use divisibility, not a sequential tower n→n+1. The finite/trivial extension case of the limit leaf has a maximal index and hence the expected finite group as limit. No mathematical statement defect was found, and the withdrawn canonical-model objection has not been reinstated.

The shared `check_dag.py` reports inherited findings elsewhere in the DAG; the required delivery preflight compares against its base and checks the delivery overlay. No unrelated node is edited. All writes here are in this sandbox, with no Lean writing, compilation, Lake, agent launch, manual git, or push. The final dry run below is the handover boundary for the next reader.

## Second reading by Q10

This final second-reading section supersedes the earlier three-child count and no-duplicate conclusion. The fresh dry-run found that `lem-exc-galois-krull-finite-limit` is now on the fetched shared base. I opened its entire statement and Mathlib match: it gives the same restriction isomorphism, with the same Galois hypotheses, finite intermediate fields, Krull topology, and product-subspace topology. It additionally gives directedness and nonemptiness. It is a Mathlib leaf, so its use does not require an off-unit tool exception.

- Step 1 checked against `def-weil-finite-field-q-elements`, `lem-sfb-finite-field-separable-closure-algebraic`, and all three clauses of `lem-weil-unique-subfield-of-closure`; verdict: the given closure is algebraic and the root subfield exists, contains K, has the required cardinality and is unique.
- Step 2 checked against the finite-dimensional span and dimension definitions; verdict: finite basis extraction and the coordinate bijection prove the cardinality/degree conversion, including the trivial extension and the zero vector space in the general counting argument.
- Step 3 checked against the complete `lem-sfb-finite-field-galois-frobenius` statement and Mathlib Finite/Basic.lean:362-406 and Finite/GaloisField.lean:196-204; verdict: Galoisness, exact order and the full power bijection are covered under the actual finite-field hypotheses.
- Step 4 checked against the Frobenius-substitution and separable-closure statements and steps 2-3; verdict: inclusion/divisibility, its converse, positive degree, finite-subextension coverage and the union are explicit elementary calculations.
- Step 5 checked against `lem-weil-pbc-separable-closure-exists-galois` part (2) at k'=K and the existing `lem-exc-galois-krull-finite-limit`; verdict: its hypotheses, complete index set and topological restriction isomorphism match. Replaced the duplicate leaf citation and its quotation.
- Step 6 checked by direct restrictions on every x in K_d and the product-subspace topology; verdict: transitions are reductions, the tuple maps are mutually inverse and continuous, and arithmetic Frobenius maps to (1 mod n)_n, including n=1.
- `lem-sfb-finite-field-separable-closure-algebraic` checked against Stacks Tag 030Z (`lemma-perfect`) and Mathlib Perfect.lean:308-311/IsSepClosed.lean:244-247; verdict: retain as an exact Mathlib leaf, using perfection of the bottom field and the specified separable closure.
- `lem-sfb-finite-field-galois-frobenius` checked against Stacks Tags 09HY (`section-finite`) and 09I1 (`lemma-finite-Galois`), the blueprint first paragraph and the Mathlib declarations above; verdict: retain as a Mathlib leaf, one declaration per clause. Finite-dimensionality is inferred from Module.Finite.of_finite at RingTheory/Finiteness/Basic.lean:241-243.
- `lem-sfb-infinite-galois-profinite-limit` checked against Stacks Tag 0BU2 (`lemma-infinite-galois-limit`) and Mathlib Galois/Profinite.lean:133-141,323-341; verdict: mathematically correct but now an exact duplicate of `lem-exc-galois-krull-finite-limit`; removed from the delivery.

Changes in this reading: removed one duplicate proposed child, repointed step 5 and proof_deps, replaced its citation with a verbatim quotation of the existing statement, corrected the split summary to two new Mathlib leaves, and added this mandatory section. Ran nine fresh alternative Mathlib searches; their actual outcomes remain in searches.jsonl, with the six for retained children appended to their mathlib_searches. The earlier existence, basis, positivity and source-place repairs were already present and retained. The final two children are statement-only, self-contained, have definition references, proper TeX, tag-and-label sources and verified Mathlib file/line matches. Full-DAG source-tag/keyword searches and the substantive field, fixed-field, Krull-topology and inverse-limit candidates were checked; the duplicate exposed by the fetched base was removed. Degree one, characteristic two, positive composite degrees, and finite/trivial Galois extensions satisfy all statements. No mathematical statement was weakened; no Lean or live repository files were changed.
