# Worker report: def-sfb-dc-open-lower-shriek

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-dc-open-lower-shriek.json: definition, split; no exact Mathlib match. Added explicit statement dependencies and the object/morphism description of the restriction, with identity comparison to the inclusions. The setting, arbitrary commutative condensed coefficient ring and mathematical meaning are unchanged.
- citations.json: empty list, because this definition has no proof steps.
- report.md: this report. searches.jsonl is the search tool's actual log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id, boundedConstructibleOpenImmersionLowerShriek, boundedConstructible_openImmersionLowerShriek_obj, and the extension-by-zero notion found no declaration of this item. Existing pro-etale extension-by-zero functors for a fixed value category do not define the condensed-ring module-object restriction.

The read-only upstream master file WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean has AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriek at line 212 and boundedConstructibleOpenImmersionLowerShriekCompatibility at line 217. Its preservation input boundedConstructible_openImmersionLowerShriek_obj at line 203 has sorry at line 208. These are reference constructions, not attachment evidence.

## WANTED

None. All sources used are available locally; no SGA source was used.

## Findings and changes

The original definition said “the setting” without naming its definition and omitted the full-subcategory and termwise-derived-functor nodes from stmt_deps. Added sk-def-sfb-dc-setting, sk-def-sfb-bounded-constructible, sk-def-sfb-derived-categories and sk-def-sfb-condensed-ring. The original module-extension and preservation dependencies remain. No hypothesis is added: the explicit reference resolves precisely the setting already assumed by the source's unit.

The definition now specifies J on underlying objects and morphisms, the preservation witness that places the object in the target full subcategory, and the comparison whose components are identities. This is the original restriction definition spelled out, not a new theorem or an alternative six-functor route. The preservation assertion stays in the existing lem-sfb-dc-open-lower-shriek-preserves; it is not copied into a new child. The definition has proof=[], proof_deps=[] and proof_origin=null.

The main snapshot's chapter and unit sources were read directly in literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/_section.md and sk-def-sfb-dc-restricted-functors/_section.md, together with its .proof.md. The shared DAG does not currently contain dag/chapters/sec-six-functors-basics.json or dag/units/sk-def-sfb-dc-restricted-functors.json, and this imported node has no chapter/unit fields. No maintainer metadata or unit file was invented or changed. This item is not the unit's key node, so no realized fields are due.

## Not duplicates

No new nodes. Whole-DAG searches for levelwise functors and restriction to full subcategories, plus blueprint_refs.py searches for “extension by zero”, “D(j_!)”, “derived factorization” and “liftComp”, found the existing preservation lemma and the larger unit, not a second definition of exactly this restricted functor. The unit includes many other functors; same_as=[] does not identify a conjunction of broader content with this definition. No new elementary or clause-restating node was created.

## Mathlib search assessment

The seven distinct searches recorded in the item were run through msearch.py and their exact queries are in searches.jsonl. On rechecking the earlier attempt, I repeated both semantic phrasings, Loogle, LeanSearch and the focused grep, and read the returned hits and the local full-subcategory source. Both semantic services and Loogle worked. The first semantic phrasing found structure-sheaf restriction and condensed locally constant functors, not this pro-etale derived module-object functor. I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:348: its restrictFunctor goes from Y.Modules to X.Modules and uses structure-sheaf modules, so it is not this item.

The second semantic phrasing and Loogle found CategoryTheory.ObjectProperty.lift and liftCompιIso. I read Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:150–172: lift at 159 wraps F.obj with the supplied property witness, sends maps to F.map, and liftCompιIso at 165 is Iso.refl. This supports the explicit elementary construction. It does not supply either the ambient module-object extension by zero or its preservation theorem, so the whole item is not a Mathlib leaf. A separate generic restriction node would be an unnecessary elementary node. The final dedicated Mathlib grep for boundedConstructible|openImmersionLowerShriek returned zero hits.

## Unfinished work

The one-level mathematical split is complete, with zero new nodes and zero Mathlib leaves. The existing preservation lemma remains an independent DAG item. No Lean was written and no compiler or Lake was run.

## Review by Q52

I read the exact main-20261015 def-sfb-dc-open-lower-shriek.md and the restricted-functors unit and proof. The source asks for the restriction of D(j_!), not a newly derived functor. The expanded definition supplies exactly that object and morphism data. I also read the upstream master lines 195–221: its lift construction and identity compatibility agree with this description, while its sorry input prevents an attachment.

There are no proof steps to audit under C1/C4; the construction's inputs were instead checked statement by statement. sk-def-sfb-module-lower-shriek explicitly gives j_!: Mod_{Lambda_U} to Mod_{Lambda_X} and exactness. sk-def-sfb-derived-categories explicitly says D(F) applies an exact F termwise. sk-def-sfb-bounded-constructible explicitly defines a full subcategory with ambient morphisms; this is why no lifting theorem for morphisms is hidden. lem-sfb-dc-open-lower-shriek-preserves says that for every commutative condensed Lambda and every open immersion of sk-def-sfb-dc-setting, D(j_!) takes every bounded constructible K to a bounded constructible object. These are exactly its use and its hypotheses here. sk-def-sfb-dc-setting specifies separated finite-type schemes over a characteristic-p field with p different from ell; sk-def-sfb-condensed-ring supplies the coefficient notion. Each cited file was opened and its statement read. No adjunction or composition theorem is claimed here.

For the functor checks, identities and compositions are the ambient functor's identities and compositions because the subcategories are full. After inclusion both functors have the same object and map functions, and the comparison is identity at every object; naturality is the equality J(a)=J(a). These checks need no separate non-elementary fact. The only non-elementary well-definedness input is the named preservation lemma already in stmt_deps. Its source proof was read as well: finite stratification on U extends by the closed complement and exactness controls cohomology. I do not claim to split that lemma in this delivery.

I tested the definition on the zero complex, the empty open and the identity open: the same restriction formula is defined without a nonempty assumption, and it introduces no special coefficient or cohomological bound hypothesis. The zero and empty cases create no missing target-property witness because the preservation lemma is universally quantified. The construction does not require properness or l-adic coefficients. No new statement was introduced, so B1–B8 and the small-case check for new nodes are vacuous; the item's TeX, dependencies and unchanged import/blueprint fields were checked. The meaningful corrections were the omitted notion dependencies and explicit identity compatibility, with no statement dispute or route departure.


The current worker recheck removed the inherited “Second reading” section: this report signs the worker self-review only; the required fresh reader has not yet performed its review. The repeated condensed-coefficient semantic search returned free and locally constant condensed-module functors over ordinary rings, again no match. I retained the earlier genuine search records and updated the corresponding results to distinguish the repeated hits. No definition data or hypotheses needed further repair.

## Dry-run

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q52 def-sfb-dc-open-lower-shriek --no-push` completed successfully after the shared worktree and fetch locks became available. It printed `OK (not pushed) deliver/Q52/def-sfb-dc-open-lower-shriek at 1dc84d9848: preflight passed`.

## Second reading by Q52

I am the fresh second reader, not the author of the split. I read delivery-errors.md B–E, GOAL.md, coord/dag-sync.md, the worker/stage-1 contract, the current main-20261015 chapter, the restricted-functors unit and its proof, the exact source file def-sfb-dc-open-lower-shriek.md (order 1785), and all six statement dependencies. This item has a blueprint source, not a Stacks tag, so there is no tag/TeX label to substitute for that exact source path.

- Item statement: checked hypothesis by hypothesis against def-sfb-dc-open-lower-shriek.md and sk-def-sfb-dc-setting: arbitrary commutative condensed ring, open immersion of separated finite-type schemes over the same characteristic-p field with p different from ell; PASS, no coefficient, properness or nonemptiness hypothesis added.
- Construction clause (ambient functor): checked against sk-def-sfb-module-lower-shriek, whose statement supplies the exact module-object functor from U to X, and sk-def-sfb-derived-categories, whose exact-functor clause supplies D(j_!); PASS, no fresh derived functor is claimed.
- Construction clause (object and morphism restriction): checked against the full-subcategory and ambient-Hom clauses of sk-def-sfb-bounded-constructible and the universally quantified statement of lem-sfb-dc-open-lower-shriek-preserves; PASS, the property witness applies to precisely the included object, with precisely the coefficient and scheme hypotheses in force.
- Construction clause (functor laws): checked directly: J(id_K)=id_{J(K)} and J(b composed with a)=J(b) composed with J(a); these are the ambient functor laws and are equalities of the full subcategory's ambient morphisms; PASS, elementary, no missing lifting theorem.
- Construction clause (compatibility): checked against the source's commutation clause: both composites have object J(iota_U K) and map J(iota_U a), so each comparison component is its identity, invertible by itself, and naturality reads J(iota_U a)=J(iota_U a); PASS, elementary.
- Proof steps: none (proof=[], proof_deps=[], proof_origin=null); PASS for a definition whose non-elementary well-definedness input is explicitly named in stmt_deps. citations.json remains [] because there are no proof-step citations.
- New nodes: none; B1–B7 and new-node duplicate/small-case checks are vacuous. No elementary, duplicate or clause-restating node has been introduced; PASS.
- Small cases: zero complex, empty open U, empty X (thus empty U), and identity open all use the same formulas and the universally quantified preservation statement; PASS. For X=Spec(k), the identity and empty opens give no additional field or coefficient condition. No claim of strict identity of ambient models is needed beyond the displayed identity-component comparison.
- Mathlib and project attachment check: my independent, differently phrased msearch.py LeanFinder query returned ObjectProperty.lift and its formulas; I read FullSubcategory.lean:150–172. These state the generic construction with a supplied ambient functor and preservation witness, rather than this specific pro-etale module-object functor. The direct slopmaster2 searches for the blueprint id and boundedConstructibleOpenImmersionLowerShriek/boundedConstructible_openImmersionLowerShriek_obj returned no declaration. The upstream master construction at BoundedConstructible.lean:203–220 agrees, but its preservation lemma has sorry, so it is reference material, not a closed attachment; PASS.

Changes: appended this independent review and recorded my fresh full-subcategory search in the item's mathlib_searches (the actual tool record is in searches.jsonl). The mathematical statement, dependencies, empty proof, and citations were already correct and were retained. No statement dispute, missing source, SGA citation or route departure was found.

Delivery invocation note: this installed deliver.py accepts group, item and --no-push, with no trailing positional dot; the documented equivalent command is used for dry run and delivery.

Second-reader final dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q52 def-sfb-dc-open-lower-shriek --no-push` printed `OK (not pushed) deliver/Q52/def-sfb-dc-open-lower-shriek at 928818b7c3: preflight passed`.
