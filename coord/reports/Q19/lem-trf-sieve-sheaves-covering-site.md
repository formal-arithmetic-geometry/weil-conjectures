# Q19 stage-1 report: lem-trf-sieve-sheaves-covering-site

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sieve-sheaves-covering-site.json: statement, split into ten steps; no exact Mathlib replacement-site theorem found.
- dag/nodes/sec-trace-formula/lem-trf-sieve-set-sheafification-exists.json: statement-only Mathlib leaf, CategoryTheory.plusPlusAdjunction, Mathlib/CategoryTheory/Sites/ConcreteSheafification.lean:590.
- dag/nodes/sec-trace-formula/lem-trf-sieve-dense-subsite-comparison.json: statement-only Mathlib leaf, CategoryTheory.Functor.IsDenseSubsite.sheafEquiv, Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:797.
- citations.json: all 19 step/node citations, quoted verbatim from the statements actually cited.
- report.md and searches.jsonl: review and actual search-command records. Helper scripts are sandbox-local only.

There are two new nodes and two Mathlib leaves. The item's statement and its statement dependencies are unchanged. Its chapter, unit, blueprint ancestry, and imported metadata are retained. The two new nodes have complete statements, empty proofs, and the same blueprint ancestor with this item inserted into their via chain. Blueprint searches found no same_as node for them.

## Attachments

None. Searches in the project Lean source by the item id, blueprint docstring tag, and the sieve-site/replacement-site notions did not find a declaration proving the whole item. The generic Mathlib adjunction and comparison declarations are leaves, not project attachments. No existing project declaration was represented as a completed proof merely because its statement exists.

## WANTED

None. The Stacks sources and Mathlib source needed here are available locally. No SGA source is used.

## Problems found and corrected

The original item requires a sieve topology on a category with no pullbacks. Stacks 03CI and 03A1 start with a covering-family site; applying their original-site comparison directly would assume the very replacement being constructed. I kept the statement and made the adaptation explicit. An initial sandbox draft cited lem-weil-pbc-sheaf-subcategory-comparison; reading that node's complete statement showed its covering-family hypothesis, so that draft was replaced before delivery. The final proof does not cite it or site-specific original-site epimorphism or limit lemmas.

The proof constructs a small full category of sheaves closed under pullbacks, defines covers by local lifting on the original sieve site, selects a set of representative covers, and compares via sheafified Yoneda. Both local representation AND local equality are necessary: equality after sheafification alone does not imply equality of original arrows. Steps 6 and 7 prove the covering-sieve equivalence explicitly, and step 8 proves the remaining dense-subsite hypotheses. This is an agent adaptation of the cited Stacks constructions, marked as such, rather than a claim that Stacks states the item verbatim. No statement dispute or route change was needed.

## Unfinished work

No mathematical part of this one-level split is left open. Both new supporting statements are Mathlib leaves with the precise declaration and specialization recorded. Delivery validation is run after this report is written; success or diagnostics are reported by the delivery command.

## Review by Q19

I read the current blueprint proof of lem-trf-local-term-locality in main-20261015, the chapter and sk-i-curve-zero unit records, and the ancestry of this generic source-localization input. The construction supplies the site's presentation required before the existing good-site argument; it does not replace the contracting-Frobenius or normal-cone route. I read Stacks sites.tex at 03CI (good site), 03A1 (special comparison), 03A0 (comparison), 00ZM (sheafification adjunction), 00ZO (sieve detection by sheafification), 00ZC (family/sieve topology), and the sheafification section 00ZG, together with sets.tex 000X (representative coverings). In particular, I checked the family-site hypothesis of 03CI/03A1 rather than silently extending it to the original category.

For the new sheafification node I read ConcreteSheafification.lean around 560-602, including plusPlusAdjunction and its homEquiv, and the Type-valued HasSheafify instance in Sites/LeftExact.lean:313-314. The statement is the adjunction itself, with its natural unit and Hom bijection, not an unproved construction or a definition cited as existence. For two categories small in universe V, Type V supplies the required limits and covering-sieve colimits. The alternative general adjunction in Sites/Sheafification.lean was also read. For the new comparison node I read DenseSubsite/Basic.lean around the class at 538-542 and sheafEquiv at 797-798, LocallyFullyFaithful.lean:84-95, and DenseSubsite/SheafEquiv.lean:35-36,107-108. The four conditions in the new statement spell out cover density, local fullness, local faithfulness, and exact preservation/reflection of covering sieves. They are precisely those class fields. The remaining small structured-arrow limits exist in Type V. The direction of the equivalence is checked: restriction is the inverse of the named sheafEquiv. Neither new leaf assumes subcanonicality or pullbacks.

I opened every existing node cited in the ten steps and compared its actual statement with the use, as follows.

1. lem-trf-sieve-set-sheafification-exists gives a left adjoint and unit for the arbitrary sieve site. The idempotence of reflection is verified using its universal Hom bijection; applying the existing lem-cbc-set-presheaf-sheafification-local-bijection to that unit then gives exactly its local representative and local equality clauses. That existing lemma explicitly requires neither pullbacks nor subcanonicality.
2. def-weil-pbc-topos supplies the sieve sheaf condition used in the componentwise gluing verification. def-weil-size-convention fixes V. Products indexed by the V-small object set and the countable iteration remain V-sets; natural transformations are a subset of a V-small product. The sectionwise pullback universal property restricts to the constructed full category, so pullbacks in the original category are never presumed. This is an explicit elementary construction, not an invocation of a definition as an existence theorem.
3. The two definition nodes supply exactly the sieve topology axioms and the three covering-family axioms. I checked that the lifting arrows form a sieve, that pullback sections pair with the restricted base section, and that composition uses the transitivity axiom on the original category. This is a direct verification of definitions and does not rely on an uncited epimorphism characterization.
4. lem-weil-pbc-small-set-of-covering-families is stated for ANY small category and class of families satisfying these three axioms. Its conclusion supplies an axiom-closed set and the same arrow support for every family. Thus it applies after step 3; no original family site is needed. The generated topology and the all-arrows test are checked directly using the representatives. This generic size tool is declared in split_report.tool_uses.
5. The sheafification leaf supplies Hom from the reflection, and lem-galois-yoneda-hom-bijection supplies Hom(h_d,F)=F(d), including naturality in both variables. I did not substitute the weaker fully-faithful Yoneda statement. The formulas for sheafified arrows and evaluation on unit sections are written out and determine the functor.
6. The topology definition gives pullback stability for sieves, which does not require categorical fibre products. The local-bijection node supplies local representatives. Refining first by local representatives and then by the pullback of the given sieve proves cover preservation; every resulting arrow really belongs to that sieve.
7. The same node supplies both local representatives and local injectivity. First lifting a section along the image sieve gives a sheafified equality; representing the intermediate section and then using local injectivity yields actual equality of original arrows. The sieve property and topology transitivity then show the original sieve covers. Thus the comparison's reflection hypothesis has been proved, not assumed.
8. The natural Yoneda bijection produces every map needed for cover density. The local-bijection statement gives respectively the local lift of an arbitrary map and local equality of parallel arrows. Steps 5 and 6 identify the exact local fullness and faithfulness sieves required by the comparison. All the indices lie in V.
9. The new comparison node states precisely an equivalence of set-valued sheaf categories under the four conditions established in steps 6-8. Both smallness hypotheses were checked in step 2 and the item hypothesis. No coefficient enlargement, enhanced-category comparison, or global full faithfulness is being inferred.
10. The family and sieve sheaf conditions in the two definition nodes are compared explicitly: matching on pairwise pullbacks makes a section on a generated sieve independent of factorization; stability of covers and uniqueness verify agreement on larger covering sieves. This is the direct elementary check of the two definitions. It gives the required family site and its covering-member pullbacks.

I checked delivery-errors B-E against the final files: new statements introduce their own objects and hypotheses; they are genuine general tools, not clauses restating the target; elementary closure and sheaf-condition verifications stay in the item's proof; no replacement definition is weakened. Every non-elementary fact used is a cited statement, and citations.json copies actual statement text, not text invented to fit a use. The uses union equals proof_deps. The new leaves have no proofs or invented dependencies, and neither new node is split recursively. Every step is under 2000 characters, and no long hidden standard lemma remains.

The small cases do not add missing hypotheses. If D is empty, its sheaf category is terminal and the constructed site still has its terminal object; the empty cover is available where lifting is vacuous, so comparison does not fail for lack of representable objects. On a chaotic topology with empty covering sieves, local lifting and equality are vacuous and the proof still gives the terminal topos. For the minimal topology the local representations specialize to ordinary section representations. Non-subcanonical topologies are handled by H_d=a(h_d) throughout. Repeated arrows do not affect lifting sieves; empty covering families satisfy the same pullback/composition checks. C has all the pullbacks the final site requires even when D has none.

Before the two new nodes were created, searches of the entire DAG and blueprint covered the tags, generic sheafification existence, dense subsite/local full faithfulness, and sieve topology. Existing covering-family comparison statements were read, as were the related specialized affine-etale and hypersheaf results listed below. Mathlib searches were issued only through msearch.py; their exact tool/query text and returned records are retained in mathlib_searches and searches.jsonl. I read the hits in the indicated files before identifying either leaf. The item's second phrasing confirms that toPretopology on the original category cannot supply the missing pullbacks. No unavailable search result is presented as a successful search, and no search was fabricated. No Lean file, shared repository file, live launcher, or compiler/build tool was touched.

## Not duplicates

lem-trf-sieve-set-sheafification-exists vs lem-trf-sieve-sheaves-covering-site: the new node gives only the sheafification adjunction on an arbitrary sieve site; the item constructs a different small covering-family site and an equivalence, with no such construction in the new node.

lem-trf-sieve-dense-subsite-comparison vs sbc-lem-small-etale-affine-colimit-detection: the existing statement detects module-sheaf colimits by evaluation on affine etale objects; the new statement compares set sheaves on two arbitrary sieve sites under four explicit functor hypotheses.

lem-trf-sieve-dense-subsite-comparison vs def-weil-pbc-special-cocontinuous-functor: the existing node defines continuity, cocontinuity and comparison conditions for covering-family sites; it asserts no arbitrary-sieve equivalence theorem.

lem-trf-sieve-dense-subsite-comparison vs lem-weil-pbc-site-equivalence-is-morphism-of-sites: the existing statement assumes an equivalence of underlying categories and matching covering families; the new statement allows a merely locally full and faithful functor of arbitrary sieve sites.

lem-trf-sieve-dense-subsite-comparison vs lem-weil-pbc-site-equivalence-sheaf-transport: the existing transport assumes an underlying category equivalence; the new comparison functor need not be globally full, faithful, or essentially surjective.

lem-trf-sieve-dense-subsite-comparison vs lem-weil-pbc-quasi-inverse-adjoint: the existing statement obtains adjunctions from quasi-inverse equivalences of categories; it contains no topology or sheaf comparison theorem.

lem-trf-sieve-dense-subsite-comparison vs lem-stage3-affine-etale-restriction-large-sets: the existing theorem is the restriction equivalence for the full affine etale inclusion of a scheme, with fixed topologies and universes; the new statement concerns an arbitrary pair of small sieve sites and a functor satisfying four local conditions.

lem-trf-sieve-dense-subsite-comparison vs lem-weil-pbc-special-cocontinuous-sheaf-equivalence: the existing theorem assumes covering-family sites and the special cocontinuous conditions of their definition; the new theorem takes arbitrary sieve topologies without source pullbacks, so that existing family-site theorem cannot be applied here.

lem-trf-sieve-dense-subsite-comparison vs lem-weil-pbc-site-equivalence-morphism-transport: the existing statement transports a morphism of covering-family sites through a square of underlying equivalences; the new statement proves an equivalence for a single locally defined dense comparison functor.

lem-trf-sieve-dense-subsite-comparison vs lem-cbc-dense-hypersheaf-comparison: the existing theorem concerns bounded-below enhanced derived Lambda-valued hypersheaves with higher descent; it is not the ordinary set-valued sheaf comparison stated in the new node.

lem-trf-sieve-dense-subsite-comparison vs cohomology-site-equivalence-fixed-degree: the existing statement identifies a fixed-degree cohomology presheaf under an underlying category equivalence of precoverage sites, with abelian sheaf and HasExt hypotheses; the new result concerns set sheaves and a functor that need not be an underlying equivalence.

The additional conceptually nearby lem-weil-pbc-sheaf-subcategory-comparison and lem-weil-pbc-site-of-sheaf-generators begin with covering-family sites, so do not replace the arbitrary-sieve construction of this item. lem-pc-dense-subsite-sheafification-compatibility assumes global full faithfulness and proves compatibility of sheafification; the present comparison needs only local full faithfulness and has a different conclusion. def-weil-pbc-sheafification specifies a universal property but is not an existence theorem on an arbitrary sieve site.
