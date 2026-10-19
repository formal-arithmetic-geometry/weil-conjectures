# Repair of thm-exc-explicit-preservation

## Files written

- `dag/nodes/sec-six-functors/thm-exc-explicit-preservation.json`: repaired five-step split; theorem statement, other four steps, and Lean record unchanged.
- `dag/nodes/sec-six-functors/lem-exc-proetale-pullback-locally-constant.json`: statement-only dependency for finite locally constant module pullback along an arbitrary scheme morphism on small pro-etale sites; searched, no Mathlib match, status unsplit.
- `citations.json`: full verbatim statements for each step/dependency pair.

One new node, zero Mathlib leaves. The new statement is a sheaf-level local-trivialization lemma. It does not restate constructible stratification, derived intervals, Tor bounds, or derived coefficient comparison, so the proof of the item remains in the item.

## Attachments

None. The exact blueprint tag has no declaration in the read-only slopmaster2 source. `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion` (OpenImmersion.lean:198) and the finite-etale analogue (Basic.lean:137) concern etale categories and do not give all the independently quantified pro-etale assertions and coefficient comparison here. They cannot attach this item. Master sorry declarations were not treated as proofs.

## WANTED

None for this repair: the blueprint snapshots and Stacks sources are present locally. The inherited proof_origin field retains the earlier worker's agent-written attribution; its old absence-of-literature note describes that worker's circumstances, not mine.

## Repair requested and made

I read the dedicated handoff in coord/returns/Q76.md. Its single numbered issue is the 2065-character step 2, which proves a separate lemma inline. I extracted its non-elementary part: inverse image transports locally constant module trivializations, including the module action and finite labels. The new node states the local covering isomorphisms and has no proof. Step 2 now cites it after constructing the pulled-back stratification and identifying the restricted pullbacks by the existing composition theorem. Step 2 is 1004 characters; every other step remains below 2000 characters. This is a mathematical extraction, not dividing the old paragraph into shorter pieces.

The item statement and stage-2 Lean record remain byte-for-byte equal to the shared item. No target statement, unit/chapter binding, maintainer field, source Lean, or launcher was changed. The node is still in its assigned unit; the current metadata unit record is broader than this explicit-case item. I did not rewrite its realized fields because this item is not its key statement. The existing general-tool declarations in split_report.tool_uses remain; they implement the same flat-model and tensor route.

## Searches and sources

I searched the whole DAG and blueprint for local constancy, constant module pullback, inverse image and Tag 093R, including tools/blueprint_refs.py search. The nearest ancestor command gives thm-exc-explicit-preservation. The only comparable imported blueprint pullback lemma is etale-specific; it does not state the pro-etale result. I searched the read-only project Lean for the tag, exceptional preservation names and constant/inverse-image concepts, and read the etale preservation declarations. No existing project declaration gives this item's entire statement or the new pro-etale local-trivialization statement.

For the new node I ran msearch.py with two LeanFinder phrasings, two Loogle patterns, LeanSearch, and three source-grep patterns (general category theory, all Mathlib, and module sheaves). All eight results are recorded in searches.jsonl and in the node with their exact query text. All services returned successfully this time. The broad grep's 25 hits are locally constant functions in topology and analysis, not locally constant sheaves. LeanSearch gives finite-limit preservation and constant-sheaf characterizations; those do not supply the local-trivialization theorem in one line. I read Mathlib/CategoryTheory/Sites/ConstantSheaf.lean (constantSheafAdj and IsConstant), Sites/Pullback.lean (sheafPullbackConstruction), and Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:139 (pullbackObjFreeIso). The latter applies to free sheaves, whereas a finite module over A need not be free (for instance F_ell over Z/ell^2). Thus none is a match. Existing item searches are retained, not invented or rerun.

The new source is Stacks Tag 093R, sites-modules.tex, label lemma-pullback-locally-constant, at line 8435. I read its full statement: it explicitly includes modules over a fixed ring and arbitrary morphisms of topoi. Its proof is omitted; the new node leaves that proof to its own future split. The displayed covering isomorphisms specialize this local-trivialization assertion to the scheme base-change functor. I also read the local-constancy definition immediately preceding it. The inherited module-operation calculation is the intended proof of this future lemma: the inverse image preserves terminal objects and coproducts, so constant sets retain their labels; finite-product preservation carries addition and scalar-action diagrams to the same labelled operations; base change of the covering supplies the local assertions. This explanatory paragraph is in the report only, not a proof inside the unsplit node.

## Not duplicates

lem-exc-proetale-pullback-locally-constant vs lem-weil-pbc-sets-etale-inverse-image-constant-sheaf: the existing Tag 093R citation supports a canonical-section comparison for constant sheaves of sets on etale sites; the new node concerns locally constant module sheaves on pro-etale sites, their module actions and finite local models.

lem-exc-proetale-pullback-locally-constant vs new-etaleSetInverseImageConstantSheaf-existence: the existing statement supplies a comparison for etale constant sets; it has no module local-trivialization or pro-etale assertion.

lem-exc-proetale-pullback-locally-constant vs new-etaleSetInverseImageConstantSheaf-uniqueness: the existing statement is uniqueness for the etale constant-set comparison, not module local constancy on pro-etale sites.

lem-exc-proetale-pullback-locally-constant vs lemma-constructible-pullback-locally-constant: the existing blueprint statement, including its blueprint_update, concerns etale sheaves. It cannot be applied to the intrinsic pro-etale sheaf in step 2.

lem-exc-proetale-pullback-locally-constant vs lem-weil-pbc-pullback-finite-locally-constant: the existing theorem concerns abelian etale inverse images and their composition; it supplies no pro-etale or constant-ring module comparison.

lem-exc-proetale-pullback-locally-constant vs lem-stage3-finite-lc-pullback-stratum: the existing statement is about a fixed etale stratification and abelian sheaf; the new statement is independent of any stratification and is on the pro-etale site.

lem-exc-proetale-pullback-locally-constant vs lem-weil-pbc-module-constant-of-set-pullback: that lemma requires a nonempty connected scheme and etale constant underlying sets. The new result pulls back given module trivializations, with neither connectedness nor nonemptiness.

## Review by Q76

I reviewed the unchanged item against its complete master blueprint statement/proof and the current main-20261015 statement/proof. Both follow the same route: exact inverse image for the two explicit adjunctions, pullback of strata and local systems, bounded flat models, and the derived tensor comparison. The unit and chapter records were read. The requested repair does not replace that route. I kept all original statement clauses, including arbitrary derived K for the coefficient comparison and bounded constructible finite-Tor K for the boundedness conclusion.

For step 1 I read prop-exc-open-adjoint, prop-exc-finite-etale-adjoint and prop-weil-pbc-proetale-constant-exact statements. They give the right adjunction and exact inverse image on the whole ordinary pro-etale derived categories. The finite-etale statement additionally qualifies the usual compact-support notation by the finite-type setting, but its ordinary direct-image adjunction used here is unrestricted; the item's finite-etale functor is explicitly f_*. Exactness gives the written cycles/boundaries calculation with no constructibility assumption.

For repaired step 2 I read the full statements of def-weil-finite-torsion-constructibility, def-weil-proetale-locally-constant-sheaf, lem-pur-scheme-constructible-preimage, lem-weil-pbc-left-exact-site-inverse-image-tensor and def-weil-constructible-intervals, and the new node. The first two give the finite stratum/trivialization data. Tag 054I (morphisms.tex, lemma-inverse-image-constructible) applies to arbitrary schemes and arbitrary morphisms, as does the existing Mathlib leaf. Pullback of the defining open and closed pieces proves locally closedness without an extra finiteness hypothesis. The composition theorem really states monoidal inverse-image composition isomorphisms, so the stratum restriction identification has the correct module action. The new node supplies exactly the previously inline local-trivialization lemma for f_nu, which is an arbitrary scheme morphism and has the same finite constant ring. The final interval follows from step 1 and the definition. No etale-origin predicate is substituted for intrinsic pro-etale constructibility.

For step 3 I read lem-sf-flat-model, the pro-etale inverse-image definition, the ringed-topos flat-pullback statement, the bounded-above flat K-flat statement, and the derived-tensor definition. The model theorem explicitly allows any scheme where ell is invertible; no Noetherian hypothesis is needed for its flat (not necessarily constructible-term) model. Stacks 05VD (sites-modules.tex, lemma-pullback-flat) gives precisely the termwise flatness needed for the ringed morphism with identified constant coefficients. The bounded model is K-flat, and the written test tensors against every module sheaf on V, not only pulled-back ones. This proves the full Tor interval.

For step 4 I read the K-flat resolution, ringed pullback of K-flat complexes, B-valued change-of-rings, tensor pullback and constant-ring-map statements. I checked Stacks 06YS, 0G7E, 06YY and 03EL against their stated uses. The resolution has flat terms as well as K-flatness; pullback preserves both. The change-of-rings theorem is a D(B)-valued assertion with resolution independence. Thus the common B-linear tensor complex and the local pure-tensor identity describe the specified natural comparison, even for unbounded K and nonflat A to B.

For step 5 I read the finite tensor constructible-cohomology statement, Tor definition and reduction-flat-model statement, and Stacks 09BQ (proetale.tex, lemma-tensor-c). The finite coefficient ring is Noetherian. K and the constant finite A-module B are bounded constructible, meeting both inputs of the tensor theorem. The Tor test gives the interval separately; no false boundedness inference from the nonflat quotient is made. Quotienting a constant label M by I produces the B-linear label M/IM, including empty trivializing objects. The reduction-flat-model theorem gives flat B-terms in the same support interval, so the final application at stage m is justified.

The new node was tested on identity morphisms, the empty source, empty covering members, disjoint finite-etale sheets, the zero module, and a finite nonfree module over Z/ell^2. None requires nonemptiness or freeness. The item's unchanged Tor proof still handles m=n, n=m=1, acyclic input and a complex in one degree; the comparison is allowed for arbitrary K while boundedness is asserted only for finite-Tor bounded constructible input. Every proof step/dependency pair has a verbatim statement quotation in citations.json. I checked B1-B10, C1-C8, D1-D5 and E1-E7: the new node is self-contained and statement-only, smaller than the item, no duplicate or source-as-proof shortcut is used, and the step's cited statements supply the actual claims. All proof steps are below 2000 characters after the extraction. The new node's statement dependencies are only previously existing notions/results and do not cite the item.

## Unfinished work

The new lemma remains unsplit by design. No Lean writing or compilation is part of this delivery. The required server dry run and final push follow this report; their outcomes are recorded in the command output.
