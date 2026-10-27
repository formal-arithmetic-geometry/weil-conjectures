# Q71 stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-line-sections-normalized-comparisons.json`: statement item, now split into eight proof steps; not a Mathlib leaf.
- `citations.json`: 21 entries, one verbatim statement quote for every step/node pair.
- `searches.jsonl`: the actual search-command log. `write_split.py` is a sandbox-only JSON generation helper.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this auxiliary node is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's exact blueprint tag and for tensorSections, tensorPullback, etale line modules and the narrower component constructions. No declaration states the full item. Read EtaleTensorSectionsSheaf.lean (associated abelian sheaf), EtaleTensorSectionsMapNaturality.lean (naturality in a module map), TensorPullbackStructureSheaf.lean (adjoint unit map), EtaleTensorUnitSectionsNatural.lean (additive unit coordinates), TensorPullbackCompositionIso.lean (chosen tensor comparison), and TensorPullbackCompositionAssociativity.lean. These are partial components, not the module-sheaf functor with all the restriction and unit coherence clauses. Consequently no attachment is claimed, regardless of their own proof status.

## WANTED

None. The Stacks sources needed for the proof are present.

## What was wrong or incomplete

The item was a statement-only node. Its statement is retained verbatim, including all module morphisms, the prescribed inverse-comparison components, and the orientation of the composition equation. The proof now supplies the construction rather than moving individual clauses to new nodes. No statement dispute or source error was found.

The imported unit/chapter records point at an older blueprint. I read the current `literature/blueprint/latest/blueprint/sec-trace-formula/_section.md`, `sk-i-curve-zero/_section.md`, and lem-trf-local-term-locality.md with its proof. The current ancestor concerns contracting local terms and contains no separate line-comparison theorem; this auxiliary item belongs to its inherited polarized scheme-descent branch, via lem-trf-scheme-etale-invertible-comparison. I have neither changed the unit nor replaced its trace-formula route. No prohibited SGA source is used.

The nearby full quasi-coherent equivalence and scheme-etale invertible comparison cannot be used as tools here: the invertible comparison already depends on this item, and the full equivalence depends on that comparison. Their statements were read, and neither was cited. This avoids a cycle.

## Mathlib and blueprint searches

The inherited Mathlib records are preserved. The six new searches are exactly those in searches.jsonl: LeanFinder with two semantic phrasings, Loogle for `"pullbackComp", "pullbackId"`, LeanSearch for the etale quasi-coherent line-sheaf construction, and two grep queries under AlgebraicGeometry and AlgebraicGeometry/Modules. All services answered. Read the relevant candidate sources: Mathlib AlgebraicGeometry/Modules/Sheaf.lean:219–315 proves identity/composition coherence for abstract module pullbacks; Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:86–128 constructs abstract unit/free pullbacks; Quasicoherent.lean defines local presentations. These do not state this whole small-etale section-functor theorem. No absence claim was made from a failed service.

Whole-DAG source/tag and keyword searches located the existing component nodes. `tools/blueprint_refs.py ancestor` gives lem-trf-local-term-locality. Blueprint searches for 03DX, etale.*module, composition.*pullback found no exact statement. The broader pullback search was also read: its numerous hits include derived operations and do not provide the present tensor-section line-module theorem. The item's same_as remains empty. No new node was created, so no duplicate-pair section is required.

## What could not be finished

Nothing mathematically outstanding in this split. Independent review and later formalization of the existing dependencies remain the project's normal subsequent work.

## Review by Q71

I read Stacks descent.tex, equation-quasi-coherent-presheaf and lemma-sheaf-condition-holds (Tag 03DR section), proposition-equivalence-quasi-coherent (03DX, especially the forward functor on the small site), remark-change-topologies-ringed-sites and proposition-equivalence-quasi-coherent-functorial (03LC), and lemma-equivalence-quasi-coherent-properties (05VG). These provide the associated-sheaf route, pullback compatibility and local finite freeness. The explicit normalized coherence calculations are written as an agent expansion, not attributed verbatim to a proof that omits them. There are no new nodes needing further source review.

For the tensor formulas I read sheaves.tex, definition-pushforward (0095), lemma-adjoint-pullback-pushforward-modules (0096), lemma-push-pull-composition-modules (0097), and the change-of-rings tensor definition and adjunction. In categories.tex I read lemma-transformation-between-functors-and-adjoints (0B65), including the Hom-bijection uniqueness argument. In modules.tex I read lemma-pullback-quasi-coherent (01BG) and lemma-pullback-invertible; the proof uses the direct rank-one local trivialization rather than invoking an uncited global invertibility theorem. The ring-unit formulas are formulas on local tensor representatives and descend to the sheaf, not a false global-sections/tensor interchange.

Step 1 cites the normalized-presheaf node for semilinearity and its exact restriction formula, the invertible-definition node for quasi-coherence, the descent node for the actual sheaf assertion, and the module-adjunction node for naturality of its unit. I opened all four statements. No claim that a definition alone proves descent is made. Module-map naturality is derived by the two explicit naturality squares, so I do not need a new naturality node. The functor category has all module maps, not just invertible ones.

Step 2 cites the structure-pullback node for both invertibility and its unit equation, and the unit-restriction-equation node for the exact restriction identity. Both statements were opened: the latter is an equality of additive homomorphisms, while module-linearity follows from the former's assertion that the map is an O_U-module morphism. The ring sheaf can be obtained using step 1 with O_X; its ring operations and all module actions are the specified sectionwise ones. The inverse tensor formula is checked by the balanced relation.

Step 3 uses the quasi-coherence-of-pullback theorem with an arbitrary scheme map and a quasi-coherent module; the hypotheses hold because L is invertible. The other two citations give the Zariski rank-one definition and the actual inverse-image/tensor formula. The local calculation on the inverse-image open cover is written out, so no separate preservation-of-invertibility node is hidden. This step is elementary relative to those statements and definitions.

Step 4 uses the general associativity node with four categories of scheme modules. The required right-adjoint equalities hold because pushforward is defined by inverse images of opens; the normalized-presheaf statement explicitly records that equality and its composite unit. The module-adjunction statement supplies each adjunction. I checked the direction: c goes from successive pullback to composite pullback, so beta is its inverse on sections. Rearranging associativity gives exactly the site-restriction square, and naturality of c gives the equation for arbitrary h. No assumption on affine objects or nonempty schemes is introduced.

Step 5 uses those same adjunction units and normalization, and the conjugate-unit uniqueness theorem. The identity multiplication map has identity adjoint, so w^*i and c_(w,id) have equal adjoints; the uniqueness theorem gives their equality. Cancellation then proves the prescribed identity equation. This is an explicit one-instance application of uniqueness, not a new coherence axiom.

Step 6 applies the associativity statement a second time, now to t,z,v, and multiplies by inverses. I checked every domain and codomain: (vzt)^*L first goes to (zt)^*v^*L, then to t^*z^*v^*L, then by t^*c_(z,v) to t^*(vz)^*L. The rearranged equation is precisely beta_(vz). There is no silent identification of a tensor-product module with its section module.

Step 7 uses the structure node's adjunction-unit equation and the module-adjunction Hom bijection, with the normalized composition from the presheaf node. Both candidate maps have adjoint the composite structure-ring map; injectivity of that stated bijection proves equality. The supplementary local tensor calculation has the same multiplication order. This verifies the otherwise ambiguous phrase about the structure comparison by a displayed commutative equation.

Step 8 cites the Zariski-etale inclusion node, whose statement explicitly says a Zariski covering goes to an etale covering. The actual frame is the inverse of the displayed three-factor composite of already constructed isomorphisms. It requires no descent theorem for recovering a line module, no quasi-compactness and no separatedness.

I checked the B–E failure cases: no new statements or unsplit nodes containing proof sketches, no duplicate or clause-restatement nodes, no unsupported non-elementary step, no citation taking material merely from a proof, no cycle through the parent equivalences, and no implicit finite-cover or Noetherian hypotheses. The generic off-unit citations are individually declared in split_report.tool_uses; they are background descent/adjunction tools rather than an alternate unit route. Each proof step has fewer than 1100 characters, so none hides a long lemma behind a >2000-character step.

Small cases checked: empty schemes and empty covers (all equations are componentwise and the sheaf over the empty object has its unique zero section), L=O_X (epsilon and beta reduce to multiplication), identity maps (step 5), two identity factors (steps 5–6), disconnected schemes (all calculations are sheaf-local), zero/noninvertible h (step 1 only uses linearity), and arbitrary infinite Zariski covers (no finite subcover is selected). Tensor formulas are valid over general rings, including nonreduced rings; no division or stalkwise rank argument assumes a field.
