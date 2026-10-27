# Stage-1 report: lem-sfb-internal-restriction-module-tensor

Group Q101; 2026-10-22. Direct delivery under the dispatcher brief. Only the sandbox was written; no Lean was written and no compiler, Lake, library build, or repository git command was run.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-restriction-module-tensor.json`: statement, split into six proof steps. Mathlib verdict: no full match. The existing searches were retained and six actual new searches were appended from `searches.jsonl`.
- `citations.json`: 16 entries, one for every step/node citation, with verbatim statement quotations.
- `report.md`: this report. `assemble.py` and `searches.jsonl` are sandbox working records only.

New nodes: 0. New Mathlib leaves: 0. The item statement and its statement dependencies are unchanged.

## Attachments

None. Searched the full project `lean/WeilConjectures/` for the item tag and internal group-action terminology, and searched its CategoryTheory and SixFunctors directories for equivariant module terminology. The hit in `CategoryTheory/Sites/EquivariantEvaluation.lean` is evaluation into representations of an external group, not the present internal-action pullback assertion. No declaration covering all clauses was found.

## Sources and searches

Read GOAL.md, the worker/stage-1 contract, the three levels in SETUP.md, delivery-errors B--E, the chapter `sec-six-functors-basics`, the unit `sk-thm-sf-ctf-stability`, and the current direct-images proof in the item's source. Paragraph (3) provides the parent direct-image route; this node is the agent-formulated infrastructure for its internal-action restriction input. The proof follows that route and is explicitly marked agent-written, rather than claiming the blueprint proves this lemma.

Read Stacks `sites-modules.tex`, label `lemma-adjoint-pullback-pushforward-modules` (03D7), `lemma-sheafification-presheaf-modules` (03CY), `lemma-abelian` (03DA), and `section-tensor-product` (03EK), including its bilinear universal property and associativity formulas. Checked these tags in `tags/tags`. These are the sources for the module tensor, unitor, exactness and comparison arguments. The internal-group part is supplied by the existing node `lem-sfb-internal-action-site-presentation`, whose statement was read in full, not inferred from a proof or from the external-group Stacks special case. No SGA source is used.

Ran the prescribed msearch command with LeanFinder twice, LeanSearch once, Loogle once, and grep twice. Actual queries and answer digests are in searches.jsonl and copied to mathlib_searches without alteration. Read the returned hits: LightCondensed monoidal structures concern one specific site with fixed coefficients; Action monoidal structures concern an external fixed monoid; SheafOfModules.restrictScalars concerns a ring morphism on one site. The general module pullback and free-module comparison hits do not state the internal-group action identification, exactness, diagonal action, and canonical identity normalization together. Read the relevant Mathlib source in `CategoryTheory/Action/Monoidal.lean`, `Condensed/Light/Monoidal.lean`, and `Algebra/Category/ModuleCat/Sheaf/{ChangeOfRings,PullbackFree}.lean`. These are infrastructure, not a one-line specialization proving the item.

Searched the whole DAG for sheafified cokernels, tensor universal properties and trilinear extensionality. Reused the existing bilinear and trilinear nodes instead of creating elementary or duplicate comparison lemmas. Whole-blueprint searches for internal group, equivariant, diagonal action, sheaf tensor, sheafification and trilinear gave no blueprint statement equivalent to this item; the representation and torsor hits have different hypotheses and conclusions. `blueprint_refs.py ancestor` reports a null inherited ancestor: kept that provenance and its via chain, and specified the actual current paragraph and parent steps in split_report.blueprint.

WANTED: none additional for this split. The inherited action-site prerequisite remains an agent-formulated theorem; this delivery relies on its explicit statement and does not assert that the external-group source proves the internal-group case.

## What was wrong and what changed

The item was statement-only, with no proof. Its statement does not need correction. The multiplication identification, exactness, tensor action and comparison coherence now have explicit arguments. General small-site bilinear and trilinear universal properties and the canonical-normalization definition are declared as tool uses, not alternative routes for the constructibility unit.

No statement dispute was found. No new definitions or helper assertions were introduced. In particular no clause was moved into another node. The old statement dependencies remain needed, and proof_deps is exactly the union of the six uses lists.

## Not duplicates

No new nodes were created. The existing action-site presentation already supplies the sheafification and kernel/cokernel infrastructure. The existing `lem-pc-sites-sheaf-tensor-bilinear-universal` and `lem-pd-sheaf-trilinear-universal` supply the universal properties; none is restated under a new id.

## Review by Q101

I checked every step against the actual statements it cites, and then wrote citations.json from those statements. The proof is conditional on the given geometric morphisms, exactly as the item is; it does not quietly use the parent theorem which depends on this item.

1. The action-site statement explicitly gives the additive equivariant-module equivalence with the same section modules, and the module-adjunction statement explicitly gives the formula S tensor over f-inverse R of f-inverse M. The structural map is an identity and the ring action is trivial, so its hypotheses give the displayed identity-ring formula. The operations on f-inverse M are unchanged operations with the new action, since the inverse images in the hypotheses are the actual trivial-inflation and action-restriction functors. I checked both destination sites, C_K and C_L.
2. The ordinary tensor definition states the balancing universal property and pure-tensor generation; module sheafification states unique factorization; the sheaf bilinear node states the bijection identifying maps out of the sheaf tensor. These supply exactly the well-definedness, descent and equality checks used for r tensor h mapping to rh and its inverse. The balancing calculation proves the inverse identity, rather than assuming a tensor-unit theorem. Linearity of b proves naturality and the assertion on morphisms. The ring is allowed to be zero.
3. The action-site statement, not merely the definition of an equivariant category, explicitly says that forgetting action creates kernels and cokernels with the required underlying formulas. The ordinary module-category node states abelianness and the same formulas without action. Module sheafification is functorial, so sheafifying the quotient action commutes with substitution through theta. Thus restriction and trivial inflation preserve those actual constructions and addition of maps. No exactness of taking fixed points is asserted or used.
4. The ordinary tensor node supplies the balancing relations and generation needed for the formula a(x tensor y)=ax tensor ay. The action-site node supplies sheafification compatibility for equivariant presheaves; the sheaf tensor definition says that the tensor is precisely the sheafification of the section tensor presheaf. The displayed restriction along (f,a) therefore computes the action-site tensor. All group operations are R(U)-linear because the coefficient-ring action is trivial; no action on R was silently allowed.
5. The action-site sheafification clause identifies the sheafifications of the literally identical tensor presheaves. I checked the identity on arrows as well as on objects. The canonical-comparison definition supplies the generalized pure-tensor normalization, and our inverse comparison satisfies it for every test sheaf because forgetting actions leaves every underlying equation unchanged. Bilinear universality gives uniqueness on the base site; forgetting action is faithful by the definition of equivariant maps. Thus this step identifies the canonical comparison, rather than merely producing an unspecified isomorphism. The coefficient unit becomes the identity under the multiplication identification of step 2.
6. Bilinear universality detects equality of the naturality, symmetry and unit composites. Trilinear universality explicitly detects equality of maps from (A tensor B) tensor T on triple pure tensors; that is precisely the domain and test used for associativity. The source and target are ordinary R-module sheaves on the original small site, so the node's size hypotheses hold. This avoids the invalid assumption that every global section of a sheafified tensor is a finite sum of global pure tensors. Faithfulness then gives the equations with their actions.

I tested the proof with K=L=1, with theta the identity, with L=1, and with a noninjective morphism of groups on a point site. None requires injectivity, surjectivity, finiteness, or flatness of theta or of a module. Zero modules and the zero coefficient ring give the same identities. Noncommuting group elements still act correctly since diagonal action preserves their original order; only R is commutative. No enough-points assumption or sectionwise-surjectivity assumption appears. All arguments involving cokernels and tensors use the actual sheafification, not a mistaken sectionwise formula for the final sheaf. Every step is shorter than 2000 characters. I also traversed the dependencies of the additional general tensor tools and the action-site node and found no path back to this item.

The B--E audit therefore leaves no new-node self-containment, duplicate, hidden-source, citation, cycle, or statement-repair issue to correct. The important correction to a tempting shorter argument was to use the existing trilinear universal property for associativity, rather than claiming global pure-tensor generation after sheafification. No work remains unfinished in the split.

## Validation

Required server dry run exited successfully: `OK (not pushed) deliver/Q101/lem-sfb-internal-restriction-module-tensor at 6a11170ac5f: preflight passed`. This includes the server preflight, DAG and split review checks, and the 16 verbatim citation checks. No Lean compile was run.
