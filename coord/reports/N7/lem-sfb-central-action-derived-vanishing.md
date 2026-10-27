# Stage-1 delivery: lem-sfb-central-action-derived-vanishing

Group N7, 2026-10-23. Direct delivery; only stage 1. No Lean files were written, no compiler or build was invoked, and no repository or launcher files were changed.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-central-action-derived-vanishing.json: existing statement, now split into five steps; Mathlib verdict no match.
- citations.json: one verbatim statement quotation for each of the five step/node citations.
- report.md and searches.jsonl: this report and the genuine search-command log.

There are zero new nodes and zero new Mathlib leaves. The existing infrastructure already carries the non-elementary facts, so creating central-action or zero-object nodes would introduce elementary facts or restate the item's clauses.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for central action, centre, invariants and derived invariants. The discrete-module derived-invariants comparisons and ordinary representation results do not cover internal condensed modules over an arbitrary condensed ring. No exact project declaration was found.

## WANTED

No additional document is needed for this split. Its internal action-category existence and derived computations are stated in existing cited nodes. The proof of the central identity itself is the agent argument written here, not an alleged theorem of the blueprint or a published condensed-group reference.

## What changed and what was wrong

The imported item had a statement and searches but no proof. Its statement, six statement dependencies and all hypotheses are unchanged. I added an actual resolution argument, including an explicit equation for the natural computation unit; equality only on cohomology would not establish the stated derived-morphism equality. The vanishing argument uses the full derived functor's additivity and preservation of inverse morphisms.

Read the main-20261015 direct-images proof, paragraph (3), its current unit section, the stored chapter/unit records, and the consuming dense-lattice comparison (step 2). The blueprint paragraph gives the ordinary direct-image route but does not itself state this auxiliary lemma. This is the existing agent extraction used to kill the invertible T_i-1 summand; it does not replace a unit route or assert a continuous-cochain theorem. The stored unit record is the older sec-six-functors version, whereas the current section is under sec-six-functors-basics. Neither record was edited.

The blueprint ancestor command reports None, consistent with the item's existing null from.node and via chain ending in lem-sfb-admissible-direct-image. I preserved that existing chain and filled the precise place rather than inventing an imported ancestor. Searching all imported blueprint nodes for “central” returned fourteen unrelated algebraic-group nodes and no equivalent. same_as remains empty.

No statement dispute was found. No repairs or missing hypotheses were necessary.

## Not duplicates

No new nodes were created. The action-module definition, the injective infrastructure, and the ordinary right-derived-functor definition were reused.

## Searches and candidate assessment

All fresh Mathlib searches ran with the required msearch.py command and appear in searches.jsonl. Two LeanFinder phrasings addressed the central identity and invertible-difference vanishing separately. Loogle searched groupCohomology with center. LeanSearch searched the derived identity for sheaves. A whole-Mathlib grep searched central/center near cohomology/invariants, and a second grep located the returned representation candidates. All services answered successfully. Preserved the item's earlier queries and recorded their actual earlier results, including its unavailable LeanSearch attempt; fresh searches were appended.

Read RepresentationTheory/Intertwining.lean:583–594: centralMul constructs an intertwining map in an ordinary representation, without invariants or derived condensed modules. Read Invariants.lean:252–275: the invariants functor is for ordinary Rep k G. Read GroupCohomology/Functoriality.lean:356–358: map₁_one concerns the trivial group homomorphism in degree one, rather than a central coefficient endomorphism. Read GroupCohomology/FiniteCyclic.lean:80–103: the quotient formula assumes a finite cyclic group and ordinary representations. These are not one-line specializations giving the item's arbitrary topological-group internal formulation. The remaining Gaussian/Lie/Brauer grep hits concern unrelated notions, and the displayed search signatures were read for the continuous topological-module candidates, whose target category also differs.

## Review by N7

I read delivery-errors B–E in both copies and checked the actual statements cited in every step, not their proofs. I read the item and all its statement-dependency statements: the coefficient is a ring sheaf on the small coherent profinite site, internal module objects are the given category, and the size convention fixes the universe. No ordinary discrete or topological module category was substituted.

For step 1 I read def-sfb-condensed-action-module. Its natural sectionwise action and definition of equivariant morphisms give precisely the two equations written: constant central action commutes pointwise with every continuous S-to-J action operator, and equivariant maps commute with that action. The restriction equation is part of naturality of the original action. This proves a natural endomorphism on the whole action category, so applying it to an injective complex really gives a chain map and an equivariant augmentation square. It is a direct calculation, not a new lemma.

For step 2 I read the statement of lem-sfb-condensed-action-injective-infrastructure in full. It explicitly gives bounded-below injective resolutions in the action category, says they are K-injective, computes the ordinary total derived invariants on them, and says their computation units are invertible. N[0] is bounded below, and its coefficient site, ring and group are exactly the stated ones. I also read Stacks derived.tex Tags 05TH (lemma-injective-acyclic), 05TI (lemma-enough-injectives-right-derived), 070Y (lemma-K-injective-defined), and 070K (lemma-enough-K-injectives-implies). These are the generic resolution source, not a substitute for the cited internal infrastructure. There is no assumption that forgetting an equivariant injective leaves an injective.

For step 3 the same action definition explicitly describes invariants as sections fixed after every profinite base change and specifies the inclusion as sectionwise injective. Taking the identity base change and a constant map is permitted even when J is neither compact nor discrete. A map of invariant objects is the restriction of the equivariant map: equivalently compose with the invariant inclusion and cancel its sectionwise injection. Thus the identity is an actual chain-map identity. I did not infer it only from cohomology or from invariance under constant points in the reverse direction.

For step 4 I read def-sfb-right-derived-functor, whose statement includes the natural transformation eta, invertibility at K-injectives, and the comparison for a quasi-isomorphic K-injective resolution. The displayed naturality equation and the augmentation square conjugate the map first at I and then at N[0]; both cancellations are by invertible maps. This directly establishes the requested equality in D(Mod_R), including its full morphism, without an uncited chain-homotopy lemma.

For step 5 the infrastructure statement explicitly says the derived functor is additive. This supplies preservation of z minus identity; an inverse to u[0] is the degree-zero map induced by its assumed action-module inverse. The remaining two equations f=f1=0 and h=1h=0 prove the zero-object universal property in an additive category, so a separate zero-object node would be elementary. Read Stacks Tag 0159 (lemma-right-derived-properties) for the generic derived-functor context. All five quotations in citations.json are copied verbatim from those nodes' statements and cover exactly the facts taken from them.

I tested the statement on the zero ring and zero module (identities and isomorphisms of the zero object are legitimate), trivial J and z=1 (the invertibility hypothesis forces the module to be zero), a trivial action on a nonzero module (the conditional premise fails), and the ordinary example J=Z acting on a rational vector space by multiplication by 2 (z-1 is invertible and the expected invariant complex vanishes). No dimension, compactness, discreteness or trivial-action hypothesis was used anywhere. Empty profinite test sets cause no exception: the constant action map and the invariant-section condition still exist. Each proof step is under 600 characters; there is no long hidden comparison or independent lemma.

The definition cited in step 4 is from another unit, but definitions are exempt from the route restriction; both theorem citations are to the existing infrastructure in this item's own unit. No tool-use exception is needed, and no cited node uses this item in its statement. The required server dry run will check the entire overlaid DAG for cycles and stale dependencies.

## Unfinished work

None in the authorized stage-1 scope. The below-item infrastructure remains its own separately tracked work. No Lean proof or formalization is claimed by this delivery.
