## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-group-algebra-exact-forgetful.json — statement, split in eight steps; no Mathlib match for the complete internal statement.
- citations.json — one verbatim statement quotation for each cited node at each proof step.
- No new DAG nodes or Mathlib leaves. All non-elementary ingredients already have DAG statements.

## Attachments

None. I searched lean/WeilConjectures/ for the blueprint id, group-algebra terminology and condensed actions. The ordinary group-algebra and representation declarations do not supply this internal sheafified statement. No exact attachment was found.

## Wanted

WANTED: an independent published reference for the internal group-algebra/action equivalence over a variable condensed ring, for lem-sfb-condensed-group-algebra-exact-forgetful. The inherited source correctly calls this an agent-formulated extraction, and proof_origin remains agent. Stacks supplies the sheafification and tensor ingredients, not the whole theorem. No SGA source is used.

## Audit and changes

The statement is unchanged. In particular the free group algebra is sheafified, and its section modules are not identified with globally free A(S)-modules. The proof was absent, not a completed split: the sandbox initially contained only dispatcher marker files. I retained all inherited searches and ran additional actual recorded searches through msearch.py, reading the hits and the source of Rep.equivalenceModuleMonoidAlgebra (Mathlib/RepresentationTheory/Rep/Iso.lean:159). This is the equivalence for an ordinary commutative ring and an abstract monoid; applying it sectionwise does not by itself prove the internal statement. LeanFinder was tried with two phrasings, in addition to LeanSearch, Loogle and the recorded greps.

I read the current main-20261015 direct-images proof, paragraph (3), the chapter record and unit record. The internal group algebra is supporting infrastructure below the open-direct-image clause, not a replacement route. The inherited blueprint ancestor command returns null, as does the inherited from.node; I kept that provenance rather than inventing a blueprint node. Its from.place was already precise and is retained. Whole-blueprint searches for group algebra, group-algebra, internal group, linearization, equivariant and sheafification found no node stating this complete item; same_as stays empty.

## Not duplicates

No new node pairs: none were created. I reused lem-sfb-condensed-free-linearization-tensor for the free-module/sheafification and monoidal comparisons, lem-pc-sites-module-sheafification-bilinear-extension for extending the action, lem-pe-internal-section-tensor-comparison for the actual internal tensor comparison, lem-sfb-condensed-action-injective-infrastructure for kernels/cokernels and exactness, and lem-sfb-equivariant-module-sheafification-reflector for the action on sheafified linearizations and tensors. Creating another action-equivalence or exact-forgetful node would have been a restatement of clauses of this item.

## Review by Q120

I read coord/delivery-errors.md B–E in full and checked the split against the actual statements, not the proofs, of every cited node. The source for the item is the current direct-images paragraph (3); I also read Stacks sites-modules.tex Section 03EK, Tag 0GMW (lemma-sheafification-tensor) and its following bilinear universal-property display, and the section-kernels abelian-sheaf-module discussion. The explicit group-algebra argument is written by this worker, while the source's omitted sheafification arguments are supplied through existing cited nodes. There are no new nodes whose source needs a separate review.

Step 1 uses the group-sheaf assertion in condensed-action-injective-infrastructure and the product and terminal-object comparisons, generator detection and coherence in condensed-free-linearization-tensor. Multiplication really is the linearization of group multiplication; associativity compares (gh)k with g(hk), and the two unit comparisons are 1g and g1. It does not assert commutativity for nonabelian G.

Step 2 uses the action-module definition for natural linear actions, the free-linearization statement for F_K^# = E_A(B), the bilinear-extension statement for extending the prescribed natural pairing, the sheaf-tensor universal property for the resulting morphism, and the internal-section-tensor comparison for the given relative tensor. I checked that both inputs of bilinear extension are module presheaves over the same A, the target is a module sheaf, and A is already a commutative ring sheaf. There is no requirement that post-sheafification sections have global finite-generator expressions.

Step 3 cites the free-linearization tensor isomorphism, bilinear-extension uniqueness, the monoidal internal-section comparison and the module-object axioms. I made its equality test explicit by identifying B tensor B with A[K times K]: both associativity maps agree on [(g,h)] paired with m, so they agree on finite sums in F_{K times K}, and the quoted bilinear-extension uniqueness proves equality on the entire sheafified tensor. This avoids an implicit iterated extension argument. The cited associator comparison identifies that equality with the actual internal module law; the unit calculation is b([1],m)=m.

Step 4 cites the action definition, module axioms and the two sheaf/tensor comparison interfaces. I checked both directions: restrict after extending fixes the generators; extend after restricting fixes the entire action by uniqueness. The criterion f(gm)=g f(m) on every S implies commutation with arbitrary finite sums before sheafification and then with the internal B-action. The two functors fix underlying modules and maps, so the identity unit and counit really give the stated equivalence over internal A-modules.

Step 5 invokes the existing action infrastructure at R=A and J=G. Its statement explicitly says the action category is Grothendieck abelian, that forgetting creates sectionwise kernels and sheafified sectionwise cokernels, and that it detects zero objects and exactness. The site and coefficient size hypotheses are those of the item. Uniqueness of quotient actions uses local lifts along the sheaf epimorphism, not a global section lift. Step 6 then writes out the elementary image formula ker(coker(f)); the same statement supports the zero-cokernel criterion for the augmentation. Thus each exactness assertion is about the underlying internal module complex, with no covert sectionwise exactness claim.

Step 7 uses the equivariant-sheafification reflector and free-linearization lemma. The reflector is general for an internal sheaf of groups, so it applies to K=underline G, not just constant group actions. I checked the presheaf formula g[x]=[gx], equivariance of A[u] on generators, and the final detection of equivariance by identifying B tensor A[X] with A[K times X]. Step 8 applies that same reflector to the presheaf balanced tensor and uses the exact actual internal-section tensor comparison. The action is balanced because g is A(S)-linear and T's action is trivial. The displayed calculations prove functorial equivariance, preservation of sums and zero; the tensor universal property extends them to sheaves.

All cited statements were opened in full. I checked the transitive dependencies of the principal candidates and found no path back to this item; the server's required DAG check will also verify this. Generic off-unit sheafification and tensor comparisons are declared in split_report.tool_uses. None substitutes a different unit-level proof route. All eight proof steps are below 2000 characters, and none hides a separate comparison lemma: the comparisons and reflectors are cited existing nodes.

Small cases checked: the zero coefficient ring and zero module give zero actions and the same zero category; G=1 gives B=A and the identity equivalence; an empty condensed X linearizes to zero; T=0 makes the tensor functor zero. A nonabelian finite G has [g][h]=[gh], with no asserted commutativity. Cokernels need only be locally lifted, including the epimorphic augmentation. These checks revealed no statement dispute. No Lean, compiler, Lake, repository git command, or repository write was used.

## Unfinished work

None in this stage-1 item. No definition, new lemma, or theorem was shifted into an unsearched new node. Independent mathematical review remains the maintainer's responsibility.

## Validation

The first server dry run exited successfully: preflight passed, including the DAG and split checks. Before the final dry run I sharpened step 3 to use F_{K times K} directly and refreshed citations.json against the full statements, so its quotations include every formula actually used.
