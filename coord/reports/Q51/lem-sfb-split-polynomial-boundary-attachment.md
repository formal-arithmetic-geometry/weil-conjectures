# Q51 stage-1 delivery: lem-sfb-split-polynomial-boundary-attachment

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-polynomial-boundary-attachment.json: item, split; no exact Mathlib theorem found.
- dag/nodes/sec-six-functors-basics/lem-sfb-truncated-simplex-presentation.json: statement, unsplit; no exact Mathlib theorem found.
- citations.json: exact statement excerpts for every step-use pair.

## Attachments

None. Searched the live WeilConjectures source for the blueprint id and for polynomial/simplicial/degeneracy terminology. Polynomial splitting lemmas concern ordinary split polynomials; no declaration gives the augmented simplicial polynomial attachment. Existing scheme-attachment declarations concern a different category and do not attach this item.

## WANTED

None. All cited Stacks sources are present. The item proof is marked agent-written: the polynomial compatible-degeneracy repair is supplied explicitly, not attributed to the printed 08PX argument.

## Issues and corrections

The item statement is retained exactly, including its compatibility hypotheses and specified lower-degree restriction. Its source already records why arbitrary independent degeneracy lifts in the proof of Stacks 08PX are insufficient. Here the polynomial labels determine compatible maps instead: D_i(x_(e,sigma)) = P(sigma delta_i)(z_e). This avoids choosing lifts. The statement does not assert a lifting to some separately specified next-degree algebra; none is used.

The newest blueprint is literature/blueprint/latest (main-20261023-1620). Read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof. The inherited long provenance refers to an alteration detail no longer printed in that newest direct-images proof. I preserve the inherited statement/source prerequisite and do not change the chapter or unit route. blueprint_refs.py ancestor returns None, which is retained verbatim as the null from.node for item and new node.

Two initial logged grep requests used an absent GeneratorsRelations.lean file and therefore produced no hits. They are not evidence of absence. The node records use the subsequent successful directory searches and actual source readings. The complete unmodified searches.jsonl retains every invocation, including these. Other service results were available. Returned declarations were read by their source definitions: truncated functors and skeletal Kan extensions do not provide the algebra assertion; Algebra.Generators.extend does not impose simplicial identities; Dold–Kan requires additive categories. For the new node, SimplexCategoryGenRel provides an unbounded presentation category, but its equivalence with Delta is not proved in the pinned files (NormalForms still has the face-normal-form uniqueness TODO). There is no bounded recognition theorem in Truncated.lean.

## Not duplicates

lem-sfb-truncated-simplex-presentation vs lem-trf-comonad-counit-augmentation: the existing statement assumes a full simplicial object with comonad-power terms already supplied and proves its counit augmentation and evaluation functor; it does not reconstruct an arbitrary truncated functor from finite operator data.

lem-sfb-truncated-simplex-presentation vs lem-trf-simplicial-operators-reconstruction: the existing theorem takes objects and operators in every nonnegative degree. The new theorem takes data only through a fixed N and requires a bounded presentation, without unspecified higher objects. It is not a one-line application of the unbounded result: constructing a coherent extension of partial data would itself need a theorem.
lem-sfb-truncated-simplex-presentation vs lem-trf-simplex-presentation-unique-lifts: the existing statement gives an inverse for the unbounded generators-and-relations presentation; it gives no bound on intermediate degrees in representing paths or relations. The new theorem needs that bound and reconstructs truncated functors and their morphisms.
lem-sfb-truncated-simplex-presentation vs lem-trf-simplex-word-evaluation-descent: the existing statement evaluates words from data in all degrees, whereas the new one only has data through N.
lem-sfb-truncated-simplex-presentation vs lem-sc-module-cup-godement-simplex-presentation-faithful: faithfulness of the unbounded presentation does not assert bounded generation, bounded relations, or reconstruction from truncated operator data.
lem-sfb-truncated-simplex-presentation vs def-weil-pbc-simplicial-coskeleton: this definition supplies what a truncated functor and natural transformation mean, not recognition from face/degeneracy equations.
lem-sfb-truncated-simplex-presentation vs lem-weil-pbc-simplex-face-factorization: factoring a single map missing a vertex through that coface does not prove presentation or reconstruction for the truncated category.

The whole DAG statements and source tags, the whole imported blueprint (blueprint_refs searches for simplicial polynomial, surjection, truncated, truncated simplex, faces and degeneracies, 0168 and 016B), and the live Lean library were searched. No existing node states the bounded theorem. The new node is generic category theory, does not mention A, B, polynomial algebras or boundary attachment, and is not a clause of the item.

## Review by Q51

I read cotangent.tex Tag 08PX (proposition-polynomial), especially the induction replacing degree n+1, and simplicial.tex Tag 017P (definition-split). The item retains the stronger split polynomial hypothesis rather than pretending that independent polynomial lifts satisfy simplicial identities. For the sole new node I read simplicial.tex Tags 0166, 0167, 0168 and 016B and the truncated definition 0180. The bounded version is a genuine residual lemma: standard epi-then-mono normal forms and the reductions used to compare them remain in degrees at most the maximum endpoint. Its future proof must establish that boundedness; it is not claimed as a Mathlib leaf or as a verbatim full statement of 016B. A route to it is to put codegeneracies before cofaces using mixed relations (which lower, rather than raise, a local peak), and then normalize each monotone block. This is a proof suggestion here, not proof text inside the unsplit node.

I opened every cited node and read its statement, not merely its title. Steps 1–4 use def-weil-pbc-mv-polynomial-ring for existence and equality of algebra homomorphisms on generators. Steps 1–3 additionally use def-weil-pbc-simplicial-coskeleton for the old functor and its contravariant composition law. Step 1 has sigma delta_i between degrees n and j <= n, so all evaluations exist before the extension. Step 2 uses the supplied boundary equality precisely on y_t, and on old variables uses the two equal increasing maps omitting i and j. There is no missing degree -1 constraint when n=0. Step 3 computes each mixed ordinal composite in its three cases; in the two nonidentity cases the old intermediate degree is n-1, so those cases are used only for n>=1. Step 4 compares the two identical ordered quotients on a generator of P_(n-1); the coincident-index case collapses three successive vertices. Thus it needs no theorem about linear combinations or products beyond polynomial uniqueness. These are elementary calculations, and are written separately instead of hidden in a 'standard identities' claim.

Step 5 cites exactly the new node's recognition and codegeneracy-generation clauses. This makes the old restriction the specified functor by uniqueness, and gives every surjective-operator formula by composition; no degeneracy starting in degree n+1 is part of an (n+1)-truncation. Step 6 cites polynomial evaluation/uniqueness and the old functor definition for the augmentation equations, and the new node's natural-transformation clause to deduce augmentation naturality. Each old generator augments to epsilon_j(z_e), and each new generator augments to the given b_t, so no equality of b_t for distinct t is assumed. I copied matching verbatim statement excerpts into citations.json for each use.

For edge cases, at n=0 the construction is Q=A[x_e,y_t] with the constant-degeneracy variables x_e, both faces on x_e equal z_e, and the faces on y_t equal a_(t,0),a_(t,1). Equal augmentation to b_t is exactly what is required. With T empty this simply attaches the forced degenerate polynomial part. With every E_j empty and T empty all rings are A and the maps are identities. The zero ring causes no exception to polynomial evaluation. For the new node N=0 gives one object and identity; N=1 gives two retractions of one degeneracy, whose corresponding constant endomorphism composites are governed by those retractions. Neither statement needs a nonempty variable set or nonzero ring. No item step exceeds 2000 characters (lengths 701, 530, 735, 594, 651, 829), and no comparison or auxiliary theorem is concealed inside a long step. All other-unit citations are existing Mathlib definitions; the new theorem inherits the item's unit. No SGA source, Lean file, compiler or git command was used.

## Unfinished work

Only the proof of the explicitly statement-only new node remains for the DAG queue. The item proof is complete conditional on that cited statement, as required for a one-level split. Delivery validation follows below.
