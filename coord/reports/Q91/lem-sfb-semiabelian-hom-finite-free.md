# Q91 stage-1 delivery: lem-sfb-semiabelian-hom-finite-free

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-hom-finite-free.json: item, split into four explicit steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-hom-matrices.json: new statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-abelian-hom-vanishing.json: new statement-only lemma; no Mathlib match.
- citations.json: verbatim statement quotes for every use in every item proof step.

## Attachments

None. Searches of lean/WeilConjectures for the item's blueprint tag, semiabelian terminology, abelian-variety Hom, and torus terminology did not find the required declaration. The existing abelian Hom result in the DAG is reused, not attached again. No Lean was written or compiled.

## WANTED

WANTED: Deligne, Le lemme de Gabber, Astérisque 127 (1985), pp.131 and 139–140, for the historical source chain of lem-sfb-semiabelian-hom-finite-free. Its path in the item's source does not exist in this read clone. The present split does not rely on an unread argument there: it is explicitly agent-written from the two available Milne PDFs.

## Issues and changes

The item was unsplit and its sandbox contained no earlier node or report. Its inherited Mathlib searches were read and retained, including the explanation that abstract addMonoidHom instances require finitely generated underlying integer modules and therefore do not handle semiabelian points. I ran logged searches for each new input: two semantic phrasings, LeanSearch, Loogle, and a whole-Mathlib grep. The first broad grep was polluted by 'functorial' and RingEquiv names; the second used word boundaries. Its hits concern analytic tori and diagonalizable linear operators. No service was unavailable.

The proof works directly with the exact sequences of represented fppf sheaves. Consequently it does not use the uncited representability claim about group algebraic spaces in the old source note. I have not strengthened the statement to assume G and H are schemes. All morphisms whose classification or vanishing is invoked have schemes as both source and target: the tori and the abelian quotients. Evaluating a natural transformation on the identity supplies the scheme morphism, with naturality checking its value on every test scheme.

The current blueprint's direct-images statement and proof were read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. They give the proper/open direct-image route, with this item an inherited supporting lemma down the alteration/Picard branch. No unit or chapter route changes. tools/blueprint_refs.py ancestor returned None, consistent with the item's existing broken-ancestor/null provenance; the exact inherited place and via list are preserved, and the new nodes prepend the item to via. Whole-blueprint searches for semiabelian, torus, split tori, diagonalizable, anti-affine, abelian varieties and Hom(A found no matching blueprint theorem. same_as is empty.

## Not duplicates

lem-sfb-split-torus-hom-matrices vs lem-trf-lattice-torus-coordinates-action: the existing node identifies one torus from a lattice basis and describes a toric action and base-change charts; it does not classify all group-scheme morphisms between two tori. The new lemma is precisely that missing classification.

lem-sfb-split-torus-hom-matrices vs lem-trf-toric-realization-finite-type: the existing statement gives geometric properties and actions of tori in rational toric realizations, not their Hom groups over an arbitrary field.

lem-sfb-torus-abelian-hom-vanishing vs lem-sfb-abelian-hom-finite-free: the existing result is about maps between two proper abelian varieties; it does not say that maps to or from a positive-dimensional affine torus vanish.

lem-sfb-torus-abelian-hom-vanishing vs lem-sfb-semiabelian-hom-finite-free: vanishing is an independent geometric input, stronger than finite freeness on the mixed pure factors, not a restatement of the item's conclusion. The item proves its extension case and injection itself.

The whole DAG was searched by titles, statements and source terms before creation. No relevant Stacks-tag duplicate pairs arise: these two inputs follow Milne rather than a Stacks theorem. The existing abelian Hom theorem and existing subgroup Mathlib leaf are cited, not recreated.

## Review by Q91

I read Milne AV I Theorem 10.15 and its proof on printed pp.49–50: its finite free conclusion applies to the abelian quotients, but says nothing about semiabelian extensions. I read Milne Algebraic Groups Theorem 12.9(a), including its fully faithful character functor and its identification D(Z)=G_m on pp.233–234, for the new torus classification. That identifies the integer exponent arrays with all scheme homomorphisms, not merely their maps on k-points. I read Proposition 8.1(b) and Example 8.4 on p.149 and §8(e) on p.151 for the new vanishing lemma, and the image factorization Theorem 5.39 on pp.108–109. The image of a torus homomorphism is affine, smooth and connected by 8.1(b), is a closed subgroup of the abelian variety by the homomorphism theorem, and hence is finite by Example 8.4; finite smooth connected over algebraically closed k means trivial. In the other direction an abelian variety is anti-affine, and §8(e) states exactly that its homomorphisms to an affine group are trivial. These arguments remain the intended future splits of the two statement-only nodes; no proof is hidden in their statements.

Step 1 cites def-trf-algebraic-space for its statement that morphisms are natural transformations, and the new vanishing lemma for Hom(T_G,A_H)=0. I opened both statements: they give exactly these claims. The kernel property and fppf-local lifting are explicit hypotheses of the item, not claims borrowed from a definition node. I wrote the descent of q_H f by local lifts, checked independence by their difference in T_G, and checked gluing into the target sheaf. Local lifting also makes that descent unique. This proves the induced abelian-quotient map and its additivity without an unmentioned quotient theorem.

Step 2 uses the other half of the vanishing statement, Hom(A_G,T_H)=0. Its hypotheses hold: k is algebraically closed, A_G is an abelian variety, and T_H is a split torus. For a map in the kernel of Phi, factorization into T_H follows from the assumed kernel property; the restriction vanishes because i_H is a monomorphism. The second local-lift argument produces A_G to T_H, so this cited vanishing gives f=0. I checked that proving only the torus-to-abelian vanishing would be insufficient here and included both directions.

Step 3 cites the new torus classification, the full existing statement of lem-sfb-abelian-hom-finite-free, and the existing Mathlib leaf lem-weil-subgroup-finite-free-abelian-group-free. Each statement was opened. Chosen split coordinates supply the torus-classification hypothesis; the abelian Hom statement allows any field, in particular this k; its basis and the finite exponent array give a finite coordinate set J. The image of the injection from steps 1–2 is a subgroup of Z^J, exactly the hypothesis of the cited subgroup statement, including its isomorphic-subgroup consequence. This is a Mathlib leaf and needs no off-unit route permission. The abelian Hom node is already in the same unit.

Step 4 is elementary: I wrote both distributivity identities, associativity and the identity. Pointwise addition is legitimate because the input groups are commutative. I checked the zero group explicitly: the empty basis and the zero ring with 1=0 are allowed by the statement. There is no demand that the ring be nontrivial.

For small cases I checked r=0 or s=0 in the torus statement (unique zero exponent array and unique trivial group map), r=s=1 (all integer powers, including negative and zero), and positive characteristic (the p-th power morphism still corresponds to a nonzero exponent). The vanishing lemma includes the zero-dimensional abelian variety and rank-zero torus. The item specializes correctly to pure tori, pure abelian varieties and G=0 or H=0. The proof also covers nonsplit extensions of the abelian quotient by the given split torus; it never chooses a splitting of the extension. No inference uses reduced k-points to detect arbitrary morphisms. Every non-elementary step has the exact cited input. Each proof step is below 2000 characters, with the two descent arguments written out rather than hidden in a long 'standard' identification. New nodes are self-contained, use existing definition nodes, have no proof or proof dependencies, and carry the recorded searches actually run.

## Unfinished work

None within this one-level split. The two new geometric inputs are intentionally unsplit queue items. No compiler, Lake, or local delivery preflight was run.
