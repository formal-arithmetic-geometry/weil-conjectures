# Q104: lem-sfb-adequate-algebra-pushforward

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-algebra-pushforward.json: split the item into five steps, preserving its statement and statement dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-algebra-smooth-image.json: statement-only lemma, no Mathlib match. Image factorization in quasi-coherent algebras with exact smooth-test comparison; deliberately no claim about injectivity on all nonflat big-fppf objects.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-cover-section-descent.json: statement-only lemma, no Mathlib match. Global algebra sections are precisely compatible sections on a smooth scheme cover, with algebraic-space relations allowed.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-smooth-permanence.json: statement-only lemma, no Mathlib match. Smooth morphisms of algebraic stacks compose and survive arbitrary base change.
- citations.json: one verbatim statement quotation for every citation of every item step.
- searches.jsonl and search-*.txt: actual search-command log and saved responses for the new nodes. The item searches were also repeated under Q104; its inherited search records and mathematical verdict were retained.

Three new nodes; zero Mathlib leaves. No Lean files, builds, compiles, repository writes or direct git commands.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag and adequate/adequately terminology found no declaration stating this item. General scheme, module-sheaf and image results do not constitute an algebraic-stack attachment.

## Wanted literature

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Lemma 4.1.7 and Sections 3.4/4.1, for lem-sfb-adequate-algebra-pushforward. The intended local literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf is absent. I read the primary HTML at https://arxiv.org/html/1005.2398v3#S4.SS1, including the full non-Noetherian proof. The item is marked proof_origin.by=agent, with this online source and the local-PDF limitation stated.

## Problems found and corrected

The imported node has an empty proof. Alper's first implication is not a license to assume that the original map is a surjection or injective: one must factor through its quasi-coherent image and actually descend the power lifts. I supplied that argument rather than extracting a child identical to the item's injective special case.

Stacks 06WV expressly warns that the embedding of quasi-coherent modules into all big-fppf module sheaves is not exact. Accordingly the image node constructs the image in QCoh, uses right exactness for the quotient surjection, and asserts injectivity only after smooth pullback. Every overlap on which the proof checks injectivity is smooth over the original stack. Nothing assumes injectivity on arbitrary nonflat tests.

Alper's HTML proof has a circular-looking sentence immediately after defining the image: it repeats the final map f_*A -> f_*B as already universally adequate. The argument needed there is f_*A -> f_*im(u), which follows from adequate affineness applied to the surjection A -> im(u). Step 1 writes this map explicitly; no change to the theorem is necessary.

The inherited blueprint ancestry is broken: tools/blueprint_refs.py ancestor reports from.node=None. I retained that exact result and the inherited via list, with the explicit inherited location. I read literature/blueprint/latest (main-20261023-1620), especially sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). The current upper proof is a compactification argument, while this existing node belongs to the recorded lower alteration/moduli prerequisite chain. No unit/chapter record or route was edited. The unit and chapter JSON were read as required.

## Search and source audit

Before creating nodes I searched the whole DAG by statement, title, Stacks tag, and smooth/image/descent keywords, and ran tools/blueprint_refs.py search for adequate, quasi-coherent image, image factorization, smooth presentation, smooth cover, section descent, smooth morphisms, 075V, and quasi-coherent. No imported blueprint node supplies the new stack statements. The general quasi-compact stack atlas already exists as lem-sfb-algebraic-stack-quasicompact-surjection; I cite it instead of creating an atlas node. The finite affine etale refinement also already exists and is cited.

For each of the three new ids I ran leanfinder, loogle, grep and leansearch using the prescribed msearch.py command and tried two semantic phrasings. Saved search outputs were read and the exact queries/results copied to each mathlib_searches. Scheme image factorizations and general sheaf images lack stack quasi-coherent exactness; general site equalizer theorems lack the stack smooth-atlas identification; smooth permanence hits concern schemes. I inspected CategoryTheory/Sites/Subsheaf.lean (imageFactorization), Sites/EqualizerSheafCondition.lean, Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean and AlgebraicGeometry/Morphisms/Smooth.lean to check those limits. Hence no new node is a Mathlib leaf or a one-line specialization. All recorded services returned actual results, not unavailable verdicts disguised as absence.

## Not duplicates

lem-sfb-stack-smooth-permanence vs def-sfb-algebraic-moduli-stack: the existing node defines algebraic stacks, atlases and smoothness over a base; it does not assert composition or arbitrary base change of smooth morphisms between stacks.
lem-sfb-stack-smooth-permanence vs lem-sfb-finite-type-stack-affine-smooth-atlas: the existing node constructs an affine atlas for finite-type stacks, with an extra smoothness refinement; it does not state smooth permanence for arbitrary stack morphisms and base changes.
lem-sfb-stack-algebra-smooth-image vs lem-sfb-finite-schemes-etale-stack-descent: the latter descends finite schemes on a Deligne--Mumford etale atlas; it does not factor arbitrary quasi-coherent algebra maps or compute their images on smooth tests.
lem-sfb-stack-algebra-smooth-image vs lem-sfb-stack-qcqs-algebra-direct-image: the latter gives a pushforward adjunction, test sections, composition and surjection detection; it does not construct quasi-coherent images or assert smooth-pullback injectivity of their inclusions.
lem-sfb-stack-algebra-smooth-image vs lem-sfb-stack-flat-scalar-sections: the latter compares global sections under a flat affine scalar extension; it neither constructs image factorizations nor treats their injectivity under smooth stack maps.
lem-sfb-stack-algebra-smooth-image vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: the latter is restricted to affine groupoids with finite locally free source and target, and its stated clauses do not give images for arbitrary algebraic stacks.
lem-sfb-stack-algebra-smooth-image vs lem-sfb-qcoh-presentation-tensor-equivalence: the latter supplies tensor-compatible descent on a Deligne--Mumford etale presentation, not smooth-test image computation on arbitrary algebraic stacks.
lem-sfb-smooth-cover-section-descent vs lem-sfb-finite-schemes-etale-stack-descent: the latter is finite-scheme descent on a Deligne--Mumford stack; the new statement glues sections of arbitrary quasi-coherent algebras along smooth covers of arbitrary algebraic stacks.
lem-sfb-smooth-cover-section-descent vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: the latter's invariant-section formula assumes affine groupoids with finite locally free arrows; arbitrary smooth covers and algebraic-space relation objects are needed here.
lem-sfb-smooth-cover-section-descent vs lem-sfb-qcoh-presentation-tensor-equivalence: the latter is for Deligne--Mumford stacks and etale atlases and does not state the required global-section equalizer on an arbitrary smooth cover.
lem-sfb-stack-smooth-permanence vs lem-sfb-dm-open-finite-etale-permanence: the latter concerns an open and finite-etale decoration of a smooth finite-type Deligne--Mumford stack; it gives no general smooth-stack composition/base-change assertion.
lem-sfb-stack-smooth-permanence vs lem-sfb-gerbe-smooth-universal-homeomorphism: the latter proves a particular gerbe map smooth and universally homeomorphic; it does not state smooth permanence for arbitrary stack maps.
lem-sfb-stack-smooth-permanence vs lem-sfb-arithmetic-nodal-curve-stack-smooth: the latter concerns the nodal-curve moduli stack and its open smooth-family locus; it is not a permanence lemma for general smooth stack morphisms.

The new nodes are not clauses of the item: image factorization needs no adequacy or morphism f, descent needs no adequate algebra map, and smooth permanence has no algebras. The actual power-exponent construction, injective descent and composition of lifting properties remain in the item's proof. No supporting node is split or carries a proof sketch inside its statement.

## Review by Q104

I read Alper's complete proof of Lemma 4.1.7 (2) => (1) before the Noetherian finite-type discussion, and its Definitions 3.4.1/4.1.1 and the affine-test discussion. The item asks only for universal adequacy, so the stronger adequate-homeomorphism conclusion and its finite-presentation caveat are unnecessary. I did not invoke Noetherian approximation, finite generation, the structure-sheaf-isomorphism part of an adequate moduli space, or affineness of the target.

For the image node I read Stacks stacks-sheaves.tex Tag 06WV, including the nonexactness warning, and stacks-cohomology.tex Tags 076X and 0GQF, including their proofs through smooth groupoid presentations. Right exactness preserves the quotient map; exact smooth pullback computes the image and injectivity on smooth charts. Multiplication and unit descend on that module image, so this is a commutative algebra factorization. The statement avoids the false extension to all big-site monomorphisms. I tested a nonflat pullback of an injective module map: injectivity can fail there, which is why the smooth hypothesis is explicit. For a zero map to the zero algebra and for an identity map, the factorization has the expected image and introduces no finiteness assumptions.

For the descent node I read the full statement of Stacks 076S and its construction via maps from a quasi-coherent module, as well as 06WV(1). Taking the structure module identifies maps with sections and the compatibility condition with equality on the relation algebraic space. Applying this to a disjoint-union smooth atlas permits a family of tests. The resulting assertion is not restricted to finite-flat groupoids or Deligne--Mumford stacks. For an identity cover the equalizer is the original section ring; for the empty cover of the empty stack it is the one-element zero ring. The statement imposes precisely the joint-surjectivity needed for descent.

For the smooth-permanence node I read stacks-morphisms.tex Tags 075V and 075W and their chart definition 075U. It allows arbitrary base change, which is what the test V -> Y requires; the projection to X is smooth because that test is smooth. Relations W_i x_Z W_j remain algebraic spaces and smooth over X by repeated base change and composition. Identity maps, empty schemes and nonseparated targets do not violate either assertion. No diagonal affineness or scheme representability of the relation was introduced.

Step 1 uses exactly the image node's surjection and smooth-test injectivity and the adequately-affine definition's quantifier over all surjective quasi-coherent algebras. The hypothesis that u is adequate passes to the image inclusion by sending any chosen lift through q; it requires no hidden theorem. Applying f's defining property to q gives f_*q, not the original desired composite.

Step 2 uses the fibre-product node to know X x_Y V is algebraic, the stack-qcqs definition for quasi-compactness after an affine test, and lem-sfb-algebraic-stack-quasicompact-surjection for a quasi-compact smooth scheme atlas. I opened that existing node: unlike the finite-type atlas lemma, its statement imposes neither finite type nor Deligne--Mumford. Smooth permanence makes the composite atlas a legitimate smooth test of X, so adequacy of the original image inclusion applies to its section b. This step does not assert adequate affineness of the base-changed f, avoiding a circular base-change theorem.

Step 3 uses the finite-affine etale-refinement statement with its own base X=U, W=id_U, and compactness provided by step 2. Its arrows belong to the original covering sieve and therefore factor through original lifting tests. I wrote the exponent calculation explicitly: N is the finite product of the n_i, and raising c_i to N/n_i gives the common image b^N. No uniform exponent across all sections, all tests or all algebras is claimed. The empty family uses N=1. Smooth permanence and the smooth-definition statement (etale implies smooth) justify every scheme test and relation space used later.

Step 4 uses the image node's stated injectivity for smooth algebraic-stack sources, including the relation algebraic spaces; it does not use a mere definition of an image or all-big-site exactness. Both overlap images are the same b^N. The descent node then gives the actual unique global section, and its equality-detection clause checks its image. The direct-image test formula is explicitly in def-sfb-adequately-affine-morphism, so this really proves the claimed local lifting statement on Y, with arbitrary smooth tests handled by affine open covering.

Step 5 is the elementary composition of two explicit power liftings: the exponent is N_i M_ij and the refined covering is etale by the site's covering-composition axiom, read in def-weil-pbc-sites-and-cohomology. It uses no uncited theorem that universally adequate morphisms compose. Neither f_*q nor f_*j is presumed sectionwise surjective. I copied a verbatim supporting statement into citations.json for every uses entry and checked the hypotheses of each citation. Every proof step is below 900 characters, so there is no step over the 2000-character review threshold concealing an additional lemma.

I checked delivery-errors B through E against the files: statements introduce all objects and notions, use TeX once, carry source tags and exact performed searches, and new nodes have no proofs. Every non-elementary fact used has a matching cited statement; the quotient, finite cover and smoothness hypotheses are verified where used; the proof does not move its own assertion into a new node. Existing stronger/generic candidates were read and reused where they apply. Same-tag candidates are distinguished above. No statement dispute or theorem weakening was necessary.

## Unfinished work

No mathematical part of this one-level split remains unfinished. The three supporting lemmas intentionally remain statement-only for later stage-1 workers. Server validation and the required direct delivery follow this report.
