# Stage-1 delivery: lem-sfb-space-affine-pullback-perfect-detection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-pullback-perfect-detection.json: item, statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-derived-pushforward-conservative.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim cited statements indexed by proof step.

## Attachments

None. Searched the blueprint tag and perfect/affine/generator/detection concepts throughout lean/WeilConjectures. The closed schemeDerivedDirectImage_isIso_of_affine and perfect_generator_pullback declarations concern schemes with Zariski structure sheaves; they do not cover arbitrary algebraic spaces and their small etale structure sheaves.

## WANTED

None. All sources used are obtained Stacks TeX.

## Corrections and scope

The item was statement-only, not previously split in the sandbox. Its statement is correct and unchanged. The local chapter/unit records were read alongside the current latest blueprint section and direct-images proof. This is an auxiliary coherent-duality tool down the already recorded alteration route, not a replacement of any unit-level step. The existing blueprint ancestor command returns None because the inherited created.item chain is broken; its null ancestor and detailed inherited place are preserved, and the new node prepends this item to the existing via list. No chapter/unit record was changed.

Searches were run only through msearch.py and read before recording. The item retained its predecessor's search records and gained this session's actual searches. Two semantic phrasings for affine conservativity yielded ordinary scheme geometry, localization and underived module functors. Loogle and grep found no conservativity match. For the item, searches yielded affine scheme pullback properties, shift comparisons and Kan-extension Hom equivalences, none of which states the algebraic-space theorem. The actual Scheme.Modules source was read at lines 165–200: its pushforward and adjunction are underived, and the faithful/full pushforward instances require an open immersion. The Kan-extension isIso_homEquiv results at lines 192 and 388 concern universal extensions, not detection by perfect complexes. No new Mathlib leaf is claimed.

## Not duplicates

lem-sfb-space-affine-derived-pushforward-conservative vs lem-sc-affine-derived-pushforward-conservative: the existing Tag 08I8 theorem concerns schemes and Zariski module derived categories; the new Tag 08II theorem concerns arbitrary algebraic spaces with their small etale structure sheaves.
lem-sfb-space-affine-derived-pushforward-conservative vs lem-pc-perfect-generator-pullback: the existing theorem concerns perfect generators on schemes; the new theorem has no generator or perfectness hypothesis and asserts conservativity of algebraic-space derived pushforward.
lem-sfb-space-affine-derived-pushforward-conservative vs lem-sfb-flat-space-derived-pushforward-base-change: the latter is a flat base-change theorem (08IR), mentioning 08II in background; the new result assumes affine and permits nonflat morphisms, and asserts reflection of isomorphisms rather than base change.
lem-sfb-space-affine-derived-pushforward-conservative vs lem-sfb-space-derived-etale-chart-calculus: chart calculus gives the derived adjunction and etale restriction comparisons but no affine conservativity.
lem-sfb-space-affine-derived-pushforward-conservative vs lem-sfb-space-affine-pullback-perfect-detection: the new lemma has no Hom-test or perfect-complex assertion; the item's cone calculation, generator theorem and adjunction are needed to turn the Hom hypothesis into the premise of affine conservativity.

lem-sfb-space-affine-derived-pushforward-conservative vs lem-sfb-space-derived-pushforward-coproducts: both involve 08FA for preservation of quasi-coherent cohomology, but the existing node asserts coproduct preservation for qcqs maps and has no isomorphism-reflection clause; the new node asserts the affine conservativity theorem 08II, which does not follow from coproduct preservation.

## Review by Q02

I read spaces-perfect.tex theorem-bondal-van-den-Bergh (09IY), remark-pullback-generator (0E4R), and lemma-affine-morphism (08II), including their proofs. The generator theorem is precisely zero-detection against all shifts, not a claim that the structure sheaf alone generates a general space. The affine lemma works on unbounded quasi-coherent categories by etale-local reduction to affine schemes; it does not need flatness, properness, finite type or Noetherian hypotheses. The new node includes the quasi-coherent codomain in that source's displayed functor, with 08FA named for this well-definedness. It has no proof or proof dependencies.

In step 1 I opened the weak-generator node: its qcqs hypotheses hold for Z, and it returns a perfect P with Hom(P[n],E)=0 detecting E=0. I opened the abstract-derived-category definition: it explicitly supplies the cone triangulation. I opened the perfect-localizing-generation statement: it explicitly includes closure of D_QCoh under distinguished-triangle cones, so the argument uses a statement clause, not its proof or a definition of quasi-coherence. This puts K in the required full subcategory.

In step 2 I checked the full Hom-into-triangle exactness statement. Its zero-composite assertion and exactness after rotations give both lifting steps. I wrote out bt=0 using injectivity at j=1, then t=as and s=vr using exactness and surjectivity at j=0, followed by av=0. Testing the original hypothesis on P[n] is legitimate because shifting a finite-projective bounded representative remains one. This avoids presuming a nontrivial shift comparison for derived pullback. The step is elementary relative to the explicitly cited exactness theorem.

In step 3 I opened the algebraic-space derived-etale-chart-calculus node: its statement explicitly says Lu* is left adjoint to Ru* on the unbounded module derived categories. It is applicable to h, whereas the ringed-spaces-only derived-adjoint node would not by itself apply to ringed topoi. Applying the new lemma gives that Rh*K is quasi-coherent. The already quoted generator criterion therefore applies and proves Rh*K zero. The new node really states isomorphism reflection, so applying it to the zero endomorphism of K is valid; an invertible zero endomorphism forces identity zero. No unproved comparison of rings, sites or coefficient categories is made here.

In step 4 the same exactness node and rotated triangle give bijectivity of Hom(W,v) once K and K[-1] are zero. The inverse is then explicitly produced using W=D and verified with injectivity at W=C. This elementary argument avoids hiding a separate zero-cone isomorphism lemma. Every cited statement was copied verbatim into citations.json. No step exceeds 2000 characters.

I checked delivery-errors B through E point by point: self-contained TeX statements with all notions either defined inline or cited, correct tags and labels, no new node containing a proof sketch, honest logged searches, no Mathlib overclaim, no duplicate or new restatement of the item's Hom-test, and no citation of a node's proof instead of its statement. The graph directions are toward generator, exactness, adjunction and affine-conservativity prerequisites; the new lemma has no proof dependencies and cannot create a proof cycle. I checked the empty space, identity h, zero C/D, an affine closed immersion with nonflat quotient ring, and unbounded complexes. In particular, h need not be surjective: affine pushforward is conservative on its source even when its image is proper. The all-integer hypothesis is used through all shifts P[n]; it has not been replaced by degree-zero tests for P alone. No source error or statement dispute was found.

## Unfinished

No work required for this stage-1 split remains, apart from the mandated dry-run and push. The one new prerequisite is intentionally statement-only for a later stage-1 worker.
