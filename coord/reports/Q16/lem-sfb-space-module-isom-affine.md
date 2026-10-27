## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-module-isom-affine.json`: statement, split; no Mathlib match. Six proof steps, using existing nodes only. The statement and statement dependencies are unchanged. The original fields and searches are retained and five actual searches from this run are appended.
- `citations.json`: 17 step/node entries, each with an exact substring of the current cited statement.
- New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for module Isom, representability and proper-support language. There is no declaration giving this relative module Isom representability theorem. Scheme isomorphism criteria and module-sheaf isomorphisms do not state it.

## WANTED

None. All sources used are available locally.

## What was wrong

The imported item had no proof. Its statement agrees with Stacks 08K9 and is unchanged. Its proper-support convention agrees with the already reviewed Hom theorem, so the four applications use identical conventions.

## Source error

In `literature/stacks-project/quot.tex`, Tag 08K9 (`proposition-isom`), the displayed map from `Hom(G,F) x Hom(F,G)` to `Hom(F,F) x Hom(G,G)` has its compositions in the wrong order: for `u:F -> G`, `u':G -> F`, the first printed component `u o u'` acts on G, not F. The corrected map is `(u',u) -> (u' o u,u o u')`. This is a type error already visible with F=k and G=k^2, even before requiring inverses. Step 3 explicitly corrects the order. The proposition itself is true and needs no statement dispute or weakening.

## Unfinished

Nothing in this stage-1 split. The existing cited nodes retain their own statuses and are not modified. No Lean was written or compiled.

## Not duplicates

No new nodes. The existing `lem-sfb-space-module-hom-affine` is exactly the 08K6 input, so I cite it instead of making a second Hom node. The other 08K9 hits are the parent Picard-sheaf representability node and `lem-sfb-space-coherent-diagonal`, neither of which states this item. The finite-locally-free relative Hom-space node concerns maps of spaces from a finite locally free source, not homomorphisms of quasi-coherent modules. Whole-blueprint searches for Isom, Isom functor, Hom functor, module Hom, finitely presented modules and sections of separated maps found no second blueprint formulation of the present theorem; `same_as` stays empty. The ancestry query reports a null blueprint node for the inherited created-node chain; I retained its existing detailed place and via chain. I read the current `latest/` direct-image proof to preserve this prerequisite's recorded route. This item is not the unit key node, so no unit realization fields are changed.

## Review by Q16

I read Situation 08JT and Proposition 08K6, then the statement and complete proof of 08K9 in `quot.tex`. I also read the relevant source statements in `spaces-morphisms.tex`: the section lemma 03KP, affine definition and 03WG/03WH/03WI, finite-presentation composition and base change 03XQ/03XR, and relative local finite presentation 05WT. For the canonical transitions I read `sites-modules.tex` 03D8; for products I read `spaces.tex` 02X2. There are no new nodes needing separate source verification.

For Step 1 I opened the entire statement of `lem-sfb-space-module-hom-affine`. It represents Hom for arbitrary quasi-coherent source and finitely presented flat proper-support target and gives finite presentation when the source is finitely presented. Both M and N meet all those hypotheses in each of the four ordered pairs. In particular I never infer flatness of the structural morphism f from flatness of these modules. The Hom node's all-scheme-test naturality is exactly what Step 3 uses.

For Steps 2 and 5 I opened the statements of the four cited nodes: `lem-trf-space-fibre-products-etale-covers` supplies existence and the universal property, `lem-sfb-space-affine-locality` supplies affine base change and composition, `lem-sfb-space-flat-proper-fp-locality` separately supplies finite-presentation base change, and `lem-sfb-space-separated-fp-composition` supplies finite-presentation composition. The flat/proper node explicitly says that the three assertions are separate, so using its fp clause does not require the Hom spaces or the identity section to be flat or proper. Each projection is identified with its actual base change before a permanence result is applied.

In Step 3 the pullback node actually specifies a functor. The tensor-composition node specifies a natural comparison, so preservation of compositions and identities, followed by conjugation with that comparison, proves the required naturality. The algebraic-space definition explicitly says that morphisms are natural transformations: there is no extra representability or Yoneda assertion smuggled in. I corrected the printed component order here.

In Step 4 the closedness of a section is proved directly on scheme tests of the relative diagonal, rather than borrowed from a scheme-only section theorem applied to spaces. The equation is equality of maps, not mere containment of point images. The two maps identifying the diagonal pullback with B x_Q T are written and are inverse using q sigma = id. The affine-locality node gives separatedness of q, hence a representable closed diagonal, and gives qc and separatedness of sigma after its affineness is established. The closed-immersion definition gives precisely the scheme affine description needed on tests. I read the relative-lfp node: its assumption is only that the composite is lfp and the second map is lft. Here the composite is the identity of B and the second map q is fp, hence lft. I used no Noetherian hypothesis and did not assume every closed immersion is fp. The identity section acquires lfp from 05WT and qcqs from affineness, which is why full fp follows.

Step 6 is the elementary two-sided-inverse calculation, not a second geometric lemma. I wrote uniqueness as v=v(uw)=(vu)w=w and checked the equations survive arbitrary tensor pullback, including nonflat base changes. This proves that the representing bijection uses exactly the transition maps in the item's statement. The two elementary steps use only functoriality, naturality and these displayed equalities; neither hides a separate non-elementary assertion. No step exceeds 2000 characters (the longest has 1305), and the section argument remains short and explicit.

I tested X empty and M=N=0: all Hom functors and Isom give B, including the zero-module identity. Over Spec k with X=Spec k and M=N=k^r, the fibre-product equations are the two inverse matrix equations; they give GL_r, with GL_0=Spec k and GL_1=Spec k[t,t^-1], as required. For M=k^r and N=k^s with r unequal to s the represented functor is empty; it is still affine and fp. With X=B and M=N=O_B the same construction works over arbitrary non-Noetherian rings. I also checked a nonflat test base change: tensor pullback still carries a given isomorphism and its inverse to inverse maps, so naturality never uses exactness of tensor.

Against delivery-errors B--E: no new statement-only nodes or undefined new notions were introduced, no source lemma is used through an unstated proof detail, and no clause is merely moved to another node. Each non-elementary input is a cited statement I opened, proof_deps is their exact union, and the only off-unit statement is generic space fibre-product existence, declared as a tool use in split_report. All 17 quotes were checked literally against those statements. The source correction is disclosed above; no item hypothesis was added or conclusion weakened. Searches were run with msearch.py and their returned hits read: they concern scheme isomorphisms, ordinary affine spaces, finite-presentation morphisms and local module presentations, not a relative module Isom representing space. The two LeanFinder phrasings and the Loogle, grep and LeanSearch queries are present verbatim in searches.jsonl and in the appended node records.
