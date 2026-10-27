## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-group-space-square-zero-difference-additive.json (statement, split, no Mathlib match), citations.json and this report. The search command produced searches.jsonl. There are 0 new nodes and 0 Mathlib leaves.

Attachments: none. The exact blueprint tag has no declaration in lean/WeilConjectures. Concept searches located GroupScheme/IdentityTangentAddition.lean:45 (identity_tangent_transport_addition), IdentityTangentOperations.lean:73, and GroupScheme/Lie/InfPointsEquiv.lean (toLie/lieEquiv). I read their signatures and constructions: the first two concern schemes over a field and dual-number tangent vectors; the latter concerns S[epsilon] with coefficient O_S for group schemes. They do not cover arbitrary square-zero ideals and group algebraic spaces, so none is an attachment.

WANTED: none. All sources used are present.

The original statement is correct and unchanged. Its proof was empty. The statement dependencies are unchanged: schemes, algebraic spaces, first-order thickenings and module sheaves; the statement itself spells out group objects, the differential universal property and tensor pullback. I reused lem-sfb-space-square-zero-lift-linearization rather than creating a product-differential theorem or restating a clause in a child node. Nothing remains unfinished within this one-level split.

## Sources and route

I read literature/stacks-project/groupoids.tex, Tag 0BF5, label lemma-group-scheme-addition-tangent-vectors, lines 687–712: a linear multiplication differential is addition because its restrictions to the two axes are identities. I read spaces-more-morphisms.tex, Tags 0618/0619/04D0, labels lemma-difference-derivation, equation-D, lemma-action-by-derivations, lines 3689–3780. The latter gives the actual difference derivation and the inverse obtained by adding it to a fixed ring map. These tags apply with trivial target thickening; the conormal compatibility hypothesis is then vacuous. The extension of 0BF5 to arbitrary ideals and spaces is explicitly marked agent-written, with the generalized lift bijection supplied by an existing cited node rather than assumed.

The existing lemma lem-sfb-space-square-zero-lift-linearization has a reviewed statement giving exactly that pointed bijection, its formula b^sharp-a^sharp, and linear postcomposition for arbitrary S-morphisms of algebraic spaces. I read its entire statement and proof. Its generic site/descent inputs are below the cited node, not additional assumptions of this item. I also read the four statement-definition nodes and checked that they define the notions used.

Read the chapter and recorded sk-thm-sf-ctf-stability unit, and the newest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. This is an infinitesimal prerequisite of the existing alteration/relative-Picard branch, not a replacement for any unit step. blueprint_refs.py ancestor returns None; the inherited blueprint provenance is preserved. Searches of the whole imported blueprint for square-zero, tangent, 0618, 0BF5, and of latest blueprint text for difference/group-square-zero notions yielded no equivalent item. The tangent hits concern fields or other geometric settings. The single proof dependency belongs to the same unit, so no off-unit tool declaration is needed. No SGA source is used.

## Searches and existing-node comparison

DAG searches for 0618, 04D0, 0BF5, square-zero groups and difference derivations locate lem-sfb-space-square-zero-lift-linearization and lem-sfb-group-space-square-zero-kernel-module. The former is the needed general tool and is cited. The latter gives a stronger kernel-module assertion with the same product/unit argument in its proof; using its statement would merely bypass the item. I instead supply that short argument using only the general linearization. Its dependency closure does not contain this item, checked across both statement and proof dependencies; there is no circular use of the kernel-module assertion or of the diagonalizable-group parent.

Seven new searches ran through the required msearch.py command, and their exact query texts and returned names are retained in mathlib_searches and searches.jsonl. Both LeanFinder phrasings returned ring derivation/lift constructions, Jacobi–Zariski formulas or manifold derivations. Both LeanSearch phrasings returned manifold tangent maps, ordinary derivation additivity, or Lie derivations. Loogle KaehlerDifferential, Derivation returned the ring universal-property equivalence. The two grep patterns, across Mathlib and AlgebraicGeometry/Group respectively, returned zero hits. I read RingTheory/Derivation/ToSquareZero.lean:115–126 and RingTheory/Kaehler/Basic.lean:327–332: neither has algebraic spaces, geometric multiplication, or arbitrary group objects in the asserted statement. The earlier inherited grep-only search is retained as historical material and supplemented by these actual logged searches.

## New nodes

None. Pairing maps into a product and showing the inverse of an injective linear bijection preserves operations are elementary steps from the cited bijections and naturality, not separate nodes. The unit-identity computation is written in the item, not moved into a child.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs requiring comparison.

## Review by Q45

I checked the actual item against 0BF5 and the deformation-map tags named above. The source 0BF5 alone covers field tangent vectors, so I did not claim that it already proves the generalization: the agent proof supplies the product identification from the stronger, existing lift-linearization statement. The four item hypotheses are retained: an arbitrary base scheme, group algebraic space, affine S-thickening and square-zero ideal; no finiteness, flatness, separation, commutativity, smoothness or characteristic hypothesis was inserted.

Step 1 uses lem-sfb-space-square-zero-lift-linearization with X=G and a=e_T. Its statement explicitly identifies the lift set with the Hom module, sends a to zero, and says its derivation is b^sharp-a^sharp; these are exactly the assertions taken. The ideal is the given associated sheaf, and multiplication by A factors through A/I because the difference of lifts of a scalar lies in I and I*I=0. This also checks the sign of the difference coordinate.

Step 2 uses the same node with X=P=G times_S G and a=(e_T,e_T). The product is already part of the group datum. Its statement applies to all algebraic spaces and to both projection morphisms; thus their induced maps are linear, with the naturality formula needed to compare q with pairing lifts. A map into P is uniquely its two S-components, and its reduction is p_0 exactly when both components reduce to e_0. That gives bijectivity, not merely injectivity, of q. The elementary inverse-linearity argument is explicit: apply injective q to both candidates. This step does not assume a product theorem for cotangent sheaves.

Step 3 again uses that node's linearity and naturality, now for multiplication m, an S-morphism even when the group is not commutative. The reference lift has image m(e_T,e_T)=e_T and reduced image e_0, so source and target Hom modules are the ones already constructed. The displayed formula for delta(xy) follows by applying the stated naturality to the paired lift. Surjectivity of delta permits arbitrary v in the axis computations; both unit laws then give F(v,0)=v=F(0,v). Additivity of this linear map, evaluated on (v,0)+(0,w), proves the conclusion. The elementary marker covers only this explicit linear-algebra calculation on top of the cited geometric input. Each step cites the same node; citations.json quotes its actual statement, with no quotation from its proof substituted for a theorem.

I tested I=0 (the kernel and Hom module are both trivial), the zero ring/empty affine test scheme, the trivial group, G_a (coordinates add), G_m ((1+i)(1+j)=1+i+j because ij=0), a nonsmooth characteristic-p example mu_p (the same computation needs no division), and noncommutative GL_n (the matrix cross term has entries in I^2). These cases confirm that no hidden smoothness, characteristic or commutativity assumption enters the argument. No additional statement was created requiring a separate small-case test. All three proof steps are under 2000 characters (574, 674, 582), total 1830; none hides an independent non-elementary lemma. The B–E checks required no statement correction: I retained the original statement and all provenance fields, wrote the argument explicitly, used the existing general lemma, and verified its hypotheses and conclusions at each use.

## Validation

The first dry run rejected two citation excerpts as shorter than its 40-character minimum. I replaced them with full verbatim statement passages including the bijection, actual difference formula and naturality, and reran the required server dry run. No Lean, Lake, compiler, local preflight, or repository git command was run.
