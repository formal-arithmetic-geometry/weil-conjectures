# Stage-1 report: lem-trf-finite-cech-augmentation-modules

## 1. Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-cech-augmentation-modules.json: existing statement, now split into seven proof steps; no Mathlib match for the item.
- citations.json: one verbatim statement quotation per cited node per step.
- searches.jsonl: actual search-command log, retained with the delivery workspace.
- report.md: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses thirteen existing dependency nodes. Its definition dependencies additionally name the constant ring sheaf and the existing inverse/direct-image notions. These only spell out the existing statement's notation; no mathematical hypothesis or conclusion changed. The unit and chapter files are unchanged.

## 2. Attachments

None for the item. I searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint tag and for finite, Cech/Čech and augmentation terminology. The topological open-cover declarations in Topology/Sheaves/CechCriterion.lean and CechCohomology.lean do not state this finite-surjective small-etale assertion. SixFunctors/Finite/Stalk.lean does state an ingredient: its isIso_piLift_stalkRestrict and stalkIsoPi give precisely the already existing finite-stalk restriction node. This ingredient does not supply the whole augmentation or its naturality.

## 3. WANTED

None. All literature needed is present locally. No literature was downloaded.

## 4. Corrections and route

The original node was an unsplit child of lem-trf-finite-base-cech-hypercohomology with a correct statement and no proof. I expanded its source, Stacks Tag 09Z2 (etale-cohomology.tex, lemma-cohomological-descent-finite), through the exact-augmentation part only. The source is stated for abelian sheaves; its inverse/direct-image units are module-linear for constant coefficients, and faithful exact coefficient forgetting gives precisely the module assertion. Neither torsion, invertibility of the coefficient characteristic, Noetherianity, flatness nor etaleness of p is needed or introduced.

The inherited blueprint ancestor is lem-trf-local-term-locality. I read its current main-20261015 proof and the sk-i-curve-zero and sec-trace-formula records. The present node is the finite-cover augmentation input on the existing nearby-cycle specialization/descent branch; the immediate parent uses it in step 1. It does not assert a new proof of the local-term unit. I retained the inherited precise ancestry and via list and searched blueprint_refs for Čech, augmentation, finite surjective, finite stalk and cohomological descent. The open-cover Cech spectral-sequence blueprint node and the hypercover free-chain nodes are different statements. No blueprint node found states this exact finite-surjective pushforward augmentation.

Generic tools from other units are declared in split_report.tool_uses. These supply finite-map stability, units, stalk comparisons and coefficient forgetting. They do not replace a unit-level argument.

The splitting does not create a second node for the nonempty-set contraction or for reflection of zero homology: both are written out in the proof. All non-elementary steps are shorter than 2000 characters. The three elementary steps are the displayed contraction, coefficient naturality by natural transformations, and the cover-map construction checked with the explicit composition-unit equation.

## 5. Unfinished work

None for this stage-1 split. No Lean was written, opened through a building service, or compiled. The independent maintainer review remains the project's normal review of the pushed delivery.

## Not duplicates

No new nodes. Existing nodes were used for each non-elementary input, including the restriction components of the finite-stalk isomorphism rather than a new module-valued duplicate of it.

## Review by Q15

I read the complete exactness proof of Tag 09Z2, not just its statement. It builds the cofaces by adjunction, reduces to geometric stalks, and identifies the alternating differential with coordinate deletion on the nonempty finite geometric fibre. I also read etale-cohomology.tex Tag 03QP (proposition-finite-higher-direct-image-zero, part 1 and proof), Tag 03Q1 (lemma-stalk-pullback, part 3 and its germ construction), Tag 03PU (theorem-exactness-stalks), Tag 0A3H (lemma-sections-upstairs, last paragraph), and the last paragraph of Tag 09ZE cited for finite geometric-point lifting. For the coefficient passage I read sites-modules.tex Tags 03DA and 03DB, and for composition sites.tex Tag 03CB; finiteness uses morphisms.tex Tags 01WK and 01WL. There are no new-node sources to audit and no forbidden SGA route.

Step 1 cites the complete constant-module inverse-image theorem, which supplies module structures, compatibility with abelian inverse image and the actual adjunction units, and the module direct-image theorem, which supplies the corresponding underlying-abelian direct image. I opened both statements. The composition-and-units node supplies the section equations and associativity; the algebraic-structures node says the inverse images and units agree after forgetting to sets. Applying those same functors to addition and each constant scalar justifies use of the set composition equation in module sheaves. The two-coordinate deletion pairing proves the complex identity. No claim that a finite map is an etale cover is made.

Step 2 uses the finite/base-change/composition node only for its explicit finite-morphism clauses. Finite geometric-point lifting assumes a finite morphism and algebraically closed Omega, both in force; surjectivity supplies a point over y and hence nonemptiness. The finite-stalk restriction node states finiteness of the indexing set and that its actual germ restrictions form an isomorphism. I use that formula with p_q, which was proved finite, and with the underlying abelian sheaf of p_q inverse F. The inverse-image stalk-germ node states the natural additive isomorphism to F at the image geometric point. The tuples are identified by the fibre-product universal property. All geometric points use the same field Omega, with no unjustified identification after an arbitrary field extension.

In step 3 I checked the maps as well as the stalk groups. The restriction-formula statement names exactly the germ maps used. The inverse-image germ statement identifies the augmentation with the diagonal. The geometric-fibre constant-pullback statement explicitly includes naturality in every Omega-morphism, so it really does identify the coefficient maps induced by coordinate projections with the identity of M. Its underlying set comparison respects the abelian operations by the algebraic-structures result; this is enough because exactness will be tested after forgetting coefficients. No comparison is borrowed merely from the proof of another node.

Step 4 writes the prepend-e_* contraction and the cancellation signs, including q=0 and the augmented term. In degree zero, h^1 d^0(a)(e)=a(e)-a(e_*), so adding the constant cochain epsilon h^0(a) returns a. In higher degrees the terms deleting the ith original entry occur with opposite signs. At the augmentation h^0 epsilon=id proves injectivity. These are direct equalities of functions, not an unrecorded homological-algebra theorem.

Step 5 cites exactness of abelian geometric stalks and the existing sets-valued criterion which detects isomorphisms. Thus applying it to 0 to a homology sheaf is legitimate, after stalk exactness has identified its zero stalks. The module-forgetting node says faithful and exact and explicitly preserves kernels and cokernels. Its faithfulness detects a zero identity map, so it reflects zero homology; I have written that short argument instead of claiming that mere exactness automatically reflects exactness.

Steps 6 and 7 use the units and their stated naturality/composition equations. I checked the variance: a map Z' to Z over the fixed base Y gives C_p(F) to C_p'(F). The identity component on F commutes with augmentation because p a=p'. Coordinate deletion commutes with applying a in each coordinate, giving exactly the square used in the composition-unit equation. The same equation checks successive cover maps. None of these naturality assertions depends on choosing compatible contraction points.

For edge cases I checked the zero coefficient ring and zero sheaf (all terms zero), Y empty (no geometric points, with its unique zero module sheaf), and p an isomorphism (E singleton, with d^0=0, d^1=id and subsequent differentials alternating). For a two-point fibre the degree-zero differential is a(e_1)-a(e_0), with kernel the constant functions, as required. If p is not surjective and F has a nonzero stalk outside its image, the augmentation there is M to 0 and fails injectivity; this confirms exactly where the actual hypothesis is used. Ramification and nilpotents cause no problem because the cited finite-stalk theorem is for all finite morphisms, not just finite etale ones.

The logged Mathlib searches were all actually executed through msearch.py. I read every returned hit: generic augmented nerves do not assert exactness, Mayer-Vietoris statements concern a different covering diagram, and module-category declarations do not give finite-cover descent. A second semantic wording and second case-sensitive Loogle pattern also found no match. Previous search records inherited from the repository are preserved; newly appended records agree with this workspace's log.

The check against delivery-errors B--E found no new-node formatting, duplicate, or statement-only-node issue. The proof has no cycle introduced through a new node, uses no absent result hidden under a tag, and records every step's actual cited statements in citations.json. The statement was not disputed or weakened. Before packaging, the server review_split check returned PASS with 0 new nodes.
