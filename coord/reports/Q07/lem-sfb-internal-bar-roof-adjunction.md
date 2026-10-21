## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-roof-adjunction.json` (statement, split; no Mathlib match), `citations.json`, and this report. The sandbox also retains the search log, original statement, and generation script. No repository, launcher, Lean file, or compiler was changed or run.

## New nodes

None. All 20 non-elementary inputs already have DAG nodes. There are no new Mathlib leaves.

## Attachments

None. Searches by the exact blueprint tag and by internal bar/roof terminology under `lean/WeilConjectures` found no declaration stating the item. The discrete representation bar and continuous-cochain declarations do not state it.

## WANTED

WANTED: an exact internal-category reference for homogeneous bar cocycle roofs, compatible derived internal-Hom totals and their canonical inflation-adjunction comparison, for lem-sfb-internal-bar-roof-adjunction. The imported source explicitly requests this reference. The proof is marked agent-written. Its general category-theoretic ingredients are existing cited nodes, with Stacks sources available locally; no SGA is used.

## Statement corrected

STATEMENT-DISPUTED: the imported degree-one sign is incompatible with its fixed positive inhomogeneous differential, shift convention and canonical derived adjunction. It also attributes `j_N` and a *normalized compatible total* to a node whose statement only asserts a natural totalization isomorphism and degree-zero invariant normalization. The delivery defines the actual compatible model and its maps in the statement, proves their claimed properties, and retains every coefficient category and universe.

In the fixed total differential d_h + (-1)^p d_I, the Hom-complex differential on a bidegree (p,r) family is d_I x + (-1)^(p+r+1) x partial. Its chain identification with the bar total must multiply by t(p,r)=(-1)^(pr+p(p+1)/2). This forces s_q=t(q,0)=(-1)^(q(q+1)/2), in particular s_1=-1, not +1. Step 12 proves equality of the specified derived arrows, rather than only cohomology classes after evaluation.

The degree-one obstruction can be seen without a general sign formula. Choose an equivariant extension 0 -> N -> E -> A -> 0 and extend N -> I^0 to v:E -> I^0 by injectivity. For a lift ell:P_0 -> E and f with i f=ell partial, write d_I v=h p. In the bar total, d(v ell)=a f+h e. Thus j c_f=-b h, whereas the canonical derived transpose of the roof is h. For a concrete nonzero example take the constant condensed ring A=F_3, G=C_3, N=A with trivial action, and E=A^2 with g(x,y)=(x+a(g)y,y), a:C_3 -> (F_3,+) the identity. The lift ell[g]=(a(g),1) gives f[g_0,g_1]=a(g_1)-a(g_0). The extension does not split equivariantly: a putative splitting evaluated at the point would send 1 to (x,1), but a generator moves it to (x+1,1). Its derived extension morphism is consequently nonzero and cannot equal its negative in characteristic 3. Hence the imported s_1=1 is a substantive false normalization, not merely an undetectable sign on zero classes.

Stacks Tag 0152 and the project's derived-category definition use the cone boundary -pr. The explicit map P -> C(i) with components (f,ell) gives rho_f=pr/v and therefore delta=-rho_f. The corrected item states both the canonical boundary delta and the alternative roof normalization delta^+=-delta. It does not silently rename the canonical triangle boundary. Also clarified d_P^0=0 (there is no partial_0 in the unaugmented resolution complex).

Citer audit: the sole current citer is `lem-sfb-internal-bar-ordered-cup`. Its conclusion still holds, including epsilon_1=1, but its steps 4-6 need repair. In step 4 its x_a is -delta, so Phi_1(x_a)=-[a] with the positive connecting-class convention of the restriction-calculus node. Step 5 consequently gets the additional product factor (-1)^q. Step 6 then uses epsilon_q=s_q T_q (-1)^q. At q=0,1 this equals 1 as required. The citer is not edited, as required by the brief; this explicit correction is reported for the maintainer. No target statement is changed.

## Sources and blueprint

Read the chapter record `dag/chapters/sec-six-functors-basics.json`, the assigned unit record `dag/units/sk-thm-sf-ctf-stability.json`, SETUP's three-level rule, and the current main-20261015 paragraph (3) of `sk-thm-sf-ctf-stability-direct-images.proof.md`. That paragraph gives the open-direct-image route, not an explicit proof of this internal normalization. The split expands that input without changing the unit or chapter route. `blueprint_refs.py ancestor` returns None for the inherited created-item chain; the existing null ancestor and full via-chain are retained, with the exact paragraph/place filled. `blueprint_refs.py search 'bar cocycle'` found zero imported matches; the broader bar search was read and found no exact replacement. The item already has same_as=[] and is not an imported blueprint node.

Read local `literature/stacks-project/derived.tex`: Tag 070I (`lemma-K-injective`), Tag 070J (`lemma-bounded-below-injectives-K-injective`), and Tag 0152 (`lemma-derived-canonical-delta-functor`, including its -p q^-1 formula). Read `sites-modules.tex` Tag 03EV (`lemma-j-shriek-flat`, both clauses and its proof); the free-module sheafification construction in `lemma-universal-module` was checked as background. No new node uses an inferred Stacks tag. Opened the statements of every cited DAG node. The internal/sheaf module equivalence and exact tensor comparison are cited explicitly, rather than silently applying sheaf-module results to unrelated internal objects.

## Mathlib searches

Ran the prescribed msearch command with LeanFinder twice, Loogle, grep, and LeanSearch, recording the exact queries and actual digest records in mathlib_searches and searches.jsonl. Every service answered. Read the actual barResolution.extIso declaration at Mathlib/RepresentationTheory/Homological/Resolution.lean:438-441 and groupCohomologyIsoExt at GroupCohomology/Basic.lean:205-208: their category is discrete Rep and the bar is a projective resolution. They cannot specialize in one line to internal modules over a varying condensed ring. Semantic hits on injective-resolution Ext cocycles give ingredients, not the internal bar comparison. Also read the existing K-injective leaf declarations at HomotopyCategory/KInjective.lean:133-135 and DerivedCategory/KInjective.lean:41-46; these are reused through their existing nodes. No Mathlib searches are invented. Imported earlier search records are retained.

## Not duplicates

No nodes created. Existing flat free-parameter sheaf, K-injective comparison, first-quadrant comparison and canonical derived-adjunction nodes are cited directly. The new proof has no extracted assertion that restates the item or one of its clauses.

## Review by Q07

I checked the item against the current blueprint paragraph, its three existing internal-bar/restriction inputs, and the actual Stacks sign convention. The missing exact internal reference remains WANTED, with the full agent argument written into the item. I corrected the false degree-one sign and the ambiguity about the totalization maps, rather than assuming either as a cited theorem. There are no new nodes to audit under B1-B9. The item is self-contained about its ring, group, categories, resolution, totals and maps and uses ordinary internal module categories throughout.

Step 1 takes Grothendieck abelianness, exact forgetting and the normalized inflation/invariants adjunction from the restriction-calculus statement; enough injectives from the existing enough-injectives leaf; resolution meaning and extension property from def-sp-injective-resolutions; and all-complex K-injective existence from the Grothendieck K-injective node. Its inductive cokernel construction is written out. These give the existence and unbounded-adjunction hypotheses needed later.

Step 2 uses the internal/sectionwise module equivalence for underlying maps, the exact monoidal tensor comparison for tensor and unit, the sheaf closed-tensor statement for the actual Hom adjunction, the module-sheafification universal property for free modules, and the 03EV node's explicit j_! presheaf formula and exact tensor conclusion. Those statements do say each part used. The parameter S is an object in the fixed profinite skeleton, not an arbitrary nonrepresentable condensed set. The free-module construction agrees by its universal property, not by assuming sections of a sheafified free object are free.

Step 3 explicitly constructs Ind left adjoint to U and proves U preserves injectives by the extension property. It uses the exactness-detection clause in restriction calculus, the free-module and coordinate statements of the bar-resolution node, the closed tensor adjunction, and the injective definition. Its last citation to the derived-invariant-bar statement supplies the meaning of the derived internal Hom being computed. The proof does not take U-preservation of injectivity from that node's proof.

Step 4 uses the bar resolution's induced coordinates and free-object property, the tensor-Hom adjunction, and the normalized fully fixed action definition. It writes each deletion face and its action explicitly, thereby verifying the action-dependent horizontal differential. It neither cites a definition for an unproved comparison nor substitutes a discrete-module theorem.

Step 5 uses the *tensored* exactness clause of the bar-resolution statement and the injective extension property to prove sectionwise exact augmented rows. Image/quotient factorization explains the kernel and lifting assertions. The definition of fully fixed sections identifies the augmentation with Gamma_G. No projective bar terms or exact global sections are assumed.

Step 6 uses the first-quadrant total comparison on the transposed double complex, whose column hypothesis is exactly the row result just proved. It checks the sign (-1)^(pr) in the transposition and finite diagonals. It uses the derived-invariant-bar statement only for its compatible derived columns and natural total comparison, and restriction calculus for computing R Gamma by equivariant injectives. The actual b and j are defined and checked here; they are not smuggled out of a cited proof.

Step 7 is the elementary single-component chain-map calculation from the explicitly cited exact homogeneous resolution. It checks q=0 as well as positive degrees.

Step 8 uses the bounded-below injective K-injective leaf with the shifted target I[q], and the localization-bijectivity leaf twice, with sources A and P respectively. Its source P is not bounded below; the cited localization lemma has no such hypothesis. This is exactly why using K-injectivity is legitimate while using the bounded-below lifting lemma on P would not be.

Step 9 uses the unit/counit equations of the canonical bounded-below derived-adjunction node to identify the termwise transpose of h, not just some abstract bijection. It uses the canonical unbounded shift-compatibility node with exact inflation and K-injective resolutions (step 1), and restriction calculus's assertion that the ordinary derived functor on bounded-below inputs is computed by these injectives. All objects in this comparison, A and I[q], are bounded below. It preserves the prescribed shifts.

Step 10 is elementary from the specified cochain and shift definitions: its displayed delta and chain-homotopy formula are expanded. Step 11 is the two parity identities comparing delta with d_h+(-1)^p d_I, using the closed tensor unit and the double-total definition. The source/target identifications were already established in step 4; no new Hom-comparison lemma is assumed. Step 12 applies those computations to the actual homotopy from step 8 and writes explicitly how its boundary gives a chain homotopy out of A[-q]. Thus equality is in the derived category of internal modules even when A is not projective. It does not confuse a section cohomology isomorphism with such an equality.

Step 13 uses the exact homogeneous resolution only for its differential identities. It constructs the kernel factor f, the two-term cone, its quasi-isomorphism v and the actual map kappa. The cited cone definition and SES-triangle statement supply precisely the -pr sign used. This is an explicit cone computation of the extension clause, not an invocation of a new lemma restating that clause.

Small cases checked: q=0, q=1, the trivial group, the zero module, the zero ring (where signs give the same zero map), split extensions (equivariant lift from A makes the cocycle zero), and the nonsplit F_3/C_3 extension above. All finite total diagonals and the shift of a nonnegative injective complex retain the required boundedness. No non-elementary proof step exceeds 2000 characters; the longest is about 1100, and none hides a separate comparison lemma. Every use has a literal full-statement quotation in citations.json, with its hypotheses retained for inspection.

I checked delivery-errors B through E individually: no statement-only node contains a proof; no new or duplicate nodes; precise definition citations and TeX; actual logged searches; every non-elementary step cites the exact statements it takes; no proof-only facts cited; no circular dependencies introduced; no replacement of the unit route; and the discovered source/sign error is reported above with a concrete nonzero case and its citer impact.

## What remains

No part of this one-level split is left unfinished. Independent maintainer review is required as usual, especially for the explicit statement correction and repair of the sole citer's sign calculation. The general internal reference remains WANTED; the supplied proof is marked agent-written.
