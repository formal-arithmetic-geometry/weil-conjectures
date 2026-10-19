# Q03: lem-trf-fppf-sheaf-representability-descent-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fppf-sheaf-representability-descent-data.json`: statement, split into nine proof steps; no exact Mathlib match.
- `citations.json`: verbatim statement quotations for every node used in every step.
- `searches.jsonl`: actual msearch records retained in the sandbox.
- `report.md`: this report.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Every substantive input already has a DAG node. In particular, the existing `lem-pe-set-sheaf-cover-descent` states both existence of the glued set sheaf and unique gluing of morphisms, and the existing `lem-weil-pbc-fpqc-representable-descent` states the unique gluing of maps into any scheme. I did not create narrower copies of these facts.

## Attachments

None. Searches of WeilConjectures in the slopmaster2 source checkout for the exact item tag, descent-data terminology, fppf descent and local representability found no declaration giving the entire equivalence and its effectivity clause. No Lean file was changed and no compiler was run. Upstream master was used only as read-only reference, not as finished-proof evidence.

## WANTED

None. All mathematical sources used are present under literature/stacks-project.

## Findings and corrections

The imported statement agrees with Stacks Tag 02W5, `descent-lemma-descent-data-sheaves`, specialized to the fppf topology. Its statement, chapter, unit, blueprint ancestry and original searches are retained. No mathematical statement correction was necessary. The imported proof was empty. Stacks constructs the inverse by a sheaf coequalizer, asserts its local identifications from the cocycle, and omits the mutual quasi-inverse checks. The split realizes that sheaf-gluing argument by the already available slice-sheaf gluing theorem, then explicitly proves the local identifications and both natural quasi-inverse isomorphisms. It assumes no effectivity of scheme descent: the schemes may fail to glue to a scheme until the final conditional clause.

The blueprint ancestor is lem-trf-local-term-locality, through the already recorded quotient-presentation support chain. The immediate use is the first and third representability steps of Tag 0265 in lem-trf-etale-affine-quotient-representable. That caller needs both production of the prescribed scheme descent datum and representation after that datum is shown effective. Both interfaces are proved here. This is a supporting generic descent argument; no chapter or unit proof step was replaced, and this item is not the unit's key statement, so no unit record was changed.

## Not duplicates

No new nodes. DAG searches included Tag 02W5, descent-data-sheaves, descent data, locally representable sheaves, Yoneda, subcanonical, Tags 04TR and 023Q, and fppf/fpqc covering comparisons. Whole-blueprint searches via blueprint_refs.py covered descent data sheaves representability fppf, representable, gluing sheaves and subcanonical. No other blueprint node states this equivalence; same_as remains empty. The generic set-sheaf descent node was reused rather than re-created, as were Yoneda, representing-object uniqueness, affine refinement, and fpqc representable descent.

## Mathlib search assessment

The item was searched with LeanFinder, LeanSearch, Loogle and grep through msearch.py, and a second semantic phrasing and another grep were run. All actual records are appended without changing their query texts. I read the returned candidate source: AlgebraicGeometry/Sites/Representability.lean starts with a Zariski sheaf and relatively representable open immersions, and supplies Zariski scheme gluing, so it is not this general fppf-descent equivalence. CategoryTheory/Sites/Descent/IsStack.lean:69-73 (`isEquivalence_toDescentData`) assumes an IsStack instance for a specified pseudofunctor. This neither identifies the category of locally representable sheaves with scheme descent data nor supplies the present inverse construction; applying it would require a new substantive identification, not a one-line specialization. The DescentData hits define the data and its pullback functors. The new queries and the original imported search history are retained in the node. No search was recorded as run unless it actually ran; this run's services all returned results.

## Review by Q03

I read the whole Stacks Tag 02W5 statement and proof in descent.tex:9335-9425, its representable-sheaf input Tag 023Q (`lemma-fpqc-universal-effective-epimorphisms`, descent.tex:4130 onward), and the actual set-sheaf gluing and morphism statements Tags 04TR and 04TQ (`lemma-glue-sheaves`, sites.tex:5848 onward, and `lemma-glue-maps`, sites.tex:5638 onward). I also read Topologies Tags 022C (`lemma-zariski-etale-smooth-syntomic-fppf-fpqc`) and 021P (`lemma-fppf-affine`). There are no new nodes with further source obligations. I opened the statements of every cited DAG node and checked that the quotation in citations.json is literally present and that the proof uses that statement, not an unexported part of its proof.

Step 1 uses the actual fpqc covering definition, the fppf site and sheaf/site definitions, and the finite-affine-refinement statement. The latter explicitly gives finitely many affine opens of the covering members that cover an affine base. Applied over an affine open V, these are opens of the original covering members as well, since the restricted source is the inverse-image open. This verifies precisely the finite-affine condition in def-weil-pbc-fpqc-covering; it does not infer quasi-compactness of the original individual maps. The base-changed covering is licensed by the site axiom. This step is non-elementary because it invokes affine refinement.

Step 2 cites lem-weil-pbc-fpqc-representable-descent, which asserts existence AND uniqueness for compatible scheme maps along arbitrary fpqc covering families. Its target need not be affine or separated. Applied first with target Z and then with target B, it gives both the glued map and the equality of its structure map with the one required over B. The site definition supplies exactly the matching-family sheaf criterion. Thus no unproved fppf-subcanonical assertion is smuggled into the construction.

Step 3 uses the full Yoneda bijection of lem-pc-yoneda, not merely full faithfulness, for the structure map X_i to T_i. Its fibre and disjoint-union formulas are written out on every test scheme and commute with precomposition. def-pur-localized-ringed-site explicitly defines these slice restriction values, including relocalization. This is an elementary unpacking of fibres of the product projection, not a new comparison lemma.

Step 4 uses the universal property and existence in def-pc-fibre-product, the unique isomorphism inducing a prescribed functor isomorphism in lem-pc-representable-unique, and the natural Yoneda bijection in lem-pc-yoneda. Both overlap schemes represent the very same product functor. Checking all base coordinates and the H coordinate proves the cocycle and the compatibility of a sheaf morphism with the comparisons. This applies to repeated indices too; it does not claim phi_ii is the identity on all of T_i times_T T_i.

Step 5 uses the existence clause of lem-pe-set-sheaf-cover-descent. I checked its small-site, all-fibre-products, set-index and universe hypotheses against def-weil-size-convention, def-pc-fibre-product and the actual big fppf site. The terminal-object slice is equivalent to the original site by forgetting the unique map to T. def-pur-localized-ringed-site gives exactly the restrictions being used. The local sheaves are representable on each slice by step 2; no unproved assertion that a restriction functor preserves a colimit is needed. The given scheme isomorphisms induce sheaf isomorphisms by direct postcomposition with the prescribed base coordinates, and the scheme cocycle gives the sheaf cocycle.

Step 6 writes the isomorphism h_Xi = h_Ti times H_D as a disjoint union over every W to T_i, not by identifying a sheaf on the big site with a sheaf on a different category without an argument. The compatibility equation e_j = theta_ij e_i says precisely that the recovered scheme comparisons are phi_ij. Yoneda detects equality. This elementary fibrewise check verifies the correspondence clause of the item.

Step 7 uses the morphism clause of lem-pe-set-sheaf-cover-descent: the statement explicitly gives a unique global map from compatible slice maps. The f_i compatibility equation implies exactly the required equality on the double slices. Uniqueness proves the functor laws, and Yoneda proves naturality of the local representing-scheme isomorphisms. Step 8 uses the same morphism clause on the local isomorphisms and separately on their inverses. It checks inverse identities and naturality using uniqueness after restriction; the step does not assume the quasi-inverse assertion which Stacks omits.

Step 9 uses the fibre-product universal property, the exact representing-object uniqueness node, and the morphism-gluing clause of the set-sheaf node. In the forward direction the scheme X itself supplies the effective datum. In the reverse direction an effective datum gives compatible local isomorphisms to the genuine sheaf h_X from step 2; unique gluing of both directions makes a global isomorphism. def-pd-descent-datum gives the definition of effective descent, with the covering-family version already explicit in the item's statement. Thus representation is conditional on effectivity and is not asserted for arbitrary scheme descent data.

The off-unit affine-refinement and set-sheaf-descent facts are declared in split_report.tool_uses with their exact purpose. Yoneda, uniqueness and fibre products are Mathlib/closed tools; the fpqc representable-descent node is an existing Mathlib leaf. I have not set maintainer-owned tool_uses. All proof dependencies are the union of the step citations. No new node is elementary, a duplicate, or a clause renamed from this item, because no new node was introduced. Every non-elementary assertion has a cited statement, and none of the nine steps exceeds 2000 characters.

I tested the identity covering (the two functors reduce to a representing scheme and its functor of points), a covering with repeated members (the cocycle is used on all triple overlaps, without forcing phi_ii to be identity away from the diagonal), and the empty covering of the empty base (the sheaf axiom forces the sole section set to be a singleton, matching the unique empty descent datum). There is no covering of a nonempty base by an empty family. The proof uses no separation, local quasi-finiteness, finite-presentation or effectivity assumption on X_i, and so does not borrow the hypotheses of the caller's separate effective-descent lemma. No coefficient category is changed and no SGA source is used.

## Unfinished work

None in this one-level split. All cited open existing nodes retain their own downstream obligations. Server dry run and direct delivery are the remaining validation steps.
