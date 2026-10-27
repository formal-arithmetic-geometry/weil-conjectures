## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-local-kummer-pushout-units.json: statement, now split; no exact Mathlib match. The statement and its single statement dependency are unchanged.
- citations.json: the verbatim statement extract used in Step 1.
- searches.jsonl: searches performed by the required msearch.py command.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record was changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for Kummer/kummer, fine saturated, sharp monoid, and local-monoid/pushout terminology. Hits concern Kummer covers of rings, cohomological Kummer sequences, and unrelated categorical pushouts; no declaration states the item's integralized monoid-pushout assertion.

## Wanted sources

WANTED: a direct published reference for units and locality of this integralized local Kummer pushout, for lem-per-local-kummer-pushout-units. The current ILO references supply the definitions and geometric application, not this exact theorem. The proof is therefore explicitly marked proof_origin.by = agent.

## Audit and changes

The sandbox contained no previous item, split, report, citations, or search log. I copied the live unsplit item and preserved its statement, source, inherited searches, creation record, chapter, unit, and blueprint ancestry. There is no repair-note file for this item. Read GOAL.md, the stage-1 brief, stages/1-dag.md, SETUP.md including its three levels, the worker role, and delivery-errors B--E. Read the chapter and unit records; this item is not their key statement, so no realized fields need changing.

Read the latest blueprint's lem-per-artin-gabber-affine-curve.proof.md and its unit record. The latest ancestor's Step 3 is a perverse-duality argument, rather than a literal assertion about monoid units: the existing supporting branch descends through regular-pair geometry to the fs-product nonemptiness argument. The existing blueprint.from.place describes that supporting branch; no new identification of the lemma with a blueprint statement is asserted. Blueprint-reference searches for local Kummer, pushout, and sharpening, and a search of the latest blueprint for integralized pushouts/root cofinality, gave no equivalent blueprint node. The exact current snapshot is main-20261024 ef6f9619fdbffa59e88528fb56483d76c70258c8.

Read ILO VI 2.1, printed p.71, for the injective positive-multiple Kummer condition; VIII 3.1.1--3.1.2, p.98, for units, sharpening, and monoids in their group completions; VIII 3.1.5, p.99, for the definition of locality; and X 1.8, pp.146--147, diagram (1.a) and its fs-base-change context. The item's original source listed VIII 3.1.1--3.1.2, but locality itself is explicitly VIII 3.1.5; the proof sources now identify it. This is a source-location clarification, not a statement dispute. No SGA source was used.

The proof starts with a zero relation rather than invoking an unproved sharp pushout theorem. Writing its group-completion witness as x-y and comparing a positive multiple of its B-component with f(z) gives na=z+v, with v a unit. Applying g then gives explicit inverses and proves the zero-relation components are units. Applying that calculation to m+(-m)=0 proves the unit-group and locality assertions. This needs neither an injection on unit groups nor a torsion-free group completion. Finite generation, saturation and locality of f are present in the statement but are not needed in this particular argument; none was removed.

## Mathlib searches

Ran and read all five new searches logged in searches.jsonl: one full-statement LeanFinder query, a second phrasing about zero sums and cancellative commutative monoids, Loogle "Monoid.Pushout", a GroupTheory grep for Kummer|sharp.*pushout|pushout.*unit, and a full-statement LeanSearch query. All services returned results successfully. No query was invented, and inherited searches were retained. The second phrasing returned Grothendieck-group embeddings, monoid pushout injections for groups, and localization descriptions, none of which is the item's assertion. Read Mathlib/GroupTheory/PushoutI.lean:54--63, and Mathlib/Algebra/Group/Units/Hom.lean:267--284. PushoutI defines the ordinary monoid amalgamated product; isUnit_map_iff assumes the locality being concluded here. Integral ring-homomorphism/localization hits concern different kinds of objects. Thus this is not a Mathlib leaf.

## Not duplicates

No new node is created, so there are no new/existing-node pairs to distinguish. Read the parent lem-per-kummer-sharp-pushout-field-extension and the neighbouring fs-product/base-change statements to verify that no finished statement supplies an attachment or replaces the calculation. The parent depends on this item, so citing it would be circular. The searches in the DAG and whole blueprint were used to check reuse, not to add a circular edge.

## Review by Q27

I checked the item against the ILO passages listed above. The fs definition and group-completion presentation actually used by Step 1 were read in the complete statement of def-trf-fs-log-blowup, not inferred from its title or proof. Its presentation by monoid generators and the relations [pq]=[p]+[q] permits every group element to be written x-y by collecting positive and negative generators. Its injectivity clause for fs monoids permits equalities in the completions to be read as monoid equalities. The citations.json extract is verbatim and supports precisely that usage. No new node has a source or hypothesis to review.

Step 1 uses only that cited definition and the quotient presentation of H in the item. The relation subgroup is already the image of a homomorphism, so a zero class has a single witness a; no injectivity of f^gp or g^gp is assumed. The signs give f(x)=b+f(y) and g(y)=c+g(x). Step 2 uses the item's root-cofinal hypothesis to produce nb=f(z)+u and its sharp injectivity to produce nx=z+ny+v. These are applications of the explicit quotient definition; no theorem about sharp group completions or exact Kummer maps is used. The units u and v have their signs fixed by those equations.

Step 3 uses only na=z+v, c=-g^gp(a), and locality of g as explicitly assumed. The inverses for g(z) and nc are exhibited in C, so a hidden assertion that a sum of nonunits is a nonunit is unnecessary. The equation g(z)+(nc+g(v))=0 proves the hypothesis needed to apply locality to z. Step 4 writes actual inverses for b and c using n>0 and z in U_A; f takes z and -z to opposite elements, independently of any locality theorem for f. These steps cite no external node because they are short substitutions and inverse calculations from the hypotheses, not invocations of a standard lemma.

Step 5 uses the already proved zero-relation calculation on (b+b',c+c') for representations of m and -m. The explicit inverses b'-(b+b') and c'-(c+c') prove that each original component is a unit. The reverse inclusion uses images of the two inverses, so U is contained in M cap (-M) without assuming the result. Step 6 uses this very argument on (b,0) and (0,c), and the definitions give both converses. M is a submonoid of H directly by addition of representatives, and its cancellation is inherited from H. All six steps are elementary calculations fully displayed, with lengths 496, 376, 317, 303, 418 and 487 characters; no step hides a comparison lemma or exceeds 2000 characters. The assembly proof totals 2397 characters.

I tested the small cases rather than assuming the statement from the application. For A=B=C=N, f(n)=dn and g(n)=en with d,e>0, the quotient is Z^2/<(d,-e)>; a relation with both coordinates nonnegative forces both zero, as predicted. Taking d=e=2 allows torsion in H, and the same conclusion holds. Group monoids, including torsion groups and maps killing units, have every element a unit, making both asserted equivalences true even when neither leg is injective. Taking A=N plus Z, f(n,t)=2n in B=N and g(n,t)=3n in C=N checks a noninjective map on unit groups; the same zero-relation proof still applies. For n=1 the formulas retain their meaning with (n-1)b=0. Zero b or c, and trivial sharp monoids, require no separate hypotheses. As a check on sharp injectivity, omitting it allows A=N^2, B=C=N, f(x,y)=x+y and g(x,y)=x+2y: both maps are local and f is root-cofinal, but H=0 and nonunits become units. Thus the proof correctly uses the sharp injection at its decisive step. Omitting locality of g also fails for A=B=N, f=id and C=0, g=0.

For B--E specifically: no unsplit new node, hollow definition, extra notion, Mathlib leaf or false search record was introduced (B); every cited statement was opened and its needed part quoted, and every remaining inference is explicitly elementary (C); the argument stays in the item, creates no renamed clauses and cites no parent or descendant (D); the equations, signs, n>0, unit inverses, and exact hypotheses were checked as above (E). No imported statement error or route departure was found. No Lean was written and no compiler, Lake, build tool, repository git command or local preflight/check_dag/review_split was run.

## Unfinished work

None in this stage-1 split. A direct published reference remains wanted; the complete agent proof is supplied meanwhile. The required server dry run and final delivery are recorded by deliver.py.
