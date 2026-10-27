# Worker report — NF

## Files written

- `dag/nodes/sec-six-functors/lem-route-inverse-image-completed-coefficient-map-is-iso.json`: statement, split; not a Mathlib leaf. Reused all required ingredients from existing nodes; 0 new nodes and 0 new Mathlib leaves.
- `citations.json`: exact statement excerpts for all seven step/node citations.
- `searches.jsonl`: original records produced by the prescribed msearch command; all seven executions retained and summarized in the item.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item tag, the completed coefficient map name and the completed-coefficient notion. No declaration there states this precise normalized limit-map assertion. The recorded SHEAF theorem at InverseImagePullbackComparison.lean:118 has `sorry`, so is not an attachment. Existing helper declarations remain attached to their existing nodes.

## WANTED

None. All sources needed here are available locally.

## What was wrong or incomplete

The live node was explicitly PROVISIONAL: a docstring and Lean signature, with no objects or hypotheses in its prose and no proof. I expanded the exact signature, retaining the assumption `[IsIso g]`, prime ell and finite-dimensional Q_ell extension, and allowing arbitrary schemes and independent site/coefficient universes. I did not add the invertibility-of-ell or finite-field assumptions used by some surrounding derived-operation definitions. No false statement was discovered and no target statement was changed.

The machine assigned Deligne Weil II as the source, although this auxiliary assertion is the elementary inverse-limit construction for constant ring sheaves. I replaced that source with the actual Stacks constructions (09A5 section-morphism, 00WX lemma-adjoint-sheaves, 0H7J example-constant-sheaf, 03CO lemma-limits-colimits-abelian-sheaves) and explicitly marked the completed assembly proof as agent-written. These tags do not themselves state this whole specialized lemma. In particular 03CO is about abelian sheaves; the cited existing inverse-limit node explicitly includes ring sheaves, which is what this argument uses.

There were no matching directories in the prescribed abandoned-attempt archive listing and no item-specific repair note in coord/repair-notes. The active sandbox initially contained only dispatcher brief markers. No prior proof or search evidence was discarded.

## Searches and reuse

I searched the whole DAG for `inverseImageCompletedCoefficientMap`, `isoSectionwiseConstantMap`, `isoSectionwiseInverseImage`, `integralCoefficientSheafSystem`, and `completedIntegralCoefficientSheafUnrestricted`, and read the existing nodes for sectionwise inverse image, its equivalence/constant-ring theorem, the completed coefficients, the general inverse limit, and the existing limit scalar chain comparison. The last assumes the completed coefficient isomorphisms, so cannot prove this assertion. The component-naturality route node already exists but is not needed: the transition equation follows immediately from part (3) of the existing site-isomorphism theorem. I did not create a duplicate for any of these facts.

Whole-blueprint searches via tools/blueprint_refs.py for “completed coefficient” (53 matches) and “isomorphism inverse image” (0 matches) found no imported node stating exactly the prescribed completed coefficient map's invertibility. The existing completed coefficient blueprint node defines the limit and the old comparison definition contains an informal assertion of invertibility; neither is a standalone statement node proving this route sorry. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`; the ancestor and intermediate transport route are preserved.

The seven required msearch executions include LeanFinder in two phrasings, LeanSearch, Loogle in two patterns, and grep in two patterns. The first Loogle pattern used an identifier the service did not recognize; its actual diagnostic is recorded, then the corrected pattern returned HasLimit.isoOfNatIso and its projection lemmas. I read Mathlib/CategoryTheory/Limits/HasLimits.lean:379-390. These facts compare already identified diagrams; they do not provide the site equivalence and normalized constant-coefficient identifications here. LeanSearch found equivalence preservation/creation of limits, LeanFinder found unrelated scheme identities or general sheaf comparison diagrams, and grep found the general categorical comparisons or unrelated analytic completions. Nothing states the item's specialized construction as a one-line Mathlib specialization. The original machine name-grep record is retained with its maintainer provenance.

## Not duplicates

No new nodes were created. Existing definitions and the existing site-isomorphism theorem are cited directly. The completed-map assertion is strictly downstream of their finite constant-ring statement.

## Review by NF

I read the exact theorem's variables and its actual definitions in lean/Sheaf/AlgebraicGeometry/ProEtale/InverseImagePullbackComparison.lean:44-120, including the finite map, components, compatibility theorem and limit lift. I also read CompletedIntegralCoefficients.lean:77-114: the diagram is indexed by natural numbers with exponent n+1, ULift changes only the coefficient size, and the unrestricted completed sheaf is literally its limit, with no finite-field datum. I read IsoSectionwiseInverseImage.lean:47-75 and 132-215 to check the arbitrary-universe sectionwise model and constant-section normalization, and opened the statement of every node used below. There are no new-node sources to check.

For Step 1 I used exactly part (3) of lem-weil-proetale-isomorphism-inverse-image: every commutative constant ring comparison is invertible and is natural for every coefficient homomorphism. Its source's normalization matches isoSectionwiseConstantMap, rather than an arbitrary isomorphism. The lifted finite rings are commutative, g is an isomorphism, and the quotient transitions are ring homomorphisms. The limit universal property in def-pur-sheaf-inverse-limit gives the map once these compatible components are supplied. This is the non-elementary input; the proof does not extract a stronger assertion from a definition.

For Step 2 the sectionwise inverse-image definition gives precisely evaluation at Phi_g U on sections and morphisms, with arbitrary coefficient Hom universe. The inverse-limit node explicitly says limits are sectionwise and extends this to rings. These two statements identify both tuple rings and show that the actual limit lift acts by c_n in every coordinate. This is the key identification with the recorded map, rather than merely exhibiting an unnamed isomorphism between the same objects.

For Step 3 the same part (3) supplies invertible sheaf maps and the forward transition square. I wrote the inverse transition square by actual composition with the two inverses, and the restriction square by the same calculation. Thus the coordinate inverse lands in compatible tuples and is a ring homomorphism commuting with restrictions. No flatness, exactness, tensor comparison, completeness theorem or new lemma is hidden in this step. Step 4 uses the sectionwise limit node's equality of tuples; the two coordinate inverse identities explicitly prove both sheaf compositions are identities. Citations.json contains a verbatim statement quote for every use in each step.

I checked delivery-errors B through E in full: self-contained objects and universes, exact Stacks tags/labels, no invented searches, no statement-only children with hidden proofs (there are no children), no use of a definition for an unstated theorem, no duplicate or cycle, no replacement of the unit route, and no hypotheses imported from surrounding definitions. None of the cited nodes depends back on this item, by a traversal of their statement/proof dependencies. The off-unit site-isomorphism theorem is explicitly declared as a generic tool use in split_report; inverse limits are an existing Mathlib leaf. All four proof steps are below 2000 characters and the assembly proof is below 3000 characters.

I tested the identity isomorphism (all c_n and q normalize to identities), empty schemes/sites (the same sectionwise universal property applies), the first quotient n=0 (exponent one), and schemes in characteristic ell (allowed because this coefficient-only assertion uses no etale torsion theorem). For arbitrary U the inverse calculation uses no surjectivity of transition maps and works for every compatible tuple, so it has no hidden Mittag-Leffler or completeness assumption. The proof requires no module at all. No SGA source is used, and no repository, launcher file, Lean source or compiler was modified or invoked.

## What remains

Nothing mathematical remains for this split. Server dry run and direct delivery are the required final validation steps.
