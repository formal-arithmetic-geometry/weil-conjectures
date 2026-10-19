# sk-def-conv — stage 1

## Files written

- `dag/nodes/sec-nagata-compactification/sk-def-conv.json`: definition, split into existing definition nodes. No new Mathlib leaf claimed.
- `dag/units/sk-def-conv.json`: only `realized` and `realized_by` changed; the key node now realizes this definition unit, whose proof-step list is empty.
- `citations.json`: empty list, because this definition has no proof steps.

New nodes: 0. New Mathlib leaves: 0. The existing definition nodes are reused rather than copied or reclassified.

## Attachments

None. Searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `sk-def-conv`, including the exact blueprint tag, and the relevant notion and declaration names. No project declaration gives the entire six-clause item. The four imported Lean names refer to separate Mathlib notions and omit surjectivity and affine schemes; they are not an attachment. The upstream master source is not used as proof evidence.

## WANTED

None. The current blueprint and all Stacks passages used for this audit are present locally.

## Problems found

The imported definition had no statement dependencies, even though every constituent notion already has a node. Its `blueprint.same_as` was unsearched. I added references without changing the conventions. In the affine clause, “is Spec” is written explicitly as “is isomorphic to Spec”, as in the existing scheme definition.

The old unit record says “finite type” in the proper clause whereas the current main-20261015 paragraph says “locally of finite type”. This is an equivalent formulation, not a statement dispute: Stacks Morphisms Tag 04XU (`lemma-universally-closed-quasi-compact`) gives quasi-compactness under universal closedness, and `def-weil-finite-type-morphism` defines finite type as locally finite type plus quasi-compactness. The pinned Mathlib directly uses the current wording in `IsProper`, Proper.lean:42. No unit statement or chapter route was edited.

## Unfinished work

None for this one-level definition split. No Lean was written or compiled. No delivery push was made; this sandbox is for the second reader.

## Not duplicates

No new nodes. Searched the whole DAG and `tools/blueprint_refs.py` for scheme/morphism conventions, properness, and the constituent phrases. `def-weil-pbc-scheme-conventions` already collects a broader list including all these meanings; `def-pc-morphism-conventions` delegates to that broader list, and `def-weil-scheme-morphism-properties` overlaps with it. None has exactly this six-clause scope, so `same_as` is empty; their constituent nodes are reused. No convention is defined anew.

## Review by NB

I read the current blueprint `main-20261015/blueprint/sec-nagata-compactification/sk-def-conv/_section.md`, the chapter and unit records, and the existing broader convention bundle. This is a definition, so splitting means naming its constituent notions, not supplying a theorem proof. The node and unit both have no proof steps. Consequently the C1/C4 per-step citation audit is empty and `citations.json` is `[]`; the substantive audit here is of every statement dependency below.

For properness I opened `def-weil-proper-morphism` and `def-weil-finite-type-morphism`: they explicitly define separatedness, universal closedness, locally finite type and finite type. I read Stacks Morphisms Tag 01W1 (`definition-proper`) and 04XU (`lemma-universally-closed-quasi-compact`), and Proper.lean:42 and UniversallyClosed.lean:160–167 in the pinned Mathlib. This checks the apparently different finite-type hypothesis without assuming a Noetherian, quasi-compact-base or finite-dimensional hypothesis. The existing proper-definition leaf already records the same bridge.

For finiteness I opened `pqf-def-affine-morphism` and `def-weil-finite-integral-morphism`. The former defines preimages of affine opens; the latter explicitly gives both the affine-local finite-module condition and the item's finite direct-image-algebra phrasing. I read Stacks Morphisms Tag 01WH (`definition-integral`, finite clause) and Properties Tag 01PB (`lemma-finite-type-module`). Here “finite algebra” means finite as a module, not merely finitely generated as an algebra. Mathlib Finite.lean:39 supplies the affine-local notion. The sheaf equivalence is contained in the cited existing node's statement; I do not pretend the bare class proves it by definition.

For immersions I opened `def-weil-closed-immersion` and `def-weil-open-immersion`. The first explicitly defines an immersion as closed followed by open, and the second defines the open factor. Stacks Schemes Tag 01IO (`definition-immersion`, item 5) and Mathlib `IsImmersion.isImmersion_iff_exists`, Immersion.lean:155, use that order. No quasi-compactness assumption and no reversal of factors is introduced.

For surjectivity I opened `def-weil-surjective-morphism`, whose statement is exactly surjectivity on all underlying points, and read Stacks Morphisms Tag 01RZ (`definition-surjective`) and Mathlib UnderlyingMap.lean:59. This is not a closed-point-only convention.

For étaleness I opened `def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`, `def-weil-flat-morphism` and `def-weil-unramified-morphism`. They respectively give the three-way conjunction, the pointwise finite-presentation condition, stalkwise flatness, and the locally finite type/open-diagonal condition. I read Stacks Morphisms Tags 02GI (`definition-etale`), 02GV (`lemma-flat-unramified-etale`) and 02GE (`lemma-diagonal-unramified-morphism`), and Mathlib Etale.lean:140. The locally finite presentation hypothesis is retained: it is what makes the ordinary unramified condition into G-unramified here. No global finite presentation or separatedness is added.

For schemes, morphisms and affineness I opened `def-pc-scheme` and `def-weil-affine-spectrum`. The former explicitly states that affine means isomorphic to a ring spectrum, and the latter defines that spectrum. I read Stacks Schemes Tag 01HW (`definition-affine-scheme`) and Mathlib AffineScheme.lean:59 and :68. Thus the item uses isomorphism of schemes, not an equality with a selected presentation.

I checked B–E against these files. There are no new statements needing hypotheses, searches or duplicate-tag comparisons, no lemma moved out of the item, no non-elementary proof assertion hidden in a step, and no off-route proof citation. All dependencies are definitions. Small cases respect the definitions: the empty scheme is affine as Spec of the zero ring and its map to a nonempty scheme is not surjective; identities have all five morphism properties; a proper nonaffine scheme is not forced to be finite; and étale morphisms are not required to be quasi-compact. The finite/direct-image and proper/local-finite-type bridges are supported by the statements read, rather than by assumptions about their proofs. All Mathlib search records correspond to actual `msearch.py` invocations; the remote search's `IsEtale` spelling was checked against the pinned source's `Etale` and was not used as a local declaration name.


## Second reading by NB

- Item `sk-def-conv`: compared all six clauses with the current main-20261015 `_section.md`, the old definition unit and the chapter route. PASS: the node states the current paragraph, with explicit scheme hypotheses and isomorphism in the affine clause; the old unit's finite-type wording is equivalent, and its ambiguous immersion wording is resolved by the current paragraph.
- Proper clause: opened `def-weil-proper-morphism` and `def-weil-finite-type-morphism`, Stacks morphisms.tex Tag 01W1 (`definition-proper`) and Tag 04XU (`lemma-universally-closed-quasi-compact`), and pinned Proper.lean:40–47 / UniversallyClosed.lean:159–168. PASS: universal closedness supplies quasi-compactness without a base hypothesis, so locally finite type agrees here with finite type. No Noetherian or finite-dimensional assumption is needed.
- Finite clause: opened `pqf-def-affine-morphism` and `def-weil-finite-integral-morphism`, Stacks morphisms.tex `definition-affine` / Tag 01WH (`definition-integral`, clause 2), properties.tex Tag 01PB (`lemma-finite-type-module`), and Finite.lean:35–40. PASS: the cited finite node explicitly includes the direct-image formulation, with finite meaning finitely generated as a module. An algebra merely of finite type would not suffice (for example k[t] over a field k).
- Immersion clause: opened `def-weil-closed-immersion`, `def-weil-open-immersion`, Stacks schemes.tex Tag 01IO (`definition-immersion`, clause 5), the open-immersion definition (`definition-immersion-locally-ringed-spaces`), and Immersion.lean:150–158. PASS: the closed factor is first and the open factor second; no quasi-compactness is imposed. The item uses exactly the factorization stated by the dependency, not any claim from its proof.
- Surjectivity clause: opened `def-weil-surjective-morphism`, Stacks morphisms.tex Tag 01RZ (`definition-surjective`), and UnderlyingMap.lean:57–67. PASS: all topological points are intended, with no restriction to closed points.
- Etale clause: opened `def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`, `def-weil-flat-morphism`, and `def-weil-unramified-morphism`; read morphisms.tex Tags 01TP (`definition-finite-presentation`), 01U3 (`definition-flat`), 02G4 (`definition-unramified`), 02GE (`lemma-diagonal-unramified-morphism`), 02GI (`definition-etale`), and 02GV (`lemma-flat-unramified-etale`), and Etale.lean:140–143. PASS: locally finite presentation, flatness, and ordinary unramifiedness are exactly the dependency's conjunction. Local finite presentation permits the G-unramified criterion; global quasi-compactness and separatedness are not required.
- Affine clause and scheme hypotheses: opened `def-pc-scheme` and `def-weil-affine-spectrum`, schemes.tex Tag 01HW (`definition-affine-scheme`), and AffineScheme.lean:58–69. PASS: an isomorphism with a ring spectrum is required; neither a chosen ring presentation nor a nonzero-ring hypothesis is imposed.
- Proof steps: there are none in either the definition node or the unit. PASS: no theorem argument is being moved to a child, no elementary flag hides a claim, and `citations.json = []` accurately records the empty proof-citation list. The equivalences above are checks of existing definitions, not uncited proof steps of this definition item.
- New nodes: none. PASS: B1–B7 and the per-new-node search requirement are vacuous. Independently rechecked the broader existing convention bundle, the component statements and whole-blueprint search; the bundle overlaps but has more clauses. Fresh LeanFinder, Loogle and grep searches confirm separate component declarations rather than a six-clause attachment. No new leaf or duplicate is justified.
- Small cases: PASS for Spec(0) and the empty scheme (the empty-to-nonempty map fails only surjectivity among the five properties), identity maps of Spec(k), and a nonfinite affine map Spec(k[t]) to Spec(k). The zero module and n=0 polynomial presentation are allowed. Infinite disjoint unions of Spec(k) over Spec(k) are etale but need not be quasi-compact, so the clause has not silently become finite presentation. No counterexample to the current item was found.

Changes: appended this independent reading and three actual second-reader search records; kept the first worker's review, all six definition clauses, the existing dependencies, the empty citation list, and the unit realization intact. No mathematical repair or new node was necessary. The brief's command with a final dot prints usage and exits 1 in this installed delivery tool; its documented equivalent without that dot is used for the required dry run and push.
