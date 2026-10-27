# NM: lem-sfb-cubical-strict-local-affine-seed

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cubical-strict-local-affine-seed.json: statement split into nine steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-abelian-quotient-ample-reflection.json: statement-only field positivity theorem; unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-cubical-ample-norm-reflection.json: statement-only global norm-reflection theorem; unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every cited node in every step.

## Attachments

None. The project-source searches for the blueprint id, cubical/cubist ampleness and semiabelian terminology returned no declaration stating the item. The Mathlib hits were convex AmpleSet facts, ordinary affine morphisms, structure-sheaf localization and invertible-module algebra, rather than these positivity results. The searches and returned names are preserved verbatim in searches.jsonl and the relevant node records; the second semantic phrasing was read for each new node. No compiler or Lake command was run.

## Literature wanted

WANTED: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), XI 1.11 and the ampleness chapters, for lem-sfb-semiabelian-abelian-quotient-ample-reflection and lem-sfb-cubical-ample-norm-reflection and the item. The named local PDF is absent. No numbered Raynaud assertion is claimed for norm reflection.

I read the current blueprint's det-thm-sf-ctf-stability-direct-images proof, especially (3), and the inherited item's provenance and statement. That proof supplies the overarching direct-image route, not a proof of this positivity input. I also read Lan's primary text Arithmetic compactifications of PEL-type Shimura varieties, online dense revision, the proof of Proposition 3.3.3.6 and the discussion/proof surrounding Lemma 4.2.1.8 (https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf). These explicitly invoke Raynaud XI 1.11 to pass ampleness from a semiabelian torus extension to its abelian quotient. I use that as a source pointer for the FIELD lemma, not as permission to transfer Lan's complete-base degeneration hypotheses to our arbitrary local base. I inspected Stacks descent.tex, lemma-descending-property-affine (Tag 02L6), and the supplied node statements for affine pullback, global generation, tensor generation and generic-line descent. The split is an agent assembly, not a transcription of an unavailable source.

## Problems and corrections

The item was unsplit, with no local report or node copy to preserve. Its statement was not changed and no statement dispute was found. The inherited blueprint ancestor is null; blueprint_refs.py ancestor reports this existing null rather than an imported ancestor. I preserved it, retained the full inherited chain, and prepended the item in each new node's via. Whole-blueprint searches for torus ampleness, norm ampleness and symmetrization found no imported matching node.

The tempting existing lem-sfb-semiabelian-supplied-norm-ampleness, lem-sfb-normal-cubical-generic-ampleness and parent lem-sfb-cubical-fibrewise-ample-criterion depend on this item. They cannot serve as inputs. I checked their transitive proof dependencies and avoided them. The norm is instead constructed as a positive tensor power of an ample line pulled back from the generic-torus quotient, using existing independent endomorphism-extension inputs.

The node lem-sc-ample-tensor is stated only over a field. I did not apply it to our relative total schemes. Step 1 writes the short section proof for ample tensor globally generated, then uses coherent twisting to deduce the ample-tensor argument. It also writes out the positive-power converse. These are steps, not spurious new nodes.

## Not duplicates

lem-sfb-semiabelian-abelian-quotient-ample-reflection vs lem-sfb-torus-torsor-picard-rational-surjectivity: the existing node descends a positive power as a line, with no positivity conclusion; the new node reflects ampleness of a specified pullback on a semiabelian extension of an abelian variety.
lem-sfb-semiabelian-abelian-quotient-ample-reflection vs lem-sfb-normal-semiabelian-generic-torus-quotient: the existing node constructs the relative quotient; the new field theorem concerns positivity of a supplied line on its abelian target.
lem-sfb-cubical-ample-norm-reflection vs lem-sfb-semiabelian-supplied-norm-ampleness: the existing node concludes relative ampleness of a norm from generic ampleness of the original line; the new node ASSUMES absolute global ampleness of the norm and concludes positivity of the original cubical line.
lem-sfb-cubical-ample-norm-reflection vs lem-sfb-cubical-fibrewise-ample-criterion: the existing node starts with positivity on every residue fibre; the new node requires a globally ample norm already constructed. It does not produce that input or a section chart.
lem-sfb-cubical-ample-norm-reflection vs lem-sfb-semiabelian-algebraic-equivalence-norm: the existing node works over a field with a geometrically algebraically trivial twisting line; it does not treat a relative normal base or recover positivity of a given cubical line from its globally ample inversion norm.

Neither new node restates the seed or a clause of it. The field node has no local base or sections. Norm reflection has a stronger, independently constructed global positivity hypothesis, no fibrewise-ample hypothesis and no strict-local section conclusion. Steps 2--7 construct that hypothesis; step 9 extracts the chart.

## Review by NM

I checked B--E of delivery-errors.md, including the merged copy, against the node files. Both new nodes introduce their own schemes, fields, groups, lines and maps; the relative node spells out its group operations and separatedness because the older group-scheme definition is stated over a field, use single TeX backslashes, and have empty proofs and proof_deps. They state genuine positivity inputs rather than a proof sketch. I checked the relevant definition-node statements, including the absolute section-locus meaning of ampleness and semiabelian geometric fibres. The original's every-prime assumption remains literally present; the argument happens to use its generic instance.

Step 1 uses precisely the affine-cap statement to intersect an affine section locus with another section locus; it does not assume an arbitrary intersection of affine opens affine. Coherent-twist global generation applies to finite-type quasi-coherent O_Z, and the positive-power node supplies only the forward power implication. The converse is explicitly proved from the ample definition.

Step 2 uses the generic-torus-quotient statement for the quotient, torus torsor and abelian generic fibre, and the local-ample-line statement for its affine cover and ample lines. The local-base argument selects the cover member containing the closed point; such an open contains every generalization and is the whole local spectrum. The inversion is an affine isomorphism and tensor-pullback formulas supply the displayed symmetry. Geometric connectedness is justified directly through the given fppf quotient by a connected torus.

Step 3 uses the affine fpqc descent statement exactly to descend affineness of the torus and its torsor projection. The latter becomes H times T over H under its own fpqc cover. Affine permanence supplies base change and the affine-target consequences; the ample-pullback statement requires an affine morphism and has no properness condition. This is an elementary assembly of these cited statements, not absolute-ampleness descent along an arbitrary fpqc map.

Step 4 checks all rational Picard-surjectivity hypotheses on the abelian target: smooth, separated, finite type, geometrically integral, and torus torsor. I added an explicit smooth-connected-fibre integrality citation here, rather than treating the word abelian as a proof of geometric integrality. It only takes the power/descent conclusion that this node actually states. The new field node supplies the missing positivity reflection for C, after its pullback is identified with a positive power of the ample generic norm. No definition node is being used as an ampleness theorem.

Step 5 checks that C and F_eta are symmetric ample before invoking the endomorphism-span statement, which really gives the tensor product of endomorphism pullbacks. The ample auxiliary E is formed by twisting C with a globally generated line; the exponent is chosen at least two. Normal-semiabelian hom-extension is applied with source and target J, over the same normal integral locally Noetherian base, to each generic endomorphism. The construction of Q and its generic power C^(da) is written out, with no hidden extension of positivity.

Step 6 uses finite global generation of a positive power of F, the cited fibre formula to see that its generating family still generates after any b_j pullback, and the tensor-generation theorem on quasi-compact J. The ample tensor and power arguments are those proved in step 1. Thus Q, not merely Q_eta, is ample, and q is already known affine.

Step 7 checks every hypothesis of the generic-line-pullback statement: both schemes locally Noetherian, base normal integral, morphism flat, nonempty integral residue fibres, and quasi-compactness. Smooth-flat and finite-type-over-Noetherian are the statements cited for those hypotheses. The smooth-connected-fibre theorem provides integrality of the fibres, not normality of the arbitrary base. This gives a base line W, whose triviality follows from local freeness on a local spectrum. It yields actual line isomorphisms and ample N^h, not merely numerical equivalence. The variable h=cda is strictly positive.

Step 8 invokes exactly the new norm-reflection statement with its crucial absolute GLOBAL ampleness hypothesis supplied by step 7. This relative positivity theorem is deliberately an unsplit input for subsequent work; I do not claim to have read a numbered proof of it. Step 9 uses affine base change and affine ample pullback, followed by the literal ampleness definition at the closed identity. No property of strict henselization beyond its specified affine ring base change is needed at this last step.

For the field node I tested torus rank zero (identity abelian quotient), abelian dimension zero (quotient a field spectrum), split products, algebraically trivial lines on a positive-dimensional abelian variety, and negative-degree lines on an elliptic quotient: none gives spurious positivity. For norm reflection I tested the zero-dimensional group, a torus (where lines are locally trivial and the relevant total schemes are affine after local splitting), and a proper abelian family (where it agrees with the familiar polarization criterion); anti-ample elliptic lines fail the norm hypothesis. I have not smuggled the false rule that arbitrary fibrewise ampleness for a nonproper family is enough into either node. All nine steps are below 2,000 characters. I checked that every proof use has a verbatim matching quote in citations.json, and that proof_deps is their union. The server review_split check passed before writing this report; full delivery preflight follows.

## Remaining work

The two new positivity inputs are intentionally unsplit, as stage 1 requires. Their future proofs must respect the no-SGA route lock. The global norm-reflection input is agent-formulated and its independent proof is not supplied here; the original Raynaud source is wanted for that work. No Lean formalization or downstream proof completion is claimed.
