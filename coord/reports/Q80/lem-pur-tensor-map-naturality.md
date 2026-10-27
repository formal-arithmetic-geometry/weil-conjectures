# Q80 stage-1 delivery: lem-pur-tensor-map-naturality

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-tensor-map-naturality.json`: statement, now split into four steps; no Mathlib match. Statement and its three statement dependencies unchanged. Added only proof, proof dependencies, proof origin, split report and actually logged searches.
- No new nodes and no new Mathlib leaves.
- `citations.json`: ten step/node entries, with verbatim quotations checked against the live dependency statements.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation helper; `searches.jsonl` was written by msearch.py.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact blueprint tag, tensor naturality, tensor transpose and tensor-formula/comparison names, including the six-functors finite-coefficient files. No declaration states the entire item. The derived lower-star projection counit formula in `SixFunctors/ProEtale/FiniteCoefficient/Derived/LowerStarProjection.lean` is for ordinary pullback/direct image, not the exceptional compact-support tensor transpose, so it is not an attachment.

## WANTED

None.

## Defects and changes

The imported item had no proof. Its mathematical statement is correct and is unchanged. The source's claim of naturality is expanded into the actual coefficient-square calculation, rather than justified by the word canonical. In particular the inverse projection formula has the correct direction, the counit is fixed at the unit object, and naturality of the left unitor finishes the calculation. The last step uses both source and target naturality of the specified relative Hom bijection.

I read GOAL.md, the chapter/unit records and the three blueprint levels in SETUP.md. This item implements only the coefficient-naturality part of the first sentence of the ancestor proof; it does not replace any diagonal/deformation/model-agreement step of the unit. Generic tool uses are explained in split_report.tool_uses. No unit record needs editing because this created item is not the unit's key statement.

The sandbox initially had no item, report or searches; there was no earlier split or delivery to repeat. All current searches were run through the prescribed msearch.py command and their recorded results were read. The inherited Q90 searches were retained as inherited records, not represented as new Q80 calls. Two different semantic phrasings return exponentiable-morphism evaluation/coevaluation facts; Loogle finds Adjunction.homEquiv_naturality_right; LeanSearch finds counit/unit naturality. I read the left/right Hom formulas at Mathlib/CategoryTheory/Adjunction/Basic.lean:226-240 and the finite-coefficient projection source. These supply general categorical ingredients, not a one-line proof of the whole projection square for the specified exceptional map. The grep hits concern comonoid counits and monoidal-functor comparisons. All services answered successfully in this dispatch.

## Not duplicates

No new nodes were created. Searches of the whole DAG and blueprint for tensor formula, projection, projection-and-counit and tensor transpose found the existing ingredients reused here; no blueprint node states precisely this coefficient-square assertion. `same_as` remains empty. The tensor formula theorem also asserts invertibility and base-change behavior and is not the same statement. The existing source projection lemma has a different adjunction, as explained above.

## Review by Q80

I read coord/delivery-errors.md B through E in both occurrences, then compared the four proof steps with the open dependency statements. For the item I read `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-smooth-purity/prop-pur-smooth-purity-naturality-cover.proof.md`, especially its first sentence. For the generic tools I read the master source statements/proofs for thm-sf-ambient-adjoint-class, fix-prop-projection-formula, thm-sf-preservation-class, lem-sf-pullback-tor-amplitude and lem-sf-tensor-ctf, together with the current DAG statements. I also read Stacks Tag 0FPT, `sites-cohomology.tex`, label lemma-symmetric-monoidal-derived, and the derived-tensor construction at Tag 06YU, label definition-derived-tor, underlying the native symmetric tensor tool. Stacks 0B65, categories.tex, label lemma-transformation-between-functors-and-adjoints, was checked as background for transposes; it is not substituted for the relative Hom-domain theorem. There are no new nodes requiring separate source reviews and no SGA source is used.

In Step 1 thm-sf-preservation-class(1) really gives bounded constructibility of the exceptional image of A_Y; its base is the required separated finite-type scheme over the algebraic closure of the finite field, with ell invertible. The constant coefficient unit has Tor interval [0,0]. Lem-sf-pullback-tor-amplitude really gives finite-Tor bounded constructibility of M_K and M_K', and lem-sf-tensor-ctf(i) really permits the other tensor factor to be merely bounded constructible. Thus the tensor sources belong to the very bounded constructible domain of the item's relative Hom bijection. I do not infer boundedness from finite Tor amplitude alone or assume purity. Def-pur-co-smoothness gives exactly the displayed composite and its specified transpose; I use its map construction, not an assumption that f already satisfies its three cohomological-smoothness conditions.

In Step 2 the generic ringed-site derived tensor is symmetric monoidal by the cited native-tensor statement, so its symmetry is natural. The small pro-etale site with the constant commutative coefficient sheaf is a ringed site in an adequate sheaf universe, and has the usual additive module sheafification. Fix-prop-projection-formula explicitly covers a bounded constructible first input and finite-Tor second input and explicitly says natural in both. Therefore it applies with Omega as first input without first knowing Omega is an invertible Tate line. Multiplication by the two inverse projection isomorphisms proves precisely the inverse naturality equation written in the step. Functoriality then proves the b-square, rather than taking that square as another lemma.

Step 3 uses just tensor interchange and unitor naturality supplied by that same symmetric monoidal structure. I checked the source and target of each factor: e maps F(Omega) to A_Y, so the interchange square has target A_Y tensor K', and the unitor then has target K'. Substituting Step 2 into the defining composite proves the coefficient square with its exact order of composition. Its elementary flag refers to this displayed three-line substitution, with the structural facts cited, not to an uncited sheaf theorem.

In Step 4 thm-sf-ambient-adjoint-class(2) explicitly states a natural Hom bijection and expressly includes bounded constructible source inputs. These are the inputs verified in Step 1, with bounded targets K and K'. The compactification is the one already defining the specified compact-support functor and its relative transpose. Source naturality uses t:T_K to T_K', target naturality uses u:K to K'; both sides therefore belong to Hom(T_K,H(K')). Applying one and the same bijection proves the assertion; its injectivity proves the converse. This does not assert an adjunction on arbitrary unbounded pro-etale objects. The ten quotes in citations.json were tested as literal substrings of the statements, not of their proofs.

I tested the equations with u an identity and a zero morphism, with K or K' zero, with an empty source, and for f the identity (relative dimension zero). The equations reduce to the usual identity or zero composites; for f=id the map is the unit tensor identification. Shifted complexes retain the natural Koszul symmetry already present in the fixed construction, so no extra sign is introduced when a degree-zero derived morphism u is moved across it. The integer d is never used in the calculation. No additional smooth-purity or Tate-orientation hypothesis was added.

For C1/C4 every non-elementary operation-domain or naturality fact has an existing cited statement and a matching quote. For D the proof contains the actual b-square, counit/unitor substitution and Hom transpose, with no relabelled clause node. For B there are no new node schemas or duplicate nodes to audit; original metadata and inherited searches remain intact, and only real Q80 calls were appended. For E the coefficient category, finiteness hypotheses, inverse-map directions and bounded relative-adjunction domain agree throughout. I checked locally that none of the main tool dependencies reaches this item. Each proof step is shorter than 2000 characters and contains no hidden independent comparison lemma.

## Unfinished work

No mathematical step is left open in this split. Server dry run and direct push are the remaining delivery actions; their outcomes are recorded by the delivery tools.

## Delivery checks

The first dry run stopped before pushing because the projection-formula quote was under 40 characters. I expanded it to include the specified projection isomorphism and coefficient-naturality clause verbatim. The proof and statement did not change.
