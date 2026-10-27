# Stage-1 delivery: lem-sfb-split-torus-normalizer-quasi-affine-quotient

## Files written

All paths below are inside the Q153 item sandbox, never the read-only repository.

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-normalizer-quasi-affine-quotient.json`: item split into eight steps; statement, statement dependencies, inherited searches and blueprint provenance retained; source pointer clarified.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-finite-torsion-normalizer-detection.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-diagonalizable-normalizer-smooth.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-diagonalizable-subgroup-parameter.json`: statement, unsplit; no Mathlib match.
- `citations.json`: one entry for every node cited by every numbered step, quoting its actual statement verbatim. Full statements are retained so all hypotheses are visible.
- `searches.jsonl`: twenty actual search invocations, five for the item and five for each new node, including two semantic phrasings, LeanSearch, Loogle and Mathlib grep. `write_split.py` is the sandbox-only reproducibility script.

There are three new nodes, zero new Mathlib leaves. None of the new nodes has proof steps, proof dependencies or a proof origin.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, normalizer, transporter, torus and the quotient notions. The Hopf-ideal normalizer declaration concerns preservation of the Zariski closure of an abstract linear subgroup; it does not construct a relative quotient or the finite-subgroup parameter functor. The source contains no exact project declaration for the item or the new inputs. No sorried declaration was counted as finished.

## Wanted literature

WANTED: Brian Conrad, *Reductive Group Schemes*, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, as `literature/conrad-reductive-group-schemes.pdf`, Proposition 2.1.2 (printed pp.56-58), Theorem 2.3.1 (pp.67-71), Lemma 2.3.4 (pp.69-70), for the item and the three new nodes. I read the online PDF; I downloaded nothing into the repository. Since the local copy is absent, the reconstructed assembly proof is explicitly marked `proof_origin.by = agent`. The specialized structural statements have no Stacks tag; the general geometric tools have the precise tags and TeX labels in their existing nodes. No SGA source is used or cited as an input.

## Audit of the imported material

The imported statement is correct and unchanged. It does not assume maximality, reductivity, connectedness, a field base, Noetherianity, or invertibility of a chosen torsion level. Its proof was empty. I clarified the source pointer: Remark 2.3.5 concerns open immersion of the orbit maps, whereas smoothness of G -> X follows from Proposition 2.1.2 and torsor descent. The inherited blueprint provenance remains untouched. The source's blanket Noetherian reduction must preserve the chosen split torus and its embedding: the new finite-torsion detector states the universally valid conclusion over any ring, rather than silently assuming the original base Noetherian.

The original blueprint provenance has `from.node = null`. The prescribed `blueprint_refs.py ancestor` command confirms that there is no imported ancestor. I retained this fact and its full `via` chain, and appended exact source-proof places for all three new nodes. Searches of the whole imported blueprint for normalizer, finite subgroup, finite torsion, finite diagonalizable, diagonalizable, multiplicative type and twists of subgroups found no matching statement. The current literature source is `literature/blueprint/latest/`; no older snapshot was used as the active blueprint. The chapter and unit records were read and are not changed: this is a supporting item, not the unit's key theorem.

The proof does not simply cite a new normalizer-quotient theorem. Its substantive assembly is the free quotient, the conjugation monomorphism, schemehood, the quasi-compactness argument needed for Zariski Main, descent of smoothness, and gluing over all affine opens. The parameter input concerns all abstract forms of a finite diagonalizable subgroup, not its conjugacy orbit or the quotient in the item. The smooth-normalizer input contains no quotient assertion. The torsion detector concerns equality of stabilizer functors and does not construct a quotient.

## Not duplicates

lem-sfb-split-torus-finite-torsion-normalizer-detection vs lem-sfb-torus-torsion-joint-injectivity: the existing node proves joint injectivity of Laurent quotient maps; the new node provides one finite level detecting conjugation on all base changes, using a finite-presentation Noetherian model and stabilization.

lem-sfb-split-torus-finite-torsion-normalizer-detection vs lem-sfb-finite-jet-normalizer-detection: the existing node uses infinitesimal neighborhoods of an identity section of a smooth connected subgroup; these neighborhoods need not be subgroup schemes. The new node uses the actual finite diagonalizable subgroup T[n], which can be fed into the finite-subgroup parameter scheme.

lem-sfb-split-torus-finite-torsion-normalizer-detection vs lem-sfb-relative-smooth-subgroup-normalizer: the latter represents a normalizer and proves base-change compatibility but gives no detecting torsion level.

lem-sfb-diagonalizable-normalizer-smooth vs lem-sfb-relative-smooth-subgroup-normalizer: the existing statement explicitly imposes no flatness or smoothness assertion about the normalizer, and assumes a smooth geometrically connected subgroup. The new node gives smoothness for split diagonalizable subgroups, including finite nonreduced ones.

lem-sfb-diagonalizable-normalizer-smooth vs lem-sfb-cartan-containing-normalizer-smooth: that statement is over an algebraically closed field and concerns a subgroup containing a maximal-torus centralizer. The new input works over any ring and for arbitrary split diagonalizable subgroups.

lem-sfb-diagonalizable-normalizer-smooth vs lem-sfb-torus-normalizer-components: the existing result is a geometric-field identity-component assertion and does not give arbitrary-base representability and smoothness.

lem-sfb-finite-diagonalizable-subgroup-parameter vs lem-sfb-finite-torsion-hom-parameter: the existing node parametrizes homomorphisms from torus torsion to a split torus by a finite constant scheme; the new node parametrizes subgroup images in an arbitrary smooth affine group scheme, modulo abstract automorphisms of the finite diagonalizable source.

lem-sfb-finite-diagonalizable-subgroup-parameter vs lem-sfb-maximal-torus-parameter-scheme: the existing node concerns maximal relative tori inside a reductive group; the new node concerns finite diagonalizable groups and their abstract forms in a smooth affine group, without maximality or reductivity.

lem-sfb-finite-diagonalizable-subgroup-parameter vs lem-sfb-split-torus-normalizer-quasi-affine-quotient: the parameter scheme also contains finite subgroups outside the given conjugacy orbit, and the item still needs a separate orbit monomorphism, quotient theorem, schemehood and quasi-affineness argument.

## Review by Q153

I read Conrad's Theorem 2.3.1 and its proof on printed pp.67-71, Proposition 2.1.2 on pp.56-58 and Lemma 2.3.4 on pp.69-70. The finite-torsion node keeps the full universally quantified scheme-test assertion from the proof's first reduction; the smooth-normalizer node is Proposition 2.1.2 specialized to H = D(M); the parameter node is the fppf-form formulation of Lemma 2.3.4. Forms are abstract group isomorphisms, not conjugacies. I checked the equivalence with the source's geometrically fixed multiplicative-type functor: its Cartier dual is locally constant finite, and its given fibre isomorphism type is that of M. Conversely an fppf form has those geometric fibres. Nothing assumes an etale torsion group when the characteristic divides its order.

I opened the statement of every cited dependency and checked it against each step. The general tools were also read in the local Stacks TeX: 06PH (`bootstrap.tex`, `lemma-quotient-free-action`), 0463 and 03XX (`spaces-morphisms.tex`, the monomorphism and schemehood labels), 06EW and 0429 (`spaces-descent.tex`, local finite type on the source and smooth descent), and 01LH (`constructions.tex`, `lemma-relative-glueing`). The remaining tool statements explicitly provide the hypotheses and conclusions taken below.

1. The normalizer node applies to M = Z^r. The torsion detector supplies n uniformly for all tests, not just over the original ring or its geometric points. The base-change nodes supply smoothness, finite presentation and closedness on every affine U. The displayed group-algebra quotient identifies H with D((Z/n)^r).
2. The free-action quotient node gives an algebraic space, a flat surjective locally finitely presented map, local sections, and its exact kernel-pair isomorphism. I checked the left-action formula a.g = g a^{-1}; its orbits are the right cosets required in the item. I corrected the draft here to cite `lem-pc-smooth-flat` for smooth implies flat and locally finitely presented, rather than asking a definition of flatness to provide a theorem.
3. The parameter node actually represents closed subgroup images, so the conjugation map lands in it. Its statement does not identify the orbit with the whole parameter space; the proof never makes that identification. Local lifts come from step 2, equality of images gives h^{-1}g in N(H), and the detector identifies this with N(T). Sheaf separation then proves monicity. The sheafification citation is used only for its universal property.
4. The finite-type cancellation statement explicitly includes local finite type without a separation assumption. The fppf source-descent statement applies to representable stack maps, hence to algebraic spaces viewed as discrete stacks. It requires precisely the flat, lfp, surjective q already obtained. The monomorphism node supplies separatedness and chartwise local quasi-finiteness. The schemehood node allows an arbitrary scheme target; no Noetherian hypothesis is inserted.
5. Quasi-compactness of X_U follows by the written open-cover argument and surjectivity of q. The scheme source-descent node gives local finite type over U. The canonical quasi-affine embedding node explicitly states separatedness of Y, so the relative diagonal over U is closed by the cited closed-immersion base-change statement. The finite-type-to-separated-target node then gives quasi-compactness of j; it was not inferred merely from monicity. All four hypotheses in the Zariski Main node are now present. This is the original finite-subgroup orbit argument over an arbitrary affine base, not a field-only shortcut.
6. After schemehood, q is an actual fppf scheme cover, so its own pullback trivializes the torsor. The smooth-locality node supplies both arbitrary base change and fppf target descent. The source smoothness-descent statement needs a flat surjective lfp q, which step 2 provides; it needs G_U smooth, which the original hypotheses provide. It does not need q quasi-compact.
7. The gluing node is exactly relative gluing over all affine opens, not merely gluing morphisms into a pre-existing scheme. The quotient sheaves restricted to smaller affine opens are identical, so their representing schemes satisfy its open-restriction and cocycle hypotheses. No intersections of arbitrary affine opens are claimed affine: restriction and compatibility are checked on the full affine basis. The original fppf quotient sheaf is therefore represented after gluing.
8. Quasi-affineness is checked for every affine open, exactly as in its definition node. I cited open immersions are etale and the definition of etale to justify using open covers as fppf covers. Smoothness of the structure map and smoothness/surjectivity of G -> X descend by the existing space-locality statement.

I checked small cases separately. For r=0, T is trivial, every normalizer is G, and the quotient is S; the detector can choose n=1. A central torus also has quotient S. For a noncentral torus, n=1 need not work, so the detector asserts existence, not that every level suffices. For A of characteristic p and n divisible by p, H may be nonreduced; all conditions use scheme functors rather than rational points, and no etaleness of H is asserted. For A with nilpotents, equality is still checked on every W and every further test. The zero ring, empty base, disconnected base, nonconnected G, and nonmaximal T are permitted. Finite presentation, affineness and smoothness remain essential assumptions.

All eight proof steps are shorter than 2000 characters. I checked B1-B10: self-contained statement-only new nodes, definitions or explicit meanings for notions, single TeX escaping, exact source places, actual logged searches, no fabricated unavailable/no-match result, and full blueprint fields. For C1-C8 I checked every cited statement, supplied the missing smooth-flat citation, used statements rather than another node's proof, and declared off-unit generic tools in `split_report.tool_uses`. For D1-D5 the item retains the actual orbit and gluing argument, no new node is its quotient conclusion, and no input depends back on the item. For E1-E7 I checked all hypotheses, the nonreduced torsion case, kernel-pair factor order, scheme rather than point equality, and the necessary quasi-compactness before Zariski Main. No statement dispute or source correction was needed.

## Unfinished work

No step of this one-level split is left unfinished. The three new structural statements are deliberately unsplit for subsequent workers. No Lean file was written and no compiler, Lake or build command was run. Delivery checks and push are performed using only the authorized delivery tool.
