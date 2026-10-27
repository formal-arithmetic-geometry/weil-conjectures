# NY stage-1 delivery: lem-sfb-group-affine-section-ampleness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-group-affine-section-ampleness.json`: item, statement unchanged, four proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-group-square-power.json`: new statement-only lemma, unsplit; no Mathlib match. A positive tensor power satisfies a fully specified relative square condition, without any affine-section or positivity hypothesis.
- `dag/nodes/sec-six-functors-basics/lem-sfb-square-action-affine-orbit-criterion.json`: new statement-only lemma, unsplit; no Mathlib match. For a line already satisfying the square condition on a scheme with an arbitrary smooth connected group action, coverage by orbits of affine section loci implies ampleness. It requires neither normality of the base nor that the scheme be a homogeneous space.
- `citations.json`: six verbatim citation entries covering every use in the four steps.

No Lean, unit, chapter, repository or launcher files were written. The sandbox also contains the actual `searches.jsonl` and a local authoring script. Only DAG nodes and the report/citation delivery inputs are intended for delivery.

## Attachments

None. I searched `lean/WeilConjectures/` by the item's exact tag and by group/ampleness, Picard-admissibility and theorem-of-the-square terminology. The group-scheme ample-family and quasi-projectivity files concern existence over an algebraically closed field, not ampleness of this supplied line over this base. They do not give the item. No proof containing sorry was counted as an attachment.

## Sources wanted

WANTED: Ning Guo, *Divisors on coherent schemes and homogeneous spaces*, March 31, 2026 version, section 5.6, Proposition 5.9 final assertion and Corollary 6.5 (also Corollary 6.6(ii)), for the item and both new nodes; requested repository path `literature/guo-divisors-coherent-schemes-homogeneous-spaces.pdf` is absent.

I read these places online at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . I did not download the source. The item remains marked `proof_origin.by = agent` because its local source is wanted, as the worker brief requires. The assembly argument is explicit rather than a reference to the paper. The new nodes have no proof. No SGA source is used.

## What was wrong or changed

The statement is unchanged; no statement dispute was found. The imported node had no proof. Its source proposes the correct two ingredients, but one must first take a square-condition tensor power and then relate the supplied section to that power. Simply saying 'apply the section criterion' would omit this hypothesis.

Guo 6.6(ii) refers to maximal points of fibres, whereas the item only says the affine locus is nonempty in each fibre. Rather than import an unstated geometric-integrality assertion into that inference, the proof uses Guo 6.5 and proves orbit coverage directly: the maps `(g,u) -> (gu,u)` and `(x,u) -> (xu^{-1},u)` are inverse on the same fibre product. This argument uses neither commutativity nor existence of rational points in the affine open. It does not require a field extension or a translation by a global base section.

The relative square condition is written as an isomorphism modulo a line pulled back from every parameter scheme B. This spells out Guo's section 5.6 notion of Picard-admissibility and does not silently assume the square isomorphism is an absolute trivialization. Using direct translations instead of inverse translations gives the same condition: inversion replaces g,h by their inverses, and the product of invertible-module classes is commutative. No coherence data is asserted.

The imported blueprint ancestry has `from.node = null`; the prescribed ancestor command reports exactly that. I retain this ancestry, append the item to the new nodes' via lists, and give precise supporting places. I read the latest `sk-thm-sf-ctf-stability-direct-images.proof.md`: its part (3) now uses compactification and open direct image. The long inherited alteration/Picard chain is the provenance of this supporting lemma, not a claim that the latest blueprint prints the square criterion. No unit or chapter route is replaced.

## Search results and duplicates

All new-node Mathlib queries were run through the required msearch.py command and their actual log objects are copied into `mathlib_searches`. LeanSearch, LeanFinder, Loogle and source grep all responded. I read every returned hit. Queries were phrased both in terms of Picard-admissibility and in terms of translation/theorem-of-the-square geometry. The hits were ring-level Picard tensor identities, affine basic-open formulas, Proj affine covers, unrelated squares, smooth manifold group sheaves, and convex ample sets. None gives either theorem or a one-line generalization. The geometric source grep on `AlgebraicGeometry` returned zero hits for the decisive names. Item searches likewise found no match. Existing imported search records are retained alongside the new recorded searches.

Before writing nodes I searched the whole DAG for Picard-admissibility, theorem of the square, Guo 5.9/6.5/6.6, group ampleness, geometric integrality and positive tensor powers; and searched all blueprint nodes using blueprint_refs.py for `Picard-admiss`, `Picard-admissibility`, `Picard admissible`, `group action ampleness`, `theorem of the square`, `affine section`, `translation line bundle`, `smooth connected group`, and `tensor power ample`. No matching blueprint statement was found (`affine section` returned only relative affine space). Existing semiabelian and abelian square statements were opened and read.

## Not duplicates

lem-sfb-normal-group-square-power vs lem-sfb-group-affine-section-ampleness: the new node has no section or ampleness conclusion; it supplies the missing square-condition power.

lem-sfb-normal-group-square-power vs lem-sfb-normal-smooth-group-local-ample-line: the existing node produces some local ample line, whereas the new one concerns a power of every supplied line and contains no positivity assertion.

lem-sfb-normal-group-square-power vs lem-sfb-abelian-polarization-calculus: the existing statement is over an algebraically closed field and for abelian varieties; the new statement allows a nonproper noncommutative smooth group over a disconnected normal affine base and asserts existence of an exponent, not a dual abelian variety or polarization.

lem-sfb-normal-group-square-power vs lem-sfb-semiabelian-picard-square-triviality: the latter is absolute multiplicativity of an algebraically trivial line on a semiabelian group over a field; this new node asserts a square condition modulo base lines for a power of an arbitrary line on a relative smooth group.

lem-sfb-normal-group-square-power vs lem-sfb-algebraically-trivial-line-multiplicativity: the latter requires a proper commutative group algebraic space and a fibrewise algebraically trivial rigidified line; the new node requires none of these and concludes only the relative square condition after taking a power.

lem-sfb-square-action-affine-orbit-criterion vs lem-sfb-group-affine-section-ampleness: the new node assumes the square condition and proves an orbit criterion for arbitrary actions over arbitrary affine bases; the item does not assume the square condition, acts on the group itself, and starts with a single fibrewise nonempty locus. The two new inputs are independently meaningful, and neither is a relabelled clause with the item's hypotheses.

lem-sfb-square-action-affine-orbit-criterion vs lem-sfb-normal-smooth-group-local-ample-line: the existing node asserts existence of local ample lines; this one detects ampleness of a specified square-condition line.

lem-sfb-square-action-affine-orbit-criterion vs lem-sfb-semiabelian-effective-square-generation: global generation of a square on a semiabelian variety is neither ampleness nor the relative orbit-cover criterion for arbitrary actions.

lem-sfb-square-action-affine-orbit-criterion vs lem-sfb-smooth-normal-affine-boundary-cartier: Cartierness of an affine boundary does not detect ampleness of a specified line satisfying the square condition.

## Review by NY

I checked B through E of delivery-errors.md against the written nodes and the sources. The new nodes are statements only and introduce their schemes, group operations, action, tensor pullbacks, relative square condition, section loci and conclusion; no purported lemma is hidden in a definition. The item is not disposed of by applying a same-statement node: taking a power, constructing the section of that power, proving orbit coverage, and reflecting ampleness are all carried by its own proof.

For the square-power node I read Guo section 5.6 and Proposition 5.9 including its final normal-integral assertion, rather than its unrelated abelian-scheme first clause. With X=H, the identity gives the required section. Smooth connected group fibres are geometrically integral: connectedness plus the rational identity gives geometric connectedness (Stacks 04KV), and connected group schemes are irreducible (groupoids.tex, Tag 0B7Q, whose source I read); smoothness supplies geometric reducedness. Thus the smooth case is of the strict (N)-type used there. The new node's finite-component version is deliberate: an affine locally Noetherian normal base is Noetherian and has finitely many disjoint open integral normal components. Apply the proposition componentwise and take a common multiple of the exponents. The square condition is preserved by positive powers by tensoring its displayed isomorphisms; the base-line witnesses glue across disjoint components, also after arbitrary parameter base change. This describes the proof route of the statement-only node; these geometric inputs are work for that node's future split, not unstated uses in this item's assembly.

For the orbit node I read the sufficient direction of Guo Corollary 6.5 and its section 6 setup. Smooth finitely presented H is flat finitely presented and universally open, and connected fibres are explicitly assumed. Separated finite presentation of X gives finite type and quasi-separatedness. Every affine section open is quasi-affine, so the source's union of all quasi-affine section loci contains the union in this node. Orbit coverage for the smaller union implies coverage for the source's union. The relative square isomorphism is precisely Picard-admissibility modulo base lines. The affine base makes the conclusion absolute ampleness. No normality, properness or transitivity of the action is used in this criterion. Future splitting of the new node must account for its own flatness/open-morphism and section-algebra inputs.

Step 1 uses exactly the existential square-power sentence of the first new node and the finite-presentation clause of `def-sbc-locally-finite-presentation`, both opened and read. All hypotheses are present verbatim in the item, including the local-ring normality and connectedness. There is no restriction to one connected base component in the assembly.

Step 2 uses the section-locus definition, read in full. The displayed local-frame computation f -> f^r proves equality of the actual open loci; it does not assume preservation of an arbitrary affine open by tensoring. Taking the rth tensor power changes degree n to degree n in A=L^r. Surjectivity of V over T is exactly the supplied fibre-nonemptiness hypothesis. This is an elementary step, not a new lemma.

Step 3 uses the entire statement of `lem-weil-pbc-surjective-base-change`, opened and read, on V -> T and G -> T. It imposes no flatness or finite-type hypothesis. The inverse morphism formula checks all action and multiplication assertions from group identities, and the resulting surjectivity remains true for the larger union U. The elementary flag concerns this short assembly from the explicitly cited surjectivity theorem; it does not declare base-change surjectivity elementary without a citation. This is the one generic tool from another unit and is declared in split_report.tool_uses.

Step 4 uses the sufficient conclusion of the orbit node, with H=X=G, and the definition of ampleness, both opened and read. Normality is not smuggled into the criterion; it was used only to obtain the power. Reassociation turns any affine-locus section of A^k into one of L^(rk), so the reflection direction follows in a few lines from the actual definition and needs no separate power lemma. This also verifies quasi-compactness of G from the ampleness just obtained. The existing `lem-sc-ample-positive-tensor-power` only gives the other direction and is deliberately not cited for reflection.

Small cases: empty T forces G empty and all four steps and both new statements have their vacuous interpretations; r can be chosen 1. A zero section over nonempty T fails the fibre-nonemptiness hypothesis. For affine G with L trivial and sigma=1 the criterion gives the expected ample trivial line. For a positive-dimensional proper abelian variety the section 1 of the trivial line has a non-affine locus and does not give a false ampleness conclusion. Nontrivial invertible modules on a normal affine base pulled back along the identity group also satisfy the relative square condition: their base-line factors are allowed. Finite disconnected normal bases are handled with a common exponent, not one exponent assumed without justification. The multiplication inverse formula holds for noncommutative groups in the order written, and all residue-field powers are valid in positive characteristic.

I checked that each new statement lacks the item's affine-section hypothesis or instead requires an independently supplied square condition, and that neither follows in two or three elementary lines from existing cited statements. Each proof step is below 2000 characters. Every proof use has a verbatim quote in citations.json; the proof-dependency list is exactly their union. No cycles or self-citations are intended. The mandatory server checks and final delivery dry run are the remaining mechanical validation.

## Unfinished

The two new nodes intentionally remain unsplit, as required for a one-level split. No part of the item's proof is left unfinished. The missing local literature copy is recorded above.
