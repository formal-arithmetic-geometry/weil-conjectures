## Worker report

Files written under dag/nodes/sec-deligne-laumon-a1/:

- lem-per-regular-potential-pullback.json: item, split into seven steps; statement unchanged.
- lem-per-regular-closed-support-base-change.json: statement, unsplit; no Mathlib match.
- lem-per-regular-specialization-geometry.json: statement, unsplit; no Mathlib match.
- lem-per-general-costalk-transitions.json: statement, unsplit; no Mathlib match.
- lem-per-regular-pinnings-low-base-codimension.json: statement, unsplit; no Mathlib match.

Attachments: none. The source search found no project declaration with the item's blueprint tag or its potential/putative-dualizing assertion. The upstream LocalizationBaseChange module constructs supported comparisons and proves boundary compatibility; it does not assert that the comparison is invertible for an arbitrary regular morphism. It is not an attachment for either this item or the general supported-comparison node.

WANTED: none. I used the retained ilo.txt, checked against the named exposition in the repository. The previous attempt had an unchanged item and this source extraction, but no report or split. Its five Mathlib search records were retained and their returned declarations read. Each new node has its own searches through msearch.py; exact queries, returned hits and verdicts are recorded, with two semantic phrasings. No search was invented or repeated merely because of the interruption.

The item correctly distinguishes ordinary regular pullback from finite-type exceptional pullback. The proof now constructs the maps, checks their Gysin normalization, and uses the source's specialization square to prove potentiality. The four new inputs are general support base change, coefficient-free geometry, general transition calculus, and the genuine base-codimension-at-most-one comparison from XVII 4.3.2.1. The last is not the full potentiality clause: an immediate specialization upstairs can have image of larger codimension, and steps 5–6 supply the missing general argument. Every new node has statement only, empty proof and proof_deps, and the item's precise blueprint ancestry and place. None is a new definition or Mathlib leaf.

Unfinished work: the four new source-level statements are intentionally unsplit for subsequent workers. No missing part of this item's one-level split remains.

## Not duplicates

lem-per-regular-closed-support-base-change vs lem-per-ind-etale-closed-support-base-change: the existing statement requires an affine locally ind-etale map; the new statement permits arbitrary regular maps and does not require affineness or an ind-etale presentation. Neither is replaced by an arbitrary flat base-change claim.

lem-per-regular-closed-support-base-change vs lem-per-regular-pullback-pinnings: the existing theorem is for a pinned potential input and its selected fibre costalks; the new theorem is for every bounded-below input and every closed subscheme, with canonical mate and pasting assertions.

lem-per-regular-specialization-geometry vs lem-per-immediate-specialization-criterion: the existing statement compares geometric and Zariski immediacy on one scheme; it gives no generic-fibre lifts, commutative square, uniqueness of those lifts, or relative codimension formula.

lem-per-general-costalk-transitions vs lem-per-trait-residue-model: the existing statement constructs the codimension-one trait residue; the new theorem provides arbitrary-codimension, factorization-independent compositions on any excellent scheme and their supported-composition compatibility.

lem-per-general-costalk-transitions vs def-per-potential-dualizing: the definition fixes codimension-one residue transitions and states the pinning condition; it does not assert the independence or transitivity theorem in higher codimension.

lem-per-regular-pinnings-low-base-codimension vs lem-per-regular-pullback-pinnings: the existing theorem's literal hypothesis requires regularity after every field extension, whereas this node uses the item's finite-extension test. This difference matters without a finite-type assumption; see the hypothesis issue below. The new statement is precisely the low-base-codimension comparison needed on the lifted top edges, not a renamed full pullback theorem.

lem-per-regular-pinnings-low-base-codimension vs lem-per-potential-extraordinary-pullback: the latter concerns compactifiable finite-type exceptional pullback and transcendence-degree normalization, not ordinary pullback with fibre-local codimension.

Before creating the nodes I searched the whole DAG by source places 4.2.3, 4.3.2.1–4.3.2.6, 3.1.2 and concepts (regular base change, supported comparison, costalk transitions, geometric specialization), and searched the whole imported blueprint with blueprint_refs.py for potential dualizing, regular, supported, closed support, regular base change, dimension function and specialization. The matching regular-immersion, trait, and inverse-image nodes have different hypotheses or conclusions as just described. The corresponding project Lean searches gave no exact statement. Mathlib's Flat.generalizingMap only gives a topological generization lift, not the geometric-point square or codimension identities; stalkSpecializes_comp concerns ordinary stalks, not normalized costalk residue maps with shifts. Algebra/Homology/LocalCohomology.lean:70–145 concerns Ext-colimits of modules over a ring, not etale supported base change. These hits are not one-line specializations of the new statements.

## Existing-node hypothesis issue

The overlapping lem-per-regular-pullback-pinnings says that *every* field extension gives a regular fibre, while this item and ILO use the finite-extension criterion. I did not silently strengthen this item's hypothesis or edit the other worker's node. For example take characteristic-zero k, L=k(t_1,t_2,...) and Spec L -> Spec k. Both fields are excellent, the map is regular in the finite-extension sense, but L tensor_k L is not Noetherian: the diagonal ideal modulo its square is Omega_{L/k}, an infinite-dimensional L-vector space. Thus the fibre after the extension L/k need not be a regular scheme under the DAG's Noetherian definition. The existing stronger-worded theorem cannot simply be applied here. The final split does not cite it or use a general existence theorem to infer the dimension function.

Two harmless source slips were checked rather than repeated: XVII 4.3.1.2's fibre in its proof is over x=f(y), and XVII 4.3.2.4's fibre-generic point belongs to the source of f. Our statements use those correctly typed objects. No target or item statement was changed.

## Review by Q12

I read ILO Expose XIV Proposition 2.5.4 (printed pp.217–218), XVII Proposition 4.1.1 and Remark 4.1.3 (p.280), Corollary 4.2.3 (p.281), Lemmas 4.3.1.1–4.3.1.2 and Remark 4.3.1.3 (pp.282–283), Lemmas 4.3.2.1–4.3.2.6 and the closing 4.3.3 argument (pp.283–286). For the transition node I read Theorem 3.1.2 (p.268) and Proposition 3.5.4 with the ensuing factorization discussion (pp.275–276). For inverse Gysin normalization I read XVII 2.4.1.1 and 2.4.4.1, and XVI 2.5.12 and 3.1.1. All coefficients specialize to n=ell, so the ring is F_ell. All schemes used for potentiality or absolute purity are Noetherian excellent with ell invertible; the general support theorem correctly needs only Noetherianity. I compared every cited node's full statement, and citations.json includes a verbatim quote for every step/node pair.

Step 1 uses the new geometry node's actual codimension identity, the transition node's finite immediate factorization, and the dimension-function definition. Summing the drops is written out. It does not assume a finite-type dimension formula or infer an arbitrary base codimension from an immediate specialization upstairs.

Step 2 uses the general support theorem for an arbitrary D+ input after localizing at x. Its statement includes that exact comparison, not merely a definition of supported sections. For excellence I checked that a fibre ring on charts is a multiplicative localization of B/pB, hence a localization of a finite-type quotient of the excellent chart ring B. The existing excellence permanence node covers arbitrary multiplicative sets, not just localizations at one element. I corrected an early citation to the inverse-image definition, which does not assert exactness: the final proof instead cites the general geometric-inverse-image exactness theorem for modules.

Step 3 uses the regular-unit node at n=1 on a nonempty connected local regular scheme, and its twist/shift clause with m=delta_X(x). The Gysin node explicitly supplies the absolute-purity isomorphism and its localized version. The displayed inverse has target delta_X(x)-c, fixing the sign and both shifts. Supported composition comes from the new general comparison's statement. No potentiality of K is assumed in this construction.

Step 4 uses the Gysin node's regular base-change and composition clauses for closed immersions between regular affine local schemes. The regular map r itself is used only as the allowed change of base, not as a finite-type Gysin morphism. Its product formula is written before taking inverses. This proves the regular normalization without quoting the item's conclusion back to itself.

Step 5 uses the geometry node's actual commutative square, the regular-unit potentiality on the local fibres, and the general transitions node's closed-support and localization compatibility. These are the exact statements needed to compare fibre transitions with ambient transitions; a definition node alone would not give them.

Step 6 uses the geometry node's chain-lifting assertion and the low-base-codimension comparison on each lifted edge. This is why the low-codimension lemma is a genuine smaller input. General transition transitivity identifies the two paths of the square, so cancellation of the three normalized identities proves the bottom edge. I kept the source theorem at the cohomology-map level, not an unjustified derived-map strengthening; the proof explains why equality there suffices for the already concentrated, one-dimensional F_ell costalks.

Step 7 uses pasting of the actual support comparisons and the regular normalization already proved in step 4. On the fibre over x both constructions apply the same p_x and then the same constant-complex normalization. This handles putative inputs as well as potential ones. Locality follows by restricting these specific maps, not by an unspecified transport.

For the new statements I tested identity maps, empty closed supports, the full support i=id, a field base (codimension zero), a trait base (codimension one), and a smooth affine-space projection at generic and closed fibre points. The codimension identity has the sign c_base+b(target)-b(source); it agrees for a vertical specialization and for a fibre-generic horizontal specialization. Codimension-zero geometric automorphisms are allowed rather than discarded as identity underlying points. The lifting statement promises uniqueness only up to possibly nonunique isomorphism. General transitions are asserted on cohomology exactly as the source does. The low-base-codimension lemma imposes no bound on the upstairs codimension. These checks also rule out replacing an arbitrary-field regular morphism by a finite-type one.

I checked delivery-errors B–E against the files: new nodes are self-contained statement-only inputs with explicit notions, genuine logged searches and blueprint ancestry; all non-elementary facts used by the item's steps are node statements, and none of the new nodes restates the whole item. The elementary arithmetic and cancellation are in the steps. The four new source facts carry the non-elementary specialization and comparison assertions. All seven steps are below 2000 characters, so no long inline argument hides an extra comparison lemma. No SGA source is cited. The two cross-unit tools are declared only in split_report.tool_uses, for the maintainer to review. No live project, Lean source, compiler, or launcher script was modified.

## Resumed validation

The initial dry run rejected the TeX matrix row separators in the specialization square as doubled backslashes (B4). I replaced the matrix by the four named specializations and the equality of their two composites, preserving the same mathematical statement, and updated the corresponding verbatim citations. I compared the item with the current shared copy: its statement, ancestry, chapter and unit remain identical; the shared item is still unsplit.
