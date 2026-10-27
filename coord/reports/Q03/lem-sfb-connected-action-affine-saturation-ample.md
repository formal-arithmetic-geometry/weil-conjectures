# Stage-1 delivery: lem-sfb-connected-action-affine-saturation-ample

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-connected-action-affine-saturation-ample.json: statement unchanged; split into five steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-connected-action-orbit-section-ampleness.json: one new statement-only node, unsplit; not in Mathlib after two semantic phrasings, LeanSearch, Loogle and source grep.
- citations.json: every proof-step citation with the verbatim cited statement.

## Attachments

None. Searched the project's WeilConjectures source by the exact blueprint tag and by saturation/ampleness, Raynaud and action vocabulary. There is no project declaration giving this statement. The torsion-module affine-saturation hit concerns an unrelated algebraic construction. Existing Sheaf orbit lemmas do not give this statement.

## Wanted literature

WANTED: Anantharaman, Schemas en groupes, espaces homogenes et espaces algebriques sur une base de dimension 1, MSMF 33 (1973), printed p.57, proposition quoted in the proof of 4.2.2, for lem-sfb-connected-action-affine-saturation-ample. Read the primary Numdam scan at https://www.numdam.org/article/MSMF_1973__33__5_0.pdf, PDF p.53 (zero-based), printed p.57. The quote applies to smooth actions over a normal locally Noetherian base and gives ample boundary-divisor lines; it assumes neither affineness nor commutativity of the group.

WANTED: Ning Guo, Divisors on coherent schemes and homogeneous spaces, online March 31, 2026 version, Proposition 6.4(b) printed p.15 and Theorem 6.8 printed p.17, for the new orbit criterion and its application. Read https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf. Local archive absent. The proof is marked agent-written because the scans are online rather than in literature/. No document was downloaded into the repository.

## Corrections and limitations

The item's statement is correct against the Anantharaman quote and stays verbatim. A tempting use of the existing normal-group square-power lemma would be invalid: it is only for the action of a group on itself. The Dedekind action-square-power node also does not cover arbitrary-dimensional normal bases. The new orbit criterion specializes Guo Proposition 6.4(b), which explicitly includes component reduction and fpqc descent; these hypotheses are not silently replaced by a square condition. Smooth morphisms satisfy the source's strict (N)-type conditions (flat, locally finite presentation, geometrically regular, hence geometrically normal fibres). Finite type over the Noetherian base supplies the topological Noetherian assumption.

The newest blueprint was read through literature/blueprint/latest (ef6f9619fdbffa59e88528fb56483d76c70258c8). Its direct-image detailed proof (3) retains the compactification/direct-image route. This item is deep in the inherited auxiliary strict-local descent chain; blueprint_refs ancestor returns null, which is preserved rather than inventing an imported ancestor. No chapter or unit file is changed.

## Not duplicates

lem-sfb-connected-action-orbit-section-ampleness vs lem-sfb-connected-action-affine-saturation-ample: the new node concerns a prescribed arbitrary line bundle and affine section opens of its positive powers; it assumes no affine open with a Cartier boundary and constructs no line. The item constructs a specific line from its affine open, after proving the saturation and fibre-density assertions.
lem-sfb-connected-action-orbit-section-ampleness vs lem-sfb-square-action-affine-orbit-criterion: the existing result assumes the square condition and allows an arbitrary affine base and an arbitrary finitely presented acted-on scheme. The new node assumes smoothness of the scheme and a normal Noetherian affine domain base and removes the square condition; this is precisely the component/fpqc devissage of Guo Proposition 6.4, not a one-line specialization of the existing node.
lem-sfb-connected-action-orbit-section-ampleness vs lem-sfb-dedekind-action-boundary-ampleness: that node requires a one-dimensional Dedekind base and an effective Cartier divisor with affine complement, and concerns its associated line only. The new criterion handles any prescribed invertible module and arbitrary dimension of the normal base.
lem-sfb-connected-action-orbit-section-ampleness vs lem-sfb-smooth-normal-affine-boundary-cartier: that existing node constructs a Cartier divisor from a fibrewise dense affine open and asserts no ampleness. It is reused unchanged in step 4.

Before creating the new node I searched the whole DAG by orbit, ampleness, square condition, the source's Proposition 6.4, and affine saturation, and blueprint_refs by saturation, boundary, square, Cartier, orbit, ampleness and orbit criterion. No imported blueprint statement equals it. Existing group-affine-section ampleness nodes are for the group acting on itself. The new node has no Stacks tag shared with existing nodes: its source is Guo Proposition 6.4(b), while the Stacks geometry is reused as existing nodes.

## Review by Q03

I read delivery-errors B--E completely and checked the item and new node against them. I read Anantharaman's printed p.57 quote to confirm the general normal-base/smooth-action statement. I read Guo Proposition 6.4(b), including its geometric-component and fpqc reduction, and Theorem 6.8, whose affine case constructs the boundary line. I also read the local Stacks morphisms.tex lemma-fppf-open (Tag 01UA), lemma-smooth-open (Tag 056G), and divisors.tex lemma-characterize-OD (Tag 01X0). No SGA source is used.

In step 1 I checked the explicit action isomorphism and its inverse, used the smooth base-change clause of lem-pc-proper-base-change (rather than its proper clause), and used the isomorphism clause of smooth-restrict-open-subschemes. The smooth-flat node supplies both flatness and local finite presentation. The ring-level openness theorem applies on affine charts, which is sufficient to prove openness of the scheme map. The open-factorization node is actually a factorization theorem, not just a definition. The group identities prove stability on points after field extension, so no assumption about existence of rational group elements over the base is made.

In step 2 I checked normality using localization-normal-domain, not the normal-ring definition alone. Affine-scheme-qcqs gives quasi-compactness of Spec A. The finite-type-over-Noetherian node applies to Z (and H); the open-Noetherian node then gives quasi-compactness for W. The open-finite-presentation node and separated-quasi-separated node have the needed hypotheses. Smoothness restriction supplies local finite presentation. The restricted diagonal is a base change of the original diagonal and proper-fp-permanence(b) explicitly preserves closed immersions under base change, so no separatedness of an arbitrary nonseparated ambient scheme is silently assumed.

In step 3 I opened all eight cited statements. Surjectivity-base-change supplies the geometric saturation; smooth base change and smooth-geometrically-normal apply after extending the residue field. The component theorem requires finitely many irreducible components on every quasi-compact open, which follows by the open-Noetherian and Noetherian-finite-components nodes of step 2 and this step. Each component is an open subscheme of the smooth fibre, hence smooth; rational-points-dense applies over the algebraically closed field both there and in the nonempty inverse image inside H. Connectedness of H over that field forces its orbit to remain in one clopen component. The resulting nonempty open in each integral component is dense. Surjectivity of Spec Omega to Spec k(t) descends this density topologically. I wrote this component argument in the step, not as a new elementary node.

In step 4 the boundary-Cartier statement explicitly permits a normal base (not merely a regular base), requires fibrewise density, and includes the empty divisor. Every one of those hypotheses was verified in steps 2--3. The divisor-line-properties statement supplies invertibility. The canonical-section-zero-scheme node supplies exactly the global section and its zero scheme; the local coefficient computation shows its nonvanishing open equals U, with no Hartogs assertion or hidden comparison.

In step 5 the new criterion applies to W with the original H and the original normal affine base. The section has exponent one and its affine locus is U, so the criterion's union V contains U and its saturation is all W. This applies a genuine ampleness criterion to a constructed line, rather than relabelling the item's conclusion in a new node. The new node is statement-only, introduces all objects, defines its section-locus union using the existing ample-line definition, and has five actual searches from searches.jsonl. The searches return affine chart/localization results or no hits; none concerns line bundles under connected scheme group actions. No Mathlib leaf is claimed.

Small cases checked: empty U gives empty W and the unique ample line; U=W gives the empty divisor, its canonical section is a basis, and an affine W has ample structure line; the trivial group gives W=U. Disconnected Z and fibres are handled component by component without connectedness of X or a section. No step is longer than 2000 characters. Every used non-elementary result is a cited existing statement or the one new criterion. I corrected an initial citation of the quasi-compactness definition to the actual affine-scheme-qcqs theorem. All citations.json quotes are verbatim from the corresponding statements. No Lean was written and no compiler was run.

## Unfinished

The new orbit criterion is deliberately unsplit as required for one-level stage 1. No part of the item's five-step assembly remains unfinished. The maintainer must archive the requested primary scans independently.

## Validation

The first deliver.py --no-push exited OK at 766a40e21ca. A final local audit corrected the smooth-open tag to 056G and made the diagonal base-change citation and component-finiteness hypothesis explicit; the final dry run below validates these corrections.
