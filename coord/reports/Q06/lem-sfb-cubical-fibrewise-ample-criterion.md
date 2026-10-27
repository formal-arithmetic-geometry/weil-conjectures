# Q06 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-fibrewise-ample-criterion.json`: split item; statement and its full fibrewise hypotheses preserved; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-strict-local-affine-seed.json`: new statement-only unsplit input; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-strict-henselian-fibrewise-section-density.json`: new statement-only unsplit input; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every step/node citation.

Two new nodes, zero Mathlib leaves. The chapter and unit are unchanged. The item is not the unit key statement, so no unit record is written.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the blueprint item tag, cubical/cubist/semiabelian terminology and related theorem-of-the-square terminology found no project declaration proving this criterion. A sorry declaration would not count. No Lean file was written and no compiler or Lake command was run.

## Literature wanted

WANTED: Raynaud, *Faisceaux amples sur les schemas en groupes et les espaces homogenes*, LNM 119 (1970), the relative cubical ampleness argument and its local affine-chart input, for lem-sfb-cubical-fibrewise-ample-criterion and lem-sfb-cubical-strict-local-affine-seed. The path named by the imported item is absent locally. I do not assert that a particular numbered Raynaud theorem states my new seed lemma.

WANTED: Bosch--Lutkebohmert--Raynaud, *Neron Models*, chapter 6 section 6, especially the translation/affine-open argument around Theorem 2(d), for comparison with the agent-written cubical chart-cover argument. This is inspiration, not an extra uncited theorem used in the proof.

The proof is explicitly agent-written. I read Stacks `morphisms.tex`, relative ampleness (Tags 01VH, 01VJ, 01VK), `limits.tex`, `lemma-limit-ample` (Tag 09MT), and `more-morphisms.tex`, `lemma-etale-nbhd-dominates-smooth` (Tag 055U), including its two proofs. The last statement is only about etale-local sections. It does NOT assert my all-geometric-fibre density lemma. The density lemma remains an independently stated unsplit input, not a claimed quotation of Stacks. No prohibited SGA source is used.

## Corrections and scope

The imported statement itself was not changed. It has no properness assumption, so the nearby proper ample-locus and fibre-ample-neighbourhood nodes cannot prove it. I rejected those routes. I also rejected using the generic symmetric ample-extension ancestors: they lead back through this item and would be circular.

An exploratory closed-fibre-only version of the affine-seed input was too strong. For an elliptic curve with split multiplicative reduction over a strictly henselian trait, its connected smooth semiabelian model has generic elliptic fibre and special fibre G_m. The inverse of a positive cubical theta line is negative on the generic fibre but its special-fibre line is trivial, hence ample on that affine fibre. Thus ampleness on the closed fibre alone cannot justify the proposed chart argument. The delivered seed retains ampleness on EVERY residue-field fibre. The discarded search queries are retained in searches.jsonl as research history; the final seed records the subsequent all-fibres queries, not those discarded formulations.

Another correction from self-review was the identification of two strict-henselization constructions. The triples lemma alone does not explicitly identify the affine pointed-neighbourhood limit over V with the algebraic strict henselization of O_(V,t). Step 6 now cites `lem-exc-affine-strict-local-ring-comparison`, whose statement gives exactly that isomorphism and compatibility of the structural morphism.

## What remains

The stage-1 item has a complete assembly argument relative to two new explicitly stated inputs. Those inputs remain unsplit for future stage-1 workers; they are not claimed proved here. In particular the affine-seed existence is the substantive local positivity input left by this split. There is no residual unsupported assertion of relative ampleness in an item proof step.

## Not duplicates

lem-sfb-strict-henselian-fibrewise-section-density vs lem-sfb-smooth-space-cover-etale-sections: the existing statement supplies an etale covering with sections of a smooth surjection; the new statement asserts geometric density of the values of GLOBAL R-sections at EVERY prime of a fixed strictly henselian local base. Etale-local existence alone does not state that density. Both mention Tag 055U as background.

lem-sfb-strict-henselian-fibrewise-section-density vs lem-sfb-projective-frames-pgl: the existing statement constructs projective frame torsors and proves etale-local sections for them; it neither treats arbitrary smooth geometrically irreducible schemes over a strict local ring nor asserts fibrewise density of global sections. Its citation of Tag 055U is for local sections only.

lem-sfb-strict-henselian-fibrewise-section-density vs lem-sfb-trait-specialization-etale-chart-density: the latter lifts prescribed trait objects through an etale stack chart and deduces density of an open substack in that chart, not density of R-sections in all geometric fibres of a smooth family over a strict local base.

lem-sfb-cubical-strict-local-affine-seed vs lem-sfb-cubical-fibrewise-ample-criterion: the new statement produces one global section and one affine nonvanishing open after strict henselization at a single base point. It asserts neither relative ampleness nor a cover of the strict-local family. Steps 3--5 supply the missing cube cancellation and all-point cover, and steps 6--7 descend that result to the original base. This is not a replacement of the item by the same criterion under another name.

lem-sfb-cubical-strict-local-affine-seed vs lem-sfb-normal-cubical-generic-ampleness: the existing generic criterion requires a symmetric line and proper generic fibre and belongs to the ancestor positivity chain. The new local single-chart input keeps all-fibre ampleness, allows toric generic fibres, and has no symmetry assumption.

Whole-DAG searches for cubical positivity, nonvanishing affine charts, strict-henselian dense sections, and the proposed ids found no existing node with either new statement. `tools/blueprint_refs.py search` over the whole imported blueprint found no same statement. The ancestry command returns a null nearest imported ancestor for this support chain; I preserved that result, copied the detailed inherited source route, and prepended the item to each new node's via list.

## Review by Q06

I reviewed the item against its full imported statement, the current blueprint's six-functor constructibility/Picard support route and the local Stacks sources above. The missing Raynaud source is recorded honestly rather than supplied with a guessed theorem number. For the seed, I checked the proposed statement itself, ordinary ampleness's global-section formulation and the all-fibre hypotheses against the negative-theta degeneration test above. For the density input I read both proofs of Stacks 055U: the etale chart and Hensel lifting motivate a stronger separate lemma, but do not permit citing 055U as though it already said density.

Step 1 uses the actual Noetherian localization statement to obtain a Noetherian local A. It takes smoothness only from clause (2) of `lem-pc-proper-base-change`, NOT properness; separatedness and finite presentation come from their respective base-change nodes. The cubical and semiabelian definitions give the termwise base-change data; the invertible-pullback statement gives the actual invertible modules. The triples node states that R is strictly henselian and identifies its residue field, while `lem-sc-strict-henselization-noetherian` supplies Noetherianity. I read each of those statements. Every residue fibre of H_A is an original fibre at a generalization, so all-fibre ampleness really is available for the seed.

Step 2 invokes exactly the new seed's single-section conclusion. Rigidification supplies the scalar e*s; its value outside the local maximal ideal makes it a unit. This is why the chosen affine chart meets every fibre, rather than merely the closed fibre. Finite presentation over an affine base supplies quasi-compactness and quasi-separatedness via the permanence statement.

Step 3 uses the fppf-exact semiabelian presentation to see connectedness: a clopen partition is constant along the connected torus cosets and descends to the connected abelian quotient. The smooth-section component statement then supplies a geometrically irreducible open containing all connected components through the identity; because the whole fibres are connected, this open is the whole family. The density lemma is used with exactly its hypotheses: Noetherian strictly henselian R, smooth separated finite presentation, an identity section, geometrically irreducible fibres. It gives global section values, not merely sections after another base change.

Step 4 is elementary tensor cancellation of the EXPLICIT eight factors in the cubical definition at (x,a,-a). I checked the signs: there are two positive L(x) factors and inverse L(x+a), L(x-a) factors; the identity factors cancel under rigidification. Base-factor triviality uses local rank-one freeness and the fact that an open containing the closed point of a local spectrum is the whole spectrum. The invertible-pullback/tensor node gives the section and fibre formulas needed to identify the nonvanishing open exactly. No theorem of the square or symmetry is silently assumed.

Step 5 cites the affine-cap-section lemma for precisely an affine open intersected with the nonvanishing locus of a section of an invertible module. The new density statement is used on the explicitly written nonempty parameter open (U-x) intersect (x-U). Both opens are nonempty in the irreducible geometric fibre. Thus one global R-section works for that point; varying it covers every geometric fibre and hence X. The definition of ample used here asks for positive tensor powers and affine nonvanishing neighbourhoods of all points on a quasi-compact scheme, exactly what was constructed.

Step 6 uses a SMALL full representative category of affine pointed etale neighbourhoods, as explicitly supplied by the strict-henselization definition, and the affine strict-local ring comparison for the structural-map identification. This repairs C4 rather than relying on the name of the triples lemma. The fibre-product universal property proves the limit of the H_i inline; no extra limit-existence or base-change-commutes-with-limits assertion is hidden. Finite presentation makes each H_i quasi-compact/quasi-separated, maps of affine base schemes are affine, and affine base change preserves that property. The cofiltered reindex statement retains the original terms/transitions. The ample limit lemma is then applied with a fixed stage, a pulled-back invertible line, affine transitions and a small nonempty directed index, matching all its hypotheses.

Step 7 checks EVERY affine open in each affine etale W_t, using affine pullback of ample lines. The ample-local statement does assert descent for a jointly surjective etale family and concludes ampleness on the inverse image of every affine base open in its scheme case. Thus it is applicable here; I did not replace it by a proper-only fibre criterion or use local ampleness without descent.

Small-case checks: the empty base is vacuous; over a separably closed field, smooth-point density includes imperfect separably closed fields by separable closed-point density; rank-zero abelian fibres are permitted, as are pure split tori; the argument does not presume constant toric rank, a proper total group or symmetry of the cubical line. The all-fibres condition is retained even in strict-local reductions. Translations by sections are genuine automorphisms on the whole family. Each step is under 1,200 characters, so none conceals a long >2,000-character subproof. I checked B--E for self-contained statement-only children, complete definitions, exact citations, non-circularity, duplicate avoidance, and the distinction between a substantive input and an elementary construction. Off-unit scheme/line/local-algebra tools are declared in split_report.tool_uses.

All recorded Mathlib searches were actually run through msearch.py and their actual log records are copied into mathlib_searches with exact query text. Both new nodes have two semantic phrasings, Loogle and source grep; LeanSearch was also run. Returned hits about dense rational-map domains, affine-space fibres, smooth algebra descent and structure-sheaf basic opens do not state either node or specialize to them in one line. No claimed Mathlib leaf or invented search result is included. No second agent was started.
