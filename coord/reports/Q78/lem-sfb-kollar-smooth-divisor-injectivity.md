# Q78: lem-sfb-kollar-smooth-divisor-injectivity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-kollar-smooth-divisor-injectivity.json`: item, split; original statement and statement dependencies retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cyclic-root-cover-eigenforms.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-hodge-first-differential-zero.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-line-module-serre-duality.json`: new statement-only node, unsplit; no Mathlib match. “Line module” here means invertible sheaf on an arbitrary-dimensional projective scheme, not projective space of dimension one.
- `citations.json`: verbatim statement quotations for every citation of every item proof step.
- `searches.jsonl` and the four `*.search-results.json` files: actual search log and full returned hits. The existing Q27 searches in the item were retained; Q78 ran additional searches.

No Lean, repository, unit, chapter, or launcher file was written. No compiler or Lake was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, Kollár/Kollar, Kodaira, cyclic/root covers, Hodge and coherent Serre duality. The Kollár declarations concern the local-ring dichotomy, not this theorem. The existing Serre-pairing files concern curves or twists on projective space, not arbitrary smooth projective schemes and arbitrary invertible sheaves. No matching sorry-free declaration was found for the item or the new inputs.

## Sources wanted

WANTED: Mihnea Popa, *Kodaira dimension of algebraic varieties*, section 1.6 opening paragraph (printed p.22), Definition 1.6.3, Lemma 1.6.4, Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7 (printed pp.23--27), for lem-sfb-kollar-smooth-divisor-injectivity, lem-sfb-cyclic-root-cover-eigenforms and lem-sfb-hodge-first-differential-zero. The named local PDF is absent. I read these places online at the author's [Harvard notes](https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf); I did not download or add a document. The assembly is therefore explicitly marked agent-written, and source entries preserve the local WANTED status.

For Serre duality I read the local `literature/stacks-project/duality.tex`: `lemma-duality-proper-over-field` (Tag 0FVV), `remark-coherent-duality-proper-over-field` (Tag 0FVX), and `remark-rework-duality-locally-free-CM` (Tag 0FW0). I checked those tag-label correspondences in `literature/stacks-project/tags/tags`. For logarithmic residues I also read the local `derham.tex`, `lemma-log-complex` (Tag 0FMW), including its local construction of the residue map.

## What needed attention

The item had a statement and earlier searches but no proof. No statement correction was necessary. The statement is the smooth-divisor input to the already split Kodaira argument, not a reformulation of Kodaira vanishing with an ampleness hypothesis.

Two potential gaps in an informal account are made explicit. The root cover need not be connected, and the Hodge input is stated accordingly. The universal derivation and its eigensheaf blocks are F-linear rather than O-linear. The cover node includes the finite-morphism cohomology comparisons and their compatibility with those F-linear maps; the assembly does not infer this compatibility merely from a decomposition of O-modules.

The residue computation fixes the normalization unambiguously: residue composed with the character-one connection is restriction divided by m; thus restriction is m times that composite. Characteristic zero makes m invertible. The theorem is kept over the given algebraically closed field, without an unjustified embedding of that field into C.

The item's inherited blueprint ancestry is broken upstream: `tools/blueprint_refs.py ancestor lem-sfb-kollar-smooth-divisor-injectivity` prints `blueprint.from.node = None`. I retained that null root and the inherited explicit place/via chain; each new node prepends this item to via and identifies its own supporting argument in place. This does not invent a blueprint ancestor. Searches of the entire DAG, latest blueprint, and `blueprint_refs.py search` found no same-statement blueprint node. The chapter and unit route is unchanged; this is the Popa injectivity prerequisite of the existing characteristic-zero Kempf/Kodaira branch.

## What remains

This is a one-level stage-1 split. The three new non-Mathlib statements remain unsplit for later workers, with no proof steps or hidden proof sketches in their statements. Their intended arguments, to preserve the source reading, are as follows. The root algebra is locally A[t]/(t^m-u), free on 1,t,...,t^(m-1); at the branch divisor the smooth coordinate u and the equation t^m=u give the smooth chart. The character-one differential is obtained from m t^(m-1)dt=du. More generally the character-a formula follows from d(bt^a). Finite affine Cech calculations give the cohomology comparison, natural even for F-linear differentials. Those calculations, smoothness/projectivity and comparison compatibility belong to the cover node's future split, not to a claim of elementary work here.

For the Hodge node, over C the first Hodge-to-de Rham differential is zero (equivalently, harmonic representatives are closed), with the algebraic/analytic comparison. For arbitrary characteristic-zero fields the scheme and the finite data descend to a finitely generated field over Q, which embeds into C; coherent cohomology and differentials commute with extension of the ground field, and faithful extension detects the zero map. A finite disjoint union of geometric components causes no issue. These are genuine non-elementary future dependencies of that node; the item cites the complete Hodge input rather than pretending to prove them inline. Serre duality follows from the smooth proper dualizing object and the natural pairings in the listed Stacks places; its future split must supply those comparisons. Nothing required for the present assembly remains unaccounted for.

## Not duplicates

lem-sfb-projective-line-module-serre-duality vs lem-sfb-flag-line-equivariant-serre-pairing: the existing node assumes a semisimple group's complete flag variety and homogeneous line bundles and asserts equivariant pairings with a canonical-character identification; the new node treats arbitrary smooth projective schemes and arbitrary line-module morphisms, supplies their transposition/naturality and all degrees, and makes no equivariance or flag-character assertion. The flag-specialized statement cannot supply this input on the arbitrary Y of the item.

lem-sfb-projective-line-module-serre-duality vs thm-sc-serre-duality-curve: the existing theorem is restricted to dimension at most one; the new node is arbitrary-dimensional.

lem-sfb-projective-line-module-serre-duality vs lem-sc-smooth-proper-relative-dualizing-general: the existing node identifies the derived dualizing object; it does not state the functorial complementary-degree cohomology pairing. The new node is that numerical/cohomological duality consequence, not another identification of derived objects.

lem-sfb-cyclic-root-cover-eigenforms vs lem-sbc-regular-divisor-root-model-normal: the existing node treats the normalization of a Kummer root model after an etale-local base change in the smooth-base-change setting; it supplies neither the global line-bundle algebra nor the logarithmic eigensheaves and cohomology maps used here.

None of the three nodes restates the item or asserts its injectivity conclusion: the residue, exact-sequence and transposed-surjection arguments are carried in the item's proof. No new node with tag 0FMW already exists. The duplicate gate's shared tag 0FVV is explained by the flag-pairing comparison above.

## Review by Q78

I read the source proof of the item in Popa 1.6.6 together with 1.6.5 and 1.6.7, rather than inferring an argument from the theorem title. I also read the characteristic-zero scope paragraph on p.22. I checked all three new statements against the sources listed above and searched the whole DAG and latest blueprint before creating them. Each new node has introduced objects, inline meanings for logarithmic forms, the root algebra, line duals and negative-degree cohomology where needed, and citations to the existing definitions it uses. The displayed root cover is a real construction from s, not data chosen from a bare existence theorem.

Step 1 cites the zero-scheme definition's exact image-ideal formula and the integral-scheme definition's affine-domain condition. Nonzero local representatives inject into the common function field, so they are nonzerodivisors; the argument and empty-divisor case are written out. It uses neither a hidden smooth-divisor theorem nor an ampleness assumption. I checked the complete statements of both cited nodes.

Step 2 uses precisely the smooth projective root cover, character cohomology comparisons and F-linear differential compatibility stated in the new cover node. Its other citation states that the whole first Hodge differential vanishes for smooth projective schemes over any characteristic-zero field, with no connectedness hypothesis. Thus projecting the zero map to the a=1 summand is justified. Neither citation takes the desired injectivity as a hypothesis or conclusion.

Step 3 uses the actual local formula for nabla_1 and the actual residue formula in the cover node. Their composite sends b to b/m modulo u. This is an explicit local calculation and hence elementary once those stated formulas are available. I checked the direction of the scalar and did not introduce a separate node for this calculation.

Step 4 uses the long exact sequence explicitly stated in `pqf-def-cohomology`, not merely the name of a derived functor. The short exact line-module sequence is proved locally in the step, using the nonzerodivisor established in step 1. Exactness at the middle cohomology group and the zero restriction map give surjectivity, including q=0. This citation is recorded as a generic off-unit tool because the ctf-stability unit does not provide coherent Zariski cohomology's long exact sequence.

Step 5 uses the new Serre-duality node's full naturality clause, not just the existence of pairings. I checked v's source and target, its dual's direction, and that local multiplication is by the same function u. For j at most n, the complementary degree is n-j and is nonnegative. Precomposition with the surjection is injective by the one-line functional argument given. For j greater than n, the node explicitly gives zero source; no unproved dimension bound is silently used.

For edge cases I checked n=0 (a nonzero section on the geometric point has empty divisor, handled before the cover argument), D empty in every dimension (multiplication is an isomorphism even for torsion L), m=2 (the character-one block is present), arbitrary disconnected root covers, and j=0, j=n, j>n. For the new duality statement I also checked dimension zero, disconnected smooth projective schemes and zero bundle morphisms. The Hodge statement allows the empty scheme and extension fields too large to embed in C, and does not assert a false characteristic-p result. All non-elementary item steps cite supporting statements that actually give what is used; the longest step is 677 characters, so no step exceeds the 2000-character review threshold. I checked sections B--E of delivery-errors against the final files, preserved the original statement and bookkeeping, and verified that every citation quote is a verbatim substring of its node's statement. Mathlib searches include two semantic phrasings, Loogle, source grep and LeanSearch for all three new nodes and the item; all returned hits were read and none is a match. No service failure was recorded as absence.
