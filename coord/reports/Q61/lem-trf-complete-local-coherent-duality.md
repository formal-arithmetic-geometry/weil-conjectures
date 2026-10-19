# Stage-1 delivery: lem-trf-complete-local-coherent-duality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-complete-local-coherent-duality.json`: item, statement unchanged, eight proof steps, status split.
- `dag/nodes/sec-trace-formula/lem-trf-regular-local-bounded-injective-resolution.json`: statement; no Mathlib match; unsplit.
- `dag/nodes/sec-trace-formula/lem-trf-finite-map-dualizing-transfer.json`: statement; no Mathlib match; unsplit.
- `dag/nodes/sec-trace-formula/lem-trf-coherent-rhom-finite-injective-dimension.json`: statement; no Mathlib match; unsplit.
- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-finite-injective.json`: statement; no Mathlib match; unsplit.
- `citations.json`: a verbatim statement quotation for every node cited in every item proof step.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item id, its `(blueprint: ...)` tag, coherent duality, complete local rings, semidualizing complexes, and regular/injective and coherent/Hom combinations. Its dualizing and biduality declarations concern geometric étale/pro-étale or perfect-complex duality, not ordinary module coherent duality over arbitrary complete Noetherian local rings. No exact project declaration was found. No compiler was used. Upstream master sorry declarations were not used as evidence of completion.

## WANTED

None: every mathematical source used here is available in the local Stacks source.

## What was wrong or incomplete

The assigned item was a statement-only auxiliary node created for semidualizing-RHom conservativity. Its statement correctly packages Stacks 0BFR case (2) and 0A7C, including genuinely unbounded coherent complexes. I have preserved it verbatim. There was no previous sandbox split or report to retain. The existing proof route is retained: complete-local coherent duality is an auxiliary algebraic input beneath the recorded contracting-local-term ancestry, not a replacement for any step of the curve unit.

The existence part is now constructed from a Cohen regular presentation and finite-map transfer; the duality part uses coherent RHom finiteness and the technical evaluation theorem. I did not create separate nodes asserting existence on complete local rings or asserting coherent biduality: those would merely relabel clauses of the item. The four new statements instead provide independent smaller algebraic inputs, each at the generality of its actual source. The elementary scalar-action calculation, canonical-map identification, categorical conclusion and degree bounds remain steps.

The Loogle query `DerivedCategory, MonoidalClosed` had an unknown identifier; this is recorded as unavailable, not mathematical evidence of absence. I reran with `DerivedCategory, CategoryTheory.MonoidalClosed`, which returned zero hits. The grep including `finite.*[Ii]njective` was noisy; the additional narrower dualizing/semidualizing grep in Algebra returned only an unrelated HomotopyFiber docstring. All queries and their actual results are recorded in `searches.jsonl`; the new nodes' records use the exact query texts. LeanFinder and LeanSearch were both run for every new statement with different phrasings, as well as Loogle and grep. Returned Ext-computation, Tor-vanishing and ordinary-reflexivity declarations do not state any new node, even by a one-line specialization. In particular, Baer's injective-dimension criterion still needs a separate regular-local homological argument. One indexed Baer result is absent from this pinned checkout, so no leaf claim relies on it.

## What remains unfinished

Only the four deliberately statement-only child nodes remain unsplit. Their proof ideas belong here, not in those statements: regular-local finite global dimension implies finite self-injective dimension (0AWX); a bounded injective model coinduces along a finite map and derived adjunction identifies the homothety (0AX0); truncating the coherent source far enough computes each fixed Ext group and reduces finite generation to bounded-above pseudo-coherent input (0G4H); the technical evaluation comparison is proved on truncations, with uniform error bounds from finite Tor and injective dimensions (0A69). These are the exact source lemmas awaiting later workers.

## Not duplicates

The whole DAG was searched by `0AWX`, `0AX0`, `0G4H`, `0A69`, by the definitional tags `0A7B`, `0A5S`, `0A67`, and by regular local, finite injective dimension, coherent RHom and biduality terminology. No existing node carries these tags or states the four new statements. Whole-blueprint searches for dualizing, coherent biduality complete Noetherian local, regular local, coherent Hom, finite injective, and each main new lemma tag found no matching blueprint statement. The existing Cohen power-series presentation and pseudo-coherence criterion were reused rather than duplicated.

lem-trf-regular-local-bounded-injective-resolution vs lem-trf-finite-map-dualizing-transfer: the first asserts finite self-injective dimension of a regular local ring; the second transports three explicitly specified properties of an arbitrary complex along a finite map. They share only the expanded definition of bounded injective dimension (0A5S), and the source definition of dualizing (0A7B).

lem-trf-regular-local-bounded-injective-resolution vs lem-trf-coherent-rhom-finite-injective-dimension: existence of a bounded injective representative for the regular ring is different from finiteness of derived Hom cohomology for a given target with such a representative. The shared tag 0A5S only defines that hypothesis.

lem-trf-finite-map-dualizing-transfer vs lem-trf-coherent-rhom-finite-injective-dimension: finite-map transfer proves the scalar-action property and finite injective dimension over a new coefficient ring; coherent RHom finiteness concerns arbitrary unbounded coherent sources over one fixed ring. Their shared 0A5S is definitional.

The evaluation node has no common source lemma tag with any existing node; its general three-input comparison is neither ordinary module reflexivity nor the existing perfect-complex biduality statement.

## Tool uses

The item declares the existing `lem-weil-pbc-cohen-power-series-presentation`, `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion`, and `lem-weil-pbc-bounded-below-injectives-kinjective` as generic tools in `split_report.tool_uses`. Their exact statements supply, respectively, the regular local surjection, pseudo-coherence of bounded-above coherent objects, and K-injectivity of the bounded injective models. This unit has no alternative statement of these generic algebraic tools. Definitions from other units are only notions. No maintainer-owned `tool_uses` or unit binding was changed.

## Review by Q61

I read `dualizing.tex` at 0BFR/lemma-ubiquity-dualizing and 0A7C/lemma-dualizing for the item, including their proofs. For each new node I read its own source: 0AWX/lemma-regular-gorenstein, 0AX0/lemma-dualizing-finite, 0G4H/lemma-finite-ext-into-bounded-injective, and `more-algebra.tex` 0A69/lemma-internal-hom-evaluate-isomorphism-technical. I also read 0A7B/definition-dualizing, 0A5S/definition-injective-dimension, and 0A67/lemma-internal-hom-evaluate to expand every technical hypothesis and identify the canonical map. The new statements contain no proofs or postponed constructions; each introduces its own ring, complexes and hypotheses. The technical evaluation node explicitly defines its finite Tor dimension assumption and good truncations, and identifies derived tensor through a K-flat total tensor model on the one-object ringed site.

For Step 1 I opened the Cohen power-series presentation node and checked its statement really gives a surjection from a complete Noetherian regular local ring, not only a power-series quotient without regularity. Its completeness hypothesis is exactly the inverse-limit completeness already assumed for R. The new regular-local node supplies the bounded injective representative of A[0]. Step 2 reads the exact finite-map transfer statement: R is generated by 1 over A, both rings are Noetherian, A[0] has cyclic finite cohomology, and its actual scalar-action map is invertible. I wrote out evaluation at 1 to establish the last hypothesis, rather than assuming any arbitrary isomorphism of endomorphism objects is the scalar-action map. I opened the existing bounded-below-injective K-injectivity statement and the internal Hom definition; together they justify this computation. The transfer conclusion gives all three properties of Omega and boundedness comes from its bounded injective representative, so no existence-only unknown object is used.

For Step 3 I checked the new coherent RHom statement permits an unbounded K; it asks exactly for finite cohomology in every degree and a finite-injective-dimension coherent target. Both hold, and no boundedness of K was silently added. Step 4 checks all three hypotheses of the technical evaluation node separately: both target inputs equal Omega and have bounded injective models; their derived Hom is R[0] by the scalar-action isomorphism, so tensor with a module is that module in degree 0; and the existing Noetherian pseudo-coherence criterion applies to every good upper truncation of K. I opened that criterion and checked it assumes boundedness above, not boundedness on both sides. The conclusion is the exact displayed comparison needed for double duality. Step 5 uses the map description and naturality in the evaluation node, with scalar 1 acting by the identity, to verify the comparison is the canonical evaluation-adjoint biduality map. It does not infer equality of maps from conservativity.

Steps 6 and 8 use only the previously established natural isomorphism of the double composite to the identity; the opposite functor is therefore a quasi-inverse, and restrictions remain so. In Step 7 I checked the actual existing Hom-complex statement gives degree-n term product Hom(P^p,J^(p+n)); the bounded-injective K-injectivity statement and RHom definition allow J to compute derived Hom. Good upper and lower truncations are explicitly described, so their termwise bounds give the two displayed inequalities directly. This is a short degree-counting argument, not a hidden boundedness lemma. Every proof-step use has a verbatim quotation in citations.json. The proof-dependency set is exactly the union of the uses. No proof step exceeds 2000 characters.

Small cases: over a field the regular-local bounded injective statement takes the ring itself in degree 0; for a DVR it is consistent with the two-term injective resolution. A singular Artinian complete local ring still uses the regular presentation and the transferred dualizing object, so the argument never claims the singular ring itself is dualizing. A finite map may be the identity or have zero target, with the transfer statement still well typed. For K=0 and arbitrary shifts all comparison maps and degree inequalities have the required form; for a complex unbounded in both directions, every upper truncation is pseudo-coherent although K itself need not be, which is exactly why 0A69 rather than its bounded-above variant is used. The coherent-Hom lemma does not claim coherence for an arbitrary non-Noetherian coefficient ring. The evaluation lemma imposes neither Noetherianity nor boundedness on K beyond its explicit truncation condition. These checks found no statement dispute.

I checked delivery-errors B through E: source labels and tags are exact, all notions are cited or defined inline, ordinary-module and sheaf/condensed categories are not silently identified, no unsupported hypothesis is inserted, no new node duplicates an existing/general statement or merely restates the item, and every non-elementary input is a node. The item statement and ancestry were preserved; no Lean, live project file, launcher, chapter or unit record was edited. The sandbox is the only write location.
