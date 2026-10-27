# Q47 stage-1 delivery: lem-sfb-proper-adjoint-diagonal-pair

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-adjoint-diagonal-pair.json: item, split; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-section-coinduction.json: statement-only input for a closed section of a flat locally finitely presented morphism; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-relative-tor-comparison.json: statement-only input for relative Tor amplitude across the two structure-ring sites; no Mathlib match.
- citations.json: each proof-step citation with the verbatim statement read.
- searches.jsonl: actual msearch results for the item and both new statements. build_delivery.py is the sandbox-only JSON assembly script.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, relative dualizing, diagonal class, proper duality, coinduction, and site-relative Tor comparisons found no project declaration stating the complete item or either new input. The smooth-purity diagonal class uses constant torsion coefficients, not the coherent structure sheaf; it is not an attachment.

## WANTED

None. All sources used are available under literature/stacks-project. No SGA source was used.

## Findings and corrections

The item statement is unchanged and is mathematically consistent. Its sources are duality.tex 0E4L, 0E2P, 0E2Z and 0E4P. The finiteness argument must not use existing Noetherian/smooth diagonal nodes: their hypotheses are too strong. It also must not directly apply the etale affine-unit theorem to Zariski complexes. The new 0DK7 comparison and the existing etale pseudo-coherence descent bridge precisely that gap. No finiteness property is inferred merely from an equivalence of derived categories.

Remark 0E4P explicitly leaves detailed compatibility with the proper-flat right-adjoint base-change maps to be proved when needed. Steps 5-6 supply the normalized counit characterization and mate calculation; citing the remark alone would not establish the last clause. The comparison with derived Hom must identify multiplication by the specified class, not just give some isomorphism of objects. The closed-section coinduction input includes that identification and the evaluation-at-one normalization.

The supplied blueprint ancestor command prints `blueprint.from.node = None`. I preserved the live null ancestor and its via chain, adding the item to the via chain of each new input. I read the latest blueprint files sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The deeper alteration/stable-curve route is recorded in the item's inherited provenance; the present work is its coherent-duality prerequisite, not an alternate route for direct-image constructibility. Blueprint searches for relative dualizing, coinduction, closed immersion, section coinduction, pseudo-coherent diagonal, Tor dimension and Tor amplitude found no blueprint theorem stating either new generic input. Whole-DAG keyword/tag searches and Lean searches were also read before creation.

Mathlib searches: each new node has two semantic phrasings, Loogle, source grep and LeanSearch, recorded from msearch.py. For coinduction the hits were ordinary pushforward as a right adjoint, restriction adjunctions for OPEN immersions, and abstract closed-monoidal internal Hom; they do not identify the extraordinary right adjoint to CLOSED direct image. For relative Tor the hits concerned ordinary etale morphisms/topologies, or unrelated relative functors. A broad case-insensitive grep also returned words containing `tor` (functor, operator); the second targeted grep in AlgebraicGeometry returned zero. No hit states the derived relative Tor comparison. Item searches found ordinary flatness and diagonal morphism properties, not relative duality. The original item's earlier searches were preserved.

## Not duplicates

lem-sfb-flat-section-coinduction vs lem-trf-relative-duality-polynomial-chart: the latter constructs polynomial models of a relative dualizing pair over a locally Noetherian base; the new input identifies closed-section coinduction for arbitrary bounded-below quasi-coherent M, without a supplied pair or Noetherian base.

lem-sfb-flat-section-coinduction vs def-trf-coherent-relative-dualizing-pair: the definition states a predicate on a supplied class; the new theorem identifies the adjunction adjunct with the multiplication map and supplies the derived Hom isomorphism.

lem-sfb-flat-section-coinduction vs lem-trf-relative-dualizing-pair-rigidity: rigidity assumes two supplied pairs over a locally Noetherian base and proves their uniqueness; the new theorem assumes neither pair and treats one closed-section adjunction and arbitrary M.

lem-sfb-flat-section-coinduction vs lem-sfb-proper-flat-families-coherent-adjoint-locality: that theorem gives restriction-to-opens of a proper S-morphism's right adjoint; it does not identify a closed-section adjoint with internal Hom or its multiplication adjunct.

lem-sfb-flat-section-coinduction vs lem-sfb-nodal-dualizing-adjunction-line-comparison: that theorem compares two invertible modules for admissible nodal families over a Noetherian base, and gives no general closed-section coinduction statement.

lem-sfb-etale-relative-tor-comparison vs lem-sfb-etale-pseudocoherence-descent: the existing theorem descends pseudo-coherence, not Tor amplitude over the inverse-image BASE ring. Both are needed separately.

lem-sfb-etale-relative-tor-comparison vs lem-trf-affine-relative-tor-amplitude-criterion: the latter compares Zariski sheaves on an affine scheme with modules over its affine base ring; it does not compare Zariski and small etale inverse-image ring sheaves.

## Review by Q47

I read the Stacks statements and proofs with their hypotheses in view. For the item I read 0E4L (including its relative-perfection argument), 0E2P's pre-rigidity equation, 0E2Z's passage from the diagonal adjunct to internal Hom, Definition 0E2T and the paragraph after it, and 0E4P. For the new closed-section theorem I read 0A9X and 0A77 in duality.tex, and 0695/0683 in more-morphisms.tex: flat locally finitely presented morphisms are pseudo-coherent, and a map between objects pseudo-coherent over the base is pseudo-coherent. Apply this to the section between W and Z over Z. Thus a closed section satisfies the pseudo-coherent closed immersion hypothesis of 0A9X; a general finitely presented closed immersion over a non-Noetherian scheme need not satisfy it. The new input retains bounded-below M, exactly where 0A9X requires it. Under the Hom model the adjunct of h has formula a -> h(1)(a); its A-linear transpose is a -> (b -> h(1)(ab)), namely multiplication by xi. This normalization is included in the statement for the later worker. For the new site-comparison theorem I read spaces-perfect.tex 0DK7 in full: it compares relative inverse-image base rings, not merely absolute structure-ring Tor amplitude. It covers arbitrary schemes and complexes and gives local finite Tor dimension in clause (2).

Step 1 uses the statements of proper base-change stability, pointwise flat base change, and qcqs right-adjoint existence. The remaining finite-presentation calculation is the displayed finite polynomial presentation after tensoring, and qcqs follows from the finite-cover/diagonal definition. Both projection and diagonal have qcqs source and target. The proper-morphism definition supplies the closed diagonal, and the scheme conventions supply the precise finite-presentation convention. These are the statements quoted in citations.json, not stronger material hidden in their proofs.

Step 2 uses exactly proper-flat right-adjoint base change with qcqs affine opens, the Zariski/etale equivalence with its stated direct-image/structure-object comparisons, the affine adjoint-unit theorem's pseudo-coherence and relative Tor clauses, pseudo-coherence descent, and the new relative Tor comparison. I checked the affine-unit theorem allows algebraic spaces and hence schemes, arbitrary affine bases, and supplied adjoints. The equivalence transports the adjunction by its Hom bijection. Local finite relative Tor dimension implies local cohomological boundedness by tensoring with the ring itself; quasi-compactness gives a finite minimum bound. Flat pullback preserves that lower bound by exact tensor on stalks, and the explicit calculation was added to the step. Thus the next step's boundedness hypothesis is proved rather than assumed.

Step 3 uses the full qcqs proper-flat base-change theorem, not the Noetherian self-product specialization. I checked the orientation: p2 is the proper morphism, f is its bottom base change, and the comparison is b(O_X) = Lp1*a(O_S). The direct-image-composition theorem and right-adjoint-composition theorem give cb = id with its pasted counit. The inverse identification at O_X defines h. Step 4 uses the NEW closed-section statement at (p2, Delta, M) and the existing pair DEFINITION only to assemble its predicate. Its theorem gives exactly the map Phi Ri*h, not an unspecified isomorphism. These two inputs say the required statements verbatim.

Step 5 is an elementary unpacking of the cited composite-counit normalization: xi is characterized by the identity under the projection adjunction. Step 6 applies the existing pair base-change statement for its Tor-independent DIAGONAL pullback and the existing proper-flat right-adjoint theorem for the PROJECTION square. I checked P' = P times_X X' and p2' Delta' = id. The existing mate-pasting statement explicitly includes pasting along adjunctions, conjugation and identity squares. Expanding the adjunct gives epsilon_b' Rp2'(B Lt*j d^-1) = Lh*(epsilon_b Rp2*j) = id. Pasting the two self-product/base-change squares identifies the beta comparisons. This proves the actual class equation without claiming diagonal exceptional base change is invertible and without using uniqueness of relative dualizing pairs over a non-Noetherian base. Step 7 uses the supplied pair pullback's identity/iteration clause for overlaps, then the Hom-bijection characterization of a trace-preserving isomorphism to identify it with the canonical adjoint comparison. All citations were opened, and citations.json quotes their statements exactly. Generic tools from other units are declared in split_report.tool_uses.

I tested the new statements on the empty scheme, the identity section, a nonregular section of a flat finitely presented family, and unbounded-above M. Empty schemes make the maps uniquely zero; identity sections reduce Phi and multiplication to the unit. A nonregular section can have infinite projective dimension, so the new statement deliberately does not claim perfectness of i_*O or an arbitrary nonflat derived-Hom base-change isomorphism. Bounded-below M is retained, while unbounded-above M is permitted by 0A9X. The site comparison imposes neither pseudo-coherence nor boundedness, in agreement with 0DK7. All non-elementary steps are below 2000 characters. No new node restates a clause of the item: both are general-purpose inputs with independent objects and hypotheses, and the item's construction and compatibility argument remain in its own proof.

## Unfinished work

None in the stage-1 split. The two new inputs are intentionally statement-only for future splitting. No Lean was written and no compiler, Lake or build tool was run.
