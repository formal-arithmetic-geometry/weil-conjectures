# Worker report: lem-per-finite-compact-support-fibre-support-bound

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-compact-support-fibre-support-bound.json: item statement, split into ten steps; no Mathlib match.
- citations.json: verbatim statement quotations for each dependency of each proof step.
- No new nodes, no new Mathlib leaves, no unit/chapter edits, no Lean edits or compilation.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, support/dimension terminology, and compact-support direct-image terminology. The nearby isPerverseLE_lowerShriek in SixFunctors/Etale/Perverse/Operations.lean:219 proves the parent assertion only via sorry; the compact-support amplitude theorem in Derived/Finiteness/DirectImage.lean bounds degrees, not support dimensions. Neither is an attachment for this item. The existing finiteness and cohomology nodes are used as dependencies, not newly attached nodes.

## WANTED

None. The local BBD PDF/text and Stacks sources suffice. No SGA source was used.

## Problems found and corrected

The statement is retained. The imported proof bundled several non-elementary consequences without citing their precise nodes. Step 1 is replaced by the existing finite-ring compact-support finiteness theorem, whose amplitude clause also gives negative-degree vanishing. Constructible nonzero-stalk sets are now cited explicitly. The closed-support cohomology comparison now cites the finite-pushforward cohomology theorem; the original essential-image theorem alone did not say that cohomology agrees. The separably closed field cd=0 input and module/abelian cohomology comparison are explicit. The fibre closure dimension uses the existing constructible-closure-dimension theorem. The generic-fibre calculation now spells out the closure/fibre identification and cites both the irreducible fibre-dimension theorem and the locally algebraic local-dimension theorem.

The source reference 0F0V is an affine ordinary cohomological-dimension bound; 0F0X is the affine ordinary direct-image support lemma, not a compact-support stalk theorem. They are replaced by the actual pertinent statements/tags. BBD 4.2.4 states the perverse amplitude estimate and gives a short proof using duality/pullback; the explicit finite-coefficient fibrewise assembly here is therefore honestly marked proof_origin.by=agent, following the human's 2026-10-19 assigned route rather than claiming this ten-step proof is printed in BBD.

## Unfinished

Nothing required for stage 1 remains; the existing cited unsplit/sorried dependencies remain their own items. No claim of a Lean proof is made.

## Not duplicates

No new node was created. Whole-DAG name/concept searches and blueprint_refs searches for compact support fibre support bound, support dimension, and fibre dimension found existing generic tools, all reused. In particular the constructible-closure-dimension theorem is reused instead of duplicated.

## Review by Q64

I read BBD 4.2.4 in the saved bbd.txt extracted from the local PDF, Stacks etale-cohomology.tex at 04CA (closed-immersion essential image), 09YS (constructible support), and the incorrectly imported references 0F0V/0F0X. I read varieties.tex at 0B2L (irreducible fibre dimensions) and 0A21 (dimension on nonempty opens of an irreducible locally algebraic scheme). There are no new-node sources to audit. I read the chapter and unit records, the current ancestor's Step 2, the standing brief and delivery-errors B--E. This is precisely the finite-coefficient sheaf estimate used by that Step 2; no route is changed.

For Step 1 I checked the finiteness node's supplied compactification, finite-ring hypothesis, bounded constructible input and amplitude [0,N]. Nagata applies since Y is qcqs and f is separated of finite type. Proper over Y ensures the compactification is finite type over k; it need not have the original fibre dimension, which is why the proof restricts to the closure of Z in each fibre later. Step 2 uses exactly constructible support and its independence of geometric-point choice, plus stalk conservativity and the two stated Noetherian consequences. Step 3 gives the finite locally closed argument for generic-point membership rather than treating constructibility alone as an unexplained lemma.

For Step 4 I checked proper base change permits arbitrary base change and all complexes over any torsion ring, and extension-zero base change explicitly includes finite module coefficients degreewise. The stalk/cohomology and geometric-point statements provide the remaining identifications; module cohomology forgets to abelian cohomology by its cited statement. For Steps 5--6 the reduced-induced structure node constructs the actual closed schemes; fibre-dimension base change is used for local dimensions, not silently asserted to state global dimension. Finite components and the locally algebraic dimension theorem give the written conversion. Constructible-closure dimension applies over the field Omega, with no perfectness assumption. Closed-support essential image applies to the underlying abelian sheaf. The sheaf vanishes off Z after pullback since the restriction to the complementary open was zero.

Step 7 uses the finite-pushforward cohomology theorem for the closed immersion, verified finite on quotient charts, and the two cd statements with c=0 and dim W=e(y). The stalk bound is thus q<=2e(y), not a bound involving the dimension of an arbitrary compactification. Step 8 chooses a maximal-dimensional component of a nonempty finite-type fibre, closes it in Z, and uses the fibre's actual subspace topology. The closure lies over T, and its fibre over t is B; its generic point therefore maps to t. Step 9 applies the irreducible dimension theorem to the reduced Z', all finite-type hypotheses satisfied; its dense open equality locus contains the generic point, where the local fibre dimension is the dimension of irreducible B by the separately cited theorem. The resulting equality dim Z'=dim T+e(t) justifies the subtraction. Step 10 contains only integer arithmetic and the written chain-in-a-finite-closed-cover argument, followed by the cited stalk conservativity.

I checked empty X or Z, empty fibres, zero F or coefficient ring, q<0, a=0, d=0, and q>2d. For f: A^d -> Spec k the extremal compact-support degree 2d with a=d makes the inequality sharp. For the identity map (d=0), positive-degree images vanish and degree zero retains the support bound. Nonclosed stalk support is allowed: its closure, not the nonzero-stalk set itself, is used throughout. No finite Tor hypothesis on F is introduced. I checked B1--B10: no new node or false leaf, every object is introduced, JSON TeX is singly escaped, preserved metadata, real searches only. C1--C8 are checked through the cited statements and citations.json; all off-unit generic tools are declared in split_report.tool_uses. D1--D5: no clause moved into a child, no circular induction or source gap hidden. E1--E7: field extensions may be inseparable, closed support is consistently distinguished from stalk support, and each dimension formula has its actual hypotheses. Every proof step is below 2000 characters, so no long step hides a separate lemma.

The saved six earlier searches were read and retained; additional searches refined the statement. Semantic hits are algebraic Module.supportDim inequalities and constructible scheme image results, not etale higher compact-support estimates. Loogle's unknown-identifier results are recorded as unusable query results, never as successful mathematical absence tests; the second earlier fully qualified Scheme dim query returned actual dimension declarations. No service-down result is represented as no match.
