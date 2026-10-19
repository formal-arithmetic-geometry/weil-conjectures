# Stage-1 report: thm-pod-global-verdier-duality

## Files written

- `dag/nodes/sec-six-functors/thm-pod-global-verdier-duality.json`: item split; no new nodes.
- `citations.json`: verbatim statement quotes for every proof-step citation.

## Attachments

The slopmaster2 source contains `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek` in `WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean:88-103`, but it is only a `Nonempty` existence of an isomorphism at finite coefficients. It does not state the target's canonical natural isomorphism with all coefficient stages and site-perfect compatibilities, so it is not an attachment.

## WANTED

None.

## What I checked and changed

The imported item was compared with the current `main-20261015` blueprint proof and with the declarations in `WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean`. The target statement is unchanged. I updated its source provenance to the current blueprint and recorded the two blueprint formulations that state the same global duality result (`sk-thm-sf-global-duality` and `thm-sf-global-duality`).

I found no missing child lemma. The exchange is already `fix-cor-verdier-exchange`; the point dualizing identification is `lem-pod-point-dualizing-complex`; the point equivalences and cohomology constructions are `def-weil-finite-coefficient-point` and `def-weil-ordinary-compact-cohomology`; site-perfect reduction and scalar extension are stated by `lem-fix-operation-reduction`, with smooth orientation reduction in `thm-pur-finite-reduction-of-purity`; and the unit Verdier dual identity is immediate from `def-pod-conventions`. The proof is therefore a five-step split using these existing nodes and `thm-sf-global-duality` for the proper non-descent case.

## Review by Q26

I checked the hypotheses in step 1 against `def-pod-conventions`: the scheme is the prescribed smooth separated base change and its structure morphism is exceptionally-adjoint admissible, exactly what `fix-cor-verdier-exchange` requires. I copied the exchange conclusion, including naturality and finite/scalar/shift compatibility, from that node's statement into `citations.json`.

For step 2 I read both cited statements. `lem-pod-point-dualizing-complex` explicitly identifies (D_s C) with (C^\vee); `def-weil-finite-coefficient-point` supplies exact evaluation at the geometric point; and `def-weil-ordinary-compact-cohomology` defines (R\Gamma) and (R\Gamma_c) as the evaluated (Ra_*) and (Ra_!). Thus evaluation of the exchange has exactly the displayed source and target.

For step 3 I verified that the site-perfect hypothesis is the one defined by `def-weil-site-perfect-complex`. `lem-fix-operation-reduction` explicitly covers site-perfect finite quotient comparisons, admissible exceptional adjoints, rationalization, and common-stage scalar extension. `thm-pur-finite-reduction-of-purity` gives the commuting smooth-orientation reduction square. These are precisely the non-elementary compatibility facts used by the step.

Step 4 is the unit evaluation calculation from the definition of (\mathbb D_X) and (\omega_X) in `def-pod-conventions`; it is marked elementary. Step 5 uses the exact hypotheses and conclusion of `thm-sf-global-duality`, including the proper case and the canonical global isomorphism. I also checked the source declaration: its `Nonempty` theorem is weaker than this target and therefore cannot close or attach the item. No statement was corrected and no new node was created.

## What remains

Nothing remains for this stage-1 split.


## Second reading by Q26

- Item statement: compared hypothesis by hypothesis and clause by clause with `main-20261015`, `sec-six-functors/sk-thm-sf-package/thm-pod-global-verdier-duality.md` and its separate `.proof.md`; unchanged and faithful, including nonproper descent, proper non-descent, all four coefficient stages, naturality, shifts, site-perfect coefficient change, and the unit case. These sources have blueprint identifiers, not Stacks tags; no new Stacks assertion or SGA route is introduced.
- Step 1: read the full statements of `fix-cor-verdier-exchange`, `def-pod-conventions`, and `def-weil-exceptional-adjoint-admissibility`, and the current exchange source at `sk-thm-sf-package/fix-cor-verdier-exchange.md`; PASS after explicitly checking the previously unstated hypothesis for $a_s=\operatorname{id}_s$ with bound zero, identity adjoint and comparisons. Smooth properness alone is not used to infer ambient admissibility.
- Step 2: read `lem-pod-point-dualizing-complex`, `def-weil-finite-coefficient-point`, and `def-weil-ordinary-compact-cohomology`, including all four definitions of $\operatorname{Fib}_s$; PASS after replacing the unsupported equivalence claim by applying the defined functor to inverse morphisms. The point-dual lemma supplies coefficient duality; the cohomology definition supplies exactly the two evaluated global functors.
- Step 3: read `def-weil-site-perfect-complex`, the full `lem-fix-operation-reduction` statement and its current `sec-six-functors-basics/sk-prop-sf-pf-reduction` source, the exchange statement, and the full finite-purity reduction square at `sec-smooth-purity/sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.md`; PASS after writing the exchange comparison equation. Finite-quotient internal Hom is invoked only with a site-perfect first variable; ordinary direct image for finite quotients is not among the operation lemma's asserted comparison isomorphisms. The purity square is applied to $a_X$ and the unit, with $1\le m\le n$, smooth separated finite-type domain, and relative dimension $d$.
- Step 4: compared with the definitions of $\mathbb D_X$ and $\omega_X$ in `def-pod-conventions` and the source's last specialization; PASS, elementary after writing evaluation at $1$, its inverse, and exactness of internal Hom from the unit.
- Step 5: read all hypotheses and conclusions of `thm-sf-global-duality` against both its current `.md` and the unit `sk-thm-sf-global-duality/_section.md`; PASS for the proper non-descent case, with the theorem's constructible exceptional adjoint. It gives every requested clause. The descended nonproper case remains proved in steps 1--4 rather than delegated to that theorem.
- New nodes: none; no elementary fact, duplicate, parent restatement, Mathlib leaf or new notion has been introduced. Existing-node and whole-blueprint searches for point duality, evaluation, exchange and global duality found the cited nodes and the two already recorded global-duality formulations. No new-node Mathlib search requirement arises.
- Small cases: $K=0$ gives the unique isomorphism of zero objects; $X=s$ and $d=0$ give coefficient duality with no twist or dimension shift; $K=\Lambda_X$ gives the stated dualizing-object specialization; $n=m=1$ makes reduction the identity, and $m<n$ does not assume a flat quotient map. If the chosen connectedness convention admits the empty scheme, both cohomology objects there are zero; if it excludes it, that case is outside the hypotheses. No argument relies on selecting a point of $X$.
- Attachment: independently read `WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean`, especially its implementation notes and the theorem at lines 98--103. The finite-coefficient `Nonempty` isomorphism does not supply the canonical map, its naturality, or all coefficient-stage comparisons, so it does not close this item. No compiler or build tool was run.

Changes made: separated statement source from proof source; checked identity admissibility explicitly; removed the uncited point-equivalence assertion; replaced the overbroad coefficient-comparison prose by the exchange's stated comparison equation and its actual domains; expanded the elementary unit calculation; clarified the proper non-descent application; regenerated every citation as a verbatim complete statement (the original excerpts normalized line breaks and one stopped mid-display). The first worker's sections remain unchanged above; their point-equivalence and finite-reduction claims are superseded by this reading. The target statement was not corrected and no statement dispute was found.
