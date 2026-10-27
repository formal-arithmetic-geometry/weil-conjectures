## Files written

- dag/nodes/sec-six-functors/fix-cor-verdier-exchange.json: item, status split; statement unchanged; proof shortened to a 2,520-character assembly by distributing its arguments, not by dropping them.
- dag/nodes/sec-six-functors/lem-sf-admissible-compositor-coefficient-square.json: statement, status unsplit, no proof or proof dependencies; no exact Mathlib match. This is the actual-operation coefficient coherence of the exceptional compositor for arbitrary composable admissible morphisms and arbitrary finite-Tor target input.
- dag/nodes/sec-six-functors/lem-sf-admissible-hom-substitution.json: statement, status unsplit, no proof or proof dependencies; no exact Mathlib match. This is signed and coefficient-natural transport of the actual derived internal Hom and ordinary direct image under an arbitrary target isomorphism.
- citations.json: verbatim witnesses for every citation in every assembly step. searches.jsonl: actual search-command log. returned-item.json: the retained, unmodified returned node; its original proof is also reproduced below. These auxiliary files are sandbox evidence, not additional project files to change.

## Attachments

None. The project search found AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek in lean/WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean:418. Its statement is only a nonempty objectwise isomorphism at torsion coefficients, without the naturality/coefficient/shift clauses. It is not an exact attachment. The Weil-sheaf variant in lean/WeilConjectures/WeilSheaf/VerdierDual.lean:178 has sorry. The recorded project theorem WeilConjectures.AdmissibleVerdierExchange.verdier_exchange in lean/Sheaf/Paper/AdmissibleVerdierExchange.lean:287 also ends in sorry; its docstring and statement were read for comparison only.

## WANTED

None. The source for these formal obligations is the available blueprint, expanded by the agent; there is no invented Stacks tag or outside-source theorem. No SGA source is used.

## Faults and repair of the return

The return asks to distribute the 4,646-character proof into at least two independently available statement-only obligations of comparable size, while retaining the mathematical statement and giving an assembly of at most 3,000 characters. Both new nodes are unsplit, with empty proof, empty proof_deps, and null proof_origin. Their statements have approximately 2,000 and 2,500 characters. The item has four steps totaling 2,520 characters, none longer than 2,000 characters. No Lean was written or compiled.

The named Q149 sandbox originally held only dispatcher marker files: there was no item, report, or old search log to reuse. I therefore read and retained the current repository's returned split, including its Q54 proof, searches, citations in the proof, review attribution, and Lean metadata. Its statement and imported/maintainer fields are preserved. The repository version has no blueprint_update. The main-20261015 statement agrees with the older imported statement; its proof follows the same mate, tensor-adjunction, compatibility route. The sandbox nodes overlay only this item's stage-1 work and the two new nodes; delivery rebases that overlay on current main.

The current DAG already has lem-sf-constructible-exceptional-compositor, which states the entire Hom characterization, pasted-counit normalization and shift compatibility needed in old step 1. Creating another node for this would be a duplicate. Assembly step 1 therefore cites that existing lemma, specialized to g=a_Y and L=Lambda_s, rather than inventing a third copy. It is declared as a generic tool use in split_report and follows exactly the source's composition-adjunction route.

Old step 4's nontrivial equality of transposed pasted counits becomes lem-sf-admissible-compositor-coefficient-square, for arbitrary g and L, without assuming the axiomatized def-sf-datum. Old steps 3 and 5, and the passage from the mate equality to the internal-Hom/direct-image comparison square in old step 4, become lem-sf-admissible-hom-substitution. Old step 2 is retained verbatim, including the finite-Tor domain check, direction of the inverse tensor-adjunction arrow, and explicit composite. The existing compositor carries old step 1 and its shift claim. The two new nodes carry all the comparison arguments; the item retains only their specialization and pasting. The complete original argument is reproduced below, so no argument has been erased or blurred.

## Unfinished work

The two new lemmas deliberately remain unsplit for other workers, as the return requires. No stage-2 or stage-3 work is part of this delivery. Their source-expanded proof tasks are described by the preserved arguments below: one transposes the coefficient square to the pasted exceptional counits, and the other verifies the signed Hom and evaluation-defined coefficient squares before passing to the specified completed/scalar realizations. All further splitting/proving is deferred to the DAG queue.

## Not duplicates

lem-sf-admissible-compositor-coefficient-square vs lem-sf-dualizing-composition-coefficient-mate: the existing node assumes a full axiomatized def-sf-datum, including A5 as supplied coherence and A6 biduality, and states a structure-map/unit comparison. The new node proves the coefficient compositor identity for the actual operations under exceptional admissibility, for arbitrary composable f,g and target L, without assuming the full package. The old theorem cannot be specialized under this item's weaker hypotheses; doing so would silently add the very coherence/biduality assumptions the construction is establishing.

lem-sf-admissible-compositor-coefficient-square vs lem-sf-constructible-exceptional-compositor: the existing statement constructs the actual compositor, characterizes its Hom action and counit, and asserts shifts/refinements. It does not state its coefficient-change square. Its compositor is reused, not reconstructed as a competing node.

lem-sf-admissible-compositor-coefficient-square vs fix-prop-adjunctions: clause (3) supplies the exceptional compositor with its pasted units and counits but has no equation comparing it at coefficients A and B. That nontrivial equation is the new obligation, not another adjunction-existence claim.

lem-sf-admissible-hom-substitution vs lem-sf-derived-hom-substitution-coherence: the existing statement assumes a full def-sf-datum and allowed A5 comparisons. The new node has only the actual operation datum and actual evaluation/mate comparison maps, with no full-package or biduality hypothesis. Dropping those hypotheses is not a one-line specialization of the existing statement. This distinction is essential to the admissible, pre-package theorem being split here.

lem-sf-admissible-hom-substitution vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement gives internal-Hom shifts and restriction on a ringed site, not the postcomposition square after ordinary image together with the specified coefficient comparison square and its signed normalization. The existing statement is infrastructure a future proof can use.

lem-sf-admissible-hom-substitution vs lem-coef-slice-hom-source-shift: the existing node concerns slice restriction with a specified normalized Hom model, not coefficient extension/reduction or ordinary direct image. No substitution square for the coefficients of this item occurs in its statement.

lem-sf-admissible-hom-substitution vs fix-lem-tensor-adjunction: the existing theorem compares exceptional image/internal Hom and gives its own compatibilities. The new node concerns an arbitrary target isomorphism in RHom followed by ordinary image, with no exceptional functor in its conclusion; it verifies the separate second arrow, including its explicit comparison square.

Each new node vs fix-cor-verdier-exchange: neither states the Verdier exchange isomorphism or any whole clause of that conclusion. The first has no internal Hom and treats arbitrary composition inputs. The second has no dualizing object or compact-support image; it concerns arbitrary target substitution. The tensor-adjunction construction remains in the parent. The two new nodes have independent statements and neither cites the item or the other new node.

## Review by Q149

I read the master fix-cor-verdier-exchange.md, the main-20261015 sk-thm-sf-package/fix-cor-verdier-exchange.md and .proof.md in full, and the associated chapter and sk-prop-sf-biduality-general unit records. The new sources point specifically to main-20261015 proof steps 1--3, not to a nonexistent numbered literature theorem. I compared the source with the live AdmissibleVerdierExchange statement/docstring and with the torsion and Weil-sheaf versions. The statement is unchanged; there is no statement dispute or added admissibility assumption. The optional ambient-admissibility hypothesis remains conditional, and is never claimed to hold for all smooth proper varieties.

For assembly step 1 I opened lem-sf-constructible-exceptional-compositor and read its statement. It states the actual canonical natural isomorphism, the complete Hom formula, pasted counit characterization, and integer-shift compatibility at all four stages. Its schemes are separated finite type; this item's exceptionally admissible structure maps provide that hypothesis, and a_X=a_Y f supplies the composition. The coefficient unit is finite-Tor, so its target input is allowed. The direct composition comparison has the required direction, and the mate uses its inverse. Its statement gives the whole old Hom-chain argument, not merely existence of an unrelated isomorphism. I checked that none of its statement/proof dependencies reaches the item.

For assembly step 2 I read fix-prop-adjunctions, fix-lem-tensor-adjunction and def-weil-exceptional-inverse-image. Clause (2) of the first explicitly restricts both exceptional adjoint functors to D^b_ctf, so a_Y! and f! may be used at the required finite-Tor inputs; the unit has amplitude [0,0]. The inverse-image definition explicitly records finite-Tor preservation as a proved property, consistent with the adjunction theorem. Thus N=omega_Y meets the tensor-adjunction theorem's finite-Tor hypothesis; M is finite-Tor by the item's hypothesis. The cited tensor-adjunction statement points from the ordinary-image Hom object to the target Hom object, so the displayed first arrow uses its inverse. The second arrow is the functorial image of the isomorphism from step 1. No preservation theorem is inferred from mere notation.

For assembly step 3 I read the new hom-substitution statement and fix-lem-tensor-adjunction again. The former explicitly states the contravariant natural isomorphism j_c and the signed shift square for every integer r. Its U=Rf!omega_Y and V=omega_X are finite-Tor by the admissible inverse-image restriction already checked in step 2 (also at a_X). Its signed source shift sends M[r] to the output shifted by [-r]. The latter theorem explicitly states naturality and shifts for the first arrow. Pasting these two squares gives precisely naturality and shifts of the composite, without concealing a new shift argument in the assembly.

For assembly step 4 I checked the new compositor coefficient identity with source C_X Rf_A! Rg_A! L and target Rh_B! C_Z L (where ! here denotes exceptional upper shriek). Specializing g=a_Y and L=A_s and then using the coefficient-unit isomorphism gives exactly kappa_X C_X(c_A)=c_B Rf_B!(kappa_Y) q_f. All of f,g,h are admissible by the item's assumptions. The new hom-substitution hypothesis v C_Xc=c' u is this very identity for u=Rf_B!(kappa_Y) q_f, v=kappa_X and c'=c_B. Its statement explicitly gives the required sigma comparison square after actual internal Hom and ordinary direct image. fix-lem-tensor-adjunction supplies the other arrow's comparison. No internal-Hom or ordinary-image comparison is assumed invertible on arbitrary ambient objects. I checked finite reduction, integral reduction, rationalization and common finite-stage extensions separately as allowed directions of coefficient change; there is no nonexistent reduction from a characteristic-zero field to a finite quotient.

I checked delivery-errors B--E against both new statements and the assembly. Every new statement introduces its field/coefficient/scheme data and all map variables; definition references are statement dependencies, not substitutes for theorems. Both are derived-category statements, not per-degree substitutes. New proofs and proof_deps are empty. The only elementary assembly work is specializing and pasting the explicitly supplied squares. The long work is exposed as independent obligations, and no new node restates a parent clause. Every proof citation has a verbatim sentence/formula witness in citations.json. Before creating nodes I searched the whole DAG by the mate/compositor, signed-Hom, substitution and coefficient terms and used blueprint_refs.py ancestor and searches for mate, dualizing, simultaneous shifts, pasted counit, structure-morphism mate, internal Hom shifts, Hom shift, substitution and coefficient mate. I opened the closest matches listed above. There is no duplicate of the new weaker-hypothesis actual-operation assertions.

Mathlib searches were made only through the required msearch.py and read as returned. For both new nodes there are two semantic phrasings plus Loogle, grep and LeanSearch; all services used for the recorded searches answered. Mates.lean:170,210 and CompositionIso.lean:65--84 give generic mate-pasting/composition infrastructure; Shift/Adjunction.lean:320--390 constructs adjoint shift structures. They do not identify the actual project's coefficient functors and their prescribed comparison maps with the corresponding formal mates. HomComplexShift.lean:62--77 uses the Conrad normalization with an additional shift-only sign, whereas this source's Hom realization uses the specified (-1)^(r d) normalization. BifunctorShift.lean:79--99 concerns covariant bifunctor totals. None is the new derived internal-Hom coefficient square after ordinary image as a one-line specialization. The original item searches remain intact; its statement/search question did not change.

Small-case checks: if f or g is the identity, the compositor square reduces to naturality of the corresponding q with the identity normalization. For L=0, all morphisms in that square are the unique zero map. For c=id and u=v, the hom-substitution square is the same map on both paths; for M=0 or an empty scheme all Hom objects are zero. For r=0 its shift square is identity normalization. For r=1 the degree-d sign is (-1)^d and the degree-(d+1) sign changes once, agreeing with d(P[1])=-d(P); postcomposition by the degree-zero map c commutes with these scalars. The comparison maps need not be invertible, so the statement remains meaningful for nonflat finite quotient changes. At Y=Spec k the parent assembly specializes to global duality, without adding a biduality axiom. No long assembly step hides another lemma. These are mathematical checks of the actual assertions, not a count of formal fields.

## Retained returned proof, verbatim

The following is the complete text of the five returned steps; it is retained as proof-planning material for the new obligations, not as a proof inside their statement-only JSON records.

### Returned step 1

Step 1: the structure-morphism mate. Put $s=\operatorname{Spec}k$, so $a_X=a_Y\circ f$. Use the composition isomorphism $\alpha:R(a_Y)_!Rf_!\xrightarrow{\sim}Ra_X{}_!$ in [def-fix-six-functor-datum]; at finite coefficients its direction is the one of [thm-sf-comp-composition]. For every $K\in D^b_c(X,\Lambda)$ and $L\in D^b_c(s,\Lambda)$, the adjunctions and their pasted units and counits in [fix-prop-adjunctions] give
$$
\begin{aligned}
\operatorname{Hom}_X(K,Rf^!Ra_Y^!L)
&\cong\operatorname{Hom}_Y(Rf_!K,Ra_Y^!L)\\
&\cong\operatorname{Hom}_s(R(a_Y)_!Rf_!K,L)\\
&\xrightarrow{\ h\mapsto h\circ\alpha_K^{-1}\ }
\operatorname{Hom}_s(Ra_X{}_!K,L)\\
&\cong\operatorname{Hom}_X(K,Ra_X^!L).
\end{aligned}
$$
This natural chain and its inverse define inverse natural maps $Rf^!Ra_Y^!L\rightleftarrows Ra_X^!L$: their composites induce identity maps on every displayed Hom group and hence are identities, by taking the identity as test morphism. Denote the resulting canonical mate at $L=\Lambda$ by $c_\Lambda:Rf^!\omega_{Y,\Lambda}\xrightarrow{\sim}\omega_{X,\Lambda}$. This uses the composition law in the operation datum at every coefficient stage, rather than applying the finite-level theorem directly to integral or field coefficients.

### Returned step 2

Step 2: the exchange and its domain. The constant coefficient object $\Lambda$ on $s$ is a free rank-one object in degree zero, hence is constructible with Tor amplitude $[0,0]$. The finite-Tor restriction of the exceptional adjunction in [fix-prop-adjunctions], applied to $a_Y$ and $f$, gives $\omega_{Y,\Lambda}\in D^b_{ctf}(Y,\Lambda)$ and $Rf_!M\in D^b_{ctf}(Y,\Lambda)$. Finite-Tor preservation of exceptional inverse image is also explicitly recorded in [def-weil-exceptional-inverse-image]. Thus [fix-lem-tensor-adjunction] applies with $N=\omega_{Y,\Lambda}$ and yields
$$
\begin{aligned}
D_Y(Rf_!M)
&=R\mathcal Hom_Y(Rf_!M,\omega_{Y,\Lambda})\\
&\xrightarrow{\ \sim\ }Rf_*R\mathcal Hom_X(M,Rf^!\omega_{Y,\Lambda})\\
&\xrightarrow{\ Rf_*R\mathcal Hom_X(M,c_\Lambda)\ }
Rf_*R\mathcal Hom_X(M,\omega_{X,\Lambda})=Rf_*D_X(M).
\end{aligned}
$$
The first arrow is the inverse of the stated tensor-adjunction isomorphism, and the second is the displayed functor applied to the isomorphism $c_\Lambda$ of step 1. Their composite is the claimed canonical isomorphism.

### Returned step 3

Step 3: naturality and comparisons. Write $\theta_M$ for the first arrow of step 2. For $u:M\to M'$, naturality in [fix-lem-tensor-adjunction] gives the contravariant naturality square for $\theta$. The square for the second arrow commutes by bifunctoriality of $R\mathcal Hom$: precomposition by $u$ commutes with postcomposition by $c_\Lambda$. Pasting these two squares proves naturality of the exchange.

### Returned step 4

For a stipulated reduction or scalar extension $C$ from coefficients $A$ to $B$, let $q_f:C_XRf_A^!\to Rf_B^!C_Y$ be the exceptional comparison, and let $\kappa_T:C_T\omega_{T,A}\to\omega_{T,B}$ be the comparison for $a_T$ evaluated on the coefficient object ($T=X,Y$). These are the adjunction-mate comparisons of [def-weil-exceptional-adjoint-admissibility]. The operation comparisons preserve the units and counits by [lem-fix-operation-reduction]. The pasted-unit/counit description in [fix-prop-adjunctions] therefore gives
$$
\kappa_X\circ C_X(c_A)
=c_B\circ Rf_B^!(\kappa_Y)\circ q_{f,\omega_{Y,A}}.
$$
To check this equation, transpose its two sides through the adjunctions in step 1. Both transposes apply the $f$-counit followed by the $a_Y$-counit, with the compact-support comparison inserted; the comparison preserves each counit, and the counit for $a_X=a_Yf$ is precisely this pasted counit. The Hom bijections in step 1 are injective, so equality of those transposes proves the equation. Applying internal Hom and $Rf_*$ gives the comparison square for the second arrow of step 2. The square for $\theta$ is exactly the comparison asserted by [fix-lem-tensor-adjunction]; pasting proves the required coefficient compatibility. This concerns the specified comparison maps on their stated domains and does not assert an extra coefficient-change isomorphism for arbitrary ordinary direct images or internal Homs.

### Returned step 5

Finally the Hom adjunction chain of step 1 commutes with simultaneous shifts because the adjunctions are derived adjunctions, so $c$ commutes with those shifts. Replacing $M$ by $M[r]$ identifies both outputs in step 2 with their values at $M$ shifted by $[-r]$. The shift compatibility in [fix-lem-tensor-adjunction] identifies the first arrow under these identifications, and functoriality of $R\mathcal Hom_X(-,c_\Lambda)$ identifies the second. Hence their composite has the stated shift compatibility.
