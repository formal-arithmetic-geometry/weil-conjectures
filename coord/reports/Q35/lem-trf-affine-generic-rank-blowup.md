1. Files written (all node paths are under dag/nodes/sec-trace-formula/):

- lem-trf-affine-generic-rank-blowup.json: assigned item, split, statement unchanged; no Mathlib match.
- lem-trf-affine-geometrically-integral-projective.json: statement-only tool, Stacks 05FT; no Mathlib match.
- lem-trf-affine-principal-fitting-generators.json: statement-only tool, Stacks 080Z; no Mathlib match.
- lem-trf-affine-generic-localization-intersection.json: statement-only tool, Stacks 0810 final paragraph using 05DH; no Mathlib match. Finite presentation and geometric-integrality hypotheses are explicit.

Also citations.json contains verbatim statements for every proof-step citation. Earlier attempted reduction and finite-locally-free nodes are not delivered: the replacement calculation and relation argument belong in the item's proof.

2. Attachments: none. The item tag and searches for blowups, geometric integral fibres, principal Fitting ideals and generic-fibre localizations in WeilConjectures/ did not yield a finished project declaration stating the item or any new tool. Upstream sorry declarations were not treated as proofs.

3. WANTED: none.

4. The imported statement matches Stacks 0810 and is retained. The earlier sandbox proof had incorrect Fitting reasoning after taking torsion quotients and an unsupported finite-presentation-reduction citation; both are replaced with explicit arguments. No statement dispute remains.

5. Unfinished work: the three genuinely non-elementary tool statements are deliberately unsplit at this stage. No unfinished argument remains inside the item.

## Source errors

The printed proof of 0810 says R'_a=R_h. In general this is false: with R=k[x,y], h=x, I=(x), and a=xy, the chart equals R[1/y], so R'_a=R[1/(xy)], whereas R_h=R[1/x]. The argument only needs R'_a=R_a and invertibility of h there. Step 9 proves those assertions and uses base change from B_h, rather than identifying the two localizations.

The source also says that an arbitrary a'=a/h is one of the coefficients of an element of J and that the divided generator is a unit in the whole chart algebra. An arbitrary element of the coefficient ideal need not be a literal coordinate. Global invertibility is false even when a coefficient is 1: for R=k, B=k[x], J=(x), the coefficient 1 of x gives divided element x, which is not a unit in B. It does avoid the generic prime (0), which suffices. Step 5 instead divides all finitely many coordinates by c, shows their quotients generate the unit ideal of R*, and at each base prime chooses one quotient outside that prime. The split maps then show the corresponding divided element avoids the fibre-generic prime. Nothing requires it to be globally invertible.

## Review by Q35

I read the entire proof of Tag 0810 in flat.tex (lemma-helper-blowup-affine-space), Tag 05FT (lemma-fibres-irreducible-flat-projective-nonnoetherian), Tag 080Z in more-algebra.tex (lemma-principal-fitting-ideal), and the local and global universal-injectivity lemmas around Tag 05DH in flat.tex. The three new statements match the particular tools these passages supply. The injection node has finite-presentation and geometrically integral fibre hypotheses, as the source's use requires; its old erroneous Algebra 00FV attribution is removed. Tag 07ZD was read but does not require a separate node because the final relation calculation suffices.

Step 1 uses the exact finite-cokernel-presentation definition in def-sc-finitely-presented-module. It proves the kernel's finite generation for the chosen surjection by two lifting matrices and the displayed formula for kernel vectors, then clears denominators. This avoids incorrectly lifting a surjection onto N_h to one onto N, and avoids introducing a node restating the reduction clause.

Step 2 takes precisely projectivity of B over R from the new 05FT node; its flat, finite-presentation and all-field-extension fibre assumptions are the item's assumptions. The split embedding is part of the stated projectivity equivalence. The existing Fitting independence/base-change node defines the minors used. The coefficient ideal's finite generation is justified using the extended multiplication endomorphism, not by assuming B finite over R (it need not be).

Step 3 uses the flatness definition for tensoring multiplication injections after reduction modulo a prime. This proves the generic-prime identification rather than assuming it. The existing Fitting node provides both presentation independence (compute the free module using its identity presentation) and localization. These yield a generator outside the generic prime and hence a coordinate outside the base prime. The two cases h in or outside the prime prove exactly V(I)=V(h).

Step 4 reads the existing chart definition literally as a subalgebra of R_a. The existing regular-generator lemma gives regularity of a, from which regularity of h and c follows because a=hc. The existing extended-ideal lemma states IR*=(a); cancelling regular h gives CR*=(c). I checked that this stronger equality is derived, not attributed directly to the cited lemma. Tensor associativity and the flatness definition prove that B* is R*-flat and that a and c remain regular there.

Step 5 is the explicit coordinate computation following those facts: dividing coefficients, applying the retraction, and cancelling c proves the claimed coordinates of u_l. Dividing an expression for c by regular c proves the divided coordinates generate the unit ideal. Consequently at every prime a suitable u_l avoids the fibre-generic prime. This corrects the source errors above without adding any hypothesis. The fibre-domain assertion follows from the original all-field-extension hypothesis, since the residue field at a base-changed prime extends the residue field at its contraction.

Step 6 uses the exact base-change clause of the existing Fitting node on P before quotienting. The new 080Z node applies to P localized at the prime, a finite module over a local ring with principal rth Fitting ideal (c). Its quotient is by the kernel of multiplication by c, exactly as stated, not power torsion. Since a=hc, this kernel maps to zero in the a-power-torsion quotient. The latter is therefore a quotient and inherits r generators. Localized power torsion is checked by clearing a denominator. No equality of Fitting ideals before and after removing torsion is used.

Step 7 writes the elementary spreading calculation using finitely many cokernel generators and a product of annihilators. This uses neither finite presentation of the torsion quotient nor an affine-sheaf comparison theorem. The product avoids the prime. Rank zero finishes here.

Step 8, for r>0, uses the existing Fitting node to identify the lower Fitting ideals in the free generic stalks. The new localization-injection statement applies to R_h -> B_h: flatness and finite presentation localize, and each field extension of a residue field still gives a domain. Its quoted injection detects that the original lower Fitting ideal vanishes on B_h. This is done before arbitrary chart base change, avoiding an unproved generic-rank identification after that base change.

Step 9 uses the chart's actual localization R_a. The explicit inverse c/a makes h invertible, so the lower Fitting vanishing base changes. The existing Fitting base-change statement applies to the finite module M* even if it is not finitely presented. Regularity of a on B* kills the lower ideal itself. Presentation independence permits computing it using the particular r-generator surjection on the open; its minors have size one, so every relation vector is zero. This proves freeness of that surjection globally on the chosen basic open, stronger than merely asserting local freeness there.

Step 10 proves the strict-transform comparison: the surjection is an isomorphism after inverting a, its kernel is individually a-power torsion, and its source has no such torsion by definition. It transfers the constructed free open to N and verifies the fibre image of g is nonzero using step 3's injection. This completes precisely the original conclusion.

Small cases checked: for r=0 no undefined Fit_-1 is used; M* vanishes on the chosen open. If h is nilpotent the equality of vanishing sets permits nilpotent I and all charts are zero, so the conclusion is vacuous. The chart a=0 is likewise zero. For a field base and B=k[x], coefficient splitting and the nonunit x behave exactly as step 5 says. For N=B/(x), r=0 at the generic point, taking g=x gives the required zero module on the nonempty open. No finite-over-base hypothesis is introduced (B=R[x] remains allowed).

I searched the DAG, current blueprint and Lean source before retaining the three tools. The additional semantic phrasings were actually run through msearch.py with the assigned item id; the returned candidates require finite modules over the base, smoothness, PID hypotheses, or concern going-down rather than these assertions. The grep results about Fitting decomposition concern endomorphisms, not module Fitting ideals. Previous actual search records and their logs were retained. No exact Mathlib match was found. No non-elementary proof step exceeds 2000 characters. No SGA source, Lean edit, compiler, Lake or local DAG-validation command was used.

## Not duplicates

lem-trf-affine-geometrically-integral-projective vs lem-trf-free-subtraction-flatness: both mention 05FT, but the existing node asserts universal injectivity of a specified map A^r -> N and flatness equivalence with its cokernel, under additional generic-basis hypotheses; it does not assert that A is projective over R. The new node is exactly the algebra-projectivity tool used to construct a split coordinate embedding.
lem-trf-affine-generic-localization-intersection vs lem-trf-affine-generic-rank-blowup: the former is injectivity of a canonical ring map for the given algebra; the latter constructs a blowup ideal and rank-r free opens for a finite module. The injection is an independent tool in its proof, not a restatement of any clause of the conclusion.
