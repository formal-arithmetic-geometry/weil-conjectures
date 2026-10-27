# Stage-1 report: lem-sfb-epp-residue-nonpower-root-dvr

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-epp-residue-nonpower-root-dvr.json — statement item, split into six proof steps. The complete statement and statement dependencies are unchanged. All inherited Mathlib searches are retained; six additional searches actually run with msearch.py are appended. No exact Mathlib match for the whole item.
- citations.json — eleven step/node pairs, each with a verbatim statement quote.
- searches.jsonl — actual search-command log; candidates.txt — filenames inspected during duplicate searches.
- report.md — this report.

There are zero new nodes and zero new Mathlib leaves. Every cited theorem already exists as a Mathlib leaf. No unit or chapter record is changed.

## Attachments

None. Searches of lean/WeilConjectures by the item id, nonpower/residue-root phrases and DVR/root terminology found no project declaration giving all the clauses. Related root-normalization results concern roots of a uniformizer or separable unit roots with invertible degree and do not give this nonpower-residue assertion. A theorem in Mathlib is not a project attachment.

## WANTED

None. The needed Stacks files and latest blueprint are present locally.

## Problems found and changes

The item statement is correct. No STATEMENT-DISPUTED correction is needed. Stacks more-algebra.tex, label lemma-pre-purely-inseparable-case (Tag 09EX, verified in tags/tags), has the entire proof "This lemma proves itself." The six steps supply that missing argument and therefore proof_origin.by is agent, rather than claiming a detailed proof occurs in the source.

The existing blueprint ancestry is historical: tools/blueprint_refs.py ancestor prints from.node = None. The live item and its reviewed parent have the same null ancestor and recorded via chain. I retained that chain and made from.place explicit. I read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the recorded chapter/unit. The latest proof does not state the auxiliary Epp algebra result; the split serves the existing historical Epp/09EY use, without changing the unit or its route. Searches of the whole current blueprint for nonpower and 09EX found no match; the monic/irreducible search found only the unrelated Stein-connectedness node.

The initial alternative of using irreducibility over the fraction field was unnecessary. The actual proof factors the minimum power of t from the coefficients of the monic quotient. This keeps the field-degree and evaluation arguments explicit and avoids assuming char(F)=p. Mathlib candidates Polynomial.Monic.irreducible_of_irreducible_map (Eval/Irreducible.lean:44, source read), the monic Gauss lemma and IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization supply possible ingredients, not the whole assertion, so no false leaf classification is made. The existing characteristic-p binomial node is applied only to k, not to F.

## Unfinished work

None in the stage-1 split. No Lean was written, no compiler/Lake/build command was run, and no repository file was written or git command run in the shared repository. All changes are confined to the assigned sandbox. Delivery checks and push are performed by the prescribed delivery tool.

## Not duplicates

No new nodes. Existing monic quotient, binomial irreducibility, field quotient, integral maximal contraction, coefficient valuation and PID-normality nodes are reused directly; no new statement restates a clause of the item.

## Review by N8

I read the item source 09EX and the calling paragraph of 09EY in more-algebra.tex, including its use of the nonpower residue criterion after the change of variable. I also read fields.tex lemma-take-pth-root (09HF) and example-quotient-polymial-ring (09FI), and algebra.tex lemma-finite-is-integral (00GK), lemma-going-up-maximal-on-top (00OI), lemma-characterize-local-ring (00E9), lemma-characterize-dvr (00PD), and lemma-PID-normal. There are no new nodes requiring a separate source audit.

For step 1 I opened and read the statements of lem-weil-pbc-monic-quotient-free, lem-weil-pbc-x-pow-p-minus-t-irreducible and lem-trf-irreducible-polynomial-quotient-field. They give precisely the monic basis and reduction isomorphism, the residue polynomial's irreducibility, and the nonzero field quotient. The prime hypothesis implies p>0, so the quotient has positive rank. Only k is fed into the characteristic-p irreducibility node. Freeness gives both the injective coefficient map and injectivity of multiplication by t; no domain property of C is assumed here.

For step 2 I read lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-maximal-contracts-maximal. The first applies because step 1 gives a finite basis; the second applies to this integral map for every maximal ideal of C. R is local with its sole maximal ideal (t), and the field quotient already proved that tC is maximal. Thus C has exactly that maximal ideal; this is a direct use of the cited statement, not of a proof hidden in it.

For step 3 I read def-sc-discrete-valuation-ring, lem-weil-pbc-dvr-unit-times-uniformizer-power and lem-weil-pbc-local-ring-unit-criterion. The definition explicitly includes the equivalent Noetherian local domain formulation, so the valuation-factorization node applies to R and its nonzero uniformizer. The set of nonzero coefficients is finite and nonempty. Dividing them by their minimum t-exponent leaves a unit coefficient, whose nonzero reduction cannot cancel in the residue power basis. The local-ring criterion is applied only after step 2 proves locality. The coefficient factorization is written out, not hidden as another lemma.

Step 4 is elementary from the preceding factorization: evaluation sends every unit to a unit and t to a nonzero element of the containing field, so its kernel is zero. Common denominators put every polynomial over F into c/b; its inverse is explicitly b t^(-m) d^(-1). This proves F[z]=F(z) rather than assuming the algebra generated by z is a field. Clearing denominators of a linear relation now uses the already proved injectivity and free basis, giving degree p. No unrecorded Gauss lemma, general minimal-polynomial identification or generic characteristic assumption is used.

Step 5 uses only the DVR definition and the preceding factorization. Choosing the least exponent occurring in a nonzero ideal gives its generator t^m; zero is handled separately. Domain follows from step 4, locality from step 2, and nonfield follows from the nonzero proper ideal tC. The residue identification is the explicit isomorphism from step 1 sending the variable to the residue of z. This is the ideal argument itself, not a new node restating the DVR clause.

For step 6 I read lem-weil-pbc-pid-noetherian-normal and def-weil-pbc-integral-closure. Step 5 established every hypothesis of the PID-normality result, and step 4 identified its fraction field as E. Every integral equation over R is also one over C, while the reverse inclusion follows from the finite-algebra integrality already established. These give both inclusions in the claimed integral closure.

Small cases checked: p=2 works without any divisions by 2. For equal characteristic the noncomplete example R=F_p(u)[t]_(t), a=u gives residue extension F_p(u^(1/p)) and unchanged t. For mixed characteristic R=Z[U]_(p), a=U, the residue is F_p(U), the uniformizer is p and the same proof gives degree p over Q(U). Perfect residue fields have no admissible a, so the statement is vacuous there. a=0 and a residue pth power are excluded; for a=1 the characteristic-p residue quotient is (T-1)^p and is not a field, showing exactly where the hypothesis is needed. No completeness, henselianity, excellence or separability was introduced.

Against delivery-errors B–E: all objects remain self-contained; TeX is single escaped in JSON; every non-elementary step cites the statements it uses, with verbatim citation evidence; proof_deps is precisely the union of uses; no step uses another node's proof; no new lemma or duplicate was created. All proof steps are below 2000 characters (longest 827). The only elementary steps are explicit fraction/evaluation and principal-ideal arguments. Every theorem dependency is a pre-existing Mathlib leaf, so there is no off-unit theorem use or route replacement and no dependency cycle through the item.
