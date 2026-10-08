+++
id = "rem-pur-ambient-only"
kind = "remark"
title = "The ambient datum of this chapter is a theorem on its coefficients"
order = 1948
uses = ["def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-exceptional-adjoint-admissibility", "lem-exc-closed-ambient", "lem-exc-closed-amplitude", "lem-exc-open-complement-known", "lem-exc-residue-tor-test", "lem-sf-proetale-constructible-origin", "prop-exc-closed-tor", "thm-sf-ambient-adjoint-class", "thm-sf-fullcd-class"]
+++
Of the three clauses of
[def-weil-exceptional-adjoint-admissibility] this chapter uses only
clause (1), the ambient exceptional right adjoint datum of
[def-weil-ambient-exceptional-adjoint]: the existence of
$Rf_n^{\times}$ on the ordinary derived categories, together with the
full cohomological-dimension condition. That clause is *not a
hypothesis* of this chapter: on the bounded constructible and finite-Tor
coefficients that every statement below quantifies over — the coefficients
of the blueprint's class [def-sf-fullcd-used-class], which by
[lem-sf-proetale-constructible-origin] are exactly the sheaves of
étale origin — both of its halves are theorems, the vanishing half
[thm-sf-fullcd-class] with the bound $2\dim\overline X$ and the
existence half [thm-sf-ambient-adjoint-class] with its unit, counit and
compactification comparisons, together
[cor-sf-ambient-adjoint-discharge]. The datum remains an assumption
only for the complexes outside that class, and no statement of this chapter
applies the adjunction $Rf_!\dashv Rf^!$ to such a complex
([rem-sf-class-adjoint-residue]). The two preservation clauses are
likewise not hypotheses:

1. clause (2), the constructibility clause, is *derived* in this
chapter for the morphisms for which purity is proved:
[cor-pur-smooth-admissibility] below shows that a smooth
morphism of pure relative dimension $d$ satisfies
$Rf^{!}\cong Lf^{*}(-)(d)[2d]$, hence carries
$D_c^{[a,b]}(Y,A)$ into $D_c^{[a-2d,b-2d]}(X,A)$; for a closed
immersion it is proved without any purity input in
[lem-exc-closed-ambient], [lem-exc-closed-amplitude];
1. clause (3), the finite-Tor clause, is likewise *derived* here
for smooth morphisms, in the same corollary: the residue-field
criterion [lem-exc-residue-tor-test] reduces it to the
vanishing degrees of $Lf^{*}(K\otimes^L_A\kappa)(d)[2d]$, which
the criterion applied to $K$ controls. For a closed immersion it
is proved without purity in [prop-exc-closed-tor]. For a
general separated finite-type morphism it is derived in the assembly
of [thm-pur-general-admissibility] and
[cor-pur-general-admissibility-datum] from the ambient datum,
which on the coefficients of those two statements is the theorem
[cor-sf-ambient-adjoint-discharge], together with the
open-complement condition supplied by
[lem-exc-open-complement-known]; no clause of
[def-weil-exceptional-adjoint-admissibility] is assumed where
the two preservation clauses are used.

In particular no statement of this chapter presupposes the admissibility
of a general separated finite-type morphism, so the present chapter and
the chapter on exceptional right adjoints do not use each other's
conclusions: that chapter records the smooth adjunction as a separate
obligation, and this chapter records the preservation clauses as
conclusions rather than hypotheses
(rem:weil-admissibility-split).

General finite-coefficient Verdier biduality on $D^b_{ctf}$ is
the independent geometric theorem [thm-fix-general-biduality].
It proves preservation before biduality by stratification, geometric
generic restriction, and dimension induction. It is not inferred
solely from existence or preservation of an ambient right adjoint.
The subsequent coefficient comparisons extend it to the specified
integral and field categories, as exported in
[thm-sf-biduality-class]. The smooth orientation constructed in
this chapter identifies the dualizing object in that separate theorem;
this navigation record is not an input to the purity proof.

The two closed-immersion statements
([lem-exc-closed-amplitude], [prop-exc-closed-tor]) are conditional on
the open-complement condition of the pair they treat, which is a statement
about the ordinary direct image and is proved in the chapter on exceptional
right adjoints from the direct-image finiteness theorems of Blueprints 06b
and 07 ([thm-sf-preservation-class]). Apart from the ambient
exceptional right adjoint datum — a theorem on the coefficients used
here, as just recorded — this chapter therefore assumes no geometric
hypothesis at all.
