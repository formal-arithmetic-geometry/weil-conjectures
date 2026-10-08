+++
id = "open-sf-preservation-gaps"
kind = "remark"
title = "Scope beyond the constructible coefficient category"
order = 2211
tags = ["latex:openproblem"]
uses = ["cor-weil-boundary-duality-discharge", "lem-coef-normalized-dvr-effectivity", "open-sf-ambient-adjoint-input", "rem-sf-class-adjoint-residue", "rem-sf-proetale-hom-status", "rem-sf-tower-shapes-occurring", "thm-fix-general-biduality", "thm-sf-biduality-class"]
+++
General finite-coefficient Verdier preservation and biduality are proved
in [thm-fix-general-biduality]; closed-boundary exchange follows in
[cor-weil-boundary-duality-discharge]. The scope beyond that theorem
is as follows:

1. General duality at $\mathcal O_E,E,\Qlb$ is now supplied
by [thm-sf-biduality-class], using the independent finite and
integral coefficient comparisons. It is no longer an open input.
1. The dimension-free internal-Hom bound $[c-b,d-a]$ still requires
a site-perfect first variable. Its failure for a general constructible
first variable, recorded in [rem-sf-proetale-hom-status], is compatible
with the geometric dimension bound for Verdier duality.
1. A coherent normalized DVR tower reconstructs by
[lem-coef-normalized-dvr-effectivity]; constructibility follows
when its terms have the required uniform bounds. No common local
model is needed for that lemma. Unverified towers and other coefficient
systems retain the scope distinctions of [rem-sf-tower-shapes-occurring].
1. An ambient adjunction outside the comparison class remains outside
these claims, as in [open-sf-ambient-adjoint-input] and
[rem-sf-class-adjoint-residue].
