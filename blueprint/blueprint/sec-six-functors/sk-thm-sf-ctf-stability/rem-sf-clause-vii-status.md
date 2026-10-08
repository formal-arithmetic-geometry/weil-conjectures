+++
id = "rem-sf-clause-vii-status"
kind = "remark"
title = "Proved coefficient transport and its domains"
order = 2207
uses = ["cor-coef-finite-verdier", "def-coef-normalized-dvr-tower", "lem-coef-finite-exceptional", "lem-coef-integral-finite-extension", "lem-coef-integral-hom-reduction", "lem-coef-normalized-dvr-effectivity", "lem-coef-rational-operations", "lem-fix-operation-reduction", "lem-fix-weil-operations", "prop-coef-integral-exceptional-adjoint", "rem-sf-tower-shapes-occurring", "thm-coef-finite-hom", "thm-coef-integral-verdier", "thm-coef-qbar-verdier", "thm-sf-hom-ctf"]
+++
Pullback, tensor, and the elementary coefficient comparisons are
[lem-fix-operation-reduction]. General finite constructible
internal Hom, duality, and exceptional inverse image have the
comparisons
[thm-coef-finite-hom], [cor-coef-finite-verdier], [lem-coef-finite-exceptional].
At integral coefficients the corresponding conclusions are
[lem-coef-integral-hom-reduction], [thm-coef-integral-verdier], [prop-coef-integral-exceptional-adjoint].
Their finite scalar-extension and rational identifications are
[lem-coef-integral-finite-extension], [lem-coef-rational-operations], [thm-coef-qbar-verdier].
These comparisons preserve the specified evaluations and adjunction
maps. The coefficient-only sharp Hom bound still requires the
site-perfect hypothesis in [thm-sf-hom-ctf]; that bound is a
different assertion from coefficient comparison.

A separately supplied DVR system reconstructs with its stated
reductions once the coherent normalization condition of
[def-coef-normalized-dvr-tower] is verified, by
[lem-coef-normalized-dvr-effectivity]. Constructibility of the
result additionally requires the stated finite-level finiteness and
uniform bounds. Common lisse local models are an optional stronger
description, as [rem-sf-tower-shapes-occurring] explains.
The formal Weil lift [lem-fix-weil-operations] applies to these
proved operations; duality equivariance is
[cor-coef-verdier-weil-equivariance].
