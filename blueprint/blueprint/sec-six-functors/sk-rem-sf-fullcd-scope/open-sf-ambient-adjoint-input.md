+++
id = "open-sf-ambient-adjoint-input"
kind = "remark"
title = "Adjunction outside the bounded comparison class"
order = 2051
tags = ["latex:openproblem"]
uses = ["thm-sf-ambient-adjoint-class"]
+++
The comparison construction of [thm-sf-ambient-adjoint-class]
provides the exceptional right adjoint relative to bounded-below inputs
of étale origin. It suffices for the bounded constructible class;
its finite-coefficient preservation is [thm-sf-preservation-class].
An adjunction for arbitrary unbounded pro-étale complexes is not proved
by that comparison and is not used as an automatic consequence; see
[rem-sf-class-adjoint-residue]. It is in fact *false in general*: for the
structure morphism of an elliptic curve over $\overline{\mathbf F}_p$ and
$A=\mathbf F_r$ there is a pro-étale sheaf, not of étale origin, with nonzero
cohomology in every degree, so $Rf_!=Rf_*$ does not preserve coproducts and
has no right adjoint on $D$ or on $D^+$ (the counterexample is recorded in the
sketch block of this remark and in rem:sf-ambient-counterexample). The former
recorded input "i:pe-direct-image-coproducts" is therefore false in general
and not used; what remains open is nothing that the blueprint needs. General finite-coefficient Verdier
biduality is independently proved in [thm-fix-general-biduality],
and its boundary exchange is [cor-weil-boundary-duality-discharge];
neither assertion needs the unrestricted ambient adjunction left open here.
