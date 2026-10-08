+++
id = "fix-prop-coherence"
kind = "theorem"
title = "Coherence of the proved comparisons"
order = 2255
tags = ["latex:proposition"]
uses = ["cor-coef-verdier-weil-equivariance", "def-fix-six-functor-datum", "fix-cor-verdier-exchange", "fix-lem-exchanges", "fix-prop-projection-formula", "lem-coef-finite-exceptional", "lem-coef-integral-finite-extension", "lem-coef-integral-hom-reduction", "lem-coef-rational-operations", "lem-fix-operation-reduction", "lem-fix-weil-operations", "prop-coef-integral-exceptional-adjoint", "prop-pur-weil-equivariance-compatibilities", "thm-coef-finite-hom", "thm-pod-finite-reduction", "thm-pur-finite-reduction-of-purity"]
+++
The operations in [def-fix-six-functor-datum] and their proved
comparison maps satisfy identity, composition, exchange and projection
coherence. The elementary coefficient comparisons of
[lem-fix-operation-reduction] extend to general constructible
finite-Tor internal Hom by [thm-coef-finite-hom], to integral
internal Hom by [lem-coef-integral-hom-reduction], and to finite
coefficient-field extensions by [lem-coef-integral-finite-extension].
Exceptional comparisons on these constructible domains are
[lem-coef-finite-exceptional], [prop-coef-integral-exceptional-adjoint], [lem-coef-rational-operations]. Smooth orientation and the site-perfect Poincare pairing have
the additional compatibilities of
[thm-pur-finite-reduction-of-purity], [thm-pod-finite-reduction].
At field coefficients these maps are Weil-equivariant, with the purity
compatibilities of [prop-pur-weil-equivariance-compatibilities].

## Proof

The identity and pasting equations are [fix-lem-exchanges].
The projection diamonds and associativity are
[fix-prop-projection-formula]; taking adjoint mates gives the
corresponding equations for [fix-cor-verdier-exchange].
The maps used here are tensor reassociation, evaluation, and adjunction
units and counits, whose coefficient comparisons are proved in
[lem-fix-operation-reduction]. The general Hom comparisons
[thm-coef-finite-hom], [lem-coef-integral-hom-reduction], [lem-coef-integral-finite-extension]
are defined by the same evaluation maps. The exceptional comparisons
[lem-coef-finite-exceptional], [prop-coef-integral-exceptional-adjoint], [lem-coef-rational-operations]
preserve units and counits, so their mates satisfy the same equations.
Their Weil structures are [lem-fix-weil-operations], with
general duality equivariance given by [cor-coef-verdier-weil-equivariance]. The geometric orientation is supplied
separately by [thm-pur-finite-reduction-of-purity] and
[prop-pur-weil-equivariance-compatibilities]; composing it with
evaluation gives the pairing comparison [thm-pod-finite-reduction].
Thus coherence is inherited from the individual maps on the stated
domains, without an additional preservation or biduality assertion.
