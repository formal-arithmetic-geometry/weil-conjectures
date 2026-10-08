+++
id = "prop-weil-pbc-rational-transport"
kind = "theorem"
title = "Functorial transport to a finite field"
order = 1306
uses = ["def-weil-pbc-rational-category"]
tags = ["latex:proposition"]
+++
Every exact $\mathcal O_E$-linear functor among the integral constructible
categories, and every natural transformation between such functors, extends
uniquely to the rationalization of [def-weil-pbc-rational-category]. In
particular $Rf_*$, completed pullback, and their exchange transformation
define exact functors and a natural transformation on $\Dbc(-,E)$.

## Proof

Localization at a central natural endomorphism (inverting the
multiplication by $\varpi$) is functorial for exact functors and natural
transformations, so every integral datum descends uniquely to the category
of [def-weil-pbc-rational-category]; applying this to the direct image,
completed pullback, and the completed exchange morphism gives the displayed
structures.
