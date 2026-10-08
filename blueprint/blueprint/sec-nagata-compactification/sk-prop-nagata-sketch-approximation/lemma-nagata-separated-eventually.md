+++
id = "lemma-nagata-separated-eventually"
kind = "lemma"
title = "Property of the selected separated descent stage, [stacks-project]"
order = 369
lean = ["AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated"]
uses = ["def-nagata-separated-descent-stage", "lemma-nagata-closed-immersion-descends", "lemma-nagata-diagonal-base-change", "lemma-nagata-finite-presentation-descends", "lemma-nagata-separated-descent-stage-exists"]
+++
The constructed morphism
$X^{\mathrm{sep}}_{\lambda_{\mathrm{sep}}(X/S)} \to S_{\lambda_{\mathrm{sep}}(X/S)}$ is
separated and of finite presentation, and its base change to $S$ is
canonically $X\to S$.

## Proof

The initial descended model is finite presentation and has base change $X$.
The diagonal base-change lemma identifies the base change of its diagonal
with the closed immersion $\Delta_{X/S}$. At the explicitly selected
closed-immersion stage, the actual diagonal is closed, hence the model is
separated. Finite presentation and the base-change identification persist
under increasing the stage.
