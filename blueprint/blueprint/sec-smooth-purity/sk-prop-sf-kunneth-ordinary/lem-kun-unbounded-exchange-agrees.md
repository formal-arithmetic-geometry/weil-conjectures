+++
id = "lem-kun-unbounded-exchange-agrees"
kind = "lemma"
title = "The unbounded exchange extends the bounded exchange"
order = 1667
uses = ["def-kun-unbounded-exchange", "def-weil-pbc-derived-exchange", "def-weil-pbc-underived-exchange", "lemma-weil-pbc-derived-exchange-replacement"]
+++
For $K\in\Dplus(X_{\Et})$ the exchange morphism
$\Ex_{\square,K}$ of [def-kun-unbounded-exchange] is the exchange
morphism of [def-weil-pbc-derived-exchange]; in particular for
sheaves (complexes concentrated in degree $0$) with
$\Lambda$-module structure it agrees with the exchange morphism of
[def-weil-pbc-underived-exchange].

## Proof

Both morphisms are defined as the same adjoint mate of the same
composite and are independent of the K-injective model
(lem:weil-pbc-derived-exchange-replacement), so they agree.
