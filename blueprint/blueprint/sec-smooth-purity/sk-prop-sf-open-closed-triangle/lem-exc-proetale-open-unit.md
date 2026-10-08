+++
id = "lem-exc-proetale-open-unit"
kind = "lemma"
title = "Restriction of open extension by zero"
order = 1848
uses = ["def-weil-extension-by-zero", "def-weil-pbc-proetale-operations", "lem-weil-extension-by-zero-adjunction"]
+++
For an open immersion $j$, the adjunction unit $M\to j^*j_!M$ is an
isomorphism on pro-etale module sheaves.

## Proof

On an object $V$ over the open subscheme, every object in a covering of $V$
is still over that open subscheme. The presheaf defining $j_!M$ is therefore
exactly $M$ on this slice, and sheafification leaves it unchanged there.
Under the extension-by-zero adjunction, the resulting identification
$j^*j_!M=M$ sends the unit to the identity on every section. This proves the
statement for the named map.
