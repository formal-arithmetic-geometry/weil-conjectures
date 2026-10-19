Files written:
- `dag/nodes/sec-trace-formula/lem-trf-log-regular-monoidal-ideal-contraction.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-kato-tor-independence-chart.json` — statement-only Kato Tor-independence input, no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited proof step.

Attachments:
- None. No finished declaration in the slopmaster2 source states this item or the new Tor statement.

WANTED: Kato, 1994, §6.1(ii), for the Tor-independence theorem used by `lem-trf-kato-tor-independence-chart`.

The imported item had no proof. I retained its statement and hypotheses, including the empty monoid ideal. The source's Exposé VIII, Lemma 3.4.3 is stated for log ideals on the whole log scheme; I specialized its chart proof to the strict henselian stalk. The only external input not already represented in the DAG is Kato's Tor-vanishing result, so it is a separate unsplit node rather than an unsupported citation. No source error or statement dispute was found.

## Review by NY

For this repair I re-read the current DAG version of `def-trf-fs-log-blowup`, whose statement now explicitly defines the chart pushout, fs conditions, characteristic quotient, and log-regular dimension condition. I checked that the item and the statement-only Tor node still use exactly this definition and that the changed chart sentence supplies the unit/characteristic identification used below. I also re-read the item node, the existing sharp-chart node, the parent `lem-trf-free-characteristic-regular-boundary` that uses this item, and the complete Exposé VIII §3.4.1–3.4.4 passage in the Illusie–Laszlo–Orgogozo PDF. I read the Kato citation location as it appears in the source proof; the Kato paper itself is recorded as WANTED because it is not in the literature directory.

Step 1 defines the contracted monoid ideal $K=a^{-1}(JA)$ and checks closure under addition directly from multiplicativity of $a$. It now explicitly cites the changed definition node for the chart pushout and its identification of the chart monoid modulo units with the characteristic monoid. Together with the sharp-chart statement, this supplies finite generation, integrality and sharpness, and ensures that nonzero chart elements are nonunits in the local ring and that the sharp monoid maximal ideal generates a proper ideal. Step 2 applies the new Tor statement separately to $J$ and $K$; the standard Tor exact sequence identifies each tensor of a monomial ideal with its multiplication image in $A$, and right exactness then makes $(KR/JR)\otimes_R A$ vanish because $JA=KA$. Step 3 spells out the source's quotient argument: finite generation permits a minimal monomial in $K\setminus J$, whose class gives an $R$-linear quotient onto $R/\mathfrak m_PR$; tensoring gives a quotient onto $A/\mathfrak m_PA$. The sharp-chart citation used there is exactly the statement that $P$ is finitely generated and sharp. Step 4 checks that $A/\mathfrak m_PA$ is nonzero because all generators are nonunits, yielding the contradiction and covering the empty ideal as well. I tested the edge cases $P=0$, $J=\varnothing$, $J=P$, and a one-generator chart $P=\mathbf N$; all reduce to the asserted contraction behavior.

All proof dependencies are the union of the step uses, every citation quote is copied verbatim into `citations.json`, and the new node is statement-only with its blueprint ancestry and four recorded Mathlib searches. No Lean files, compiler, Lake, or build tool was used.
