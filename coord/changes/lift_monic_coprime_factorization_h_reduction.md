# Polynomial.lift_monic_coprime_factorization_h_reduction

## Reason
The split-off lemma omitted the reduced factorization hypothesis and monicity of the first reduced factor, so it was false. For example, with identity maps, `g₀ = 1`, `h₀ = 1`, `g' = 1`, `h' = 2`, and `f = 2`, the old hypotheses hold but the conclusion fails.

## Old
The theorem had only `hh₀`, `hfactor`, and `hgred` as relevant hypotheses.

## New
The theorem additionally takes `hg₀ : g₀.Monic` and `hfactor₀ : f.map (Ideal.Quotient.mk I) = g₀ * h₀`.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale | C3 | supplies the two hypotheses from its target assumptions |

## Status
landed 20261012T113945-L-820245 2026-10-12 (merge of deliver/C3/Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale)
