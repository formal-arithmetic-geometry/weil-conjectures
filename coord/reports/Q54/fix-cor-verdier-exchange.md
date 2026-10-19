# Worker report: fix-cor-verdier-exchange

Files written: the existing item node `dag/nodes/sec-six-functors/fix-cor-verdier-exchange.json`; no new nodes; `citations.json` records every proof-step citation. The item is retained as a split statement with five proof steps and no Mathlib leaves. Its imported `split_report` and maintainer review metadata are preserved.

Attachments: none. No sorry-free declaration in the checked source states this old-master item exactly; the nearby `sk-thm-sf-verdier-exchange` declaration has different hypotheses and is not an attachment.

WANTED: none.

I checked the item against `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/fix-cor-verdier-exchange.md` (node order 2117) and its proof, and compared the route with the corresponding `main-20261015` proof file. The statement keeps the source's exceptional-admissibility hypotheses, coefficient stages, finite-Tor domain, canonical exchange, and the three stated compatibilities. The repository item already contains the expanded Hom-mate argument and does not alter the imported statement or maintainer fields.

## Review by Q54

For step 1 I opened `def-fix-six-functor-datum`, `thm-sf-comp-composition`, and `fix-prop-adjunctions`. The first supplies compact-support composition data, the second supplies the natural composition isomorphism with its direction, and the third supplies the exceptional adjunctions and their units and counits. The displayed Hom chain therefore constructs the mate `Rf^!Ra_Y^!L ≅ Ra_X^!L`; I checked that `a_X=a_Y∘f` and that the finite-level composition theorem is used only at finite coefficients. The exact sentences used from each node are copied verbatim in `citations.json`.

For step 2 I read `fix-prop-adjunctions`, `fix-lem-tensor-adjunction`, and `def-weil-exceptional-inverse-image`. The adjunction node explicitly restricts the Hom bijections to `D^b_ctf`; the tensor-Hom node has exactly the required canonical isomorphism and coefficient/shift naturality; the exceptional-inverse-image node explicitly records finite-Tor preservation. Thus `N=ω_Y` and `Rf_!M` are in the required domain, and the two displayed arrows have the claimed source and target.

For steps 3–5 I read the compatibility clauses in `fix-lem-tensor-adjunction`, the unit/counit and refinement clauses in `fix-prop-adjunctions`, the scalar-extension requirement in `def-weil-exceptional-adjoint-admissibility`, and the comparison-preserves-units/counits clause in `lem-fix-operation-reduction`. These support the naturality square, the mate comparison equation, finite reduction and scalar extension, and simultaneous shifts. I checked that the coefficient claim is restricted to the stipulated comparison maps and does not introduce an ambient coefficient-change isomorphism. The small identity case and the zero/empty-object cases reduce to the stated adjunction identities. The retained long compatibility step was separated into naturality, coefficient, and shift steps. The coefficient part is a single transpose calculation with the explicitly cited pasted counit, rather than a new independent comparison lemma. No new node was necessary: every cited fact is already stated by an existing node, and no step merely cites a definition for a theorem.

The previous attempt had no report or citations file, so this continuation added those required delivery artifacts, source locations and the split status. No Lean file was written and no compiler or build tool was run.

## Not duplicates

No new nodes. Blueprint search for Verdier and a DAG search for the exchange formula found `sk-thm-sf-verdier-exchange` and `thm-sf-verdier-exchange`; both have a more general unconditional constructible-adjoint formulation. They are recorded under `blueprint.same_as`; the assigned conditional item is retained, and its proof follows its own tensor-Hom route.
