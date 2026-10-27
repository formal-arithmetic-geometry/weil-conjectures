## Files written

- `dag/nodes/sec-six-functors/lem-sf-projection-base-change-integral.json`: statement, split with four steps, no Mathlib match. The statement and its seven statement dependencies are unchanged. Added only proof, proof dependencies, proof origin, split report, and the current NW search evidence.
- `citations.json`: ten verbatim step/node quotations. `searches.jsonl` is the original output log of the required search command.
- No new nodes and no Mathlib leaves. No unit record is changed: this is not the unit's key statement.

## Attachments

None. The exact source candidate `WeilConjectures.sixFunctorProjection_baseChange_integral` at `lean/Sheaf/Paper/ProjectionFormulaCoherence.lean:523` still ends in `sorry`, so it is not an attachment. The search of `lean/WeilConjectures/` for the item tag and for projection/base-change concepts found finite etale square theorems and higher-coefficient isomorphism assertions; none states this completed integral equality in the supplied operation coordinates. In particular the integral proper input theorem in `LocalizingInputs.lean:111` is sorried and asserts preservation and isomorphisms, rather than this equality.

## WANTED

None. All source material used is available locally. No SGA source was used.

## Corrections and source audit

No statement correction or statement dispute. I read GOAL.md, SETUP.md's three levels, the chapter, the unit, the latest blueprint proposition and its proof, and delivery-errors B--E in full. The latest blueprint proof has precisely the open/proper route followed here. The live source allocation retains an old parent proof, but it is evidence rather than an independent proved result. I checked its theorem header against the item: K is arbitrary bounded constructible, L has the uniform finite-reduction Tor predicate, the square includes its chosen compactification, and only f is separated.

A tempting inherited citation was rejected: `fix-lem-exchanges` assumes separatedness of every arrow, so it cannot justify this item's arbitrary horizontal map. The supplied exchange-stage construction of `def-sf-operation-stages`, and the explicitly unrestricted open-factor lemma, are used instead. There is no reduction-of-equality argument: finite evaluation need not be faithful. The source proof's rationalization, common field stage, and compactification-independence sentences concern other clauses and are not needed for this chosen integral square.

The archived-attempt listing prescribed in the brief returned no matching directories for this item, including other groups. The active sandbox initially had only dispatcher `.brief*` files, no item or report. I retained the live NB-created item's complete statement, source header, candidate information and historical Mathlib search records. Those inherited records are NB evidence, not searches claimed as mine. NW ran the four required search tools, with a second LeanFinder phrasing, as recorded in `searches.jsonl`; appended records identify their returned names. Returned ordinary adic-completion statements, monoidal adjunction laws, and underived sheaf pullback-composition declarations do not supply the specified completed compact-support square. I read the returned underived pullback file and the project's general mate theorem. The complete general mate square already has its own DAG node, so no new infrastructure node is warranted.

## Not duplicates

No new nodes. I searched the whole DAG and the blueprint for projection/base-change and the mate/pasting concepts and reused `lem-sf-pf-open-base-change-square`, `lem-sp-categorical-projection-mate-square` and `lem-sf-pf-compactification-pasting`. The whole blueprint's coherence proposition contains this as one clause, but is not the same statement as this coefficient-specific chosen-square node, so `blueprint.same_as` remains empty. The existing nearest ancestor is `prop-sf-pf-coherence` and its base-change paragraph remains the recorded place.

## Review by NW

For the item I read `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, its proposition, and the exact source theorem/docstring at lines 509--550 of ProjectionFormulaCoherence.lean. There are no new-node sources to review.

Step 1 reads the statements of `def-weil-finite-tor-amplitude` and `lem-sf-pf-open-base-change-square`. The former exactly defines the supplied uniform positive-quotient predicate. The latter explicitly covers the integral completed category, arbitrary finite-type horizontal g, K without finite Tor, all four intermediate proper images, the monoidality formula, and the actual open-factor identity. It therefore supplies both domains and a genuine open equation. I also read `lem-pur-integral-operations-preserve-constructible` (pullback clause for any morphism with l invertible) and `lem-coef-integral-residue-tor` (derived-complete bounded constructible equals the uniform-reduction finite-Tor class). Together they check the domain of the lower projection at GL without silently adding separatedness to g. The prime is invertible throughout because every scheme is over k of characteristic p different from l.

Step 2 reads `def-sf-operation-stages` for supplied ordinary adjunctions and the actual exchange-stage proper/open composites. It does not infer the mate property from an isomorphism theorem. I read the complete statement of `lem-sp-categorical-projection-mate-square`, and its published source theorem `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv` in ProjectionMapMate.lean. Its comparison direction is G followed by F' to F followed by H in functor order, namely theta:F'G to HF in conventional right-to-left notation. I verified the assignment of all four categories, both adjunctions, four tensor bifunctors, both tensor-pullback maps, and m_C=mu_H, m_D=mu_G. The open lemma's displayed theta monoidality is exactly its ComparisonCompatible hypothesis. Its conclusion gives the proper-factor equation including theta inverse, with neither projection nor exchange invertibility assumed. No restriction theorem for horizontal direct image is used.

Step 3 reads the entire statement of `lem-sf-pf-compactification-pasting`. The two equations from steps 1 and 2 are its two hypotheses, with the same M,Q,d,z,theta,sigma. Its formula supplies v and the ordered proper/open composites. No new lemma merely renames the requested square.

Step 4 reads `def-sf-operation-stages` and `lem-pur-derived-pullback-tensor-iso` for the specified normalized models and composition-compatible comparisons. I wrote the second-factor map t explicitly, with its source U_a U_f L and target U_f' U_g L. Substituting theta and sigma in compositor notation gives c_f'g t=c_af by compositor associativity, hence precisely the kappa in the item. The tensor comparison composition identity combines the two factor mu maps. The remaining coordinate changes are substitution of definitions and cancellation of endpoint isomorphisms; this is the elementary step. There is no independently chosen source, target, exchange, tensorator or projection map.

The generic off-unit tools are declared in split_report.tool_uses: coefficient pullback closure, the residue Tor criterion, normalized pullback tensor composition, and the abstract mate square (plus the supplied stage/domain definitions). These are tools for the unit's own open/proper route, not alternate routes through purity or duality. I checked the read-only dependency closures and found no path back to this item.

I tested the identity compactification, identity horizontal map, empty X, K=0, L=0, and n=1. The formulas remain defined; identity open factors cancel, zero routes have the same zero target, and the proof does not assume nonzero inputs or positive-dimensional fibres. No finite-Tor condition on K, no separated structure morphism, no separated g, and no projection/exchange invertibility is introduced. Every non-elementary fact used is a cited statement, all citation quotes are verbatim, and every proof step is shorter than 2000 characters.

## Unfinished work

None in this one-level stage-1 split. No Lean was written, compiled, or built. The existing cited nodes retain their own proof obligations and statuses.

## Validation

The required server dry run exited 0 and printed `OK (not pushed)` at 29eb185a543, with preflight passed. The initial citation check required longer excerpts for the uniform Tor definition and residue-Tor consequence; both were replaced by complete relevant passages. A final dry run validates this completed report before push.
