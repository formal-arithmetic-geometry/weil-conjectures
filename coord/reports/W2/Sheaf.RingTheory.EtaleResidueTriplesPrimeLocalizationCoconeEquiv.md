## What changed

Replaced the single sorry in `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeEquiv`
with a complete Lean reduction to unique extension and unique restriction of compatible
cocone legs. Added a concrete Prop-valued relation in its own module and two theorem modules.
The original theorem signature and visibility are unchanged.

For each global cocone, the extension theorem uniquely determines the local cocone chosen
in the proof. Restriction gives injectivity and surjectivity of this assignment.
`Equiv.ofBijective` packages the resulting bijection. Associativity shows that postcomposition
preserves the relation; uniqueness proves naturality. The relation applied to the identity
R-triple proves agreement on R using `t.compatible`, `hψ`, and `hK`.

All four modules compile individually through lcompile.py, each in under five seconds.
This is a decomposition, not an axiom-free proof of the mathematical descent theorem.

## Proved and sorry left

Closed one original hole by decomposition:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_coconeEquiv`
(node `new-lem-sbc-etale-triples-prime-localization-cocone-equiv`).

Added two holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_extension`
  (node `new-lem-sbc-etale-triples-prime-localization-cocone-extension`).
- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction`
  (node `new-lem-sbc-etale-triples-prime-localization-cocone-restriction`).

The concrete `etaleResidueTriples_primeLocalization_coconeRelation` definition has no hole.
Each remaining theorem states only one direction for one fixed vertex and one fixed cocone;
neither asserts an equivalence, vertex naturality, or the final identity-leg equation.
The parent proves those conclusions using both directions.

Edge cases checked mathematically: R a field (localization is the identity), arbitrary K
without separable-closure assumptions, the zero vertex ring, and a vertex receiving no
cocones. The relation uses only pointed R-maps and never assumes an algebra structure on V.
For the zero vertex the legs are unique. Nonexistent global cocones are not assumed to exist;
the two lemmas quantify over a supplied cocone. All denominators are nonzero in K because
the kernel of the prescribed base pointing is p (respectively q).

## No longer needed

Removed the parent's direct proof imports of
`Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations` and
`Sheaf.Paper.EtaleFiniteDataDescent`. They remain needed by the planned extension obligation;
the localization-colimit input is also available for the restriction obligation.
No original dependency node is globally pruned by this reduction. No unit realization is
bypassed: `sk-prop-input-spreading.realized` has no statements or steps attached to this node.
The three new proof imports are the relation (transitively), extension, and restriction.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its two existing inputs do not directly state
the required pointed-cocone constructions. The missing glue consists of descent of pointed
models and the converse base-change/restriction construction. Those steps are now explicit
independent obligations with full proofs in words. Mathlib searches found only generic
`coconesEquiv` for final functors and `Equiv.ofBijective`; LeanSearch was unavailable.

An initial sandbox attempt claimed naturality for arbitrary equivalences. That claim is
false without a compatible-leg specification and was discarded completely. The delivery
contains none of those initial declarations or nodes. Naturality is now a proved consequence
of the compatible-leg relation and unique extension.

## New nodes

`new-def-sbc-etale-triples-prime-localization-cocone-relation` defines compatibility of two
cocones on every ring map between a global and a local triple respecting the R-structure and
pointings into K. Its data is an explicit formula; it has no sorry.

`new-lem-sbc-etale-triples-prime-localization-cocone-extension` isolates the forward descent
construction, independence of models, compatibility of all legs, and uniqueness. Its planned
proof uses the original localization-colimit and finite étale data descent inputs.

`new-lem-sbc-etale-triples-prime-localization-cocone-restriction` isolates the reverse
construction by base change of each global triple and restriction of local legs. Its proof
uses base-change stability of étaleness and the universal property of localization.

No existing interface changed, so no change record or forced adaptations are required.

## Second reading by W2

1. **Visible declarations and statements.** Compared the delivered parent module with the repository version. The target theorem signature is byte-for-byte unchanged; the new relation and two split-off theorem signatures are explicit and match their DAG nodes. Verdict: pass.
2. **Compilation and proof hygiene.** Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds. The parent has no `sorry`, while the two named descent obligations contain exactly their documented `sorry`s. No forbidden axioms, unsafe declarations, or hollow definitions were added. Verdict: pass.
3. **Truth and strength of split statements.** The relation is a concrete Prop expressing exactly compatibility along pointed maps. Extension and restriction each quantify over one supplied cocone and assert existence and uniqueness of the corresponding cocone; they are strictly smaller than the parent equivalence and are needed by its construction. Their proof obligations remain honestly split with source prose and DAG nodes. Verdict: pass.
4. **Shortest route and pruning.** The parent uses the split extension/restriction inputs and elementary associativity/uniqueness; removed direct proof-only imports are no longer used by the parent. The extension and restriction modules retain the imports required by their planned obligations. No unit route is bypassed. Verdict: pass.
5. **DAG agreement.** Updated proof and proof-dependency records for the parent and supplied matching records for all new declarations. The realized unit remains unchanged. Verdict: pass.

Changes made during second reading: added this review section only; no Lean declaration or statement required repair.
