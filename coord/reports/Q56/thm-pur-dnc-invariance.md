# Q56 worker report: thm-pur-dnc-invariance

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-dnc-invariance.json`: the item, retained as a five-step split and marked `split`; no new dependency nodes and no Mathlib leaves.
- `citations.json`: 42 verbatim statement quotations, one for every use of a cited node in the five proof steps.
- `report.md`: this report and the Q56 review signature.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for `thm-pur-dnc-invariance`, `dncInvariance`, `existsUnique_dncInvariance`, `nonempty_iso_sectionInvariant_normalCone`, and the DNC/section-invariant names. The source contains only comments about the target; it has no declaration under `WeilConjectures/` stating this item. The upstream/master sorry declarations and the imported `lean` metadata in the DAG were not treated as finished proofs.

## Sources wanted

None. The proof follows the imported `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-dnc/thm-pur-dnc-invariance.md` route, while I also checked the current `literature/blueprint/main-20261015/` update and the chapter/unit records. No SGA 4 or SGA 4½ source is used.

## Source error

`STATEMENT-DISPUTED:` The short blueprint statement delegates its hypotheses to `def-pur-dnc-section-family`, whose statement assumes finite type and smoothness but does not require (B) and (V) to be separated. The family-constancy proposition used by the proof, and the chapter's constructible exceptional inverse image, require the separated finite-type domain. A concrete type-check example is the finite-type doubled-origin affine line (B), with (V=\mathbf A^d_B), projection (g), and its zero section: this satisfies the unqualified family description but does not satisfy the separated-base hypotheses of the proposition or the stated exceptional-operation domain. I retained the corrected imported statement, which explicitly assumes separated finite-type (B,V), separated finite-type (g), and quantifies base changes (B'\to B) with (B') separated finite type. This records the source gap rather than silently applying the proposition outside its hypotheses.

## What was wrong and what changed

The repository already held the expanded split but still had `status: "unsplit"` and no Q56 handoff report. I did not move the item's proof into a new node: the five steps are the proof itself, and every non-elementary input is an existing DAG node. I changed only worker-owned split metadata and supplied the required citation file and report. The long coordinate and uniqueness steps were read in full; their local chart calculations and sheaf-gluing argument are routine expansions of the cited statements, not hidden separate comparison lemmas.

## Review by Q56

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-thm-dnc.json`, the current main-20261015 blueprint node, and the master blueprint proof. I opened every statement in the 26 direct dependencies named by the item and checked that each quotation in `citations.json` is a verbatim statement substring. I also checked that all proof uses occur in `proof_deps`, that the statement dependencies name the objects in the statement, and that there is no new node, duplicate, or dependency cycle.

Step 1 uses `prop-pur-dnc-family-constancy` for the lisse-line, normalized family comparison, and its separated finite-type hypotheses. The domain checks use the existing finite-type-over-Noetherian, separated-base-change, blow-up properness, proper-morphism, Noetherian-open, quasi-compact-open-immersion, proper/finitely-presented permanence, exceptional-inverse-image, closed-immersion ideal-sheaf, DNC geometry, DNC-family, derived-pullback, closed-immersion, and locally-Noetherian definition statements. I verified the center ideal calculation (R[t]\twoheadrightarrow(R/I)) with kernel ((I,t)), the finite-generation argument on Noetherian affine charts, and that (D_sV), (N_s), and all three exceptional maps are in the separated finite-type domain before applying the family proposition.

Step 2 uses the geometry statement for the zero fibre and the derived-pullback functor. I checked the direction of (i_0^*\kappa): it maps the normal-fibre object to (C(g,s)), so the inverse is required in the displayed composite (C(g,s)\to C(\pi_N,0_N)). The pullback identification from (a\circ i_0=\mathrm{id}_B) supplies the remaining factor.

Step 3 uses the DNC geometry and family-constancy statements for the standard pair, punctured comparison, fibre identifications, and normalized comparison. The chart refinement is affine over an affine base and preserves principal opens; I checked that it does not claim a global isomorphism (V\cong\mathbf A^d_B). The coordinate maps and their deformation maps are checked finite type and separated using the cited quasi-compactness and relative-diagonal permanence statements. The cohomological-smoothness locality/composition statements give the displayed dualizing comparisons, and the family proposition identifies the normalized chart map with the global κ. The two fibre identities at (t=0,1) then give (n_i\alpha_i c_i^{-1}=\mathrm{id}), exactly the required coordinate normalization.

Step 4 uses family constancy for the common shift and lisse line, twist preservation to cancel the invertible twist, derived-single full faithfulness to reduce a derived automorphism to a sheaf automorphism, and the DNC coordinate geometry for local identity. I checked the localization objects and restriction formula from the derived-pullback, pro-etale-site, localized-ringed-site, and weakly-etale-localization statements. The sheaf-hom cover-gluing lemma then makes the local identity global. This proves uniqueness without assuming faithful pullback on arbitrary derived morphisms.

Step 5 uses separated finite-type base change, smooth relative-dimension permanence, and proper/finitely-presented permanence to verify every primed construction and section remains in the allowed domain. Family constancy and DNC geometry supply the base-changed κ, zero-fibre comparison, and fibre identifications. I checked the cartesian equality \(\bar b\,i'_0=i_0b\), the induced equality of pullbacks, and that the derived-pullback functor preserves composites and inverses, yielding (b^*\alpha=\alpha'). Taking an etale separated finite-type chart as (b) gives localization. No flatness of (b) is used.

I tested edge cases at the statement level: (d=0) makes the normal bundle the zero bundle and all shifts/twists trivial; the standard pair gives the identity comparison; a nonseparated finite-type base exposes the source type gap recorded above; and arbitrary nonflat base change is covered by the proposition's stated clause. The two steps longer than 2000 characters (coordinate normalization and uniqueness) were read for hidden lemmas; they are explicit local calculations and ordinary sheaf descent using the cited statements. No new node is justified, and no Mathlib declaration matches the geometric DNC comparison.

## What remains unfinished

Nothing at this one-level stage-1 split. The existing prerequisites remain separate DAG nodes, and no Lean file was written or compiled.
