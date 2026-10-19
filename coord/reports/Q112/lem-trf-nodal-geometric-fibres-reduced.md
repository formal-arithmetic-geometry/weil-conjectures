# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-nodal-geometric-fibres-reduced.json` — statement split, no new nodes, no Mathlib leaf for the full assertion.
- `citations.json` — verbatim statement quotes for every cited node and proof step.

Attachments: none.

WANTED: none.

The item was already present in the repository as an unsplit statement. I preserved its hypotheses and source, and supplied a five-step proof. The existing Mathlib searches in the item were read and reused; they found only general geometric-reducedness APIs, not the nodal assertion. A whole-DAG and whole-blueprint search found no duplicate supporting node. No statement correction was needed.

## Review by Q112

I read the item and the current blueprint ancestor `lem-trf-local-term-locality`, then read Stacks Project `curves.tex`, Tag 0E37 (the geometric-reducedness paragraph of `lemma-facts-about-nodal-curves`) and its cited reducedness and finite-inseparable inputs. The item agrees with Tag 0E37 in allowing an arbitrary field, empty base changes, one-dimensional components, smooth closed points or completed ordinary nodes, and no properness, separatedness, connectedness, or marking assumptions.

Step 1 fixes an arbitrary algebraically closed extension and handles the empty case. The finite-type-over-Noetherian statement supplies Noetherianity of the base-changed curve, and the locally-finite-type-over-a-field Jacobson statement supplies closed specializations. I checked that these hypotheses hold for `C_Ω` and that the intended localization argument only needs reducedness at closed points.

Step 2 checks the two kinds of closed points separately. At a smooth point, a smooth neighbourhood over `Ω` satisfies the cited smooth-geometrically-reduced statement, so its local ring is reduced. At a node, I checked the completed model directly: restriction to the two axes embeds `Ω[[u,v]]/(uv)` into `Ω[[u]] × Ω[[v]]`; a series vanishing on both axes is divisible by `uv`, and each one-variable power-series factor is a domain by the cited Mathlib leaf. The finite-type Noetherian hypothesis makes completion faithful flat, hence injective, so reducedness of the completion reflects reducedness of the local ring. The completion and node hypotheses are used exactly where stated.

Step 3 uses the Jacobson closed specialization and the localization map from a closed point to its generization. Reducedness localizes, so all stalks are reduced; the reduced-scheme definition then gives `C_Ω` reduced. This is the local-to-global conclusion of Tag 0E37, with no hidden properness or irreducibility assumption.

Step 4 checks an affine chart `Spec A` and a finite purely inseparable extension `E/k`. Embedding `E` into an algebraically closed extension `Ω` gives an injective map `A ⊗ₖ E → A ⊗ₖ Ω` by flatness over a field and exactness after tensoring. Step 3 makes the target reduced, and the cited finite-purely-inseparable test then gives reducedness of `A ⊗ₖ L` for every field extension `L/k`. Step 5 identifies these tensor rings with the affine open charts of `C_L` using the cited open-fibre-product and affine-fibre-product statements, and applies the reduced-scheme definition. Thus the final geometric-reducedness conclusion has exactly the stated quantifier over all `L/k`.

The only off-unit generic input is `sbc-lem-smooth-geometrically-reduced`, declared in `split_report.tool_uses`; it supplies the standard smooth-point reducedness fact that this unit does not state. Every other proof dependency is an existing DAG node or Mathlib leaf, and every citation quote is recorded verbatim in `citations.json`. Edge cases checked were `C=∅`, a smooth affine line, the nodal affine curve `Spec Ω[u,v]/(uv)`, a disjoint union of such components, and purely inseparable field extensions. No SGA source was used.

What could not be finished: nothing.
