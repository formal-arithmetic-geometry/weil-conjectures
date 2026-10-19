# Worker report: def-trf-iterated-weil-map

## Files written

- `dag/nodes/sec-trace-formula/def-trf-iterated-weil-map.json`: existing definition item, status changed from `imported` to `split`; statement and its three existing statement dependencies retained; no new nodes and no Mathlib leaves.
- `citations.json`: empty, because the definition has no proof steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id, by iterated Weil and scheme-Frobenius terminology, and by the relevant declarations. The source declaration `AlgebraicGeometry.ProEtale.WeilComplex.coeffIterate` in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Frobenius.lean` is a sorry-free definition of an iterate of an arbitrary coefficient morphism, but it does not define the required composite with the scheme/Galois comparison `κ^(m)`, so it does not state this item exactly and is not an attachment.

## WANTED

None.

## What was checked

The item is a definition, so its proof and proof dependencies remain empty. Its statement uses exactly `def-trf-strict-weil-complex` for the pair `(K, φ)`, `def-trf-scheme-frobenius` for `g_γ` and `Φ`, and `prop-trf-scheme-galois-comparison` for `κ^(m)`; all three are already in `stmt_deps`. The cocycle assertion is a forward pointer to `lem-trf-iterated-weil-cocycle`, not a dependency needed to define the maps. I searched the whole DAG and both blueprint snapshots for duplicate iterated-Weil or scheme-Frobenius-map statements; the only matching item is this node, while downstream nodes merely use it. The current main-20261015 blueprint statement was read and retained, including `m ≥ 1`, the derived pullback domains, and invertibility of both composites. I checked `m = 1` (the composite reduces to the one-step Weil map after `κ`) and the empty/zero-object cases, where the same typed composition is the unique available map. No statement correction, new node, or Mathlib leaf is required.

## Review by Q85

I read the stage-1 brief, the chapter `sec-trace-formula`, unit `sk-d-weil`, delivery-errors B–E, GOAL.md, coord/dag-sync.md, and the current and master blueprint files for this node. I opened the full statements of `def-trf-strict-weil-complex`, `def-trf-scheme-frobenius`, and `prop-trf-scheme-galois-comparison`. The first supplies `K ∈ D^b_ctf,W(X,A)` and the isomorphism `φ : Lg_γ^*K ≅ K`; the second supplies the iterated maps `g_γ^m` and `Φ^m`; the third explicitly supplies the natural isomorphism `κ^(m) : LΦ^m* ≅ Lg_γ^{m*}`. Thus every object and morphism in the item is stated by an existing dependency, with no hidden proof fact or uncited hypothesis. Since this is a definition, there are no proof-step citations to quote and `citations.json` is correctly empty.

I read the source implementation around `WeilComplex.frobeniusIterate` and `WeilComplex.coeffIterate` (Frobenius.lean, lines 139–264) and verified that it only constructs the coefficient iterate, while the required `u_m = φ^[m] ∘ κ^(m)_K` interface is absent. That prevents an exact attachment. The source states the edge case `m = 1` as `coeffIterate_one` (lines 258–261), but that lemma has body `sorry`; it is not proof evidence. The blueprint definition itself gives `φ^[1] = φ` and `u_1 = φ ∘ κ_K`; no stronger source declaration was inferred. No new node was created because the definition's construction is a direct composition of the three existing notions, and creating a helper would duplicate or merely restate a clause of this item. The item remains self-contained, with `blueprint.same_as = []`, unchanged imported metadata, and `status = split`.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to report.

## Unfinished

None. The split is ready for the second reader; I did not run a compiler or write Lean.

## Second reading by Q85

- Item statement: checked both displayed definitions against `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/def-trf-iterated-weil-map.md`, order 2639, and its `blueprint_update`; verdict: exact agreement in hypotheses, positive exponent range, pullback domains, composition order and invertibility. The retained cocycle sentence is only the existing forward pointer, absent from the new snapshot, and adds no condition or dependency. This item cites the blueprint, not a Stacks tag; there are no new source tags to verify.
- First defining composite (no proof step): opened `def-trf-strict-weil-complex` and `def-trf-scheme-frobenius`; verdict: the former supplies the isomorphism `φ : Lg_γ^*K ≅ K`, and the latter the automorphism `g_γ` and its iterates. For `m = 2`, start with `L(g_γ²)^*K ≅ Lg_γ^*Lg_γ^*K`, apply `Lg_γ^*φ`, then `φ`. Repeating this composition gives exactly the displayed finite product. The pullback notation is inherited through the strict-Weil definition from `def-weil-derived-pullback-tensor-hom`; each pulled-back arrow is an isomorphism since its inverse is the pullback of `φ⁻¹`. No helper theorem or new node is needed.
- Second defining composite (no proof step): opened `prop-trf-scheme-galois-comparison` and `def-trf-coefficient-conventions`; verdict: `κ^(m)_K` has source `LΦ^{m*}K` and target `Lg_γ^{m*}K`, exactly the source of `φ^[m]`. Its finite-ring hypothesis holds for `A = O_E/ϖ_E^n`: this is a finite commutative ring killed by a power of `ℓ`, and `ℓ ≠ p` makes that power invertible in `k`. The composite is an isomorphism with inverse `(κ^(m)_K)⁻¹ ∘ (φ^[m])⁻¹`.
- Edge cases: for `m = 1`, the product has one factor and yields `u_1 = φ ∘ κ_K`; `m = 0` is deliberately outside the source's range. For `K = 0` and for the empty scheme, all these arrows are the unique arrows between zero objects and remain isomorphisms. Over `X_0 = Spec F_q` with a constant finite free coefficient sheaf and Weil map an invertible matrix `M`, the canonical constant-sheaf identifications give `φ^[m] = M^m`; the composition order and exponent agree. Verdict: no missing hypothesis or statement dispute.
- Proof steps and citations: none; this is a definition with empty `proof` and `proof_deps`, not an omitted proof of a proposition. `citations.json = []` correctly contains no proof citations. The cocycle theorem is not used to define the maps, so adding it as a dependency would be circular.
- New nodes: none; verdict: no elementary helper, duplicate, restatement or Mathlib leaf was introduced. I independently searched the entire imported blueprint with `tools/blueprint_refs.py search` for `iterated Weil` and `scheme-Frobenius map`, and searched `dag/nodes/` by the item id and the composite's terminology. The related `def-trf-frobenius-coefficient-morphism` uses scheme pullback and arbitrary coefficient maps, and cites this item; it neither supplies the strict Galois-Weil composite nor replaces this definition.
- Lean attachment check: opened `Frobenius.lean` lines 120–148 and 224–267 and searched `WeilConjectures/`, `Comparator/` and `dag/lean_names_upstream.json` by the id and scheme/Galois-comparison names. Verdict: `WeilComplex.coeffIterate` iterates a coefficient morphism for an endomorphism over the scalar scheme; it has no `κ^(m)` construction. The Galois automorphism `g_γ` in this item is not generally a morphism over `Spec k`, so this implementation cannot be attached to the full definition by simply substituting it for that scalar-linear endomorphism. `coeffIterate_one` is explicitly unfinished. No source declaration is attached and no compiler was run.

- Independent Mathlib searches: ran `msearch.py ... grep "Frobenius.*(iterate|pullback)|WeilComplex|coeffIterate" AlgebraicGeometry` (zero hits) and LeanFinder with the more general query "Iterate an isomorphism from the pullback of a sheaf along an automorphism to the sheaf by composing its pullbacks" (eight hits, recorded verbatim by the tool in `searches.jsonl`). The results are ordinary sheaf/module pullback comparisons such as `SheafOfModules.pullbackComp`, not this derived pro-etale strict-Weil definition with its specified scheme/Galois comparison; no search result is asserted to finish the item. No new nodes require Mathlib search records.

Changes made: corrected `ν_m` to the item's `u_m` in the first review, and replaced its claim that the source implementation confirms the one-step case with the actual evidence: `coeffIterate_one` has a `sorry` body. Added the independent type, coefficient, edge-case, duplicate and attachment checks above. The node statement and all mathematically correct first-worker sections are retained; no new nodes were needed.
