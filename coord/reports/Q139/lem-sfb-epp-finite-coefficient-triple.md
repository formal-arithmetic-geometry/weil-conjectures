## Worker report

The module `Sheaf.RingTheory.EppFiniteCoefficientTriple` states
`IsDiscreteValuationRing.exists_epp_finite_coefficient_triple`, with its whole proof
`sorry`. It publicly imports `Sheaf.RingTheory.EppWeakSolution` and reuses
`IsDiscreteValuationRing.IsEppWeakSolution`. The shared definition is supplied in this
packet under the new definition node `def-sfb-epp-weak-solution`, since the module
named by the return is absent from the current published sources. Its data consists
of the actual tensor quotient, integral closures and canonical normalization map,
with no choices and no postponed proofs. The triple theorem module declares only
the theorem, and there is exactly one definition of the weak-solution predicate.

Read the item, all seven statement-dependency records and their recorded Mathlib signatures
and docstrings, the available proof-dependency records, Stacks More on Algebra
`lemma-special-case` (09F8), `theorem-epp` (09F9), `remark-construction` (09EM), and
`definition-solution` (09EN). The tag identifiers were checked in `tags/tags`.
The latest blueprint's direct-images proof is proper/open direct-image assembly; as the
node's reviewed provenance says, this item refines a historical auxiliary algebra input,
not a new assertion about the blueprint unit.

Hypotheses and clauses, in order:

- Prime p: `(p : ℕ) (hp : p.Prime)`.
- Three DVRs: separate `CommRing`, `IsDomain`, `IsDiscreteValuationRing` binders on U, V, W.
- Injective local U -> V -> W: `Algebra U V`, `Algebra V W`, both `IsLocalHom` binders,
  `hinjUV`, `hinjVW`. The direct U -> W algebra and `IsScalarTower U V W` encode the
  specified composite, rather than an extra map.
- Fraction fields F, G, J: their `Field`, `Algebra` and `IsFractionRing` binders.
  The field-algebra and scalar-tower binders express exactly the coherent inclusions
  F -> G -> J and compatibility with the three ring embeddings. Ring maps from fields
  are automatically injective; no separability or finiteness of G/F is imposed.
- U and V complete: `IsAdicComplete (IsLocalRing.maximalIdeal U) U` and its V counterpart.
  No independent completeness hypothesis is imposed on W.
- Algebraically closed lower residue: `IsAlgClosed (IsLocalRing.ResidueField U)`.
  Mathlib's splitting definition is equivalent to the nonconstant-polynomial-root
  condition, by `IsAlgClosed.exists_root` and `IsAlgClosed.of_exists_root`.
- Residue characteristic p: `CharP (IsLocalRing.ResidueField U) p`.
- Bottom ramification index one: `hunram` is exactly extension of the maximal ideal of
  U to the maximal ideal of V.
- J/G finite-dimensional: `Module.Finite G J`, equivalent for vector spaces to finite
  dimension, including the degree-one case.
- Perfect-core equality inside the upper residue: `hcore` equates the range of the
  canonical `IsLocalRing.ResidueField.map (algebraMap U V)` with the set of x for which
  `∀ n : ℕ, ∃ y, y ^ (p ^ n) = x`. This is the image of k, not an independently selected
  subfield. n = 0 imposes no condition and the intersection equals that for n >= 1.
- Finite weak solution for U -> W: the first existential supplies H, its field structure,
  F-algebra structure and compatible U-algebra structure, and `IsEppWeakSolution U W F J H`.
  The existential universe is the maximum of all the input universes; any finite extension
  has a representative there. There is no constraint equating input universes.
- In `IsEppWeakSolution`, `T` is `(L ⊗[K] H) ⧸ nilradical (L ⊗[K] H)`, exactly reduction
  by all nilpotents. `C` is `integralClosure B T`, and the lower ring is `integralClosure A H`.
  Its local `f` is restriction of H -> T (right tensor inclusion followed by quotient),
  with integrality transported by `IsIntegral.map` and `IsIntegral.tower_top`.
  `Module.Finite K H` expresses finiteness. For every maximal ideal q of C,
  `(q.comap f).IsMaximal` is maximal contraction. Both localizations have existential
  domain and DVR structures. The final equality extends the contracted ideal and q to
  `Localization.AtPrime q`; these are precisely n(V_H)_q and q(V_H)_q. No residue
  separability or extra stability property is included.
- If F has characteristic p: the second conjunct starts `CharP F p →` and quantifies over
  every specified t with `Irreducible t`, equivalent to maximalIdeal U = span {t}.
  It supplies a weak solution H, a finite separable intermediate field S/F,
  r : ℕ and a : H with `a ^ (p ^ r) = algebraMap U H t` and
  `S ⊔ IntermediateField.adjoin F ({a} : Set H) = ⊤`. Thus in the common field H,
  H is the compositum of S with F[t^(1/p^r)]. The root is algebraic (also H/F finite),
  so field adjunction equals the indicated simple algebraic extension.
- No assertion about arbitrary further extensions appears.

Dependency declarations used:

- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing`, and `irreducible_iff_uniformizer` for the uniformizer encoding.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` / `algebraMap`.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`, `IsIntegral.map`, `IsIntegral.tower_top`.
- `def-weil-pbc-module-tensor-product`: `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct`, exposed by `Mathlib.RingTheory.TensorProduct.Quotient`; the latter
  also exposes the canonical algebra tensor inclusions and quotient algebra structure.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable` (already entails algebraicity).

Supporting statement imports are `Mathlib.RingTheory.Localization.FractionRing`
(`IsFractionRing`), `Mathlib.RingTheory.LocalRing.ResidueField.Basic`
(`IsLocalRing.ResidueField.map`), `Mathlib.FieldTheory.IsAlgClosed.Basic` (`IsAlgClosed`),
and `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` (`IntermediateField.adjoin`, sup).

Plain proof imports cover every already-stated proof dependency: complete finite
normalization (`Sheaf.RingTheory.CompleteDVRFiniteNormalization`), uniformizer-root
algebra (`WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra`),
monic quotient power basis (`Mathlib.RingTheory.AdjoinRoot`), and PID Noetherian/normal
arithmetic (`Mathlib.RingTheory.Polynomial.RationalRoot`, with the PID module transitively).
The DVR definition is already a public import. At inspection, the filtration,
weak-solution descent, totally ramified base change, arbitrary-DVR Abhyankar,
purely inseparable and Artin-Schreier degree-p, mixed finite-level preparation,
mixed level-lowering, coefficient-field arithmetic, finite-extension perfect-core,
and normal-base branch-conjugacy proof nodes had no Lean statements. They therefore
have no imports yet; their names and full proof roles are preserved in the docstring.
They are not missing statement prerequisites for this delivery.

Edge cases checked: identity ring maps, J = G and a tower of length zero; n = 0 in
the intersection; r = 0 in the root clause (a is then t itself); mixed characteristic
(the extra conclusion is conditional); p = 2; finite extensions with inseparable part;
imperfect and non-finitely-generated upper residue; multiple maximal upper branches;
and independent input universes. Fields and zero rings cannot accidentally count as
DVRs because Mathlib requires a nonzero maximal ideal. Localizations are required to
be DVRs explicitly rather than silently assumed domains.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder "Epp elimination of wild ramification finite coefficient
  extension weak solution complete discrete valuation rings"`: eight hits on Tilt,
  PreTilt, Henselian rings and unramified loci; no match.
- `msearch.py ... loogle "IsDiscreteValuationRing, IsAdicComplete, IsLocalHom,
  integralClosure"`: zero hits.
- `msearch.py ... grep "Epp|[Ww]eakSolution|weak.solution|perfectCore" RingTheory`:
  four unrelated hits on a local variable ePp in tensor calculations.
- `msearch.py ... leansearch "Epp weak solution finite extension complete discrete
  valuation rings"`: eight hits on DVR local compactness and standard instances;
  no Epp theorem or weak-solution predicate.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with the same pattern:
  no upstream match; the existing Epp essentially-finite-type theorem has different
  assumptions and a stronger persistence/residue conclusion. Its normalization
  helpers were read. It is downstream of this item (via weak-perfect-residue),
  so importing that theorem to use its helpers would close a proof dependency cycle.
  The shared definition in EppWeakSolution uses Mathlib constructions directly;
  no second named reduced tensor, upper normalization or normalization map is introduced.
- The exact node-id search in `lean/WeilConjectures`: no match.
- `rg` in `dag/nodes` finds no definition node of weak Epp solutions. The repair
  adds `def-sfb-epp-weak-solution` as its shared owner, and the theorem cites it.
- `tools/blueprint_refs.py search Epp`: zero blueprint nodes.
- No released repair note exists for this item.

No statement correction, disputed statement or dependency-record repair.
The theorem signature is unchanged and recorded verbatim. The item gains only the
new definition dependency in addition to its updated lean record.

Validation after repair: `scompile.py Q139 lem-sfb-epp-finite-coefficient-triple
<EppWeakSolution.lean> <EppFiniteCoefficientTriple.lean>` compiled both delivered files
separately in dependency order, with no diagnostics. Shared-definition compilation
took 11.1 s; triple-theorem library compilation took 1.9 s.

## Second reading by Q139

Author's separate second pass, with the node and complete module open; the maintainer
provides the independent review. Checked every hypothesis and clause against the mapping
above. In particular both lower and upper local DVR assertions are present; contraction
uses the constructed canonical map; the ideal equality is in the upper localization;
the perfect-core equality uses the canonical residue embedding; and the prescribed
uniformizer is universally quantified after the characteristic-p condition. No stronger
separability, upper-residue perfection or stability hypothesis was introduced. The shared definition's
local lets are in its body, while the theorem signature has no let binders.
The only correction in this second pass was the source tag for definition-solution:
09EN, checked against the tag map. No mathematical signature change was needed.



## Returned-delivery repair

The return on head 6f7e8c466aeb reports a duplicate definition of
`IsDiscreteValuationRing.IsEppWeakSolution` and requires importing
`Sheaf.RingTheory.EppWeakSolution`. Removed the entire local definition and its
source docstring from EppFiniteCoefficientTriple.lean, added the public import,
and removed the imported name from the item's lean.declarations. The mathematical
theorem signature is unchanged.

On both repair attempts the requested shared module was absent from the read clone
and current server sources; `scompile.py --source` reported it unavailable, and
compilation with just that import failed with a missing object file. The current
server DAG/source search has no owner or declaration of this notion. The previously
reported collision is not present in the published sources. Under brief-stage2
section 1(A), this packet now supplies that missing shared definition at precisely
`Sheaf.RingTheory.EppWeakSolution`, with its own definition node. The triple theorem
imports and reuses it. This resolves the previous missing import without renaming
the declaration, duplicating it, or changing the theorem.

## New nodes

`def-sfb-epp-weak-solution` owns the single shared definition
`IsDiscreteValuationRing.IsEppWeakSolution` in `Sheaf.RingTheory.EppWeakSolution`.
The statement introduces the compatible A,B,K,L,H algebras, the nilradical quotient,
both integral closures and their canonical map. Its conditions are finiteness,
maximal contraction at every upper maximal ideal, both local DVRs, and equality of
the extended maximal ideals. This is exactly Stacks Tags 09EM and 09EN in the DVR
fraction-field case, written as the same explicit criterion for general compatible
ring/field algebras. The broader input domain adds no assertion that those conditions
hold and does not change the triple theorem's input objects. The definition's
signature has exactly the compatible algebra and scalar-tower binders used by its
construction; its body is exactly the former local definition.

Every clause is literal in the body: T is the nilradical quotient of the tensor;
C is the upper integral closure; the domain of f is the lower integral closure;
f is the tensor inclusion restricted using integrality; `Module.Finite K H`
is finiteness; `∀ (q : Ideal C) [q.IsMaximal]` covers every branch;
`(q.comap f).IsMaximal` gives maximal contraction; the two existential domain/DVR
conjunctions supply both local DVRs; the equality of `Ideal.map` terms is precisely
the extended-ideal condition. All variables and five universes are explicit.
No new lemma is postponed, and no choice, arbitrary map or sorry appears in this module.

New searches were LeanSearch on weak Epp solutions and normalized tensors (eight
hits on integral closure, tensor maps and reducedness), LeanFinder on normalized
local branches of ramification index one (eight hits on unramifiedness and index
arithmetic), and Mathlib grep for IsEppWeakSolution/EppWeakSolution/weak.solution
(zero hits). Exact queries and results are recorded in mathlib_searches. Project
and current-server source/DAG searches find no shared definition; blueprint search
finds no weak-solution blueprint node. The inherited blueprint ancestor is null,
reported by blueprint_refs.py ancestor; the new node preserves the item-first via
chain rather than inventing a blueprint parent.

Second reading of the repair: the theorem module contains no definition of
IsEppWeakSolution, the imported module contains exactly one such definition,
and only its new node owns it. Both modules compile together in the server's
private dependency overlay. The theorem's hypotheses and conclusions, including
both localization conditions and the prescribed-uniformizer clause, are unchanged.
