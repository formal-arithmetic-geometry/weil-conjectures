## Worker report

The module `Sheaf.FieldTheory.NormalRamificationFiltration` states the two clauses of
`lem-sfb-epp-normal-ramification-filtration` as
`IsDiscreteValuationRing.normal_ramification_filtration` and
`IsDiscreteValuationRing.normal_ramification_filtration_baseChange`. Both proofs are `sorry`.
Four helpers unpack this node's own filtration conditions and canonical composita; they
introduce no alternative definition of a DVR, integral closure, residue field, normality,
separability, tensor product or intermediate field. Their data is explicit.

Hypothesis and conclusion correspondence:

- Complete DVR B: `[CommRing B] [IsDomain B] [IsDiscreteValuationRing B]` and
  `[IsAdicComplete (IsLocalRing.maximalIdeal B) B]`.
- Fraction field L: `[Field L] [Algebra B L] [IsFractionRing B L]`.
- Prime positive residue characteristic: `[Fact p.Prime]` and
  `[CharP (IsLocalRing.ResidueField B) p]`. Primality supplies positivity.
- Any finite M/L: `[Field M] [Algebra L M] [Module.Finite L M]`.
- Finite normal N/L containing M: existential field, algebra, `Module.Finite L N`,
  `Normal L N`, and `Nonempty (M →ₐ[L] N)`. N lives in `Type (max v w)`, which
  accommodates the normal closure independently of B's universe.
- Tower: `F : Fin (n + 1) → IntermediateField L N`, `F 0 = ⊥`,
  `F (Fin.last n) = ⊤`, and the monotonicity in `IsNormalRamificationChain`.
- B^j: literally `integralClosure B (F i)`. The step map is Mathlib's
  `IntermediateField.inclusion`, restricted to B, followed by `AlgHom.mapIntegralClosure`.
- Every nonidentity step: `F i.castSucc ≠ F i.succ → IsNormalRamificationStep ...`.
- Type (a): `CharP E p`, degree `Module.finrank E F = p`, and
  `∀ x : F, ∃ a : E, f a = x ^ p`. This is exactly the stated exponent-one meaning.
- Type (b): `IsGalois E F ∧ Module.finrank E F = p`.
- Type (c): `IsGalois E F`, `IsCyclic (F ≃ₐ[E] F)`, degree coprime to p,
  an exponent e coprime to p with the exact mapped-maximal-ideal power equality,
  and `Algebra.IsSeparable` for the induced residue map. No total ramification or
  perfect residue-field condition is assumed.
- Type (d): the mapped maximal ideal equals the new maximal ideal, and the induced
  residue extension satisfies `Module.Finite` and `Algebra.IsSeparable`. No Galois
  or separability condition on the fraction fields is added to this case.
- Local structures in the step predicate are existential structures on the exact integral
  closure types, not replacement rings. The residue algebra is the canonical
  `IsLocalRing.ResidueField.map` of the closure inclusion. The `letI`s here install
  structures in helper definitions; neither theorem signature contains a let binder.
- Arbitrary base change: the second theorem is independently universal, not restricted to
  a tower obtained from the first theorem. A, B, K, E, T, K', W have separate universes.
  A and B are complete DVRs, `hinj` is injectivity and `IsLocalHom (algebraMap A B)`
  is locality. K and E are their fraction fields with the scalar tower compatibility.
  `[Module.Finite E T]` packages the finite tower in one ambient top field.
- Original arbitrary E^j: the intermediate fields F, their base and top equalities,
  and `hchain`. Identity steps are permitted. Completeness of their normalizations
  is not assumed in hchain.
- Finite K'/K: `[Algebra K K'] [Module.Finite K K']`.
- Field factor of the reduced tensor: field W with the surjective T-algebra homomorphism
  `q : T ⊗[K] K' →ₐ[T] W`. Every such q kills nilpotents; conversely every field factor
  of the reduced finite tensor algebra has this surjection. This equivalent presentation
  avoids choosing a product decomposition or a representative of a factor.
- E^j_1: `normalRamificationBaseChangeFields` is the supremum of the image of F_j
  and `IntermediateField.adjoin E` of the image of K' through the tensor-product
  `includeRight` and q. This is exactly the generated compositum, with canonical maps.
- New types and complete DVRs: the first two conjuncts are `IsNormalRamificationChain`
  and `HasCompleteRamificationClosures` of precisely those fields. The latter concludes
  a DVR structure and maximal-ideal adic completeness for every integral closure.
- Deleting identities: there exist r ≤ n and a `StrictMono H` with the same range as the
  composita, satisfying the same step predicate. Equal consecutive fields have disappeared;
  no new intermediate stages are inserted.

Dependency declarations used:

- def-sc-discrete-valuation-ring: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` (its mathlib_match is usable without a lean record).
- def-weil-pbc-adically-complete-ring: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`.
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- def-weil-pbc-integral-closure: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`; its functorial map is Mathlib's `AlgHom.mapIntegralClosure` from
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`.
- def-weil-pbc-separable-algebraic-extension: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; `IsGalois` is Mathlib normality plus this separability.
- def-weil-pbc-module-tensor-product: `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct`; the algebra structure and canonical inclusion are provided by
  `Mathlib.RingTheory.TensorProduct.Basic`.

The recorded non-Mathlib proof-dependency modules are imported privately. All thirteen
proof steps and the names of every node used in each step are copied into the two theorem
docstrings. No proof-only unstated prerequisite is silently given a new declaration.

Edge cases checked: n=0 gives a single intermediate field and no step conditions;
base extension collapsing all stages permits r=0 (StrictMono on Fin 1 is vacuous).
M=L is permitted. Identity steps do not need any of the four alternatives. Mixed
characteristic remains allowed, and case (a) explicitly forces positive characteristic.
Imperfect residue fields are allowed. Type (d) allows inseparable fraction extensions.
The tensor algebra may have nilpotents or multiple field factors; a field quotient kills
the former and selects exactly one of the latter. The upper field extension T/E is finite,
but E/K is not required to be finite, as required by the node.

Searches performed with the prescribed msearch wrapper:

- leanfinder: "A finite extension of a complete discrete valuation field embeds in a normal
  extension with a tower of purely inseparable prime degree, Galois prime degree, cyclic
  tame, and unramified steps". Eight hits including normal-closure and Galois theory,
  no declaration of the combined filtration theorem.
- loogle: "IsDiscreteValuationRing, ramificationIdx, residueField". Zero hits; the service
  reported unknown identifier ramificationIdx. The subsequent source searches used the
  exact mapped-ideal equality and did not depend on that identifier.
- leansearch: "Ramification filtration of a finite normal extension of complete discrete
  valuation fields into wild prime degree, tame cyclic and unramified steps". Eight hits,
  including fundamental ramification identities and unrelated ordinal filtrations,
  no exact statement.
- msearch grep: "normal.*ramification.*filtration|ramification.*tower|integralClosure.map".
  Thirteen hits, ramification-index tower lemmas and integralClosure_map_algEquiv;
  no combined tower or its base-change statement.
- rg in Mathlib, lean/WeilConjectures and lean/Sheaf for ramification/filtration,
  NormalRamification/normalRamification/IsNormalRamification, and the node id.
  Existing inertia and tame-extension statements do not give the target statement;
  no name collision or existing helper for these four alternatives was found.
- DAG search and `tools/blueprint_refs.py search ramification` found general ramification
  nodes and no node defining this exact four-case predicate or its chain/composita helpers.
  `ancestor` reports no current blueprint ancestor; this agrees with the node's historical
  supporting-input explanation. The latest blueprint path was searched; the source
  remains the explicitly recorded Stacks Tag 09F8.

No statement correction, dependency repair, or new independent definition node is needed.
The existing stage-1 residue-characteristic correction is preserved unchanged.

## Second reading by Q99

Independent reading by the maintainer's reviewer (the delivered section was a second pass
by the same worker, H11; it is replaced here). The worker report above is unchanged.

Node clauses and their Lean (module `Sheaf.FieldTheory.NormalRamificationFiltration`):

- Complete DVR B, fraction field L: `IsDomain`, `IsDiscreteValuationRing`,
  `IsAdicComplete (maximalIdeal B) B`, `IsFractionRing B L`. Correct.
- Residue characteristic p, p prime: `Fact p.Prime`, `CharP (ResidueField B) p`; no `CharP L`,
  so mixed characteristic is kept. Correct.
- Finite M/L embeds in finite normal N/L: `Module.Finite L M`; existential `N : Type (max v w)`
  with `Module.Finite L N`, `Normal L N` (not `IsGalois`), `Nonempty (M →ₐ[L] N)`, B-algebra
  structure pinned by `IsScalarTower B L N`. Correct.
- Tower L = L^0 ⊆ … ⊆ L^r = N: `F : Fin (n+1) → IntermediateField L N`, `F 0 = ⊥`,
  `F (Fin.last n) = ⊤`, `Monotone F` inside `IsNormalRamificationChain`. Correct.
- B^j = integral closure: `integralClosure B (F i)`; step map `AlgHom.mapIntegralClosure` of
  `IntermediateField.inclusion`; residue map `IsLocalRing.ResidueField.map`. Canonical.
- Only nonidentity steps are constrained: `F i.castSucc ≠ F i.succ → IsNormalRamificationStep`.
- (a) `CharP E p`, `finrank E F = p`, `∀ x, ∃ a, f a = x ^ p`. Exactly the node's meaning.
- (b) `IsGalois E F ∧ finrank E F = p`. Correct.
- (c) `IsGalois`, `IsCyclic (F ≃ₐ[E] F)`, degree coprime to p, `∃ e` coprime to p with
  `map 𝔪_{B^j} = 𝔪_{B^{j+1}} ^ e`, separable residue extension. Correct (e = 0 is excluded
  automatically by locality).
- (d) `map 𝔪 = 𝔪`, residue `Module.Finite` and `Algebra.IsSeparable`; no fraction-field
  separability. Correct.
- The DVR and `IsLocalHom` existentials inside the step predicate hold for every finite
  extension of a complete DVR (node proof step 1), so in `hchain` they are not a stronger
  hypothesis; in the first theorem `HasCompleteRamificationClosures` adds a conclusion that
  proof step 2 proves. Accepted.
- Base change: A, B′ complete DVRs, `hinj`, `IsLocalHom (algebraMap A B)`; K, E fraction
  fields with `IsScalarTower A K E`, `IsScalarTower A B E`; `CharP (ResidueField B) p` for B′
  (the stage-1 correction); arbitrary tower `F` in `IntermediateField E T`, `T/E` finite, no
  E/K finiteness; `K′/K` finite; the field factor of `(T ⊗_K K′)_red` as a surjective
  `q : T ⊗[K] K′ →ₐ[T] W` (every field quotient kills nilpotents and selects one factor of the
  reduced finite algebra, and conversely). Remaining scalar towers (K→E→W, B→T→W) follow
  from the given ones; no extra hypothesis.
- E^j_1: `(F j).map (toAlgHom E T W) ⊔ adjoin E (range (q ∘ includeRight))`, the subfield
  generated by the images of E^j and K′. Canonical.
- Conclusion: chain and complete-DVR closures for the composita, and deletion of identities
  as `r ≤ n`, `StrictMono H`, equal range, chain for H. Length at most s, types (a)-(d) with
  respect to the closures of B′, all closures complete DVRs. Correct.

Edge cases: n = 0 (no steps; r = 0, `StrictMono` on `Fin 1` vacuous), M = L, K′ = K, total
collapse of all composita, inseparable K′/K (nilpotents), characteristic 0 L (type (a) absent),
imperfect residue fields. All covered as the node states them.

Records: only the item's `lean` record changes (statement, stmt_deps and proof are identical
to the live node); `lean.statement` appears verbatim in the file; all six stmt_deps are Mathlib
matches (`IsDiscreteValuationRing`, `IsAdicComplete`, `Algebra`, `integralClosure`,
`Algebra.IsSeparable`/`IsGalois`, `TensorProduct`); the eleven proof-dependency imports exist in
the live tree. Helpers have real data; both theorems are `sorry`; docstrings carry the source
place, `(blueprint: …)` and all thirteen proof steps; lines ≤ 100 characters.

Note: Q66 delivered the same item at the same file path (1e92000a, reviewed PASS, not landed
when this was read). Only one of the two deliveries should land; the second must not rebind.

Mismatches found: none in the Lean. Changed: this section only.
