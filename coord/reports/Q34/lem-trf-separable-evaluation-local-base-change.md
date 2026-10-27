## Worker report

The module `Sheaf.RingTheory.SeparableEvaluationLocalBaseChange` states
`lem-trf-separable-evaluation-local-base-change`. Its five named theorems have
`sorry` proofs. Four elementary evaluation statements precede the main theorem
because their maximality/contraction proofs are needed to type the specified
localizations and canonical local map. All helper definitions/abbreviations
have explicit data; none chooses an unspecified map or isomorphism. They belong to
this node's evaluation/localization construction and are listed in `lean.declarations`.
There are no new nodes, dependency repairs, statement corrections or disputed clauses.

I read the node, all seven statement-dependency nodes and their recorded source
signatures/docstrings, and the five additional proof-dependency nodes. I read
`literature/stacks-project/varieties.tex`, the complete statements/proofs of
`lemma-change-fields-flat` (0C4Y) and
`lemma-change-fields-algebraic-unramified` (0C50). The finite-dimensional residue
extension gives the zero-dimensional fibre required by 0C50; no extra equality of
dimensions is assumed. I also read the current blueprint unit `sk-i-curve-zero`
and its ancestor `lem-trf-local-term-locality` under `literature/blueprint/latest/`.
The item is an auxiliary algebra statement and is not the unit statement.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Field k, commutative k-algebra S, finitely generated | `{k : Type u} [Field k]`, `{S : Type v} [CommRing S] [Algebra k S]`, `[Algebra.FiniteType k S]` on the main theorem. |
| Maximal p; F = S/p | `(p : Ideal S) [p.IsMaximal]`; F is always the actual quotient `S ⧸ p`, with its canonical field and k-algebra structures. |
| F/k finite and separable | `[FiniteDimensional k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)]`. |
| Any field extension K/k, chosen k-algebra embedding iota | `{K : Type w} [Field K] [Algebra k K]`, `(ι : (S ⧸ p) →ₐ[k] K)`. A unital algebra homomorphism from the field F is injective; no separate or stronger hypothesis is supplied. |
| C = S tensor K and evaluation epsilon(s tensor a) = iota(s mod p) a | `S ⊗[k] K` with Mathlib's commutative algebra tensor product; `evaluation` is `Algebra.TensorProduct.productMap (ι.comp (Ideal.Quotient.mkₐ k p)) (AlgHom.id k K)`. `productMap_apply_tmul` gives exactly the node's formula. |
| q = kernel epsilon; epsilon onto; q maximal; contraction p | `evaluationIdeal := RingHom.ker (evaluation p ι)`, `evaluation_surjective`, `evaluationIdeal_isMaximal`, `evaluationIdeal_comap`. The last equality is `p = q.comap includeLeftRingHom`. |
| C is finite type over K | The first conjunct of `local_base_change` is `RingHom.FiniteType` for `includeRight : K →ₐ[k] S ⊗[k] K`, thus for the right-factor K-algebra structure. |
| A = S_p, B = C_q, m = pA | `Localization.AtPrime p`, `localRing := Localization.AtPrime (evaluationIdeal p ι)`, and `p.map (algebraMap S (Localization.AtPrime p))`. |
| A and B Noetherian local | The four conjuncts `IsNoetherianRing A`, `IsLocalRing A`, `IsNoetherianRing B`, `IsLocalRing B`. |
| Canonical g(s/u) = (s tensor 1)/(u tensor 1) | `localMap` is exactly Mathlib's `Localization.localRingHom p q includeLeftRingHom (evaluationIdeal_comap p ι)`; its documented `localRingHom_mk'` formula is the stated fraction formula. No arbitrary homomorphism is a parameter. |
| g faithfully flat and local | `(localMap p ι).FaithfullyFlat ∧ IsLocalHom (localMap p ι)`. |
| r = kernel of residue evaluation | `residueEvaluation := productMap ι (AlgHom.id k K)` and `residueEvaluationIdeal := RingHom.ker (residueEvaluation p ι)`. Its maximality is separately stated by `residueEvaluationIdeal_isMaximal` (node proof step 4). |
| F tensor K finite-dimensional over K and reduced | Explicit `@FiniteDimensional K ((S ⧸ p) ⊗[k] K) ... Algebra.TensorProduct.rightAlgebra.toModule` and `IsReduced ((S ⧸ p) ⊗[k] K)`. In particular the dimension is over K, not over k or F. |
| Canonical B/mB -> (F tensor K)_r -> K, as K-algebra isomorphisms | Existential `θ` and `φ` have actual `AlgEquiv K` types. `fibreAlgebra` and `residueLocalAlgebra` explicitly supply the K-algebra structures induced by `a ↦ 1 ⊗ a`, followed by localization and quotient. These are explicit arguments, not file-local instances. |
| Canonicity of the first isomorphism | The first formula states `θ([c/v]) * image(π(v)) = image(π(c))`, with `π = tensorQuotient`. This is exactly `θ([c/v]) = π(c)/π(v)` without building a second choice of denominator proof. The denominator image is a unit: if π(v) lay in r, evaluation would put v in q. Hence the equation uniquely specifies the canonical quotient-localization map. |
| Canonicity of the second isomorphism | The second formula is `φ(d/w) = residueEvaluation d / residueEvaluation w` on every fraction of the residue tensor localization. |
| Composite formula on pure-tensor fractions | The third formula is literally `φ (θ ([(s ⊗ a)/v])) = ι (Ideal.Quotient.mk p s) * a / evaluation p ι v`. Here v belongs to `q.primeCompl`, expressing v not in q. |
| mB = qB is B's maximal ideal | `closedFibreIdeal` is the map of pA under the canonical g; `evaluationLocalIdeal` is q mapped into B. The two equalities preceding the isomorphisms identify these ideals with each other and `IsLocalRing.maximalIdeal B`. |
| B/qB = K via the same evaluation | Existential `ψ` is a `K`-algebra equivalence, with the fourth formula `ψ([c/v]) = evaluation c / evaluation v`. Its values agree with the composite φθ on the displayed pure fractions; both are the same evaluation identification. |

Every variable and each universe is explicitly declared. The independent universes
u, v and w allow arbitrary sizes for k, S and K. There are no file-local notations,
private declarations, instance assumptions changing the mathematical hypotheses,
`let` binders in signatures, or proof-import instances used invisibly by the statement.
The two maximality theorems are public global instance theorems, with sorry as their
whole proofs; the underlying ring/localization data remain concrete constructions.

Dependencies actually used (their module and declaration):

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, together with its algebra-instance form `Algebra.FiniteType`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable` (whose separability includes algebraicity).
- `def-weil-pbc-module-tensor-product`: Mathlib's `TensorProduct`, read in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; bilinear lift/uniqueness read in
  `.Basic`, and `LinearMap.rTensor` read in `.Map`. The algebra tensor imports
  publicly expose the tensor used by this statement.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.localRingHom`. The node's other recorded notions `Ideal.ResidueField`
  and `Ideal.Fiber` were read; they are not replacements for F = S/p in this item.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
- `def-weil-pbc-faithfully-flat-ring-map`:
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`, `RingHom.FaithfullyFlat`, defined
  through `Module.FaithfullyFlat` from `.Flat.FaithfullyFlat.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`,
  `Algebra.TensorProduct.instCommRing`, `includeLeftRingHom`, `includeRight`,
  `productMap`, `productMap_apply_tmul`, and `ext`.

Proof dependencies are plain imports: finite-type Noetherianity from
`Mathlib.RingTheory.FiniteType`; field-extension faithful flatness from
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` (which imports `.Basic`);
`RingHom.Flat.localRingHom` from `Mathlib.RingTheory.RingHom.Flat`;
`Module.FaithfullyFlat.of_flat_of_isLocalHom` from `.Flat.FaithfullyFlat.Algebra`;
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` from
`Mathlib.RingTheory.TensorProduct.Quotient`; localization Noetherianity from
`Mathlib.RingTheory.Localization.Submodule`; `Ring.KrullDimLE.of_isLocalization`,
`nilradical_eq_maximalIdeal` and `isField_of_isReduced` from
`Mathlib.RingTheory.KrullDimension.Zero`; and
`Algebra.isReduced_tensorProduct_of_finiteSeparable` from
`Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced` (the recorded declaration).
No proof-dependency module is omitted because of an import cycle.

Edge cases checked before drafting and again against the final statement:

- S = F = k and p = 0: A = k, B = K, both evaluation maps are multiplication,
  and both fibre equivalences are the identity after the canonical identifications.
- S = k[t]/(t^2), p = (t): nonreduced S is allowed; the assertion concerns the
  reduced residue tensor, and mB = qB still holds.
- A nontrivial finite separable F/k splitting inside K: F tensor K can be a
  product of fields. The specified embedding selects r; only its localization is
  identified with K. No global identification F tensor K = K is asserted.
- K = F, K = k when the embedding exists, arbitrary characteristic, and inseparable
  K/k: no extra separability hypothesis on K was introduced.
- A purely inseparable F/k would make F tensor F nonreduced, and is properly
  excluded by `Algebra.IsSeparable k (S ⧸ p)`.
- The zero ring S has no maximal ideal and therefore gives no input; no nonempty
  index or characteristic assumption silently excludes a valid input.

Searches actually run:

1. `msearch.py ... leanfinder "Localization of a tensor algebra at a specified separable residue field evaluation point gives a faithfully flat local map and residue field equal to the extension field"`:
   8 hits, including `Algebra.instIsSeparableResidueFieldOfFormallyUnramified`,
   `Ideal.ResidueField.exists_smul_eq_tmul_one`,
   `Algebra.FormallyUnramified.of_map_maximalIdeal`, and
   `Algebra.isUnramifiedAt_iff_map_eq`. None states this collection of clauses or
   supplies the specified evaluation fibre isomorphisms.
2. `msearch.py ... loogle "Algebra.TensorProduct.productMap, Localization.localRingHom"`:
   successful search, 0 hits.
3. `msearch.py ... grep "separable.*[Ll]ocal|[Ll]ocal.*[Ss]eparable|evaluation.*[Tt]ensor" RingTheory`:
   6 hits in NormalClosure and DedekindDomain integral-closure/localization results;
   no match for the item.
4. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
   `separable.*evaluation|evaluation.*[Ll]ocal|lem-trf-separable-evaluation-local-base-change`:
   unrelated sheaf and derived evaluation/localization results, no item match.
5. `grep -rn 'lem-trf-separable-evaluation-local-base-change' lean/WeilConjectures`:
   no match. `rg` of both Lean roots and `dag/lean_names_upstream.json` for
   `separableEvaluation|separable_evaluation`: no match.
6. Direct Mathlib `rg` searches located `productMap`, `rightAlgebra`,
   `localRingHom`, `Quotient.mkₐ`, and the recorded dependency signatures, which
   were then read with their source docstrings. These are reused, not restated.

Validation: `scompile.py Q34 lem-trf-separable-evaluation-local-base-change <module>`
compiled the sandbox module and the actual library module successfully, without
warnings. Initial compilation diagnosed a reserved lambda binder and the
reducibility warnings for class-valued definitions; the binder is now `a` and
those explicit algebra structures are abbreviations. No warning was suppressed.
The final name is `Algebra.SeparableEvaluation.local_base_change`; the delivery
dry run recompiles the final file.

## Second reading by Q34

Q34 reopened the node and final module for a second clause-by-clause pass, recorded
in the table above. This is a worker self-check; the independent reading is the
maintainer's delivery review, as the dispatcher brief directs. No other agent was
started and no independent-reader result is claimed.

The pass checked in particular that the first localization equation multiplies by
`π(v)`, not `π(c)`; that finite dimension is over K using the right tensor scalar
structure; and that θ, φ and ψ are K-algebra equivalences with the specified scalar
maps, not arbitrary ring isomorphisms. It also checked that the local map is the
canonical localization of `includeLeftRingHom`, that pA is extended along this same
map, and that the last quotient uses qB. The four initial theorems account for all
surjectivity, maximality and contraction clauses not repeated in the main theorem.
No mismatch with the node or source remains; no node field beyond `lean` changed.

Dry-run repair: the initial declaration inventory mistakenly matched the prose
words `theorem makes` in a docstring. The inventory is now extracted only from
Lean declaration lines; the nonexistent name was removed. No Lean statement
changed. The dry run is rerun below.
