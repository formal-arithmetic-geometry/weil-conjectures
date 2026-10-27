## Worker report

This stage-2 delivery states `LieAlgebra.exists_kostant_integral_pbw_basis` in
`Sheaf.Algebra.Lie.KostantIntegralPBW`. Its entire proof is `sorry`. It also supplies
one new definition node, `def-sfb-kostant-integral-form`, with four concrete
constructions in `Sheaf.Algebra.Lie.KostantIntegralForm`. There are no postponed
helper theorems or definition proofs, and no dependency repair modules.

The old BLOCKED ending concerned a stage-1 unchanged-item gate: the item already
had Q103's reviewed split. The present assignment and `coord/queue.tsv` put it
in stage 2, and the current node has no Lean record. The stage-2 handoff in
`coord/brief-stage2.md` §0 therefore applies. This delivery preserves the statement,
proof, proof dependencies and accepted split. Only `lean` and the addition of the
new definition node to `stmt_deps` change on the item.

I read Milne, Algebraic Groups (2017), printed pp.508–511 (PDF pp.520–523): the
Chevalley basis and bracket coefficients in Theorem 23.71, the rational form on
p.509, and the admissible-lattice condition involving all root divided powers on
p.510 before (152). As the reviewed DAG explains, Milne does not prove integral
PBW there. The full Kostant, Groups over Z (1966), and Steinberg, Lectures on
Chevalley Groups (1967), sources remain WANTED; this delivery makes no claim to
have obtained or read them. Its natural-language proof is the accepted seven-step
DAG proof, reproduced in the theorem docstring (spanning and independence are
combined in its Step 5). No statement correction or STATEMENT-DISPUTED flag is
needed.

Hypotheses and fixed objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Rational Lie algebra | `L : Type u`, `[LieRing L]`, `[LieAlgebra ℚ L]`; the existing Mathlib Lie bracket is used. |
| Finite-dimensional | `[FiniteDimensional ℚ L]`. |
| Semisimple | `[HasTrivialRadical ℚ L]`, precisely the definition recorded by `def-wf-semisimple-lie-algebra`, meaning no nonzero solvable ideal. |
| Splitting maximal abelian subalgebra | `H : LieSubalgebra ℚ L`, `[IsLieAbelian H]`, and `hmax`: any abelian Lie subalgebra containing H equals H. The full eigenbasis below encodes splitting. |
| Root system in the dual of H, coroots in H | `I : Type v`, `[Finite I]`, `P : RootPairing I ℚ (Module.Dual ℚ H) H`, `[P.IsRootSystem]`, `[P.IsCrystallographic]`, `[P.IsReduced]`. These are the existing reduced crystallographic root-system notions, including injectivity and spanning; none is a private root-system copy. |
| Actual root-coroot evaluation pairing | `heval : ∀ a h, P.toLinearMap a h = a h`. Thus `P.root_coroot_two` gives exactly `α(h_α) = 2`. |
| Simple roots and the chosen simple-coroot order | `Δ : P.Base`, `δ : Fin r ≃ Δ.support`. A Mathlib base supplies the simple roots and sign-coherent nonnegative integral coordinates. For finite reduced crystallographic systems the coroot-base part follows from the root-base condition, as the existing `RootPairing.Base.mk'` records, so it adds no mathematical restriction. `Δ.toCoweightBasis` is precisely the basis of H by simple coroots. The equivalence δ merely enumerates it. |
| Positive roots and any chosen order | `β : Fin N ≃ {i : I // Δ.IsPos i}`. `Base.IsPos` is positive height, hence positive roots relative to this simple base. Every ordering is permitted; no convex ordering is imposed. |
| Nonzero root-space generators and `[h,e_α] = α(h)e_α` | `e : I → L` and `he : ∀ i, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0`. `LieModule.mem_weightSpace` says exactly `∀ h : H, ⁅h,e i⁆ = P.root i h • e i`. These are ordinary simultaneous eigenspaces, not generalized root spaces. |
| They are a Chevalley basis, with simple coroots forming a basis of H and root vectors spanning the root spaces | `B : Module.Basis (Fin r ⊕ I) ℚ L`, `Bh : B (Sum.inl i) = (P.coroot (δ i) : L)`, `Be : B (Sum.inr i) = e i`. This is the already fixed Chevalley basis made explicit, not an added PBW assumption. Together with the ordinary eigenvector condition, the zero-weight H and distinct nonzero roots give precisely the splitting decomposition and one-dimensional root spaces. |
| `[e_α,e_-α] = h_α` | `hopp`, using `P.reflectionPerm i i` as the negative root index. `root_coroot_two` and the reflection equation give `root(reflectionPerm i i) = -root i`, so this uses the actual opposite root with no extra arbitrary involution. It also puts each coroot in the bracket of its opposite root spaces. |
| Nonopposite bracket coefficient `±(p+1)` | `hadd : ∀ i j k, P.root i + P.root j = P.root k → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ⁅e i,e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k`. Mathlib's `chainBotCoeff` is the largest nonnegative integer p with `β-pα` a root, on independent roots. In a reduced system a pair whose sum is a root is independent, so its junk value on dependent roots never enters. |
| Zero brackets when the sum is neither a root nor zero | `hzero`, with both `P.root i + P.root j ∉ Set.range P.root` and `P.root i + P.root j ≠ 0`, concluding the bracket is zero. |
| U_Q is the associative tensor-algebra quotient | `UniversalEnvelopingAlgebra ℚ L` and `UniversalEnvelopingAlgebra.ι ℚ`; the existing `Rel.lie_compat` and `ringCon` implement exactly `xy-yx=[x,y]`. No arbitrary enveloping algebra is substituted. |
| U_Z is the unital integer subalgebra generated by all divided root powers | `kostantIntegralForm e`, defined by `Algebra.adjoin ℤ` of `{x | ∃ i n, x = rationalDividedPower (ι ℚ (e i)) n}`. Both positive and negative roots and all natural exponents are included. |

Conclusions, clause by clause:

| Node | Lean rendering |
| --- | --- |
| The displayed negative/toral/positive monomials | `kostantPBWMonomial (fun i ↦ (P.coroot (δ i) : L)) (fun j ↦ e (P.reflectionPerm (β j).val (β j).val)) (fun j ↦ e (β j).val) d`. The index is `d : (Fin N → ℕ) × (Fin r → ℕ) × (Fin N → ℕ)`. |
| Root divided powers and toral binomials have the stated formulas | `Algebra.rationalDividedPower x n = (1 / (n.factorial : ℚ)) • x^n`; `Algebra.rationalBinomial x n` is the same scalar times `((List.range n).map (fun k : ℕ ↦ x-(k:A))).prod`. Lists preserve all three specified orders in the noncommutative enveloping algebra. |
| Every displayed monomial belongs to U_Z | The first conjunct asserts membership in `kostantIntegralForm e` for every exponent triple. |
| They form an integer basis of U_Z | The second conjunct supplies `b : Module.Basis ((Fin N → ℕ) × (Fin r → ℕ) × (Fin N → ℕ)) ℤ (kostantIntegralForm e)` and fixes the image of every basis element to exactly the indicated monomial. This asserts both independence and spanning, not just freeness or existence of an unrelated basis. |
| Every element is an integer linear combination of them | This is the spanning part of that `Module.Basis`: `b.repr z` is a finitely supported integer family, whose reconstruction equals z. Thus this clause is present without an extra redundant spanning hypothesis or separate placeholder theorem. |
| Every representation extends uniquely | The third conjunct quantifies over every `V : Type w` with `[AddCommGroup V] [Module ℚ V] [LieRingModule L V] [LieModule ℚ L V]` and asserts `∃! φ : UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V`. There is no finite-dimensionality, faithfulness or nonzero condition on V. |
| Extension sends each generator to its representing operator | Its predicate is `∀ x : L, φ (UniversalEnvelopingAlgebra.ι ℚ x) = LieModule.toEnd ℚ L V x`, the existing representing Lie homomorphism. |
| Zero Lie algebra gives U_Z = ℤ | The final conjunct is `Subsingleton L → Function.Bijective (algebraMap ℤ (kostantIntegralForm e))`. Thus the canonical integer algebra map, with its actual ring operations, identifies ℤ with the constructed subalgebra. This is the canonical ring identification, since literal equality of differently typed rings would be ill-typed. |

Dependency declarations read and used:

- `def-wf-lie-algebra`: `Mathlib.Algebra.Lie.Basic`, `LieRing`, `LieAlgebra`,
  `LieRingModule`, `LieModule`; `Mathlib.Algebra.Lie.Subalgebra`, `LieSubalgebra`;
  `Mathlib.Algebra.Lie.OfAssociative`, `LieModule.toEnd`. The dependency's
  `mathlib_match` supplies these existing interfaces, so it needs no Lean repair.
- `def-wf-semisimple-lie-algebra`: `Mathlib.Algebra.Lie.Semisimple.Basic`,
  `LieAlgebra.HasTrivialRadical` (defined in `.Defs`) and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`. I also read the published
  `WeilConjectures.Mathlib.Algebra.Lie.Radical` bridge
  `hasTrivialRadical_iff_forall_isSolvable_eq_bot`; the Mathlib predicate already
  says exactly what the dependency means, so no duplicate specialization is made.
- `def-sfb-kostant-integral-form`: all four new definitions listed above; this is
  the sole new statement dependency.
- Existing standard definitions: `Mathlib.Algebra.Lie.Weights.Basic`,
  `LieModule.weightSpace`; `Mathlib.LinearAlgebra.RootSystem.Base`,
  `RootPairing.Base`, `Base.IsPos`, `Base.toCoweightBasis`; `.Chain`,
  `RootPairing.chainBotCoeff`; `Mathlib.Algebra.Lie.UniversalEnveloping`,
  `UniversalEnvelopingAlgebra`, `ι`, `lift`, `lift_ι_apply`, `lift_unique`;
  `Mathlib.Algebra.Algebra.Subalgebra.Lattice`, `Algebra.adjoin`.
- The proof dependency `lem-sfb-root-base-rational-integral-spans` is a Mathlib
  match: `.BaseExists`, `RootPairing.Base.mk'`, and `.Base`, the weight and
  coweight bases and the two integral-span equalities. `.BaseExists` is a plain
  proof import; `.Base` is already public because the signature uses it.
- The proof dependency `lem-sfb-enveloping-universal-property` is the Mathlib
  `lift`/`lift_ι_apply`/`lift_unique` match, already publicly imported through
  the definition module. The other four proof nodes (Newton expansion, rank-one
  straightening, rank-two straightening, rational PBW) currently have neither a
  Lean module nor an exact Mathlib match, so no nonexistent module is imported.
  Their proof dependencies and docstring citations are retained unchanged.

Edge cases checked before drafting:

- The zero Lie algebra and empty root/simple-root sets are permitted. There is
  no `Nonempty I`, `0 < r`, `0 < N` or `Nontrivial L`. Empty product lists are one,
  the exponent-index type has a single element, and the canonical integer map
  expresses exactly U_Z = ℤ.
- Every root or toral exponent may be zero. `0! = 1` and both power zero and the
  falling empty product are one; there is no division by a zero rational.
- Rank one has only opposite-root interactions and remains within the statement;
  the zero-bracket clause explicitly excludes opposite roots. Repeated roots
  have no root sum in a reduced root system and their alternating bracket is zero.
- Products are list products, so arbitrary orders are respected and no
  commutativity of U_Q or convexity of the root order is assumed.
- Every root vector normalization meeting the specified Chevalley relations is
  allowed; there is no new sign-coherence assumption on the structure constants.
- V can be zero or infinite-dimensional. Universes u, v, w are explicit and
  independent; all binders, including the binomial list index, are explicit.

Searches for an existing statement and constructions:

- `msearch.py leanfinder`, query `Kostant integral PBW basis divided root powers
  binomial Cartan elements`: eight Geck-construction hits, not an integral
  enveloping form or a PBW theorem.
- `msearch.py loogle`, query `UniversalEnvelopingAlgebra, LieAlgebra.IsKilling,
  LieAlgebra.IsChevalleyBasis`: no hits, with the diagnostic that the proposed
  `IsChevalleyBasis` name is unknown. I did not infer absence from this alone.
- `msearch.py grep`, query `ChevalleyBasis|Kostant|kostant|dividedPower` under
  `Algebra/Lie`: zero hits.
- `msearch.py leansearch`, query `Kostant integral form is the integer subalgebra
  generated by root vector divided powers`: eight hits including algebra
  presentation cores and the Killing root system, none the required construction.
- `msearch.py loogle`, query `"dividedPower"`: twelve commutative-ideal
  `DividedPowers` hits, unsuitable for a noncommutative enveloping algebra.
- `msearch.py grep`, query `Kostant|kostant|rationalDividedPower|rationalBinomial`:
  zero hits over Mathlib.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for Kostant, divided powers,
  and all four proposed names found no construction or statement. A concurrent
  refresh exposed `ChevalleyRootNormalization`, whose full signature and docstring
  I read; it proves existence of the Lie-algebra basis, not the integral form or
  its PBW basis. It is not a duplicate of this item. Exact item-id grep in the
  upstream source returned no matches.
- `rg -l` over `dag/nodes` for Chevalley bases and Kostant forms found only related
  statement nodes, not a definition node. `tools/blueprint_refs.py search` for
  `Kostant` and `Chevalley basis` both returned zero blueprint matches. The existing
  `dag/lean_names_upstream.json` likewise had no Kostant or ChevalleyBasis match.
- Mathlib's full enveloping-algebra declaration, quotient relation and universal
  property were read directly; they supply the reused U_Q, not the absent
  noncommutative integral construction. `Ring.choose` is for binomial commutative
  semirings and does not apply to U_Q, so the scalar-times-falling-product formula
  is written explicitly without introducing such a structure on U_Q.

Validation: the two files compiled separately in dependency order using the
prescribed `scompile.py`, on the server against the live published library. The
first attempt identified an untyped list lambda in the binomial formula; it was
repaired by binding `k : ℕ` explicitly. Both modules then compiled cleanly. The
final delivery dry run and push are performed with `deliver2.py`. The first
dry run required the live new-node schema field `import_flags`; the empty list
was added and the check re-run.

## New nodes

`def-sfb-kostant-integral-form` introduces the root-divided-power integer
subalgebra and the displayed ordered triangular monomials. Its generic scalar
formulas `Algebra.rationalDividedPower` and `Algebra.rationalBinomial` also cover
zero exponents. All four definitions have concrete data and their own source and
blueprint docstrings; no integrality or PBW theorem is used to define them. The
new node cites `def-wf-lie-algebra`, and the item cites it. Its source is Milne
23h pp.508–510 and the supporting Kostant integral-form input already identified
by the item; it makes no claim that Milne proves integral PBW. Searches above and
in its `mathlib_searches` establish that no existing definition node, Mathlib
interface, upstream declaration, or Sheaf declaration carries these constructions.
The inherited blueprint ancestor is null (the imported blueprint has no such
node), and the explicit place and full via chain are retained with this item
prepended. The node does not introduce a second root-system or Chevalley-basis
notion: those remain the existing Mathlib objects and explicit hypotheses of the
item's theorem.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
