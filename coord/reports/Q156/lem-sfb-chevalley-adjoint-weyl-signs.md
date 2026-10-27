## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyAdjointWeylSigns` states
`LieAlgebra.chevalley_adjoint_weyl_signs`, with its sole proof `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The item node changes only in `lean`.

Hypothesis-by-hypothesis correspondence:

- The rational Lie algebra is `L : Type u`, `[LieRing L]`, `[LieAlgebra ℚ L]`.
  Finite dimension is `[FiniteDimensional ℚ L]`; semisimplicity is the dependency's
  `[HasTrivialRadical ℚ L]`, which means no nonzero solvable ideal.
- The splitting Cartan is `H : LieSubalgebra ℚ L`, `[IsLieAbelian H]`, and `hmax`
  (maximal abelian). The diagonal splitting is recorded by `hdecomp`: the internal
  direct sum of H and the ordinary simultaneous eigenspaces of its roots. This
  implies each adjoint of an H-element is rationally diagonalizable.
- The finite reduced root system is `I : Type v`, `[Finite I]`,
  `P : RootPairing I ℚ (Module.Dual ℚ H) H`, with root-system, crystallographic,
  and reduced instances, exactly as in the recorded normalization module.
  `heval` identifies its pairing with evaluation, so roots and coroots are the
  actual functionals and Cartan elements in the node, not an abstract unrelated pairing.
- `hdim` gives one-dimensional root spaces. `e : I → L` and `he` put a nonzero
  chosen rational vector in each of them. Together with `hdecomp`, these render
  the displayed direct sum H plus the lines Q e_beta, and the weight brackets
  `[h,e_beta] = beta(h)e_beta`. `LieModule.mem_weightSpace` is precisely that equation.
- `hopp` is `[e_alpha,e_-alpha] = h_alpha`, using
  `P.reflectionPerm i i` for the negative-root index. The root-pairing axiom gives
  alpha(h_alpha)=2, after `heval`.
- `hadd` is the bracket constant `±(p+1)` when the sum is a root, with
  `P.chainBotCoeff i j` the maximal backward endpoint distance. In a reduced system,
  whenever the sum is a root the two roots are independent, so this endpoint
  definition is meaningful (its dependent-root junk case is never used).
- `hzero` states the bracket vanishes if the sum is neither a root nor zero.
  There is no extra pinning, positivity, or choice of a simple base in the item.

Clause-by-clause correspondence:

- The first conjunct concludes `∀ i, IsNilpotent (ad ℚ L (e i))`.
  In particular the negative-root adjoint, and its negative, are nilpotent too.
  Thus every `IsNilpotent.exp` in the statement is the intended finite exponential,
  rather than its value on a nonnilpotent endomorphism. Mathlib defines it as
  the sum of `(n.factorial : ℚ)⁻¹ • D^n` up to `nilpotencyClass D`;
  `IsNilpotent.exp_eq_sum` identifies it with any sufficiently long truncation.
- The three-factor product is literally
  `exp(ad e_i) * exp(-ad e_-i) * exp(ad e_i)` in `Module.End ℚ L`.
  Multiplication composes operators from right to left, agreeing with q_alpha.
- `P.reflectionPerm i j` indexes s_alpha(beta): `P.root_reflectionPerm` identifies
  its root with `P.reflection i (P.root j)`, and evaluation makes this
  beta - beta(h_alpha) alpha.
- `∀ j, ∃! ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ...` states the root-vector identity and
  the sign range. The uniqueness expresses the last sentence that the signs are
  determined by the fixed basis; it follows from the nonzero target vector.
- The second conjunct for every `i` states for every `h : H` that the same product
  takes `(h : L)` to `(h : L) - P.root i h • (P.coroot i : L)`.
- There is no nonempty index hypothesis. When I is empty every conclusion is
  vacuous, and the root-system spanning and direct-sum data force the zero algebra.

Dependency declarations read and used:

- `def-wf-lie-algebra`: Mathlib `LieRing`, `LieAlgebra`, `LieSubalgebra`, and
  `LieAlgebra.ad` (`Mathlib.Algebra.Lie.Basic`, `.Subalgebra`, `.OfAssociative`).
  These enter through the public import of the normalization module.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  (`Mathlib.Algebra.Lie.Semisimple.Defs` / `.Basic`).
- `lem-sfb-chevalley-root-normalization`:
  `LieAlgebra.exists_chevalley_basis_of_pinning`
  (`Sheaf.Algebra.Lie.ChevalleyRootNormalization`), publicly imported.
  Its full signature and proof docstring were read. The chosen root vectors here
  are the same output data: `he`, `hopp`, `hadd`, `hzero`, together with the
  ordinary weight-space direct decomposition. No duplicate Chevalley-basis definition.
- Proof input `lem-sfb-split-semisimple-root-decomposition`:
  `LieAlgebra.exists_splitSemisimple_rootDecomposition`
  (`Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`), plain imported.
- Proof input `lem-sfb-root-string-integer-interval`: the exact Mathlib match
  `RootPairing.root_add_zsmul_mem_range_iff`
  (`Mathlib.LinearAlgebra.RootSystem.Chain`), already publicly imported through
  normalization. Its finite-index, characteristic-zero, domain,
  crystallographic, and root-independence hypotheses were read.
- `lem-sfb-integrable-sl2-reflection-automorphism` has no recorded Lean or Mathlib
  declaration at preparation time, so it cannot yet be imported. It remains a
  future proof input, not a missing notion needed to type this statement.
- `IsNilpotent.exp` and `IsNilpotent.exp_eq_sum`
  (`Mathlib.RingTheory.Nilpotent.Exp`), publicly imported; these supply the
  canonical finite exponential without any new helper definition.

Edge cases checked before writing: empty root system/zero Lie algebra; equal
roots and opposite roots (normalization handles the rank-one string, while
`hadd` only constrains actual root sums); rank one, where q sends e_alpha to
-e_-alpha and negates its coroot; reducible root systems and roots in different
components (the absent-sum bracket is zero). Arbitrary rational rescaling of
simple pinning vectors is allowed. No positivity, connectedness, nonempty root
set, or extra universe equation is introduced. The sign is unique even though
its value changes with allowed changes of the fixed Chevalley basis.

Searches made using the prescribed msearch.py wrapper (Q156/item):

- LeanFinder: `In a rational Chevalley basis the adjoint exponential Weyl operator
  sends each root vector to plus or minus its reflected root vector`.
  Eight hits, including `LieAlgebra.IsKilling.reflectRoot`,
  `RootPairing.weylGroup.ofIdx_smul`, `RootPairing.reflection_apply_self`,
  and `RootPairing.reflection_apply_root'`; none states the signed adjoint identity.
- Loogle: `LieAlgebra.ad, RootPairing.reflectionPerm`: zero hits.
- Mathlib grep: `chevalley|Chevalley|exp.*reflection|reflection.*exp` in
  `Algebra/Lie`: fourteen hits, referring to Lie cohomology, Jordan--Chevalley,
  or the Chevalley-basis TODO; none states this result.
- Direct rg of Mathlib's Lie and Nilpotent directories found the canonical finite
  exponential and the derivation exponential. The latter is an automorphism
  construction, not the root-vector sign theorem.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Chevalley, adjoint Weyl, exponential/reflection,
  and the proposed declaration found normalization/integral-PBW modules, but no
  existing signed adjoint Weyl identity. The exact item-id search of
  `lean/WeilConjectures` had no matches.

Source checked: local Milne PDF, printed pp.508–511 (PDF pages 520–523).
Theorem 23.71 gives bracket magnitudes, and the following discussion gives rational
Chevalley data and nilpotent exponential actions. The signed Weyl conclusion is
correctly identified by the DAG as an agent-expanded consequence, not a quotation
of that theorem. No STATEMENT-DISPUTED flag or node fault was found.

Validation: scompile.py compiled both sandbox and library module names cleanly
(1.9 s / 2.2 s respectively); no unexpected warning. Every variable and universe
is bound explicitly, with autoImplicit and relaxedAutoImplicit disabled.

## Second reading by Q156

The dispatcher explicitly forbids starting another agent; the maintainer supplies
an independent review after delivery. This section records the worker's separate
rereading, not a claim that another worker reviewed it.

Compared the node and module clause by clause. The root pairing and ordinary
weight spaces agree with the normalization dependency. Nilpotence is concluded,
not assumed as an extra hypothesis. The middle exponential has the required
minus sign and negative-root index; the composition order is right to left.
Both the root identity and the Cartan formula use exactly that same product.
The unique sign adds no mathematical restriction because `he` makes each root
vector nonzero; it records dependence on the fixed basis. Empty roots are allowed.
No missing clause or mismatch was found in this rereading, so no correction was made.
