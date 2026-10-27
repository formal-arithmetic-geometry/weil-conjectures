## Worker report

The single module `Sheaf.Algebra.Lie.RationalKillingRootDuality` states
`LieAlgebra.rational_killing_root_duality`, with one `sorry` and no new definitions.
The node's statement, dependencies, proof and other metadata are unchanged; only `lean` is set.

Hypotheses, in the order of the node:

- A rational Lie algebra is `L : Type u`, `[LieRing L]`, `[LieAlgebra ℚ L]`.
  Its finite dimension is `[FiniteDimensional ℚ L]`. Semisimplicity is precisely the
  recorded `[LieAlgebra.HasTrivialRadical ℚ L]`, not Mathlib's differently defined
  `LieAlgebra.IsSemisimple`.
- `H : LieSubalgebra ℚ L` is abelian by `[IsLieAbelian H]`; `hmax` says every abelian
  Lie subalgebra containing H equals H. It is maximal among all abelian subalgebras.
- The finite set of rational roots is `R : Finset (Module.Dual ℚ H)`. A root is
  indexed by `ρ : R`. `P : RootPairing R ℚ (Module.Dual ℚ H) H` with
  `[P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]` supplies the standard
  reduced crystallographic root-system structure. `hroot` identifies `P.root ρ`
  with the actual functional `ρ.val`; `hpair` identifies its pairing with evaluation.
  In particular `P.root_coroot_two`, rewritten using these two identifications, is
  exactly `ρ.val (P.coroot ρ) = 2`, so every root is nonzero. These identifications
  prevent an unrelated root system or an arbitrary root-coroot pairing being used.
- The given normalized `h_ρ` is `P.coroot ρ : H`. The root-system reflection
  permutations and integer Cartan pairings are data/properties of the assumed root
  system; no Killing-form nondegeneracy or duality is assumed in P. Its perfect
  pairing is just the ordinary pairing between H and its full linear dual.
- `LieModule.weightSpace L (fun h : H ↦ ρ.val h)` is exactly the ordinary
  simultaneous eigenspace, by `LieModule.mem_weightSpace`. This is not a generalized
  root space. `hsplit` is `DirectSum.IsInternal` on the `Option R` family whose
  `none` summand is H and whose `some ρ` summand is that weight space. It states
  exactly the internal direct-sum decomposition. Because all the summands are actual
  rational eigenspaces, it also expresses simultaneous diagonal action over ℚ.
  No extra algebraic-closure or abstract Cartan-subalgebra hypothesis is imposed.
- `hdim` gives dimension one of each such root space.
- `hbracket` says the linear span of all `[x,y]`, with x of root ρ and y of root
  -ρ, lies in H. `hcoroot` says `P.coroot ρ` lies in that same linear span, exactly
  the meaning of `[L_ρ,L_{-ρ}]` specified in the node's proof. The negative root
  space uses `fun h ↦ -ρ.val h`, so it needs no arbitrary choice of a negative index.

Conclusions, clause by clause:

- B is the existing `killingForm ℚ L`. Its definition is `LieModule.traceForm ℚ L L`;
  `killingForm_apply_apply` unfolds it to ordinary `LinearMap.trace ℚ L`
  of `LieAlgebra.ad ℚ L x ∘ₗ LieAlgebra.ad ℚ L y`, the requested B(x,y).
  Bilinearity is part of its `LinearMap.BilinForm` type.
- `LinearMap.IsSymm (killingForm ℚ L)` states symmetry. The next universally
  quantified equality states `B([x,y],z) = B(x,[y,z])` with the exact argument order.
- `∀ h : H, h ≠ 0 → 0 < killingForm ℚ L h h` is positive definiteness on H,
  with the rational order.
- The existential `t : Module.Dual ℚ H →ₗ[ℚ] H` is the family `t_ℓ`. For each ℓ,
  the first component says `∀ h, B(t ℓ,h)=ℓ(h)`; the second says every v satisfying
  that equation equals `t ℓ`. This is existence and uniqueness for every functional.
  Packaging the family as a linear map records its forced linearity; it introduces
  no hypothesis and follows from uniqueness and bilinearity, as in proof step 5.
- The existential `b : LinearMap.BilinForm ℚ (Module.Dual ℚ H)` together with
  `∀ ℓ μ, b ℓ μ = killingForm ℚ L (t ℓ) (t μ)` defines exactly the stated dual form.
  Its bilinearity is encoded in its type; `LinearMap.IsSymm b` is symmetry;
  `∀ ℓ, ℓ ≠ 0 → 0 < b ℓ ℓ` is positive definiteness.
- For every root and every pair of functionals, the displayed equality for
  `ℓ - ℓ (P.coroot ρ) • ρ.val` and `μ - μ (P.coroot ρ) • ρ.val` is exactly reflection
  invariance of b, including when either functional is zero.
- The last universally quantified conjunction gives `0 < b ρ.val ρ.val`, hence d_ρ>0;
  `P.coroot ρ = (2 / b ρ.val ρ.val) • t ρ.val` is the coroot formula in H; and the
  final equality for x and y in the two actual weight spaces is
  `[x,y] = B(x,y) • (t ρ.val : L)`, the bracket formula in L.

Dependency declarations read and used:

- `def-wf-lie-algebra`: Mathlib `LieRing`, `LieAlgebra` in `Algebra.Lie.Basic`,
  `LieSubalgebra` in `Algebra.Lie.Subalgebra`, and `LieAlgebra.ad` in
  `Algebra.Lie.OfAssociative`, exposed through the public Lie imports. Bracket spans
  use ordinary `Submodule.span` as required by this dependency's definition.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  `Mathlib.Algebra.Lie.Semisimple.Defs`, imported via `Semisimple.Basic`;
  `hasTrivialRadical_iff_no_solvable_ideals` there confirms the exact definition.
- `def-weil-endomorphism-trace`: `LinearMap.trace` in `Mathlib.LinearAlgebra.Trace`,
  used by `killingForm` in `Mathlib.Algebra.Lie.TraceForm`. Read its definition and
  `trace_eq_matrix_trace`; no private trace is introduced.
- Proof dependency `lem-sfb-finite-dimensional-perfect-pairing` is the Mathlib leaf
  `LinearMap.IsPerfPair.of_injective` in `Mathlib.LinearAlgebra.PerfectPairing.Basic`,
  imported without `public`. Its full signature and `IsPerfPair` were read.

The additional standard interfaces were read in `Mathlib.Algebra.Lie.Weights.Basic`
(`weightSpace` and its membership theorem), `Mathlib.Algebra.DirectSum.Basic`
(`DirectSum.IsInternal`), and `Mathlib.LinearAlgebra.RootSystem.Defs`, `Reduced`,
`IsValuedIn` (`RootPairing` and all three indicated classes).

Sources: read Milne's local PDF pages 515 and 520–521 (printed 503 and 508–509),
including the simultaneous rational eigenspace decomposition and the normalization
of opposite-root brackets by root evaluation 2. Read the latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`; this item is a supporting
calculation along the recorded chain, not a change to that unit's own statement.

Edge cases checked: the zero Lie algebra, H=0 and R empty are admitted (no Nonempty
or Nontrivial hypothesis). For R empty the root-system spanning axiom forces H=0,
consistent with semisimplicity and the direct sum. Positivity at zero is not claimed;
ℓ=0 has unique t=0. All root denominators are positive conclusions, not assumptions.
The weight spaces are literal eigenspaces over ℚ. The ambient universe u is arbitrary;
there is no independent small universe for test objects or roots. Reducible semisimple
algebras are allowed. No statement defect or dispute was found.

Searches executed with `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- `leanfinder`: "The Killing form of a split semisimple rational Lie algebra is positive
  definite on a split Cartan subalgebra and identifies roots with coroots" returned
  rootSystem, coroot formulas, the opposite-root bracket theorem and
  restrict_killingForm_eq_sum. They assume Cartan/IsKilling interfaces and do not state
  the present positivity theorem from the explicit hypotheses.
- `loogle`: "killingForm, LieAlgebra.IsKilling.cartanEquivDual, RootPairing" returned
  no hits for that combined query.
- `grep`, subdirectory `Algebra/Lie`: "weightSpace|rootSpace|killingForm|IsMaximalAbelian"
  returned 25 hits, including TraceForm and weight-space material; no complete match.
- `leansearch`: "The Killing form of a split rational semisimple Lie algebra is positive
  definite on its split Cartan and identifies coroots with Killing dual roots" returned
  killingForm, IsKilling, coroot, rootSystem, traceForm_coroot and cartanEquivDual;
  none is the whole statement.
- Direct `rg -n` searches in `lean/WeilConjectures` and `lean/Sheaf` for rational
  Killing positivity, maximal abelian and root duality found no matching declaration;
  the exact item ID search in `lean/WeilConjectures` was empty. Searches for the
  proposed declaration name in Mathlib, both project source trees and
  `dag/lean_names_upstream.json` were empty. Read the related Mathlib signatures.
- Searched definition-node statements for root systems/root pairings and found no
  node needed to introduce a new notion: all notation in this statement is supplied
  by existing Mathlib definitions. No new definition or dependency module is necessary.

Validation: scompile.py compiled the module in sandbox mode and its library module
mode cleanly, with no warnings or errors. Initial parser/linter diagnostics (reserved
lambda token and broad Classical opening) were corrected before the clean compile.

## Second reading by Q130

I reread the node and final module side by side as a self-audit; no additional agent
was started, as the dispatcher brief prohibits delegation. Independent review is the
maintainer's delivery review. I checked especially that the root pairing is ordinary
evaluation, roots are the actual functionals in R, H is maximal among abelian
subalgebras, the direct sum uses actual eigenspaces, the bracket span is a linear
span rather than a Lie ideal, and coroot normalization follows from root_coroot_two.
I checked both uniqueness of each t and the defining equality for b, and that the
reflection formula uses evaluation of the arbitrary functional on the coroot.
Finally I checked positivity of every d, the coroot equality in H, and the bracket
equality in L with the requisite coercion. No mismatch was found and no statement
change was made.
