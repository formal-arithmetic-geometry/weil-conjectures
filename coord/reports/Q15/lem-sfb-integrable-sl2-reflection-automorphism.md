## Worker report

The module `Sheaf.Algebra.Lie.IntegrableSl2ReflectionAutomorphism` states
`LieAlgebra.exists_integrableSl2_reflectionAutomorphism`, with its sole proof
`sorry`. The item node changes only in `lean`. No statement correction, new
definition, or dependency repair is needed.

Hypothesis and conclusion correspondence, checked against the full node:

- The rational Lie algebra of arbitrary dimension is `(L : Type u) [LieRing L]
  [LieAlgebra ℚ L]`, with explicit universe `u`. There is no finite-dimensional
  hypothesis or weight-space decomposition hypothesis.
- The abelian subalgebra is `(T : LieSubalgebra ℚ L) [IsLieAbelian T]`.
  The element in that subalgebra is `(h : T)`; `(e f : L)` are in the ambient
  algebra; `(α : T →ₗ[ℚ] ℚ)` is the given rational linear functional.
- `hα : α h = 2` is exactly the normalization. `hef` says `⁅e, f⁆ = (h : L)`.
- `hte` says `⁅(t : L), e⁆ = α t • e` for every `t : T`.
  `htf` says `⁅(t : L), f⁆ = -(α t) • f` for every `t : T`.
- `hne` and `hnf` each quantify first over `x : L`, then over a positive
  natural exponent annihilating that vector under `ad ℚ L e` or `ad ℚ L f`.
  Thus the bound may depend on the vector. Requiring a positive exponent
  loses no case of “some power”: if exponent zero annihilates x, then x = 0
  and exponent one also annihilates it.
- `∃ w : L ≃ₗ⁅ℚ⁆ L` asserts a bijective rational linear bracket-preserving map.
  Its underlying function is specified by `⇑w = ... ∘ ... ∘ ...`, with the
  factors in the exact order exp(ad e), exp(-ad f), exp(ad e).
- Each factor is the existing Mathlib finite-support sum
  `∑ᶠ n : ℕ, (n.factorial : ℚ)⁻¹ • (D ^ n) x`.
  Powers are powers of `Module.End ℚ L`, so power zero is the identity.
  If D^N x = 0 then all terms for n ≥ N vanish. Consequently this `finsum`
  equals the node's finite sum for any annihilating bound. The same applies
  to -ad f because its nth power on x differs by the scalar (-1)^n.
  No infinite series convergence, arbitrary exponential map, or uniform
  bound is substituted. No new notion is introduced: the three existing
  `finsum` expressions directly render the formula in the node.
- The next conjunct is `∀ t : T, w (t : L) = (t : L) - α t • (h : L)`.
  The following conjuncts are `w e = -f` and `w f = -e`.
- For every `β : T →ₗ[ℚ] ℚ`, the final conjunct provides a rational linear
  equivalence from `LieModule.weightSpace L (fun t : T ↦ β t)` to
  `LieModule.weightSpace L (fun t : T ↦ β t - β h * α t)`.
  Its equation `∀ x, (φ x : L) = w (x : L)` makes it the restriction of
  this same w, rather than an unrelated isomorphism between the spaces.
  `LieModule.mem_weightSpace` identifies these spaces exactly with the
  simultaneous bracket eigenspaces defined in the node.

Dependency declarations read and used:

- `def-wf-lie-algebra` is a Mathlib leaf with a `mathlib_match`, not a missing
  `lean` record. Its relevant declarations are `LieRing`, `LieAlgebra`, and
  `LieEquiv` in `Mathlib.Algebra.Lie.Basic`, `LieSubalgebra` in
  `Mathlib.Algebra.Lie.Subalgebra`, and `LieAlgebra.ad` in
  `Mathlib.Algebra.Lie.OfAssociative`. Their signatures and defining fields
  were read. The public imports expose these same definitions transitively.
- `IsLieAbelian` in `Mathlib.Algebra.Lie.Abelian` is the trivial self-action,
  exactly vanishing of all brackets within T.
- `LieModule.weightSpace` and `LieModule.mem_weightSpace` in
  `Mathlib.Algebra.Lie.Weights.Basic` give ordinary simultaneous eigenspaces,
  not generalized weight spaces. No nilpotence or finite-dimensionality
  assumptions are required by these declarations.
- `finsum` in `Mathlib.Algebra.BigOperators.Finprod` sums precisely the finite
  support. The local nilpotence hypotheses ensure that its zero-for-infinite-
  support default never applies to any of the three factors.
- The proof-only node `lem-sfb-locally-nilpotent-derivation-exponential` has
  no recorded Lean declaration or module in the read DAG. There is therefore
  no stated proof-dependency module to import. Its proof role is retained
  explicitly in the theorem's complete five-step natural-language proof plan.
  The present signature uses only Mathlib notions and does not require a
  separate definition of a locally nilpotent exponential.

Sources: read Milne's actual PDF, printed pp.503–504 (Theorem 23.63 and first
proof) and p.508 (extension to all characteristic-zero fields). The expanded
local exponential and reflection calculation is explicitly agent-supplied in
the node and remains identified as such in the module. Read the current
`literature/blueprint/latest/` stability unit and direct-images proof for the
ancestor context; this item is a supporting lemma, not the unit statement.

Edge cases checked before writing:

- L may be infinite-dimensional; no uniform annihilating exponent is needed.
- The zero vector may use exponent one; its exponential sum is zero.
- L = 0 or T = 0 makes α(h) = 2 impossible over ℚ. The signature adds no
  independent nonzero hypothesis, and does not use `IsSl2Triple`, whose
  separate nonzero condition would need accounting for.
- β = 0 yields the same zero-weight space; β = α yields weight -α.
  A missing weight space is the zero subspace and still admits the asserted
  restriction equivalence. No nonzero-weight assumptions occur.
- Elements t with α(t) = 0 are fixed, while t = h gives w(h) = -h.
  The sl2 matrix model confirms the two minus signs on e and f.
- The weight equivalence is linear, not asserted to be a Lie equivalence:
  arbitrary nonzero weight spaces need not be Lie subalgebras.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "locally nilpotent sl2 adjoint exponentials give a
  Weyl reflection automorphism on weight spaces"`: eight hits, including
  `LieAlgebra.IsKilling.reflectRoot`, root-pairing reflections, and sl2 module
  formulas. `reflectRoot` requires a finite-dimensional Killing Lie algebra;
  none states the present arbitrary-dimensional automorphism theorem.
- `msearch.py ... leansearch "Weyl reflection from locally nilpotent adjoint
  exponentials on a rational Lie algebra"`: eight hits, led by
  `LieDerivation.exp`; other hits concerned globally nilpotent operators or
  the abstract Weyl group. No match.
- `msearch.py ... loogle "LieDerivation.exp, LieModule.weightSpace,
  LieAlgebra.ad"`: zero hits. The focused query `"LieDerivation.exp"` returned
  `LieDerivation.exp`, `exp_apply`, and `exp_map_apply`. Read their actual
  source: exp requires `IsNilpotent D.toLinearMap`, a uniform bound, so it
  cannot be used here as the pointwise exponential construction.
- `msearch.py ... grep "locallyNilpotent|LocallyNilpotent|def exp|weightSpace"
  Algebra/Lie`: 25 hits, principally the global exponential and ordinary or
  generalized weight-space files. The ordinary weight space was reused.
- Direct `rg` in Mathlib's Lie sources found and checked `LieAlgebra.ad`,
  `LieRing`, `LieAlgebra`, `IsLieAbelian`, `LieEquiv`, `weightSpace`, and exp.
  Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `locallyNilpotent|LocallyNilpotent|integrableSl2|sl2Reflection` found no
  existing declaration. Searching the item id in `lean/WeilConjectures`
  found none; in `lean/Sheaf` it found only proof-plan references in
  `RationalSerrePresentation` and `ChevalleyAdjointWeylSigns`.
  The new declaration name has no hit in `dag/lean_names_upstream.json`
  or either library source tree. No existing statement was duplicated.

Validation: `scompile.py Q15 lem-sfb-integrable-sl2-reflection-automorphism
<module file>` passed both sandbox and library module compilation, with no
diagnostics (8.4 s and 50.2 s, respectively). Every universe and variable is
explicitly bound, with `set_option autoImplicit false`. No disputed statement
or node fault was found.

## Second reading by Q15

In a separate reading pass, the same dispatcher-started worker reopened the
node and the delivered Lean file. No subagent was started, as required by the
dispatcher brief; independent review is the maintainer's delivery review.

The rereading checked every binder against the node: rational scalar field,
arbitrary universe and dimension, actual abelian subalgebra and h membership,
the linear α, its normalization, the bracket of e and f, both bracket-weight
relations for every t, and both vector-dependent positive nilpotence bounds.
The conclusion uses a Lie automorphism with the specified underlying three
finite-support sums, the t formula and both negative root-vector formulas.
Every β is covered by the ordinary Mathlib weight spaces, and the equation on
φ ties the equivalence to this same w. In particular, replacing weight spaces
by generalized ones or leaving φ unrelated to w would have been mismatches;
neither occurs. No finite-dimensionality, nonzero vector, root-system,
Killing-form, or weight-decomposition assumptions were added. No mismatch
was found and no signature change was needed after this reading.
