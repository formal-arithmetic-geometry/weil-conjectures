## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyRankTwoStraightening` states
`LieAlgebra.chevalley_dividedPower_commutator_lower_degree`, with `sorry` as its
entire proof. It changes no mathematical statement or accepted stage-1 split.
The inherited BLOCKED ending concerned stage-1 re-splitting; the current queue
lists this node at stage 2 and the current brief's stage-handoff rule explicitly
permits writing its missing Lean statement. There is no released repair note.

The node gains the already landed `def-sfb-kostant-integral-form` in `stmt_deps`
to cite the shared divided-power definition. No new definition, dependency
replacement, private notation, helper theorem, or additional axiom is introduced.

Hypothesis-by-hypothesis correspondence:

- The rational Lie algebra is `(L : Type u) [LieRing L] [LieAlgebra ℚ L]`.
  `FiniteDimensional ℚ L` is finite dimensionality, and
  `LieAlgebra.HasTrivialRadical ℚ L` is precisely the blueprint's semisimplicity,
  following the `mathlib_match` of `def-wf-semisimple-lie-algebra`.
- `(H : LieSubalgebra ℚ L) [H.IsCartanSubalgebra]` is the Cartan subalgebra.
  `[LieModule.IsTriangularizable ℚ H L]` is the splitting condition: the
  Mathlib CartanSubalgebra docstring explicitly specifies this mixin for a
  splitting Cartan. No algebraic closure or extra coefficient extension is used.
- `(I : Type v) [Finite I]` indexes the roots. The arbitrary universe `v`
  does not require a nonempty or specifically enumerated root system.
  `P : RootPairing I ℚ (Module.Dual ℚ H) H`, together with
  `P.IsRootSystem`, `P.IsCrystallographic`, `P.IsReduced`, gives the reduced
  crystallographic root system in the dual of H. `heval` identifies its
  perfect pairing with actual evaluation on H, rather than an unrelated pairing.
- `Δ : P.Base` selects the simple roots implicit in a Chevalley basis.
  `B : Module.Basis (Δ.support ⊕ I) ℚ L`, `Bh`, and `Be` give exactly the
  simple coroots and root vectors as a basis. These are basis data, not an
  assumed divided-power straightening result.
- `e : I → L` is the chosen family of root vectors. `he` gives their
  nonvanishing and membership in the ordinary simultaneous eigenspace
  `LieModule.weightSpace L (P.root i)`. By `LieModule.mem_weightSpace` this
  says `[h,e_i] = (P.root i h) • e_i` for every h in H, as in the node.
- `hopp` is `[e_i,e_(-i)] = h_i`. The opposite index is
  `P.reflectionPerm i i`, whose root is `-P.root i`. The coroot is
  `P.coroot i : H`, coerced into L. The RootPairing axiom
  `root_coroot_two` and `heval` give its evaluation 2. Together with `hopp`
  and `he`, it lies in the bracket of the positive and negative root spaces,
  so this also preserves the node's explicit coroot convention.
- `hadd` states the exact integer sign and root-string normalization:
  `ε : ℤ`, `ε = 1 ∨ ε = -1`, and bracket coefficient
  `(ε : ℚ) * (P.chainBotCoeff i j + 1)`. Mathlib Chain.lean defines
  `chainBotCoeff i j` as the largest downward index in the i-string through j.
  This is the node's p with the correct argument order. Its dependent-pair junk
  value cannot affect `hadd`: in a reduced system such a pair has no root sum.
- `hzero` gives zero bracket when the sum is neither a root nor zero.
- `(α β : I)`, `hne : α ≠ β`, and `hnopp : P.root α ≠ -P.root β`
  are precisely the distinct, nonopposite roots. `(m n : ℕ)` includes every
  nonnegative integer exponent, including zero.

Conclusion clause correspondence:

- `∃ (t : ℕ) (c : Fin t → ℤ) (w : Fin t → List (I × ℕ))` is a finite
  integer linear combination of ordered words. Neither a nonzero coefficient
  nor a nonempty word or sum is imposed.
- For every term i and pair d in its word, `1 ≤ d.2` gives positive exponents.
  The index `d.1 : I` makes each letter a root. The existential naturals p,q
  and `P.root d.1 = p • P.root α + q • P.root β` give exactly membership
  in the nonnegative integral cone, using nsmul in the rational dual space.
- `((w i).map Prod.snd).sum < m + n` is strictly lower total degree.
- `((w i).map (fun d ↦ d.2 • P.root d.1)).sum =
  m • P.root α + n • P.root β` is the weight requirement for each word,
  not merely for the entire linear combination.
- `Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e i)) a`
  is exactly `e_i^a/a!` in the canonical tensor-algebra quotient. The equation
  has the node's commutator order, and its right hand side is
  `∑ i : Fin t, c i • ((w i).map ...).prod`. Integer scalar multiplication
  is the integer linear-combination operation; list product preserves order.
- The second conjunct explicitly states that if `m = 0 ∨ n = 0`, that same
  commutator is zero. This is not dropped as an implicit consequence.

Dependency declarations read and used:

- `def-wf-lie-algebra` is a Mathlib leaf; its relevant declarations are
  `LieRing`, `LieAlgebra` (Mathlib.Algebra.Lie.Basic), `LieSubalgebra`
  (Mathlib.Algebra.Lie.Subalgebra), and the induced adjoint Lie module.
  These definitions are reexported by the direct imports.
- `def-wf-semisimple-lie-algebra` is also a Mathlib leaf, using
  `LieAlgebra.HasTrivialRadical` (Mathlib.Algebra.Lie.Semisimple.Defs) and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  (Mathlib.Algebra.Lie.Semisimple.Basic). The full signatures and docstrings
  were read: the former says radical = bottom and the latter says every
  solvable ideal is bottom.
- `def-sfb-kostant-integral-form` is already landed as
  `Sheaf.Algebra.Lie.KostantIntegralForm`. Its relevant shared declaration is
  `Algebra.rationalDividedPower`, explicitly `(1 / (n.factorial : ℚ)) • x ^ n`.
  Its other constructions are not copied. Read its complete module and node.
- Mathlib's `UniversalEnvelopingAlgebra`, `UniversalEnvelopingAlgebra.Rel`,
  and `UniversalEnvelopingAlgebra.ι` in Mathlib.Algebra.Lie.UniversalEnveloping
  give the specified quotient and canonical generators. Read their definitions.
- The root and Cartan interfaces use Mathlib.Algebra.Lie.CartanSubalgebra,
  Mathlib.Algebra.Lie.Weights.Basic, and Mathlib.LinearAlgebra.RootSystem.Base
  (which reexports Chain, root-system finiteness and crystallographic structure).
  Read IsCartanSubalgebra, IsTriangularizable, weightSpace, RootPairing,
  IsRootSystem, Base, and chainBotCoeff signatures and docstrings.
- Both proof dependencies, `lem-sfb-chevalley-string-central-parity` and
  `lem-sfb-formal-class-two-exponential`, currently have neither a Lean record
  nor a Mathlib match. Their statements were read and the proof docstring
  retains their exact role. There is therefore no recorded module to import.
  In particular this module does not import the downstream Kostant PBW theorem,
  which would close a dependency cycle. The maintainer can add proof imports
  when those proof nodes acquire statements, as stages/2-statements.md specifies.

Source and edge checks:

- Read Milne's PDF around printed pp.508–510 with pdftotext. Theorem 23.71
  gives precisely ±(p+1); the preceding paragraphs give the simple-coroot/root
  vector Chevalley basis. Milne does not prove this divided-power identity,
  as already acknowledged by the node's source and proof_origin. The module
  identifies the formal coefficient argument as agent-written. No fabricated
  attribution or replacement proof is introduced. The current blueprint is
  literature/blueprint/latest (main-20261024); no direct blueprint statement
  with this node id exists, agreeing with blueprint.is = null.
- If m or n is zero, the factorial denominator is 1 and the divided power is 1.
  The commutator is zero and t = 0 gives the empty combination. The word
  conditions then hold vacuously even for m = n = 0 and strict degree < 0.
- In a commuting A1 × A1 pair the combination may again be empty for positive
  m,n. For A2 and m = n = 1 the correction has one letter of exponent 1,
  degree 1 < 2 and weight α+β, with integer coefficient ±1.
- Empty root systems and the zero Lie algebra are not excluded by any
  Nontrivial or Nonempty binder. In those cases no pair α,β exists; for A1
  there is no distinct nonopposite pair. No artificial restriction is added.
- Ordered products use List.prod rather than a commutative product; weights
  use additive list sums. Root indices automatically remain in the root set.
- No statement fault, counterexample, or STATEMENT-DISPUTED flag was found.

Searches for an existing statement:

- msearch.py leanfinder: "Chevalley divided powers commutator integral linear
  combination lower degree words universal enveloping algebra" returned 8
  hits: UniversalEnvelopingAlgebra.Rel/Rel.lie_compat, LieAlgebra.ad_pow_lie,
  GeckConstruction root brackets, Serre relations, and DividedPowers.dpow_comp.
  None states the integral lower-degree straightening result.
- msearch.py loogle: "UniversalEnvelopingAlgebra, RootPairing.chainBotCoeff"
  returned 0 hits. Both interfaces themselves exist and are reused directly.
- msearch.py grep: "divided|straighten|Kostant" in Algebra/Lie returned 0 hits.
- msearch.py leansearch: "Commutator of divided powers of Chevalley root vectors
  is an integer linear combination of lower degree words" returned 8 hits,
  all commutative-ideal DividedPowers lemmas, not noncommutative enveloping words.
- rg in lean/WeilConjectures for Chevalley/root-basis/straightening and the exact
  node id found no such theorem. Existing Chevalley hits are constructibility
  or Beck–Chevalley, unrelated to root divided powers.
- rg in lean/Sheaf found ChevalleyRootNormalization and KostantIntegralPBW,
  whose full statements were read. The first constructs a normalized basis;
  the second uses this missing result in its proof. Neither is an exact match.
  It also found KostantIntegralForm and its rationalDividedPower, reused here.

Validation: scompile.py compiled this module in sandbox and library module
modes on the live server, with the default 60-second limit, no errors and no
warnings other than the allowed sorry warning (the wrapper output showed no
additional warnings). Delivery dry-run results follow below when available.

The required deliver2.py --no-push completed successfully: commit b94bb85f5f0
passed the server preflight and per-file compile, with nothing pushed. A final
local read confirmed the only changed existing node fields are lean and the
single added statement dependency; all Lean lines have at most 100 characters.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
