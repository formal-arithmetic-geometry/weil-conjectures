## Worker report

The module `Sheaf.LinearAlgebra.RootSystem.AdjacentRootLengthRatio` states
`RootPairing.adjacent_root_length_ratio` with `sorry`. No definition, auxiliary theorem,
or proof was added. The node is unchanged except for its `lean` record.

Source read: Milne, Algebraic Groups (2017), Appendix C.19–C.20, printed p. 611
(PDF p. 623), and Section g, printed pp. 621–622 (PDF pp. 633–634), table (180)
and the four rank-two root diagrams. These are the source of the agent-formulated
identity, rather than a verbatim theorem of Milne. C.20 supplies the invariant-form
formula; the node's five-step algebraic proof is included in the declaration docstring.

Hypothesis and conclusion correspondence:

- The finite index set is `{I : Type u} [Finite I]`, with an arbitrary explicit universe.
- The rational vector spaces are `{V : Type v} [AddCommGroup V] [Module ℚ V]` and
  `{W : Type w} [AddCommGroup W] [Module ℚ W]`. Their universes are independent.
  The dependency `def-weil-field` is Mathlib's `Field`, read in
  `Mathlib.Algebra.Field.Defs`; the coefficient field is the actual `ℚ`.
- The stated root pairing is `(P : RootPairing I ℚ V W)`. Its definition at
  `Mathlib/LinearAlgebra/RootSystem/Defs.lean:82` bundles the two injective families,
  perfect bilinear pairing, value 2, and simultaneous reflection permutations.
- Integral root-coroot evaluations are `[P.IsCrystallographic]`, the abbreviation
  for `P.IsValuedIn ℤ` in `Mathlib.LinearAlgebra.RootSystem.IsValuedIn:60`.
- Reducedness is `[P.IsReduced]`; the class in
  `Mathlib.LinearAlgebra.RootSystem.Reduced:50` says a dependent pair of roots is
  equal or opposite, exactly the stated proportional-root condition over ℚ.
- The form is `(b : LinearMap.BilinForm ℚ V)`. Symmetry is `(hsymm : b.IsSymm)`.
  The signature retains full positivity as
  `(hpos : ∀ x : V, x ≠ 0 → 0 < b x x)`, including vectors outside the root span.
- Reflection invariance is `(hinv : ∀ l : I, b.IsOrthogonal (P.reflection l))`.
  `LinearMap.IsOrthogonal` in `Mathlib.LinearAlgebra.SesquilinearForm.Basic:437`
  means `∀ x y, b (s x) (s y) = b x y`. The reflection formula in
  `RootPairing.reflection_apply` (`Defs.lean:238`) is precisely
  `x - P.coroot' l x • P.root l`, with `coroot'` the original pairing evaluation.
- The indices are `(i j k : I)`. Their independence is
  `(hij : LinearIndependent ℚ ![P.root i, P.root j])` and the adjacent-root condition
  is `(hk : P.root k = P.root i + P.root j)`.
- The endpoint names p and q are expanded directly into `P.chainBotCoeff i j` and
  `P.chainTopCoeff i j`. Their definitions in `Mathlib.LinearAlgebra.RootSystem.Chain`
  at lines 115 and 125, and endpoint characterizations at lines 137–164, agree with
  the node: bottom measures subtraction and top measures addition.
- The sole conclusion is
  `(P.chainTopCoeff i j : ℚ) * b (P.root k) (P.root k) =
  ((P.chainBotCoeff i j : ℚ) + 1) * b (P.root j) (P.root j)`.
  The casts make this the equality in ℚ requested by the node. No endpoint bound,
  integrality conclusion, or extra root-system spanning hypothesis was added.

All dependency interfaces were read in full. The three proof dependencies are
Mathlib leaves from `Mathlib.LinearAlgebra.RootSystem.Chain`, already publicly
imported for the coefficients:
`RootPairing.chainBotCoeff_sub_chainTopCoeff` (line 405),
`RootPairing.root_add_zsmul_mem_range_iff` (line 186), and
`RootPairing.chainBotCoeff_add_chainTopCoeff_le_three` (line 475).
Their finite-index, crystallographic, independent-root, and reducedness hypotheses
are available exactly where the node's proof uses them. No dependency module is needed.

Edge cases checked before writing: no `Nonempty I`, finite-dimensionality, or spanning
assumption is imposed. Empty I and rank-one systems admit no independent indexed pair,
so the implication remains vacuous without excluding them. The zero vector is excluded
only in the positivity premise; roots are nonzero by their coroot evaluation being 2.
A2 has (p,q)=(0,1) and equal adjacent lengths. The simple short-root strings in B2
and G2 have (0,2) and (0,3), respectively, with the next root's squared length 1/2
and 1/3 of the starting long root's; both satisfy the displayed identity. Internal
positions give (1,1), (1,2), and (2,1), as in the proof. The independent-root premise
avoids the junk-value cases of Mathlib's coefficients, and hk forces q≥1. The form
may be on a larger ambient space; no positivity restriction was silently weakened
to positivity on roots. No statement dispute or correction was found.

Searches actually run with `msearch.py Q37 lem-sfb-root-string-adjacent-length-ratio`:

- LeanFinder: “For adjacent roots beta and alpha plus beta in an alpha string with
  endpoints minus p and q, q times squared length alpha plus beta equals p plus one
  times squared length beta”. Eight results include
  `RootPairing.chainBotCoeff_mul_chainTopCoeff`, embedded G2 identities, and a canonical
  form identity. Read the product lemma's full signature in GeckConstruction/Lemmas.lean:
  it concerns five indices and a product of endpoint coefficients, not this equality.
  The G2 identities concern particular distinguished roots, not arbitrary adjacent roots.
- Loogle: `RootPairing.chainBotCoeff, RootPairing.chainTopCoeff`. Twelve results give
  endpoint bounds, reflection formulas, shifts, and the endpoint difference; no form ratio.
- Mathlib grep via msearch: `chain.*(rootForm|length|form)|rootForm.*chain|adjacent.*length`
  in `LinearAlgebra/RootSystem`. Two hits, both in the introductory Chain.lean docstring;
  neither is a declaration of the identity.
- LeanSearch: “Root string adjacent roots invariant positive bilinear form squared length
  ratio endpoint coefficients”. Eight results include `InvariantForm.apply_eq_or`,
  `posRootForm`, and `RootPositiveForm.rootLength`; none states this endpoint identity.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `root.string|chainTopCoeff|adjacent.*length`, and for the item id, found existing
  Chevalley root-string statements but no adjacent-root length identity. Searches for
  `adjacent_root_length_ratio` across Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no declaration collision. The id search in
  `lean/WeilConjectures` found no upstream statement of this node.
- Read `RootPairing.InvariantForm` and `RootPairing.RootPositiveForm` in RootPositive.lean.
  The former bundles nonzero root lengths and the latter positivity on roots; neither
  alone expresses the node's full positivity on every nonzero vector, so the statement
  uses the existing bilinear-form predicates and the explicit full positivity premise.

Validation: scompile.py compiled both its sandbox module and the actual library module
cleanly, with no errors or unexpected warnings (4.1 s and 1.2 s).

## Second reading by Q37

This is the author's final self-check; the dispatcher requires no sub-agents and the
maintainer supplies the independent review. Re-read the node and delivered signature:
finite index and independent ambient universes are explicit; ℚ is unchanged; the pairing
bundles exactly the stipulated data; crystallographic and reduced mixins are present;
b is genuinely bilinear, symmetric, positive on all nonzero vectors, and reflection
invariant on all vectors. The indices, ordered independent pair, and sum equality agree
with the node. Checked the bottom/subtraction and top/addition convention against the
actual coefficient definitions rather than the swapped p/q letters in introductory
comments. Checked that multiplication and the plus-one factor are both interpreted in ℚ.
There is exactly one conclusion and every theorem proof is the whole `sorry`.
No mismatch was found, no correction was needed, and no dependency record was changed.
