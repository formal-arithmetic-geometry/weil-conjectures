## Worker report

The module `Sheaf.AlgebraicGeometry.SplitTorusTorsorLinePullback` states
`AlgebraicGeometry.split_torus_torsor_line_pullback`. Its sole theorem has proof
`sorry`; there are no new definitions or auxiliary postponed theorems. The natural-language
statement, proof and proof dependencies are unchanged.

Hypotheses and clauses, read against the node:

- The field is `{k : Type u} [Field k]`. Mathlib's `Field` extends a commutative ring
  and division ring, including nontriviality.
- The k-scheme is `X : Over (Spec (.of k))`. Smoothness is `[Smooth X.hom]`;
  separatedness is `[IsSeparated X.hom]`, whose defining field says its diagonal
  is a closed immersion. Finite type is the recorded conjunction, expressed by
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- The nonnegative rank is `r : ℕ`. The torus is the existing
  `MultiplicativeType.splitTorus k r`. Its recursive definition is the finite
  product of `Grp.mk (StandardGroupSchemes.multiplicative k)`, with the terminal
  group in rank zero. The latter multiplicative scheme is `Spec` of
  `LaurentPolynomial k`, with the Laurent Hopf multiplication, identity and inverse.
- `P : RepresentedRightTorsor (MultiplicativeType.splitTorus k r) X` is exactly
  the scheme Y, its projection q and its right action from the node. Explicitly,
  `P.space.left` is Y and `P.projection.left` is q. `projection` is a morphism
  over k. The record fields `flat` and `surjective` give faithful flatness;
  `lfp`, `qc`, `qs` give finite presentation (locally finite presentation,
  quasi-compactness, quasi-separatedness), not merely local finite presentation.
- Its `action : space ⊗ H.X ⟶ space` is the morphism Y ×_k T -> Y.
  `one_action` and `mul_action` are the right-action laws on every test k-scheme.
  `torsor : IsPullback (fst space H.X) action projection projection` both makes
  the action over X (commutativity) and says that (y,t) -> (y,yt) is the canonical
  isomorphism Y ×_k T -> Y ×_X Y. The categorical cartesian square is equivalent
  to the node's isomorphism, preserving both specified projections; it does not
  assert only an unrelated isomorphism of these schemes.
- The arbitrary invertible module is `(L : P.space.left.Modules) [L.IsInvertible]`,
  using the recorded locally-trivial-rank-one module class.
- The conclusion is `∃ N : X.left.Modules, N.IsInvertible ∧ Nonempty
  (L ≅ (Scheme.Modules.tensorPullback P.projection.left).obj N)`.
  It supplies an actual invertible module on X and an isomorphism to its tensor
  inverse image; `Nonempty` only turns the type of isomorphisms into a proposition.
  The existing `tensorPullbackObj` constructs O_Y tensor over q⁻¹O_X with q⁻¹N
  by inverse image and change of rings. There is no uniqueness or injectivity clause.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (available through the geometric imports).
- `AlgebraicGeometry.Scheme` and its morphisms, `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, the recorded
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` interface and its QuasiCompact import.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; the represented torsor
  uses the equivalent `CategoryTheory.IsPullback` universal property in `Over`.
- `AlgebraicGeometry.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.Flat` (its docstring
  and `Flat.iff_flat_stalkMap` identify affine-local flatness with stalkwise flatness).
- `AlgebraicGeometry.Surjective`, `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, via the recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly importing
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. The latter defines the actual
  tensor inverse image; the former supplies its normalized adjunction.
- `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- Two already-landed definition nodes are added to `stmt_deps`:
  `def-sfb-tori-multiplicative-type` supplies `MultiplicativeType.splitTorus` from
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`;
  `def-sfb-split-solvable-right-torsors` supplies `RepresentedRightTorsor` from
  `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`.
  These are reused, with neither a private copy nor a new node. The torsor
  definition is general for arbitrary groups; using it does not assume split
  solvability beyond the explicit chosen split torus.

The proof dependencies already carrying Lean records are plain imports:
`Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`,
`WeilConjectures.AlgebraicGeometry.ModulePullbackTensor` and
`WeilConjectures.AlgebraicGeometry.TensorPullback`. Their theorem signatures and
proof docstrings were read. The two remaining proof dependencies,
`lem-sfb-invertible-extension-factorial-complement` and
`lem-sfb-projective-bundle-picard-classification`, have no Lean record in the read
repository and therefore no import is available. Neither is needed to type this
statement; both remain in `proof_deps` and in its four-step proof docstring.

Sources: read `literature/stacks-project/divisors.tex`,
`lemma-extend-invertible-module` (Tag 0BD9), including its proof and lack of a
Noetherian-global or density hypothesis. Read EGA II Remark 4.2.7, printed p.75
(PDF page 72), for the projective-bundle Picard formula. The formula there is
stated for connected locally Noetherian bases: here the smooth finite-type bases
are Noetherian, and one applies it on their open connected components, allowing
locally constant integer degrees. This is an extracted consequence, not a claim
that Tag 0BD9 alone proves the theorem.

Edge cases checked before writing:

- Rank zero: the terminal group torsor is an isomorphism, so every line descends;
  `r : ℕ` includes zero and the existing split-torus definition uses the empty product.
- Empty base: a scheme mapping to the empty scheme is empty. No nonemptiness is
  imposed on either X or P. The unique empty-scheme module case remains included.
- Disconnected base: no connectedness or integrality binder is present. The proof
  allows the projective degree to vary over connected components.
- Arbitrary characteristic and imperfect fields: there is no algebraic-closedness,
  perfectness, characteristic-zero or separability hypothesis; smoothness suffices
  for the regular local rings used in the proof.
- Nontrivial torsor: no global section or trivialization is supplied. For example,
  pulling the defining line to its frame torsor trivializes it, so injectivity would
  fail in general; our conclusion asserts only existence.
- Universes: k and all underlying schemes use the existing common scheme universe u.
  Tests in the torsor definition are all `Over (Spec k)` schemes in that universe,
  including the torsor and the product objects themselves, so the action laws and
  cartesian square are not a small or vacuous field-points test.

Searches performed for an existing exact statement:

- `msearch.py ... leanfinder "Every invertible module on a split torus torsor over
  a smooth separated finite type scheme over a field is pulled back from the base"`:
  8 hits, consisting of affine-space declarations and `CommRing.Pic.mk_eq_one`.
  Reading their returned types gives no matching scheme-torsor line-pullback theorem.
- `msearch.py ... loogle '"IsInvertible", "tensorPullback"'`: 0 hits.
- `msearch.py ... grep
  '([Tt]orsor.*[Pp]ic|[Pp]ic.*[Tt]orsor|[Ii]nvertible.*[Tt]orus|split_torus.*pullback)'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg -n 'split.torus|SplitTorus|torusTorsor|TorusTorsor'` in the project's Sheaf
  and WeilConjectures algebraic-geometry directories found frame geometry,
  character pushouts and the rational-surjectivity consumer, but no exact theorem.
  The latter explicitly cites this missing lemma and only gives a positive power
  for general tori, so it is not the same statement.
- `rg -l 'lem-sfb-split-torus-torsor-line-pullback' lean/WeilConjectures` gave no
  hits. DAG searches for torus and torsor notions identified the two landed
  definition nodes used above. No missing notion needs a new definition node.

No statement dispute, statement correction, unusable dependency interface or hollow
construction was found. Validation is through the prescribed server `scompile.py`
and `deliver2.py` dry run; expected `sorry` warnings are the only permitted warnings.

## Second reading by Q06

No independent second worker was started: the dispatcher's instruction prohibits
starting agents, and deliveries receive the maintainer's independent review.
A self-rereading checked the full node against the signature and the reused torsor
record: every base hypothesis, both action laws, finite presentation (including qc/qs),
faithful flatness, the specified torsor square, arbitrary invertible L, invertible N
and the exact tensor pullback occur. No global section, geometric integrality,
connectedness, nonemptiness or uniqueness was added. The only DAG edits are the
Lean attachment and the two already-landed notion dependencies. No mismatch required
a statement correction.
