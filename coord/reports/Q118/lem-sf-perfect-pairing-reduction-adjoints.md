## Worker report

Stage 2, Q118, 2026-10-22. The delivery defines the specified isomorphism
`CategoryTheory.perfectPairingDualComparison` and states
`CategoryTheory.perfectPairing_reduction_adjoints` in
`Sheaf.CategoryTheory.PerfectPairingReductionAdjoints`. The definition has real data;
the theorem has exactly one `sorry`. The node changes only in `lean`. There are no
new nodes, dependency repairs, statement corrections, or disputed statements.

The previous attempt confused the Q148 stage-1 split with a Lean statement already
being present. I read Q148's report and the node's independent review: they explicitly
say no Lean was written. The live node has no `lean` field. This delivery supplies it.
There is no repair note for this item.

I read the entire item statement and six proof steps, both statement-dependency nodes
and their Mathlib source declarations and docstrings, the uncurrying proof-dependency
node and all three of its matched Mathlib signatures, and the current blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-finite-reduction.proof.md`.
The final paragraph takes adjoints of the commuting pairing square, deduces that the
second-variable comparison is invertible, and then inverts the horizontal adjoints.
The theorem docstring records all six steps, including each named DAG ingredient.

Hypothesis and clause correspondence:

- The categories are `𝒞 : Type u₁`, `𝒟 : Type u₂` with independent hom universes
  `Category.{v₁}`, `Category.{v₂}` and `MonoidalCategory` instances. No symmetry,
  braiding, zero object, additivity, rigidity, or linearity is required.
- Chosen internal Homs and the natural tensor-Hom adjunctions are the two
  `MonoidalClosed` instances. Mathlib's `Closed` stores the chosen right-adjoint
  functor and adjunction, rather than just their existence. The dual of `U` is
  `(ihom U).obj (𝟙_ _)`; evaluation is `(ihom.ev U).app (𝟙_ _)`.
- The strong monoidal functor is `F : 𝒞 ⥤ 𝒟` with `m : F.CoreMonoidal`.
  The specified unit constraint is `m.εIso`, and the tensor constraints are
  `m.μIso`. Thus the formulas retain the chosen forward tensorator and inverse
  unit map instead of silently treating the functor as strict monoidal.
- The four objects are `{C D : 𝒞}`, `{C' D' : 𝒟}`. The two pairings are
  `β : C ⊗ D ⟶ 𝟙_ 𝒞`, `β' : C' ⊗ D' ⟶ 𝟙_ 𝒟`. The first comparison is
  `c : F.obj C ≅ C'`; the second is only `r : F.obj D ⟶ D'`.
- The invertible adjoints are `b : D ≅ (ihom C).obj (𝟙_ 𝒞)` and
  `b' : D' ≅ (ihom C').obj (𝟙_ 𝒟)`, with
  `hb : b.hom = MonoidalClosed.curry β` and the analogous `hb'`. These equality
  binders identify the named isomorphisms with the actual adjoints. They are a
  presentation of exactly the assumption that those adjoints are isomorphisms:
  an invertible curry supplies such an isomorphism, and conversely these binders
  imply curry is invertible. No arbitrary comparison or independent adjoint is used.
- `h` has precisely the specified source `F(C dual)` and target `(FC) dual`.
  `heval` is the assumed evaluation normalization, written in Lean's forward
  composition order: `(FC ◁ h.hom) ≫ ev_FC = μ ≫ F.map ev_C ≫ u.inv`.
- `hpair` is the pairing-square hypothesis
  `(c.hom ⊗ₘ r) ≫ β' = μ ≫ F.map β ≫ u.inv`.
- The definition of `ell` is `perfectPairingDualComparison F c h`. Its data is
  `h ≪≫ ((MonoidalClosed.internalHom (C := 𝒟)).mapIso c.symm.op).app (𝟙_ 𝒟)`.
  Mathlib's `Iso.op` reverses the endpoints; `c.symm.op` therefore goes from
  `op (F C)` to `op C'`, and `internalHom.map` is precomposition by its unop,
  namely `c.inv`. The resulting forward map is definitionally
  `h.hom ≫ (MonoidalClosed.pre c.inv).app (𝟙_ 𝒟)`.
  Its inverse is built by the isomorphism constructors, not chosen by existence.
- The first conjunct is the required evaluation equation for `c` and `ell`,
  with the same `μ` and `u.inv` as `heval`.
- The second conjunct is the adjoint square:
  `r ≫ b'.hom = F.map b.hom ≫ ell.hom`.
- The third conjunct is the inverse-adjoint square:
  `F.map b.inv ≫ r = ell.hom ≫ b'.inv`.
- The fourth conjunct is the displayed formula for `r`:
  `r = F.map b.hom ≫ ell.hom ≫ b'.inv`.
- The final conjunct is `∃ rIso : F.obj D ≅ D', rIso.hom = r ∧
  rIso.inv = b'.hom ≫ ell.inv ≫ F.map b.inv`. This states invertibility of the
  specified map `r`, together with exactly its stated inverse. The `Iso` fields
  enforce both inverse identities. This is an equivalent formulation of the
  node's last clause, not an invertibility hypothesis on `r`.

Dependencies and existing constructions used:

- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`, including tensor bifunctor laws.
- `def-sfb-strong-monoidal-functor`: `CategoryTheory.Functor.CoreMonoidal`,
  `Mathlib.CategoryTheory.Monoidal.Functor`, including naturality and coherence.
- `lem-pod-closed-uncurry-laws`: `CategoryTheory.MonoidalClosed.uncurry_curry`,
  `uncurry_natural_left`, `uncurry_eq` in
  `Mathlib.CategoryTheory.Monoidal.Closed.Basic`.
- The same closed module supplies `MonoidalClosed`, `ihom`, `ihom.ev`, `curry`,
  `pre`, and `internalHom`. Ordinary `Functor.mapIso`, `Iso.app`, `Iso.op`, and
  isomorphism composition supply the data for `ell`. The one public import of
  the closed module exposes all statement and proof dependency modules.

Edge cases checked before writing:

- Identity functor and identity comparisons reduce to the ordinary adjoint and
  inverse-adjoint equalities.
- A change of basis `c` in finite-dimensional vector spaces makes `ell` the
  inverse transpose composed with `h`; this checks the essential inverse variance.
- Multiplying `β` and `β'` by invertible scalars changes the two adjoints; the
  formula for `r` retains these factors and the inverse formula cancels them.
- Zero-dimensional vector spaces and zero pairings on zero objects are included;
  no nonzero or dimension condition is imposed. On nonzero spaces a zero pairing
  fails the explicit adjoint-isomorphism assumption, as it should.
- Non-symmetric closed categories are allowed: no tensor factors are exchanged.
  The object and hom universes of the two categories are independent.
- An arbitrary noninvertible candidate `r` can be passed to the hypotheses; if
  the pairing square and the two invertible-adjoint hypotheses hold, the final
  clause forces it to be invertible, rather than excluding it in a binder.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: "A strong monoidal functor transports adjoints of perfect pairings
  through an evaluation compatible dual isomorphism, and a pairing preserving
  map is an isomorphism". Eight hits: `exactPairingOfFaithful`,
  `ExactPairing.ofFaithful`, `exactPairingOfFullyFaithful`, `leftDualIso`,
  `ExactPairing.ofFullyFaithful`, `rightDualIso`, `exactPairingCongrRight`,
  `exactPairingCongrLeft`. These concern rigid exact pairings, with additional
  coevaluations or faithful functors; none is this closed-category statement.
- Loogle: `CategoryTheory.ihom.pre, CategoryTheory.MonoidalClosed.curry` initially
  returned zero hits because `ihom.pre` is not the declaration's namespace.
  Corrected query `CategoryTheory.MonoidalClosed.pre` returned twelve hits,
  including `pre`, `pre_id`, `pre_map`, `internalHom_map`, and evaluation/uncurry
  formulas; these give the existing precomposition construction used here.
- Mathlib grep: `perfect.*[Pp]air|[Pp]air.*perfect|pre_app.*ev` restricted to
  `CategoryTheory/Monoidal` returned the two evaluation-precomposition occurrences
  in `Closed/Basic.lean`; no full comparison theorem.
- LeanSearch: "An evaluation compatible dual comparison for a strong monoidal
  functor transports perfect pairing adjoints and their inverses". Eight hits
  including `Functor.Monoidal.ofBifunctor`, rigid tensor adjunctions and evaluation
  mates, and `LinearMap.IsPerfPair.dualEval`; none states the requested comparison.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` found no occurrence of the
  item tag or proposed declaration names. Concept searches in their category
  theory trees found specialized cup/internal-module comparisons and upstream
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`. I read that
  upstream module: it supplies the general ihom comparison and the perfect-pairing
  predicate, but not this theorem for arbitrary normalized `h` and arbitrary `r`.
  No duplicate notion has been introduced; adjoints are stated directly using
  the existing `curry`, and `ell` is the composite expressly defined by this node.

Validation: `scompile.py Q118 lem-sf-perfect-pairing-reduction-adjoints` compiled the
single delivered module in both sandbox and library-name contexts successfully,
with no errors or unexpected warnings. Every universe and variable is explicitly
bound. No `let`, local notation, local instance, opaque data, or private definition
occurs in the statement module.

## Second reading by Q118

I reread the node and completed module together after compilation. This is a
single-worker consistency check, not an independent-worker review: the dispatcher's
instructions forbid starting another agent and provide for the maintainer's
independent delivery review. I checked every hypothesis and clause against the
correspondence above. In particular I opened the actual `Iso.op` and `internalHom`
definitions: the choice must be `c.symm.op`, not `c.op`. I checked both directions
of the inverse formula by their endpoints: `D' → dual(C') → F(dual C) → FD`.
The formulas in Lean use forward composition, so the square for inverses is
`F.map b.inv ≫ r = ell.hom ≫ b'.inv`. The proof-dependent Mathlib uncurrying
module is already the direct public import. No mismatch or statement correction
was needed; the item is separate from Q148's stage-1 split.
