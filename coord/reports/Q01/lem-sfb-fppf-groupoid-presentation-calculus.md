## Worker report

The module `Sheaf.AlgebraicGeometry.FppfGroupoidPresentationBaseChange` states
`CategoryTheory.fppf_groupoid_presentation_baseChange`, with its entire proof `sorry`.
No definitions, helper theorems, new nodes, dependency repairs, or statement corrections
are introduced. The source is Stacks 0DTG, `groupoids-quotients.tex`,
`lemma-base-change-quotient-stack`, read through its proof. The enclosing current blueprint
is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.

The conclusion expresses the equivalence by showing that the actual 2-fibre product
is a quotient presentation of the base-changed groupoid, with its specified chart and
arrow map. This is the existing library's characterization of the fppf stackification
up to equivalence. It does not replace the quotient by its orbit sheaf, choose a
stackification from a mere existence theorem, or assume that base-changed spaces are
schemes. In particular the original nontrivial automorphisms survive the arrow clause.

Hypotheses and clauses:

- The field is `(k : Type u) [Field k]`; the base is `Spec (.of k)`.
  `U R : Over (Spec (.of k))` are the original schemes P and Q over that base.
- The groupoid structure maps are `s t e i c`, with `c` defined on the actual
  scheme pullback. `hF.groupoid : Scheme.IsGroupoid ...` is the exact recorded
  `def-a1-scheme-groupoid-laws` predicate. The quotient presentation bundles this
  necessary groupoid hypothesis, so it is not redundantly repeated.
- `[s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]` are exactly finite
  local freeness of source and target, with no degree condition or surjectivity.
- `F`, `aF`, and `hF : SchemeGroupoidQuotientPresentation ...` bind an arbitrary
  realization of `[P/Q]` and its chart. They specify the quotient named in the node,
  rather than add a geometric restriction: this interface characterizes precisely
  the fppf stackification, with its original arrows and composition.
- `B : AlgebraicSpace ...`, `a : yoneda.obj U ⟶ B.obj.obj`, and
  `ha : yoneda.map s ≫ a = yoneda.map t ≫ a` are exactly the invariant map P → B.
- The existential `f` is its extension to the quotient. Its vertical 2-isomorphism
  `aF.comp f ≅ discreteModuliMap a` specifies it on the original groupoid chart.
  Uniqueness follows locally from the presentation and the sheaf property of B;
  the theorem does not posit an unrelated map.
- `B'` and `g` are an arbitrary algebraic space and arbitrary map to B. There is
  no flatness, finiteness, smoothness, etaleness, or scheme condition on this map.
- `U' R'`, `p b q d`, and the two `IsPullback` bind arbitrary realizations of
  P ×_B B' and Q ×_B B', with Q → B equal to `yoneda.map s ≫ a`.
  They introduce the actual base-change objects rather than impose a new condition:
  algebraic-space fibre products exist, and any realization is allowed. Presheaf
  pullbacks of their fppf sheaves are the same fibre products.
- `s' ≫ p = q ≫ yoneda.map s`, the analogous target equality, and `s' ≫ b = d`,
  `t' ≫ b = d` specify both coordinates of the source and target.
- The test-scheme equalities for `e'` and `i'` specify the original identity and
  inverse on the first coordinate, while `e' ≫ d = b` and `i' ≫ d = d` specify
  their second coordinate. These are pointwise formulas, avoiding an unjustified
  assumption that the base-changed objects are schemes.
- The equality for `c' ≫ d` fixes the second coordinate of composition. Its
  test-scheme clause fixes the first coordinate using the original scheme `c`
  and the uniquely induced map `z₀` from the scheme pullback universal property.
  The first factor is the later arrow, matching the recorded original convention.
- `h' : SpaceGroupoidQuotientPresentation ... (moduliTwoFiberProduct f
  (discreteModuliMap g)) a'` asserts that this very product stack is the fppf
  quotient of the specified base-changed groupoid, including all groupoid laws,
  fppf descent, unique original arrows between chart objects, local object lifts,
  and compatibility with the specified composition.
- `ε` identifies the first projection of `a'` with the original chart after p.
  The following quantified arrow equality identifies the image of every R'-arrow,
  after conjugation by ε, with the original Q-arrow under q. Endpoint proofs are
  kept in the displayed subtypes, exactly as in the existing presentation API.
- The final `ModuliTwoIso` identifies the second projection with b. Thus both
  legs and the arrow map of the canonical comparison are retained. This quotient
  presentation of the actual product is exactly the claimed base-change equivalence.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.Algebra.Field.Defs`: `Field` (the field node is a Mathlib leaf, with no lean record).
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `AlgebraicGeometry.Scheme.IsGroupoid`,
  used as `hF.groupoid` by the quotient-presentation structure.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (finite, flat, lfp).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, with `.over` for
  the big slice site used in both quotient-presentation interfaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its underlying fppf sheaf/presheaf; morphisms are natural transformations.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
  Their full definitions and docstrings were read. The actual vertical iso-comma
  category is used, without passing to isomorphism classes.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: the recorded algebraic-stack
  definitions were read and the module is publicly imported. The node's introductory
  representability/property conventions add no separate hypothesis to this theorem.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`, read with its full
  signature and publicly imported as the recorded statement dependency.
- Existing landed definition nodes added to stmt_deps:
  `def-sfb-scheme-groupoid-quotient-presentation`, module
  `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`, declarations
  `SchemeGroupoidQuotientPresentation`, `schemeGroupoidPresentationArrow`;
  `def-sfb-space-groupoid-quotient-presentation`, module
  `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`, declarations
  `SpaceGroupoidQuotientPresentation`, `spaceGroupoidPresentationArrow`;
  `def-sfb-open-moduli-substack`, module `Sheaf.AlgebraicGeometry.OpenModuliSubstack`,
  declaration `moduliTwoFiberSnd` and its projection equality theorem.
  These nodes already own the exact interfaces; no duplicate is introduced.
- Proof dependency `def-trf-scheme-algebraic-space` is supplied by the private import
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (`schemeSpace` and its property
  theorem were read). The other proof dependency,
  `lem-sfb-quotient-stack-invariant-base-change`, currently has no lean record or
  module, and is not imported. It is not needed to type the statement; its mathematical
  application is recorded in the proof docstring for stage 3.

Edge cases checked mathematically: g = identity gives the original presentation;
B' empty gives the empty groupoid and empty stack, including the empty-cover descent
condition; the identity groupoid Q = P gives ordinary sheaf fibre-product formation;
a finite constant stabilizer with nontrivial automorphisms retains those automorphisms
through hF/h' and the explicit arrow compatibility. Nonflat g is allowed. The theorem
uses no quotient as a set of orbits and assumes no freeness of the groupoid. No connectedness,
nonemptiness, characteristic, or degree restriction is inserted. F's morphism and object
universes v and w are independent of u; the product has their required maxima with
those of the discrete algebraic-space category. No extra universe equality is imposed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "The fppf quotient stack of a groupoid commutes with
  base change along an invariant map"`: eight hits, on scheme-module pseudofunctor
  coherence and existing-stack descent, not this statement.
- `msearch.py ... leansearch "Quotient stack of a groupoid commutes with invariant
  base change"`: eight hits, representation invariants and ordinary morphism-property
  stability; no match.
- `msearch.py ... loogle '"Stack", "pullback"'`: zero hits.
- `msearch.py ... grep 'quotient.stack|stackification|fppf.*groupoid'`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` for quotient-stack, stackification, and fppf-groupoid
  terminology, and for the item id: no exact statement. Broader quotient/base-change
  queries find ring quotients and sheaf coefficients, not quotient stacks.
- `rg` over `lean/Sheaf` found the already landed scheme and algebraic-space quotient
  presentation interfaces, which are reused. No invariant-base-change theorem was found.
- `rg` over Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` for
  `fppf_groupoid_presentation_baseChange`: no existing declaration with this name.

Validation: the module compiles both in the private sandbox and with its library module
name through the prescribed `scompile.py` (16.8 s / 18.0 s), with no compiler messages.
The first probe exposed a dependent-source mismatch in an objectwise second-coordinate
formula; this was replaced by the existing `moduliTwoFiberSnd` and a vertical 2-isomorphism.
The final file includes no probe commands. No STATEMENT-DISPUTED issue was found.

## Second reading by Q01

Self-review of the node and final file, without spawning another agent (as required by
the dispatcher's instruction). The maintainer supplies the independent review.
The field, finite local freeness, invariance and arbitrary algebraic-space base change
are retained. The quotient and its arrow map use the recorded presentation structures.
The initial draft constrained only the atlas objects; rereading showed that this did
not pin down the original arrow identification under the first projection. Added the
explicit conjugation equality for every R'-arrow and the selected presentation `h'`.
Both coordinates of every groupoid operation, and both product projections, now appear.
The presheaf-pullback hypotheses specify the base-change construction and do not restrict
g. The product itself being a quotient presentation is the claimed equivalence in the
existing interface, without a second arbitrary choice of stackification data.
