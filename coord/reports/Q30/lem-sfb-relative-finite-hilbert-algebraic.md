## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertAlgebraic` states
`AlgebraicGeometry.RelativeFiniteHilbert.isAlgebraicModuliStack_groupoid`, with its sole
proof `sorry`. No definitions or mathematical proofs are added. The node's statement,
statement dependencies, proof, and proof dependencies are unchanged.

Source read: Stacks `criteria.tex`, lemma-hilbert-stack-relative-space (Tag 06CI),
lines 2399 onward, and `examples-stacks.tex`, construction preceding and definition
of the degree-d finite Hilbert stack (Tag 05WC), lines 1710–1814. The hypotheses
are exactly that X is an algebraic space and F is representable by spaces,
surjective, flat, and locally of finite presentation. The target's diagonal is
not assumed. The module docstring records all six steps of the DAG's proof,
including the derivation of that diagonal and the natural equivalences in the
Weil-restriction and setoid arguments.

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`. Explicit universes `u v₁ w₁ v₂ w₂`
  allow independent sizes for the two total categories and their morphisms.
  Schemes, fields, and algebraic-space presheaf values use the existing site
  universe `u`; the category `Over S` is the recorded big-site category.
- The two categories over S are `X : BasedCategory.{v₁,w₁} (Over S)` and
  `Y : BasedCategory.{v₂,w₂} (Over S)`. The morphism is `F : BasedFunctor X Y`.
- Being fppf stacks (fibred in groupoids, sheaf descent for arrows and effective
  object descent) is `hX : IsFppfModuliStack X` and `hY : IsFppfModuliStack Y`.
  This uses the fppf predicate exported by the relative Hilbert dependency,
  not the étale-only `IsModuliStack` hypothesis.
- Representability of F is `hF : IsRepresentableByAlgebraicSpaces F`.
  `R : ∀ T y, Representative (F := F) T y` fixes the representatives X_y
  already specified by the recorded relative Hilbert definition. A representative
  includes its algebraic space, its actual projection to h_T, and a based
  equivalence to the explicit category of triples, compatible with that projection.
  It is not an arbitrary map or a bijection on isomorphism classes. Fixing the
  representatives is the convention in the dependency and adds no mathematical
  restriction to representability.
- Flatness and local finite presentation of each X_y → T on étale scheme charts
  are exactly `hflat : FlatLfp R`. This expands to `SpaceProperty` for Mathlib
  `Flat` and `LocallyOfFinitePresentation`, with a surjective étale chart of T's
  target and of the pullback source and the actual compatible scheme map.
- X being equivalent over S to an algebraic space is `hspace`: there exist an
  `A : AlgebraicSpace S` and a `BasedFunctor (discreteModuli A.obj.obj) X`
  whose underlying functor is an equivalence. Thus all automorphisms and the
  scheme-base projection are retained.
- Every X_y → T being surjective on field-valued point classes is `hsurj`,
  `∀ T y, AlgebraicSpace.IsJointlySurjective
  (fun _ : Unit ↦ (R T y).projection)`. The singleton index precisely gives
  the node's one-member family. The definition quantifies over every field
  representative and permits a lift after a field extension; it does not
  demand a lift over the original field or scheme representability.
- Every integer d ≥ 1 is encoded by `(d : ℕ+)`; the conclusion is exactly
  `IsAlgebraicModuliStack (groupoid F d hX hY)`. The existing construction retains
  the finite locally free degree-d cover, y, x, α and the specified cartesian
  compatible arrows. `IsAlgebraicModuliStack` means an étale stack, algebraic-space
  diagonal and a representable smooth surjective scheme atlas. There is no
  hypothesis `HasAlgebraicSpaceDiagonal Y` or assumption that Y is algebraic.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`,
  `Scheme.fppfPrecoverage`; the slice topology is `.over S`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `discreteModuli`,
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`,
  `moduliTwoFiberProduct`, `IsModuliStack`, and `HasAlgebraicSpaceDiagonal`.
- `Sheaf.CategoryTheory.SiteStackification` (publicly available through the Hilbert
  dependency): `CategoryTheory.IsFppfModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `AlgebraicGeometry.RelativeFiniteHilbert.groupoid`, `.Representative`,
  `.FlatLfp`, `.SpaceProperty`. The entire source module was read, including the
  actual objects, arrows, projection compatibility and pullback construction.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `.IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`.
- `def-weil-size-convention` is a metatheoretic convention; it has no Lean
  declaration and is rendered by explicit universe levels, not a new definition.

The already-stated proof dependencies are imported with plain `import`:
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`Sheaf.AlgebraicGeometry.SpaceChangeBase`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus`, and
`Sheaf.AlgebraicGeometry.RepresentableSourceAlgebraic`. Their recorded theorem
signatures and docstrings were read. Statement dependencies are public imports.
The following proof-only nodes have no recorded declaration yet, so have no
module to import: `lem-sfb-finite-hilbert-stack-descent`,
`lem-sfb-fppf-space-atlas-bootstrap`,
`lem-sfb-finite-locally-free-weil-restriction`,
`lem-sfb-finite-cover-stack-algebraic`, and
`lem-sfb-representable-pullback-over-space`. They are not needed to type the
statement and are left for their assigned stage-2 work.

Edge cases checked: d = 1 is included, d = 0 is excluded exactly as in the source
construction. No nonemptiness hypothesis is imposed on S, X, Y or test schemes;
the empty scheme and empty fibres remain allowed. The singleton-family condition
allows field extension before lifting. A nonempty fibre cannot be silently replaced
by scheme representability. Arbitrary stack automorphisms remain in Y; no diagonal
assumption or algebraicity of Y was introduced. Positive-degree covers give the
faithfulness argument in the proof plan, including empty bases. Flatness and lfp
are genuine properties of each projection, not identity-map predicates. No
independent smaller universe for test schemes or fields is introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with “The relative finite Hilbert stack of a
  representable flat locally finitely presented surjective morphism from an
  algebraic space is algebraic”: eight hits on scheme flatness, finite
  presentation, finite morphisms and descent; no finite Hilbert stack theorem.
- `msearch.py ... leansearch` with “The finite Hilbert stack of an algebraic space
  mapping flat locally finitely presented and surjectively to a stack is algebraic”:
  eight scheme-morphism finiteness and flatness hits, no matching statement.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.RelativeFiniteHilbert, CategoryTheory.IsAlgebraicModuliStack`:
  zero hits; RelativeFiniteHilbert is not in the Mathlib search index.
- `msearch.py ... grep` with
  `HilbertStack|hilbert_stack|finite.?Hilbert|AlgebraicStack`: only the unrelated
  finite Hilbert basis result in `Mathlib/Analysis/InnerProductSpace/l2Space.lean`.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for
  `relative_finite_hilbert|RelativeFiniteHilbert|lem-sfb-relative-finite-hilbert-algebraic`:
  no upstream result; the project has the recorded construction and an lci
  consumer, but no algebraicity statement. A further concept search over the DAG
  and project did not find an existing equivalent theorem.

Validation: the required `scompile.py Q30 lem-sfb-relative-finite-hilbert-algebraic`
compiled this module in both sandbox and library contexts in 3.2 seconds each,
without errors or non-sorry warnings. Every universe and variable is explicitly
bound and `autoImplicit` is false. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

## Second reading by Q30

This dispatcher assignment requires direct delivery and forbids starting other
agents; the maintainer performs the independent review. This section records an
additional self-check, not a claim of an independent second worker.

Re-read the node and final signature together: the fppf hypotheses are hX/hY,
representability is hF with its fixed compatible representatives R, the two local
properties are FlatLfp R, source algebraic-space equivalence is hspace, the
singleton point-surjectivity predicate is hsurj, and the sole conclusion is
algebraicity of the existing degree-d groupoid for every positive d. The signature
adds no target diagonal or smoothness assumption, does not replace groupoids by
classes, and has no theorem conclusion beyond the node's. No mismatch or correction
was found. The natural-language proof contains all six DAG steps and names each
required proof prerequisite, including those not yet stated in Lean.
