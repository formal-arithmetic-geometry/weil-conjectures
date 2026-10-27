## Worker report

The new module `Sheaf.AlgebraicGeometry.AlgebraicStackQcqsPermanence` states
`CategoryTheory.algebraicStack_qcqs_permanence`, with `sorry` as its sole proof.
No definitions or auxiliary theorems are introduced. The node statement and accepted
proof split are unchanged. Its `stmt_deps` gains the already landed
`def-sfb-relative-moduli-inertia`, whose recorded `moduliBaseStructure` is used directly.

Source read: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-quasi-compact-quasi-separated-permanence`, Tag 075S, clause (2), lines 1855–1875;
`definition-separated`, Tag 04YW, clause (4), lines 388–421. These state precisely the
qcqs permanence assertion and the qcqs-diagonal definition. The accepted three-step
DAG argument is included in the theorem docstring, including the graph square and
transport back from the absolute base. None of the five additional theorem proof
dependencies has a Lean record or Mathlib match in the inspected DAG, so there is no
module for those to import. The already stated definition proof dependencies are
available through the public statement imports.

Hypothesis and clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, with no separation, finiteness, or nonemptiness
  assumption on S.
- Universes: `universe u v₁ w₁ v₂ w₂ v₃ w₃`; X and Y have independent morphism/object
  levels `BasedCategory.{v₁, w₁}` and `BasedCategory.{v₂, w₂}`. The concluding
  `IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₃, w₃}` retains arbitrary
  enlargement of the test-stack universe, exactly as in the recorded definition.
- Algebraic stacks over S: `hX : IsAlgebraicModuliStack X` and
  `hY : IsAlgebraicModuliStack Y` for based categories over `Over S`.
- A morphism over S: `(f : BasedFunctor X Y)`, using its actual base compatibility.
- X quasi-compact: `hXqc : IsQuasiCompactModuli X`, the recorded existential smooth
  surjective atlas by a quasi-compact scheme; no atlas is fixed as input.
- X absolutely quasi-separated: `hXqs` applies
  `IsQuasiSeparatedAlgebraicModuliMap` to
  `moduliBaseStructure (BasedCategory.ofFunctor
  (X.p ⋙ Over.map (specULiftZIsTerminal.from S)))`.
  Mathlib's `specULiftZIsTerminal` has target `Spec (.of (ULift.{u} ℤ))`.
  `Over.map` sends `T → S` to `T → S → Spec ℤ` and leaves its underlying scheme
  and morphisms intact. Composing X's projection therefore regards its actual total
  category as a category over schemes over Spec ℤ. This is the canonical absolute
  stack, not the relative diagonal over S. `moduliBaseStructure` is its projection
  to the identity based category of `Over (Spec ℤ)` (the represented base scheme).
  The relative diagonal of that structural functor is precisely X's absolute
  diagonal up to the canonical equivalence of the identity based category with
  the discrete representable. The recorded quasi-separatedness predicate says its
  scheme-base-change algebraic-space projections are both quasi-compact and
  quasi-separated, including representability of that diagonal.
- Y absolutely quasi-separated: `hYqs` is the identical construction with Y, with
  no quasi-compactness requirement on Y.
- f quasi-compact: the first conjunct is the recorded
  `IsQuasiCompactAlgebraicModuliMap ... f`, testing actual 2-fibre products at every
  quasi-compact algebraic stack in the chosen enlarged bound.
- f quasi-separated: the second conjunct is
  `IsQuasiSeparatedAlgebraicModuliMap f`, retaining both properties of its relative
  diagonal on algebraic-space scheme tests.
- The final exclusions in the prose are respected: there is no DM, Noetherian,
  finite-type, or representability hypothesis on f, and no hypotheses asserting
  representability of X or Y. Representability of the diagonal is the intrinsic
  conclusion/predicate for algebraic stacks, not a hypothesis on f.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (structure and morphism docstrings/signatures, lines 38–45 and 73–90),
  `AlgebraicGeometry.Spec` and `Spec.map` (lines 469–481).
- `Mathlib.AlgebraicGeometry.Limits`: `AlgebraicGeometry.specULiftZIsTerminal`
  (lines 54–58), explicitly exhibiting the universe-u copy of Spec ℤ.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`
  and its smooth atlas and space-map definitions (full module read).
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompactModuli`,
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`,
  including their full docstrings and signatures. The current server copy was also
  read with `scompile.py --source`, and agrees with the local read clone.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `IsModuliStack`, `HasSpaceBaseChange`, and `HasAlgebraicSpaceDiagonal`, read in
  full with their docstrings. The independent stack universes are preserved.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `moduliRelativeDiagonal`
  (canonical object `(x,x,id)`, full construction read), used by the qcqs predicate.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`, full
  signature, construction, and docstring read; its owning node was read as well.
- `Mathlib.CategoryTheory.FiberedCategory.BasedCategory`:
  `BasedCategory.ofFunctor` and `BasedFunctor`, retaining the real category and
  base compatibility. `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.map`,
  with `map_obj_left`, `map_obj_hom`, at lines 199–213.
- `def-weil-size-convention` is a metatheoretic convention, so it supplies explicit
  universes rather than an imported declaration.

Edge cases checked before writing: the empty stack and empty base impose no
nonempty hypotheses; the empty source satisfies the expected vacuous fibre-product
tests. Identity morphisms and schemes reduce to the ordinary qcqs permanence fact.
A quasi-compact classifying stack such as BG_m is not excluded by a DM or
representability restriction. The target may be non-quasi-compact. In particular,
for a non-quasi-separated S, the formulas explicitly use Spec ℤ rather than silently
substituting relative quasi-separatedness over S. Arbitrarily unequal endpoint and
test universes are bound explicitly; `ULift ℤ` places the absolute base in the same
scheme universe and does not restrict the characteristic or the base field.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` with query
  `A morphism from a quasi compact quasi separated algebraic stack to a quasi separated algebraic stack is quasi compact and quasi separated`:
  eight scheme-morphism results, including `QuasiCompact.of_comp`, quasi-compact
  composition and base change, and quasi-separated composition. No stack theorem.
- `msearch.py ... leansearch` with the same query: eight scheme-only results,
  including `quasiCompact_of_compactSpace` and `QuasiSeparated.of_quasiSeparatedSpace`.
  None covers general algebraic stacks.
- `msearch.py ... loogle` with `"QuasiCompact", "QuasiSeparated"`: seven results on
  scheme diagonals and quasi-separated spaces; none is the algebraic-stack statement.
- `msearch.py ... grep` with `algebraicStack|quasiSeparatedStack|qcqs.*stack`:
  zero Mathlib matches.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for qcqs/quasiSeparated and then
  `IsQuasiSeparatedAlgebraicModuliMap`, `absoluteModuli`, `moduliOverIntegers`,
  `BasedCategory.ofFunctor`, `Over.map`, and `moduliBaseStructure`: found the
  recorded qcqs predicates, the existing structural functor, and applications such
  as `FlatAffineActionStackPresentation`; no permanence theorem or separately named
  absolute-stack construction. The application over Spec k explicitly notes its
  special base is separated over Spec ℤ; we do not impose that restriction here.
- `grep -rn 'lem-sfb-algebraic-stack-qcqs-permanence' lean/WeilConjectures` and
  `rg` for the item id in `dag/lean_names_upstream.json`: no upstream attachment.
- Name search for `algebraicStack_qcqs_permanence` in project/upstream: no clash.

No statement dispute, statement correction, new nodes, or dependency module repairs.
Validation: prescribed `scompile.py` compiled the sandbox and final library-path
module cleanly (21.2 s and 4.7 s respectively), with no errors or other warnings.

## Second reading by Q121

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
