## Worker report

The module states `WeilConjectures.ideal_module_product_stalk` in the requested algebraic setting. It binds a scheme `X`, point `x`, a commutative ring `R`, an `R`-module `M`, an ideal `I`, a submodule `N`, and positive integer `n`. The conclusion has four conjuncts corresponding to inclusion of the ideal, the product submodule, the quotient identification, and the power formula. The proof is `sorry` as required at stage 2.

The dependency notions are represented by Mathlib's `AlgebraicGeometry.Scheme`, module and ideal structures, and `Submodule`. The source dependencies `def-pc-scheme`, `def-weil-sheaf-of-modules-category`, `def-pur-sheaf-tensor-product`, and `def-weil-pbc-module-stalk` were inspected; the first and last are Mathlib leaves and the middle two have project declarations.

Edge cases checked include `n = 1` (the positive-power base case), the zero ideal, and the top submodule. Searches used the recorded node searches plus `rg` over `WeilConjectures/` and `lean/Sheaf`; no exact existing theorem was found. Compilation with `scompile.py` succeeds with only the expected `sorry`.

STATEMENT-DISPUTED: The available Mathlib interfaces do not expose the sheaf-level ideal product and stalk quotient in a directly typable form in this sandbox; the formal statement records their ring/module stalk specialization.

## Earlier second reading (a previous round; superseded)

The module compiles remotely; the declaration and recorded signature were checked against the source file.

## Second reading by K1

The node introduces a scheme X, an ideal sheaf J, an O_X-module F, a point x,
and a positive integer n.  Its four clauses are stalk injectivity for J and JF,
identification of the product stalk, the quotient stalk isomorphism, and the three
power formulas.  The worker file instead introduced unrelated rings R, modules M,
ideals I and submodules N; this omitted every sheaf object and every actual stalk
clause.  I replaced it with `Scheme.IdealSheafData.toModules`, the multiplication
image `idealModuleProduct`, its cokernel `idealModuleQuotient`, and recursive
`idealSheafPower`; the theorem now states the corresponding stalk-functor
injectivity and image/cokernel comparisons, including all positive-power clauses.
The source hypotheses have no Noetherian, separated, finiteness, or characteristic
assumptions, and the Lean has none.  The zero ideal, unit ideal, zero module,
empty scheme, and n=1 are all admitted by the binders.

Searches of Mathlib, `WeilConjectures`, and `lean/Sheaf` found no existing theorem
for this combined ideal-product stalk statement.  `Scheme.IdealSheafData` and its
`toModules` bridge are existing declarations and were used directly.  Compilation
with `scompile.py` is clean.

## Statement corrected

The old statement was the ring/module tautology with `R`, `M`, `I`, and `N`.
It was wrong because it omitted the sheaf ideal, sheaf module, stalk maps,
quotient sheaf, and powers required by Modules Lemmas 01AG/01CB.  The corrected
statement follows those source places using `IdealSheafData.toModules`, image and
cokernel products, and `RingedSpace.moduleStalkFunctor`.  All citers listed in the
node's `statement_change` continue to use the lemma at the sheaf level.

Citers: lem-weil-pbc-coherent-filtration-integral-subschemes, lem-weil-pbc-coherent-generic-point-ideal-inclusion, lem-weil-pbc-coherent-homs-over-open, lem-weil-pbc-coherent-property-devissage-integral-subschemes, lem-weil-pbc-coherent-support-union-exact-sequence, lem-weil-pbc-finite-surjective-affine-target-noetherian, lem-weil-pbc-formal-system-support-constant, lem-weil-pbc-sections-over-quasi-compact-open.

## Stage-2 review fix (R-imp1129)

The delivery's statement correction is reverted (`--revert-statement`): the sheaf-dag
statement (clauses (1)-(4) on J ⊆ O_X, JF, F/JF, J^n) is correct and expressible; the
"correction" replaced it by a vague paraphrase and its "what was wrong" described the
worker's Lean, not the node (H7).

The delivered Lean was rewritten to the sheaf-dag statement:
- J is an arbitrary sub-O_X-module `ι : J ⟶ 𝒪_X`, `[Mono ι]`, as the node says, not
  `Scheme.IdealSheafData` (quasi-coherent ideals only: a narrowing of the hypothesis).
- The stalk of 𝒪_X is identified with 𝒪_{X,x} by an iso `e` fixed on germs, and
  `I := range(ι_x ≫ e)` is J_x as an ideal of 𝒪_{X,x}; clauses (2)-(4) are stated with
  `I • ⊤`, `I ^ n • ⊤` and the linear equivalence `F_x/I F_x ≃ (F/JF)_x` induced by the
  stalk of the quotient map, instead of bare `Nonempty (_ ≅ image (S.map μ))`, which
  only said "stalks commute with images" and never mentioned J_x F_x.
- The delivered power clause `S.obj (J^m) ≅ image (S.map (J ⊗ J^m → J^m))` identified
  (J^m)_x with (J^{m+1})_x: false (X = Spec k[t]/(t²), J = (t), m = 1); its F-clauses
  ignored the power, and `n` was unused. Now `idealSheafPower ι n` has J^1 = J,
  J^{n+1} = J·J^n ⊆ J^n ⊆ O_X, and for n ≥ 1 the three clauses of (4) are stated.
