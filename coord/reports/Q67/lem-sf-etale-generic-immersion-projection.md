## Worker report

This repairs returned immutable head `9bd13b53d991`. The saved packet was inspected first and
its prescribed `deliver2.py --no-push` check passed mechanically (commit `57ed874617`). The
self-check confirmed that it still contained both mathematical defects of the return, so
it was not pushed unchanged. Comparing its node with the current shared node showed only
a `lean` difference. The original natural-language statement, proof and other node fields
are retained. The only additional statement dependency is the already landed
`lem-kun-tensor-sym`, whose recorded canonical symmetry this repair uses.

The module is `Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection`. It defines the actual
canonical arrows and states the entire node as `immersionProjectionFormula`. Its only
postponed theorem is that named theorem, with the five-step proof plan in its docstring.
All four helper definitions have real data and belong to the same immersion comparison.
There are no new nodes, dependency repairs or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`, in the recorded
  small-etale module-sheaf universe convention. There is no nonzero or characteristic
  assumption.
- The chosen factorization is `{S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)` with
  `[IsClosedImmersion i] [IsOpenImmersion j]`. The immersion `s` is `i ≫ j`.
- Ordinary unbounded `D(T_et,A)` is always
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. Neither boundedness,
  constructibility, perfectness nor Tor-amplitude hypotheses are imposed on either input.
- `Rs_! = j_! i_*` is `immersionLowerShriek A i j`, defined as
  `R((i)_*[ModuleCat A]) ⋙ D((j)_!open[ModuleCat A])`. Closed direct image and open extension
  by zero are exact. `Rs_*` and `Rs^! = Ri^! j^*` in the node are contextual notation;
  they occur in none of its three conclusions and require no extra chosen functor binder.
  The recorded ambient-right-adjoint and recollement modules are imported. Similarly
  derived internal Hom is context, not an additional conclusion; its recorded module is
  imported rather than a second internal-Hom construction being introduced.
- `s^* C` is `(L((i ≫ j)^*[ModuleCat A])).obj C`, the derived version of the exact
  constant-coefficient inverse image. Tensor objects and tensor morphisms are the recorded
  `derivedTensor` and its `derivedTensorHom` operation.
- The specified arrow `C ⊗ᴸ Rs_! P → Rs_!(s^* C ⊗ᴸ P)` is `immersionProjectionMap A i j C P`.
  Its body is, in order: the canonical signed symmetry on `X`; the inverse of
  `derivedOpenImmersionLowerShriekProjectionIso` at `(Ri_* P,C)`; inside `j_!`,
  `rightDerivedLowerStarProjectionMap` at `(P,Lj^* C)`; inside `Ri_*`, the signed symmetry
  on `S` and tensoring the inverse of `leftDerivedUpperStarComp i j` with `P`.
  This is the open/closed composite, with no zero arrow, arbitrary isomorphism, or choice
  from a `Nonempty` assertion.
- The theorem's first conjunct is `∀ C P, IsIso (immersionProjectionMap A i j C P)`.
- The second conjunct states two-variable naturality for arbitrary `f : C ⟶ C'` and
  `h : P ⟶ P'`:
  `(f ⊗ Rs_! h) ≫ π(C',P') = π(C,P) ≫ Rs_!(s^* f ⊗ h)`.
  This equation is in the Lean type, not just a docstring.
- The third conjunct quantifies over all primed schemes, all three vertical maps, and
  Cartesian witnesses `hi : IsPullback gS i' i gU` and
  `hj : IsPullback gU j' j gX`. The primed immersion instances express the base-changed
  closed/open factorization; these properties follow from the Cartesian hypotheses, so
  they exclude no pullback. Any Cartesian square for `s` is represented by such a diagram
  by pulling back its chosen intermediate `U`; the chosen pullback is not fixed in Lean.
- The node's particular `b_P` is `immersionLowerShriekBaseChangeMap A hi hj P`. Its body is
  `(derivedOpenImmersionLowerShriekBaseChangeIso hj).inv.app (Ri_* P)`, followed by
  `Dj'_!` of `(derivedBaseChangeMap hi.toCommSq).app P`. Thus it is exactly the composite
  of open extension-by-zero base change and closed finite exchange. The third conjunct
  explicitly includes `IsIso b_P`, on the unbounded categories.
- Write `t_g` for `leftDerivedUpperStarTensorComparison` and `d` for
  `immersionProjectionBaseChangeTensorMap`. The latter is `t_gS` followed by tensoring
  `(derivedSquareUpperStarIso (hi.toCommSq.vert_comp hj.toCommSq)).inv.app C` with the
  identity of `gS^* P`. The final equation in the theorem is
  `gX^*(π(C,P)) ≫ b_(s^*C ⊗ P) ≫ Rs'_!(d) =
   t_gX(C,Rs_!P) ≫ (1 ⊗ b_P) ≫ π'(gX^*C,gS^*P)`.
  Both paths start at `gX^*(C ⊗ Rs_!P)` and end at
  `Rs'_!(s'^*gX^*C ⊗ gS^*P)`. This renders precisely the equality under the node's tensor,
  composition and extension-by-zero base-change identifications.

Recorded dependency declarations read and used:

- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` / ordinary `DerivedCategory`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor` and `derivedTensorHom`.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
  `AlgebraicGeometry.etaleInverseImageModulesExact`. Exact pullback is the existing
  `Etale.upperStar`, with `leftDerivedUpperStarIsoMapDerivedCategory` identifying its
  derived and termwise functors.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses` (context only).
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  `AlgebraicGeometry.baseChange_iterated`; Cartesian squares use Mathlib `IsPullback`.
- `lem-cbc-open-closed-recollement`: `Sheaf.AlgebraicGeometry.OpenClosedRecollement`,
  `AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed` (context).
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`
  (context).
- `lemma-weil-pbc-finite-exchange`: `WeilConjectures.SixFunctors.Finite.BaseChange`,
  `AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite` and the preceding sheaf exchange.
  Its published instance is on `D⁺`; the unbounded map used here is the existing canonical
  `derivedBaseChangeMap`, and its needed invertibility is included explicitly in this
  node's theorem. It follows from exact closed direct image, not a boundedness restriction.
- Added existing dependency `lem-kun-tensor-sym`:
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`,
  `AlgebraicGeometry.Etale.derivedTensorSymmetry`; its actual signed K-flat construction
  is used, not the old existence-only `nonempty_iso_derivedTensor_flip`.

All available modules of the proof dependencies are also imported. The constructions use
`derivedOpenImmersionLowerShriekProjectionIso` in
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`,
`rightDerivedLowerStarProjectionMap` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
`derivedOpenImmersionLowerShriekBaseChangeIso` in its corresponding derived base-change
module, and `derivedBaseChangeMap` / `derivedSquareUpperStarIso` in
`WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`. Their full signatures and map
directions were checked. Missing/stale local source files were read via `scompile.py --source`.

Edge cases checked: `i = id`, `j = id`, both identity, empty `S`, empty pulled-back `S'`,
`C = 0`, `P = 0`, and the zero coefficient ring. The definitions retain the same canonical
maps in these cases. No nonemptiness, Noetherian, properness, finite-type, nonzero, or
boundedness assumption is added. The two-variable equation includes identity and zero
morphisms. Cartesian compatibility is for arbitrary vertical maps, not merely étale maps.

Searches retained from the saved packet: LeanFinder for derived projection with locally
closed immersion and for closed pushforward/open extension tensor compatibility (no exact
match); LeanSearch for locally closed projection/base change (only geometric immersion
results); Loogle for `"Sheaf", "projectionFormula"` (no hits); Mathlib grep for
`extensionByZero.*tensor|tensor.*extensionByZero|immersion.*projectionFormula` (no hits).
Repair searches: LeanFinder for "canonical derived tensor projection formula for a closed
immersion followed by an open immersion compatible with Cartesian base change" returned
only unrelated scheme pullback projection declarations; Loogle for
`rightDerivedLowerStarProjectionMap, derivedOpenImmersionLowerShriekProjectionIso`
reported unknown identifier/no hits (the service indexes Mathlib, not these upstream names);
Mathlib grep for `immersion.*[Pp]rojection|[Pp]rojection.*[Ii]mmersion` returned only the
unrelated ringed-space open-immersion pullback construction. `rg` of the named upstream and
side Lean trees found no `immersionProjectionMap`, `immersionProjectionFormula`, or
`immersionLowerShriekBaseChangeMap`; searching the item id upstream found none. Searching
for the symmetry found the already recorded `lem-kun-tensor-sym`, which is reused.

The source passages read were sites-modules.tex at `lemma-j-shriek-and-tensor` (Tag 0E8I)
and etale-cohomology.tex at `lemma-cohomology-with-support-triangle` (Tag 0A45). The node is
an agent-derived immersion extension of these, with open derived tensor and exchange
supplied by its existing proof dependencies. No STATEMENT-DISPUTED or node fault remains.

## Second reading by Q67

Author self-check for this dispatcher repair; no separate agent was started. The previous
report's assertion of an independent reading was not retained as evidence. Read the node
and final module together after repair. The former constant-zero body has been replaced
by the explicit five canonical comparison factors. Checked their successive objects:
`C ⊗ j_!Ri_*P → j_!Ri_*P ⊗ C → j_!(Ri_*P ⊗ j^*C) →
j_!Ri_*(P ⊗ i^*j^*C) → j_!Ri_*((i≫j)^*C ⊗ P)`.
The theorem now has all three clauses: isomorphism for arbitrary unbounded complexes,
naturality for arbitrary maps in both inputs, and the complete Cartesian comparison
square with the specified composite `b`. Its two paths have the same endpoints. The
inverse square comparison is necessary in the target transport and is oriented from
`gS^*s^*C` to `s'^*gX^*C`. The open comparison uses its inverse, whereas the closed
exchange uses its forward direction. The finite exchange instance's `D⁺` scope was checked;
it is not silently used to restrict the unbounded theorem.

A compile attempt using concrete `⊗`/`⊗ₘ` and `β_` hit the 60-second limit. Reading the
implementation notes of upstream `TensorStructure` identified the concrete monoidal
instance comparison as the cause. The final source instead uses the existing
`derivedTensor`, `derivedTensorHom`, and recorded canonical `derivedTensorSymmetry`.
This changes only the presentation of the same maps. All variables/universes are bound
explicitly and every source line is at most 100 characters. The theorem proof remains
`sorry`, as required for stage 2. Delivery is checked and rebased through `deliver2.py`.
