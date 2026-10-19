## Worker report

The module `lean/Sheaf/Paper/PurEtaleLisseStratumCompact.lean` states
`AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf`.
It formalizes the compactness of the degree-zero étale sheaf obtained by applying ordinary
extension by zero along an open immersion `j : V ⟶ Z` and ordinary closed direct image along
`g : Z ⟶ X`, for a finite locally constant sheaf of `C`-modules whose geometric stalks are
flat. The conclusion is compactness in the ordinary unbounded derived category
`DerivedCategoryModule C X`.

The Lean rendering of the hypotheses and conclusion is as follows.

* `k : Type u` with `[Field k] [IsAlgClosed k]` renders an algebraically closed field.
* `ell : ℕ`, `hell : Nat.Prime ell`, and `hellk : IsUnit (ell : k)` render a prime
  invertible in `k`.
* `C : Type (u + 1)` with `[CommRing C] [Finite C]` and
  `hC : ∃ r : ℕ, (ell : C) ^ r = 0` render a finite commutative ring annihilated by a
  power of `ell`.
* `g : Z ⟶ X` with `[IsClosedImmersion g]` renders the closed immersion.
* `j : V ⟶ Z` with `[IsOpenImmersion j]` renders the open immersion into the closed stratum.
* `f : X ⟶ Spec (CommRingCat.of k)` with `[LocallyOfFiniteType f]`
  `[QuasiCompact f]` renders that `X` is finite type over `k`; no separatedness hypothesis
  is introduced.
* `L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)` is the ordinary sheaf of
  `C`-modules on the small étale site, and
  `[Scheme.IsFiniteLocallyConstantSheaf L]` is the recorded finite locally constant
  (lisse) condition.
* `hL` quantifies over every separably closed field `Ω` and geometric point
  `s : Spec (CommRingCat.of Ω) ⟶ V`; its conclusion
  `ObjectProperty.flat ((Scheme.pointSmallEtale s).sheafFiber.obj L)` is exactly flatness
  of every geometric stalk. The stalk is Mathlib's `Point.sheafFiber` specialization.
* The result supplies `hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C X)` and
  applies `@CategoryTheory.IsCompactObject` with that coproduct structure to
  `DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) 0`
  applied to
  `((Etale.lowerStar ... g).obj ((Etale.openImmersionLowerShriek ... j).obj L))`.
  Thus the sheaf is placed in degree zero and compactness is the exact project definition.
  The explicit existential coproduct structure is required by the available derived-category
  interface and matches `finiteRing_compactGenerators`.

Dependency declarations used for the statement are:

* `Sheaf.CategoryTheory.CompactObject`, declaration `CategoryTheory.IsCompactObject`;
* `WeilConjectures.ConstructibleSheaf.Defs`, declaration
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`;
* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, declaration
  `AlgebraicGeometry.Etale.DerivedCategoryModule`;
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, declaration
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`;
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declaration
  `AlgebraicGeometry.Etale.lowerStar`;
* Mathlib `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsOpenImmersion`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, and the derived-category
  `DerivedCategory.singleFunctor`.

The edge cases checked were: `V` empty (the extension-by-zero sheaf is zero), `Z` or `X`
empty, `L` the zero sheaf, the zero family in the compactness definition, `ell = 0` being
excluded by `Nat.Prime ell`, and the exponent `r = 0` in `hC` (which correctly forces the
zero ring). No separatedness assumption was added. Flatness is imposed on all geometric
stalks, including the vacuous case of an empty stratum.

Searches for an existing declaration were made before writing:

* `msearch.py ... grep 'IsCompactObject|lisse.*compact|openImmersionLowerShriek'` in
  `Mathlib/AlgebraicGeometry`: zero hits.
* `msearch.py ... leanfinder 'finite locally constant flat sheaf compact unbounded etale derived category'`:
  hits concerned condensed sheaves and finite presentation, with no matching theorem.
* `msearch.py ... loogle 'IsCompactObject, DerivedCategory, openImmersionLowerShriek'`:
  zero hits / unknown `IsCompactObject`.
* `rg -n` over `WeilConjectures` and `lean/Sheaf` found the underlying functors and the
  general finite-ring compact-generator theorem, but no statement of this lisse-stratum
  compactness lemma.

The source statement is from Bhatt--Scholze, *Pro-étale topology*, Section 6.4,
Example 6.4.1, Lemmas 6.4.4 and 6.4.6, and the final paragraph of Proposition 6.4.8,
printed pp. 48--49. Its proof plan is recorded in the theorem docstring: finite-type and
qcqs reductions, exact inverse image and coproduct preservation, the closed-support triangle
for `Rg!`, finite projective local retracts, internal-Hom coproduct preservation, and the
open/closed adjunction computation. The only postponed proof is the theorem's single
`sorry`, as required for stage 2.

## Second reading by NF

I read the node against Bhatt--Scholze, Section 6.4, pp. 48--49 (Example 6.4.1, Lemmas
6.4.4 and 6.4.6, and the last paragraph of Proposition 6.4.8), then matched every item
with the Lean signature. The algebraically closed field is `k : Type u` with
`[Field k] [IsAlgClosed k]`; the prime and invertibility hypotheses are `ell : ℕ`,
`hell : Nat.Prime ell`, and `hellk : IsUnit (ell : k)`. The finite coefficient ring is
`C : Type (u + 1)` with `[CommRing C] [Finite C]`, and
`hC : ∃ r : ℕ, (ell : C) ^ r = 0`. The locally closed factorization is
`X Z V : Scheme.{u}`, `g : Z ⟶ X` with `[IsClosedImmersion g]`, and `j : V ⟶ Z`
with `[IsOpenImmersion j]`. Finite type over `k` is rendered by
`f : X ⟶ Spec (CommRingCat.of k)` with `[LocallyOfFiniteType f] [QuasiCompact f]`,
the recorded interface of the finite-type-morphism node; no separatedness hypothesis is
added. The sheaf is `L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)` with
`[Scheme.IsFiniteLocallyConstantSheaf L]`. Geometric flatness is exactly `hL`, quantified
over every separably closed `Ω : Type u` and every
`s : Spec (CommRingCat.of Ω) ⟶ V`, with conclusion
`ObjectProperty.flat ((Scheme.pointSmallEtale s).sheafFiber.obj L)`.

The conclusion supplies `hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C X)` and
applies `@CategoryTheory.IsCompactObject` to the degree-zero object
`DerivedCategory.singleFunctor ... 0` applied to
`((Etale.lowerStar ... g).obj ((Etale.openImmersionLowerShriek ... j).obj L))`.
This is exactly `g_* j_! L` in degree zero with the project's compact-object definition.
No mismatch was found, so no Lean statement or node field was changed. The explicit
coproduct witness is required by the recorded definition and is the same interface used by
`finiteRing_compactGenerators`, rather than an additional mathematical assumption.

The dependency declarations were checked at their definitions: Mathlib's
`IsClosedImmersion`, `IsOpenImmersion`, `pointSmallEtale`/`sheafFiber`, and
`DerivedCategory.singleFunctor`, together with the project declarations for finite lisse
sheaves, the derived module category, `openImmersionLowerShriek`, and `lowerStar`, all match
the node's notions. No hollow definition or private duplicate is present.

Edge cases checked: empty `V` gives the zero extension-by-zero sheaf; empty `Z` or `X` is
admitted by the scheme binders; the zero sheaf `L` and an empty coproduct family are
admitted; `Nat.Prime ell` excludes `ell = 0`; and `r = 0` in `hC` describes the zero ring.
The stalk condition is vacuous on an empty stratum. All universes are explicit and the
stalk field universe agrees with `Scheme.{u}`.

I repeated the existing-declaration searches with `msearch.py` (LeanFinder and Loogle)
for compact lisse/constructible étale sheaves and `openImmersionLowerShriek`, and with
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`. They found only unrelated condensed
or topological compactness results and the underlying functors. The theorem is new. The
required `scompile.py` run compiled the module successfully with only the expected `sorry`
warning.
