## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint` defines the normalized
open compact-support identification `openCompactSupportIso`, the composition mate
`openExchangeIso`, and the canonical cartesian compact-support exchange
`canonicalCompactSupportExchange`.  Its main theorem `openExchange_adjunct` states both
clauses of the node: the adjunct of
`κ = δ⁻¹ ≫ Rf_!(ε_v)` is `C⁻¹`, and equivalently
`κ = Du_!(C⁻¹) ≫ ε_u`.  The theorem proof is `sorry`, as required for stage 2; all
helper definitions have real data.

The node's coefficient hypothesis is rendered by
`A : Type (u + 1)`, `[CommRing A]`, and `[Finite A]`.  The Noetherian standing hypothesis is
rendered by `[IsNoetherian X]`, `[IsNoetherian U]`, `[IsNoetherian S]`, and
`[IsNoetherian (pullback f u)]`.  The open immersion is `[IsOpenImmersion u]`.  The separated
finite-type compactifiable hypothesis on `f` is rendered by `[IsSeparated f]`,
`[LocallyOfFiniteType f]`, `[QuasiCompact f]`, and `[HasCompactification f]`; finite type is
locally finite type plus quasi-compact.  The fibre product is Mathlib's
`pullback f u`, with `v = pullback.fst f u` and `f_U = pullback.snd f u`; its equality
`v ≫ f = f_U ≫ u` is `pullback.condition`.  The object clause is
`F : DerivedCategoryModule A X`, with no boundedness binder.  `Dv_!`, `Du_!`, and inverse
image are respectively `openImmersionLowerShriek ... .mapDerivedCategory` and
`upperStar ... .mapDerivedCategory`; their evaluation counits are the derived
open-immersion adjunction counits.  The compact-support functors are
`rightDerivedLowerShriek`, and the specified composition maps are assembled from
`unboundedEtaleLowerShriekCompIso` and `unboundedEtaleLowerShriekCongr`.

Dependency declarations used: `AlgebraicGeometry.Etale.DerivedCategoryModule` from
`Sheaf.AlgebraicGeometry.DerivedCategories`; `AlgebraicGeometry.Etale.derivedTensor` from
`WeilConjectures.SixFunctors.Etale.Derived.Tensor` (ambient derived-tensor convention);
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and
`rightDerivedLowerShriek` from `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`;
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`,
`unboundedEtaleLowerShriekCongr`, and
`unboundedEtaleCompactSupportBaseChange` from
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`;
`CategoryTheory.Limits.pullback` from Mathlib;
`AlgebraicGeometry.IsOpenImmersion` from Mathlib;
`AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction` from
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction` from
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`; and
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion` from
`WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion`.
The exact inverse-image module and exceptional-adjoint declarations are imported through the
comparison and derived-adjunction modules; they impose no extra hypothesis in this statement.

Edge cases checked: the empty open is handled by the open-extension Kan extension and the
base-change map; the identity open gives the identity compactification normalization; the
zero object and arbitrary unbounded complexes are allowed because `F` is unrestricted;
`pullback.condition` handles the canonical equality without choosing an arbitrary map.
No characteristic, boundedness, or nonempty-open assumption is introduced.

Searches for an existing declaration: `msearch.py ... leanfinder "canonical compact support
exchange for open base change is adjoint to extension by zero and composition comparison"`
returned generic adjunctions (`restrictAdjunction`, `TopCat` adjunctions) and no geometric
match; `msearch.py ... loogle "rightDerivedLowerShriek, openImmersionLowerShriek,
derivedOpenImmersionLowerShriekUpperStarAdjunction"` returned no hits; `msearch.py ... grep
"shriek.*exchange|exchange.*adjoint" AlgebraicGeometry` returned zero hits.  `rg` over
`lean/Sheaf` and `WeilConjectures` found only the underlying comparison and adjunction APIs,
with no declaration of this item or its mate identity.  The item therefore receives a new
module declaration.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NR

I reread the node and the module signature clause by clause.  `pullback.fst` and
`pullback.snd` render exactly `v` and `f_U`, and `pullback.condition` supplies the stated
factorization equality.  `openExchangeIso` has source `Dv_! ⋙ Rf_!` and target
`Rf_{U!} ⋙ Du_!`, so its inverse at `v^*F` is precisely the first leg of `κ`; the following
map is the evaluation counit `Rf_!(ε_v)`.  The first conjunct applies the `Du_! ⊣ u^*`
hom bijection to that map and equates it to `C^{-1}`.  The second conjunct is the displayed
counit formula with `Du_!(C^{-1})` followed by `ε_u`, in the same order as the node.
Every scheme and coefficient hypothesis is bound explicitly, and `F` is an arbitrary object
of the ordinary unbounded derived category.  No mismatch was found.

## Maintainer review fix (cc second reader, 2026-10-17)

The statement `openExchange_adjunct` is unchanged (verbatim). Two repairs in the module:
the helper `openCompactSupportIso` was a pure alias of the existing upstream
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion` (same signature, body
the upstream term) and is removed (one definition per notion, H4); `openExchangeIso` now uses
the upstream declaration directly, and its redundant `letI` was dropped. The docstring of
`openExchange_adjunct` now carries the node's three proof steps in full (tower formula
`δ_M⁻¹ = P(a_M⁻¹) ∘ Γ_{J'M}`, the identity `e_F ∘ b^*h ∘ η_{b,H} = 1_H`, the cartesian
interchange clause and the computation `C_F ∘ m_F = 1`, then injectivity of the adjunction
bijection) (H8), and `openExchangeIso` names the node's `δ`. The worker report's first
sentence about `openCompactSupportIso` refers to the delivered version.
