/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek

/-!
# Functoriality of the direct image with compact support of Weil complexes

The direct image with compact support `Rf₀! = Rḡ_* ∘ ī_!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) is defined through the compactification
`X ⟶[i] Z ⟶[g] Y` of `f` chosen by Nagata's theorem. This file records the compatibilities of
`Rf₀!` collected in the blueprint theorem `prop-functor-package` of the six-functor chapter that
the Deligne–Laumon reduction (`sec-deligne-laumon-general`) uses:

- *independence of the compactification* (clause 2): for every compactification `c` of `f`,
  `Rf₀! ≅ R(c.g)_* ∘ (c.i)_!`;
- *composition* (clause 3): `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`, and the distinguished triangle
  `R(j ≫ f)₀! j^*K ⟶ Rf₀!K ⟶ R(i ≫ f)₀! i^*K ⟶` obtained by applying `Rf₀!` to the
  localization triangle of an open immersion `j` and its closed complement `i`;
- *base change* (clause 4): `h^* Rf₀! ≅ Rf'₀! g^*` for a cartesian square.

These belong to the six-functor chapter and are stated here with `sorry`, each with the clause of
`prop-functor-package` it states. From them, and from the identification of `Rf₀!` with `Rf₀*`
for proper `f`, which is proved here, follow the open–closed triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶` of a Weil complex (`prop-sf-open-closed-triangle-all-stages`) and
the identification of `Rj₀!` with the extension by zero for an open immersion `j`.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar`: `Rf₀! ≅ Rf₀*` for `f` proper.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`,
  `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriekCompIso`,
  `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` and
  `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`: clauses 2, 3 and 4 of
  `prop-functor-package`.
- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`: the open–closed triangle
  (`prop-sf-open-closed-triangle-all-stages`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilComplex

section Proper

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper f] [LocallyOfFiniteType f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **For a proper morphism, the direct image with compact support is the direct image**: for the
chosen compactification `X ⟶[i] Z ⟶[g] Y` of the proper morphism `f`, the open immersion `i` is
proper, hence a closed immersion, so that `Rf₀!K = Rg_*(i_!K) ≅ Rg_*(i_*K) ≅ Rf₀*K`
(blueprint: `prop-functor-package`, clause 3, "for proper `f`, `Rf_! ≃ Rf_*`"). -/
noncomputable def derivedLowerShriekObjIsoDerivedLowerStar (K : WeilComplex k₀ l X) :
    (derivedLowerShriek k₀ l f).obj K ≅ (derivedLowerStar f).obj K := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

end Proper

section Package

variable {X Y Z U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))]

/-- **The direct image with compact support along an open immersion is the extension by zero**
(blueprint: `prop-functor-package`, clause 2, compactification comparisons for
`Rf_! = Rf̄_* j_!` are independent of the refinement, applied to the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`; and `def-weil-extension-by-zero`). For a
quasi-compact open immersion `j` and a Weil sheaf `G` on `U`, `Rj₀!G ≅ j₀!G` in degree zero. -/
theorem nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l U) :
    Nonempty ((derivedLowerShriek k₀ l j).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.extensionByZero j).obj G)) :=
  sorry

/-- **The open–closed triangle** (blueprint: `prop-sf-open-closed-triangle-all-stages`): for a
quasi-compact open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X` and a Weil complex `K`
on `X`, the open counit and the closed unit extend to a distinguished triangle of Weil complexes
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`. -/
theorem exists_distTriang_openClosed (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l X),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerStar i).obj ((upperStar i).obj K)) :=
  sorry


/-- **Composition of direct images with compact support** (blueprint: `prop-functor-package`,
clause 3: `R(gf)_! ≃ Rg_!Rf_!`; this is `lem-zl-shriek-composition` of
`sec-deligne-laumon-general`). For composable separated morphisms of finite type
`X ⟶[f] Y ⟶[g] Z` of `k₀`-schemes, `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`. -/
theorem nonempty_derivedLowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l (f ≫ g) ≅
      derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) :=
  sorry

/-- **Direct image with compact support of the localization triangle** (blueprint:
`prop-functor-package`, clause 3: for a closed immersion `i` with open complement `j`, applying
`Rf_!` to the localization triangle gives `R(fj)_!j^*K ⟶ Rf_!K ⟶ R(fi)_!i^*K ⟶`). -/
theorem exists_distTriang_derivedLowerShriek_openClosed (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l Y),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l (j ≫ f)).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ (derivedLowerShriek k₀ l f).obj K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerShriek k₀ l (i ≫ f)).obj ((upperStar i).obj K)) :=
  sorry

/-- **Base change for the direct image with compact support** (blueprint: `prop-functor-package`,
clause 4, `g^*Rf_! ≃ Rf'_!g'^*` for arbitrary base change, and `thm-cbc-qbar`): for a cartesian
square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h^* Rf₀! ≅ Rf'₀! g^*`. -/
theorem nonempty_upperStar_derivedLowerShriek_iso {X' Y' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ upperStar h ≅ upperStar g ⋙ derivedLowerShriek k₀ l f') :=
  sorry

end Package

end WeilComplex

end AlgebraicGeometry
