/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical Weil arrows for condensed localization
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-general/sec-real-sheaves-on-an-arbitrary-base/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.md, final open–closed gluing paragraph: the arrows in
0 → j_!j^*G → G → i_*i^*G → 0 are Weil-equivariant
(blueprint: lem-zl-condensed-open-closed-localization-maps-core).

The module operations are the condensed module-object inverse image, direct image and open
extension by zero, with the canonical coefficient identifications built in. The Frobenius
comparisons are pinned to the open adjunction mate and the direct-image base-change map of
det-sf-open-closed-sequence-ring-sheaf (4).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Limits
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- The geometric base change `f = f₀ × id_k` of a morphism of `k₀`-schemes.
Source: thm-zl-real-mixed-by-curves.md, final open–closed gluing paragraph ("denote their
geometric base changes by j, i")
(blueprint: lem-zl-condensed-open-closed-localization-maps-core). -/
abbrev extensionGeometricMap
    {S₀ T₀ : Over (Spec (.of D.k₀))} (f₀ : S₀ ⟶ T₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

variable {U₀ Z₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The open extension by zero `j_!` on `Λ`-module objects, `Λ = Q̄_ℓ` condensed.
Source: thm-zl-real-mixed-by-curves.md, final open–closed gluing paragraph (the functor
`j_!` of the localization sequence)
(blueprint: lem-zl-condensed-open-closed-localization-maps-core). -/
abbrev openModuleExtension (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsOpenImmersion (extensionGeometricMap D j₀)] :=
  CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
    (extensionGeometricMap D j₀)

/-- `j_!` on Weil modules: the Weil structure of `j_!N` is `j_!(θ_N) ∘ e`, for the
comparison `e : g_X^* j_! ≅ j_! g_U^*`.
Source: thm-zl-real-mixed-by-curves.md, final open–closed gluing paragraph ("every extension
… is Weil-equivariant")
(blueprint: lem-zl-condensed-open-closed-localization-maps-core). -/
noncomputable def openWeilExtension (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)]
    (e : openModuleExtension D l j₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius U₀).hom ⋙ openModuleExtension D l j₀) :
    condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius U₀).hom ⥤
      condensedWeilModules (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀).hom := IsoAlgebra.mapOfNatIso e

end WeilConjectures.CondensedWeil
