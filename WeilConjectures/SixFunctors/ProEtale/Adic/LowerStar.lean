/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module

/-!
# Finiteness for the pushforward of constructible `ℓ`-adic sheaves

Let `K` be an algebraically closed field of characteristic different from `ℓ`, `Y` a scheme
locally of finite type over `K` and `f : X ⟶ Y` a quasi-compact, quasi-separated morphism
locally of finite type. The *finiteness theorem* (SGA 4½, *Th. finitude*, Th. 1.1, with
`ℓ`-adic coefficients as in Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8, and the
blueprint `sk-prop-sf-finiteness`) asserts that for a constructible `ℓ`-adic sheaf `F` on
`X_proét`:

- the pushforward `f_* F` is constructible
  (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.lowerStar`);
- every higher direct image `Rⁿf_* F`, the `n`-th cohomology sheaf of the total derived
  pushforward `Rf_*(F[0])`, is constructible
  (`AlgebraicGeometry.ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar`);
- if moreover `Y` is quasi-compact, then `Rf_*(F[0])` is bounded
  (`AlgebraicGeometry.ProEtale.bounded_rightDerivedFunctor_lowerStar`). It is concentrated in
  degrees `≥ 0`, and bounded above since the cohomological dimension of `f_*` is at most twice
  the dimension of the fibres, which is bounded on a quasi-compact `Y`
  (`AlgebraicGeometry.ProEtale.exists_isLE_rightDerivedFunctor_lowerStar`).

These are the inputs for the finiteness of the pushforward of Weil sheaves and Weil complexes
(`WeilConjectures.WeilSheaf.LowerStar`). The first is deduced from the second in degree `0`;
boundedness below holds for any sheaf. The constructibility of the higher direct images and
the upper bound are stated here with `sorry`. Their proof
(blueprint `sk-prop-sf-finiteness`) proceeds by generic constructibility for open immersions
(Deligne's dévissage), the proper case, and a Čech argument for a finite affine cover of `X`.

The objects with bounded constructible derived pushforward form a triangulated subcategory
(`AlgebraicGeometry.ProEtale.finiteLowerStar`), so the finiteness theorem is stable under
extensions, kernels and cokernels of short exact sequences and extends to bounded complexes
with constructible cohomology (`AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded`).

## Missing infrastructure

The two statements left with `sorry` need, beyond this dévissage: the recollement for closed
immersions on the pro-étale site (exactness of `i_*`, which rests on lifting weakly étale maps
along henselian pairs), so as to reduce a constructible sheaf to lisse sheaves on strata; and,
for the lisse case, a comparison of `ℚ̄_ℓ,X`-modules with `ℓ`-adic towers of torsion étale
sheaves (lattices, `Rf_*` commuting with `R lim` and with `⊗ ℚ`) together with the finiteness
theorem for torsion étale coefficients
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y)

/-- **Finiteness for the higher direct images of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the higher direct
images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated
morphism locally of finite type, with target locally of finite type, are constructible. -/
theorem isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l)
    [LocallyOfFiniteType s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) (n : ℤ) :
    IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- **Finiteness for the pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the pushforward
of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism locally of
finite type, with target locally of finite type, is constructible: it is the degree `0` case
of `AlgebraicGeometry.ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar`,
`f_*` being left exact. -/
theorem IsAdicConstructibleSheaf.lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((f)_*ᵃ[l].obj F) :=
  (isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar s f hK hF 0).of_iso
    ((f)_*ᵃ[l].homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
      (f)_*ᵃ[l].rightDerivedZeroIsoSelf.app F)

/-- **Cohomological dimension of the pushforward of a constructible `ℓ`-adic sheaf**
(SGA 4½, *Th. finitude*; SGA 4, Exp. X): over an algebraically closed field of characteristic
`≠ ℓ`, the higher direct images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a
quasi-compact quasi-separated morphism locally of finite type, with target quasi-compact and
locally of finite type, vanish in large degrees: the cohomological dimension of `f_*` is at
most twice the dimension of the fibres, which is bounded on a quasi-compact target. -/
theorem exists_isLE_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    ∃ b : ℤ, ((f)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b :=
  sorry

/-- **Boundedness of the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the derived
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism
locally of finite type, with target quasi-compact and locally of finite type, is bounded. It is
concentrated in degrees `≥ 0`, and bounded above by
`AlgebraicGeometry.ProEtale.exists_isLE_rightDerivedFunctor_lowerStar`. -/
theorem bounded_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    DerivedCategory.TStructure.t.bounded
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  ⟨⟨0, (f)_*ᵃ[l].isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    exists_isLE_rightDerivedFunctor_lowerStar s f hK hF⟩

section Devissage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (l) in
/-- The objects `K` of the derived category of `ℓ`-adic sheaves on `X_proét` whose derived
pushforward `Rf_* K` is bounded with constructible cohomology sheaves. The finiteness theorem
asserts that it contains every constructible sheaf placed in degree `0`. -/
def finiteLowerStar : ObjectProperty (DerivedCategory (AdicSheaf l X)) :=
  (DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)).inverseImage
      (f)_*ᵃ[l].rightDerivedFunctor

instance : (finiteLowerStar l f).IsClosedUnderIsomorphisms := by
  dsimp [finiteLowerStar]
  infer_instance

/-- **Dévissage for the finiteness theorem**: on a locally noetherian target, the objects with
bounded constructible derived pushforward form a triangulated subcategory, constructible
sheaves being a Serre subcategory and `Rf_*` a triangulated functor. -/
instance [IsLocallyNoetherian Y] : (finiteLowerStar l f).IsTriangulated := by
  have : (DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)).IsTriangulated :=
    inferInstance
  exact inferInstanceAs (ObjectProperty.IsTriangulated (ObjectProperty.inverseImage _
    (f)_*ᵃ[l].rightDerivedFunctor))

/-- **Two out of three for the finiteness theorem**: in a short exact sequence of `ℓ`-adic
sheaves on a scheme over a locally noetherian base, if the outer terms have bounded
constructible derived pushforward then so has the middle one. -/
lemma finiteLowerStar_X₂_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₁ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₃ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₂ _ hS.singleTriangle_distinguished h₁ h₃

/-- **Two out of three for the finiteness theorem**, kernel form. -/
lemma finiteLowerStar_X₁_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₂ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂))
    (h₃ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₁ _ hS.singleTriangle_distinguished h₂ h₃

/-- **Two out of three for the finiteness theorem**, cokernel form. -/
lemma finiteLowerStar_X₃_of_shortExact [IsLocallyNoetherian Y] {S : ShortComplex (AdicSheaf l X)}
    (hS : S.ShortExact) (h₁ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₂ : finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₂)) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj S.X₃) :=
  (finiteLowerStar l f).ext_of_isTriangulatedClosed₃ _ hS.singleTriangle_distinguished h₁ h₂

/-- The finiteness theorem extends from constructible sheaves to bounded complexes with
constructible cohomology sheaves (dévissage along the truncation triangles). -/
lemma finiteLowerStar_of_bounded [IsLocallyNoetherian Y]
    (h : ∀ F : AdicSheaf l X, IsAdicConstructibleSheaf F →
      finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj F))
    (K : DerivedCategory (AdicSheaf l X)) (hK : DerivedCategory.TStructure.t.bounded K)
    (hK' : _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l X) K) :
    finiteLowerStar l f K :=
  DerivedCategory.prop_of_bounded _ (adicConstructibleSheaf l X) h K hK hK'

end Devissage

end AlgebraicGeometry.ProEtale
