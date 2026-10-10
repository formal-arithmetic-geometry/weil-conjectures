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
public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
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
(`WeilConjectures.WeilSheaf.LowerStar`). All of them are deduced from the case of a
quasi-compact target, `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`, which is
stated with `sorry`: the pushforward is the degree `0` case, `f_*` being left exact; boundedness
below holds for any sheaf; and constructibility is local on `Y`
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.of_openCover`), while the higher direct
images commute with restriction to an affine open subscheme of `Y`
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`). The proof of the remaining statement
(blueprint `sk-prop-sf-finiteness`) proceeds by generic constructibility for open immersions
(Deligne's dévissage), the proper case, and a Čech argument for a finite affine cover of `X`.

The objects with bounded constructible derived pushforward form a triangulated subcategory
(`AlgebraicGeometry.ProEtale.finiteLowerStar`), so the finiteness theorem is stable under
extensions, kernels and cokernels of short exact sequences and extends to bounded complexes
with constructible cohomology (`AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded`).

## Missing infrastructure

The statement left with `sorry` needs, beyond this dévissage: the recollement for closed
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

section Devissage

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

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

instance {Z W : Scheme.{u}} (g : Z ⟶ W) : (g)_*ᵃ[l].PreservesKInjectiveComplexes :=
  (adicUpperStarLowerStarAdjunction l g).preservesKInjectiveComplexes

/-- Transport of the finiteness property along an isomorphism of derived pushforwards. -/
lemma finiteLowerStar_of_iso {X' : Scheme.{u}} {g : X' ⟶ Y} {K : DerivedCategory (AdicSheaf l X)}
    {K' : DerivedCategory (AdicSheaf l X')}
    (e : (f)_*ᵃ[l].rightDerivedFunctor.obj K ≅ (g)_*ᵃ[l].rightDerivedFunctor.obj K')
    (h : finiteLowerStar l g K') : finiteLowerStar l f K :=
  ObjectProperty.prop_of_iso (DerivedCategory.TStructure.t.bounded ⊓
    _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)) e.symm h

variable (l) in
/-- For an open immersion `j : Z ⟶ X` and a K-injective complex `I` on `X`,
`Rf_* (j_* j^* I) ≅ R(j ≫ f)_* (j^* I)`. -/
noncomputable def rightDerivedFunctorLowerStarObjQIso {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] (I : CochainComplex (AdicSheaf l X) ℤ) [I.IsKInjective] :
    (f)_*ᵃ[l].rightDerivedFunctor.obj (DerivedCategory.Q.obj
        (((j)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((j)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≅
      (j ≫ f)_*ᵃ[l].rightDerivedFunctor.obj
        ((j)^*ᵃ[l].mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
  (f)_*ᵃ[l].rightDerivedFunctor.mapIso ((j)_*ᵃ[l].rightDerivedFunctorObjQIso _).symm ≪≫
    (Functor.rightDerivedFunctorCompIso' (j)_*ᵃ[l] (f)_*ᵃ[l] (adicLowerStarComp l j f)).app _ ≪≫
    (j ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso (((j)^*ᵃ[l].mapDerivedCategoryFactors).app I).symm

/-- **Mayer–Vietoris for the finiteness theorem** (the Čech step of `sk-prop-sf-finiteness`):
let `X = U ∪ V` be an open cover. An object `K` of the derived category of `ℓ`-adic sheaves on
`X` has bounded constructible derived pushforward along `f` as soon as its restrictions to
`U`, `V` and `U ∩ V` have, along the restrictions of `f`.

The unit `K ⟶ Rj_{U*} K|_U` has a cone `C` vanishing on `U`, hence `C ≅ Rj_{V*} C|_V`
(`AlgebraicGeometry.ProEtale.isIso_Q_map_unit_of_isZero`); restricting the triangle to `V`
and computing `(Rj_{U*} K|_U)|_V` on `U ∩ V` by open base change, `C|_V` sits in a triangle
with `K|_V` and the pushforward of `K|_{U ∩ V}`. -/
theorem finiteLowerStar_of_openCover [IsLocallyNoetherian Y] {U V : Scheme.{u}} (jU : U ⟶ X)
    (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base)
    (K : DerivedCategory (AdicSheaf l X))
    (hU : finiteLowerStar l (jU ≫ f) ((jU)^*ᵃ[l].mapDerivedCategory.obj K))
    (hV : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj K))
    (hW : finiteLowerStar l (pullback.fst jV jU ≫ jV ≫ f)
      ((pullback.snd jV jU)^*ᵃ[l].mapDerivedCategory.obj
        ((jU)^*ᵃ[l].mapDerivedCategory.obj K))) :
    finiteLowerStar l f K := by
  obtain ⟨I, _, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  refine (finiteLowerStar l f).prop_of_iso eK.symm ?_
  obtain ⟨C, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (adicUpperStarLowerStarAdjunction l jU).unit (ComplexShape.up ℤ)).app I))
  -- the pushforward of `K|_U`
  have h₂ : finiteLowerStar l f (DerivedCategory.Q.obj
      (((jU)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((jU)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    finiteLowerStar_of_iso f (rightDerivedFunctorLowerStarObjQIso l f jU I)
      ((finiteLowerStar l (jU ≫ f)).prop_of_iso
        ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eK) hU)
  -- the cone vanishes on `U`
  have hCU : IsZero ((jU)^*ᵃ[l].mapDerivedCategory.obj C) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _ ((jU)^*ᵃ[l].mapDerivedCategory.map_distinguished _ hT)
      (isIso_mapDerivedCategory_Q_map_unit l jU I)
  -- hence the cone is pushed forward from `V`
  obtain ⟨J, _, ⟨eC⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective C
  have hJ := isIso_Q_map_unit_of_isZero l jU jV hcov J
    (hCU.of_iso ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eC.symm))
  -- the restriction of the triangle to `V`
  have hTV := (jV)^*ᵃ[l].mapDerivedCategory.map_distinguished _ hT
  have hsq : IsPullback (pullback.fst jV jU) (pullback.snd jV jU) jV jU :=
    IsPullback.of_hasPullback jV jU
  let J₀ := ((jU)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have h₁V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj
      (DerivedCategory.Q.obj I)) :=
    (finiteLowerStar l (jV ≫ f)).prop_of_iso ((jV)^*ᵃ[l].mapDerivedCategory.mapIso eK) hV
  have h₂V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj
      (DerivedCategory.Q.obj (((jU)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj J₀))) :=
    finiteLowerStar_of_iso (jV ≫ f)
      ((jV ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso
          ((jV)^*ᵃ[l].mapDerivedCategory.mapIso ((jU)_*ᵃ[l].rightDerivedFunctorObjQIso J₀).symm ≪≫
            (adicDerivedBaseChangeIso l hsq).app _) ≪≫
        (Functor.rightDerivedFunctorCompIso' (pullback.fst jV jU)_*ᵃ[l] (jV ≫ f)_*ᵃ[l]
          (adicLowerStarComp l (pullback.fst jV jU) (jV ≫ f))).app _)
      ((finiteLowerStar l (pullback.fst jV jU ≫ jV ≫ f)).prop_of_iso
        ((pullback.snd jV jU)^*ᵃ[l].mapDerivedCategory.mapIso
          ((jU)^*ᵃ[l].mapDerivedCategory.mapIso eK ≪≫
            ((jU)^*ᵃ[l].mapDerivedCategoryFactors).app I)) hW)
  have h₃V : finiteLowerStar l (jV ≫ f) ((jV)^*ᵃ[l].mapDerivedCategory.obj C) :=
    (finiteLowerStar l (jV ≫ f)).ext_of_isTriangulatedClosed₃ _ hTV h₁V h₂V
  have h₃ : finiteLowerStar l f C :=
    finiteLowerStar_of_iso f
      ((f)_*ᵃ[l].rightDerivedFunctor.mapIso (eC ≪≫ asIso (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (adicUpperStarLowerStarAdjunction l jV).unit
            (ComplexShape.up ℤ)).app J))) ≪≫
        rightDerivedFunctorLowerStarObjQIso l f jV J ≪≫
        (jV ≫ f)_*ᵃ[l].rightDerivedFunctor.mapIso
          ((jV)^*ᵃ[l].mapDerivedCategory.mapIso eC.symm)) h₃V
  exact (finiteLowerStar l f).ext_of_isTriangulatedClosed₁ _ hT h₂ h₃

end Devissage

section Finiteness

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y)

/-- **Finiteness for the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the derived
pushforward `Rf_* F` of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated
morphism locally of finite type, with target quasi-compact and locally of finite type, is
bounded with constructible cohomology sheaves `Rⁿf_* F`. Boundedness above holds since the
cohomological dimension of `f_*` is at most twice the dimension of the fibres, which is bounded
on a quasi-compact target. -/
theorem finiteLowerStar_singleFunctor (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj F) :=
  sorry

/-- **Constructibility is local on the base**: an `ℓ`-adic sheaf whose restrictions to the
members of an open cover are constructible is constructible. -/
lemma IsAdicConstructibleSheaf.of_openCover {G : AdicSheaf l Y}
    (h : ∀ y : Y, ∃ (V : Scheme.{u}) (j : V ⟶ Y), IsOpenImmersion j ∧ y ∈ Set.range j.base ∧
      IsAdicConstructibleSheaf ((j)^*ᵃ[l].obj G)) :
    IsAdicConstructibleSheaf G := by
  intro y
  obtain ⟨V, j, hj, ⟨v, rfl⟩, hG⟩ := h y
  obtain ⟨W, i, hi, ⟨w, rfl⟩, hW⟩ := hG v
  exact ⟨W, i ≫ j, inferInstance, ⟨w, rfl⟩,
    hW.of_iso ((adicUpperStarComp l i j).app G).symm⟩

/-- **Finiteness for the higher direct images of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the higher direct
images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated
morphism locally of finite type, with target locally of finite type, are constructible.
Constructibility being local on `Y` and the higher direct images commuting with restriction
to an open subscheme (`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`), this is the case
of an affine target, `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`. -/
theorem isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l)
    [LocallyOfFiniteType s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) (n : ℤ) :
    IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  refine IsAdicConstructibleSheaf.of_openCover fun y ↦ ?_
  obtain ⟨R, j, hj, v, rfl⟩ := Scheme.exists_Spec_apply_eq y
  have : QuasiCompact (j ≫ s) := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2
    inferInstance
  have hsq : IsPullback (pullback.snd f j) (pullback.fst f j) j f :=
    (IsPullback.of_hasPullback f j).flip
  have h := finiteLowerStar_singleFunctor (j ≫ s) (pullback.snd f j) hK
    (hF.upperStar (pullback.fst f j))
  refine ⟨_, j, hj, ⟨v, rfl⟩, (h.2 n).of_iso ?_⟩
  exact (DerivedCategory.homologyFunctor _ n).mapIso
      ((Functor.mapIso _
          (((pullback.fst f j)^*ᵃ[l].mapDerivedCategorySingleFunctor 0).app F)).symm ≪≫
        ((adicDerivedBaseChangeIso l hsq).app _).symm) ≪≫
    (((j)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _).symm

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
locally of finite type, vanish in large degrees. -/
theorem exists_isLE_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    ∃ b : ℤ, ((f)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b :=
  (finiteLowerStar_singleFunctor s f hK hF).1.2

/-- **Boundedness of the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the derived
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism
locally of finite type, with target quasi-compact and locally of finite type, is bounded. -/
theorem bounded_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    DerivedCategory.TStructure.t.bounded
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  (finiteLowerStar_singleFunctor s f hK hF).1

end Finiteness

end AlgebraicGeometry.ProEtale
