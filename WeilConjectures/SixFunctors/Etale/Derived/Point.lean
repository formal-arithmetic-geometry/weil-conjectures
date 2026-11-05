/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# The point category

Let `k` be a separably closed field and `s = Spec k`. An étale sheaf on `s` is determined by its
global sections (`AlgebraicGeometry.Scheme.isZero_of_subsingleton_sections_of_isSepClosed`). In
the derived category `D(s_ét, Λ)` of étale sheaves of `Λ`-modules, the *point category*, the
shifts `Λ_s[r]` of the constant complex therefore detect isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.isIso_iff_bijective_comp_of_isSepClosed` (`lem-sf-detection`): a
  morphism `u : P ⟶ Q` of the point category is an isomorphism if and only if
  `Hom(Λ_s[r], u)` is bijective for every `r : ℤ`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual`
  (`lem-sf-point`): evaluation at the point carries the dual `RHom_s(C, Λ_s)` of an object of
  `D^b_c(s, Λ)` to the dual `RHom_Λ(RΓ(s, C), Λ)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence`
  : the same for any coefficient category `A` and scheme `X` for which the constant sheaf functor
  `A ⥤ Sheaf X_ét A` is an equivalence of categories.
- `AlgebraicGeometry.Etale.isEquivalence_rightDerivedGlobalSections_of_isSepClosed`
  (`lem-sf-point`): evaluation at the point `RΓ(s, -)` is an equivalence of categories.
- `AlgebraicGeometry.Etale.homSingleShiftEquivOfIsSepClosed` (`lem-sf-point`): morphisms
  `Λ_s[-r] ⟶ C` are the global sections of the `r`-th cohomology sheaf of `C`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

open Scheme Pretriangulated ZeroObject

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [Ring Λ]

section GlobalSections

/-- Over a separably closed field `k`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec k` preserves epimorphisms: an epimorphism of sheaves is surjective on
sections over the terminal object, every covering sieve of which is maximal. -/
instance preservesEpimorphisms_Γ_of_isSepClosed :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    let e := Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) isTerminalEtalePoint
    have h : (Sheaf.Γ _ _).map φ =
        e.hom.app F ≫ ((sheafSections _ _).obj _).map φ ≫ e.inv.app G := by
      rw [← reassoc_of% (e.hom.naturality φ)]
      simp
    have : Epi (((sheafSections (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj (op (etalePoint k))).map φ) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_epi_of_isSepClosed k φ)
    rw [h]
    infer_instance

/-- Over a separably closed field `k`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec k` is exact. -/
instance preservesFiniteColimits_Γ_of_isSepClosed :
    PreservesFiniteColimits (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  have h := (Functor.preservesFiniteLimits_tfae
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 3 0
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 0 3
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

/-- Over a separably closed field `k`, the cohomology of the derived global sections of an
object `L` of `D(Spec(k)_ét, Λ)` is the global sections of its cohomology sheaves:
`Hⁿ(RΓ(Spec k, L)) ≅ Γ(Spec k, Hⁿ(L))`, the global sections functor being exact. -/
noncomputable def homologyRightDerivedGlobalSectionsIsoOfIsSepClosed (n : ℤ) :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) ⋙
        DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙
        Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Functor.rightDerivedFunctorHomologyFunctorIso _ n).symm

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` inject into its stalk at any geometric point: a section vanishing on an étale
neighbourhood of the point vanishes, as that neighbourhood has a `k`-point. -/
lemma injective_toPresheafFiber_etalePoint_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of k))
    (x : (pointSmallEtale s).fiber.obj (etalePoint k)) :
    Function.Injective ((pointSmallEtale s).toPresheafFiber (etalePoint k) x F.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro z₁ z₂ h
  obtain ⟨Y, f, y, -, hy⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' _ x z₁ z₂).1 h
  have : AlgebraicGeometry.Etale Y.hom := Y.prop
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed Y.hom (𝟙 _)
    ((y.left : Spec (.of Ω) ⟶ Y.left) (default : Spec (.of Ω)))
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  let σ : etalePoint k ⟶ Y := MorphismProperty.Over.homMk (A := etalePoint k) (B := Y) l
    (hl.trans rfl)
  have hσ : σ ≫ f = 𝟙 _ := isTerminalEtalePoint.hom_ext _ _
  have := congrArg (F.obj.map σ.op) hy
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hσ, op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using this

/-- Over a separably closed field `k`, the global sections of a constructible étale sheaf of
modules over a noetherian ring `Λ` on `Spec k` form a finite `Λ`-module: they inject into the
stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`, which is finite. -/
lemma finite_Γ_of_isConstructibleSheaf [IsNoetherianRing Λ]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    Module.Finite Λ ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F) := by
  have hfin := (IsConstructibleSheaf.isFiniteSheaf (F := F)
    inferInstance).isFinitelyGenerated_sheafFiber k (𝟙 _)
  rw [ModuleCat.isFinitelyGenerated_iff] at hfin
  have : Module.Finite Λ (((pointSmallEtale (𝟙 (Spec (.of k)))).presheafFiber
    (A := ModuleCat.{u + 1} Λ)).obj F.obj) := hfin
  let x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k) :=
    Over.homMk (𝟙 _) (by simp [etalePoint])
  let e := (Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F
  exact Module.Finite.of_injective
    (e.hom ≫ (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj).hom
    ((injective_toPresheafFiber_etalePoint_of_isSepClosed F _ x).comp
      ((ConcreteCategory.bijective_of_isIso e.hom).1))

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` are its stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`: the canonical map is
injective by `AlgebraicGeometry.Etale.injective_toPresheafFiber_etalePoint_of_isSepClosed`,
and surjective since every étale neighbourhood of this point has a `k`-point through which the
point factors. -/
lemma bijective_toPresheafFiber_etalePoint_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k)) :
    Function.Bijective
      ((pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj) := by
  refine ⟨injective_toPresheafFiber_etalePoint_of_isSepClosed F _ x, fun p ↦ ?_⟩
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, z, rfl⟩ := (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber_jointly_surjective
    (P := F.obj) p
  let σ : etalePoint k ⟶ V := MorphismProperty.Over.homMk (A := etalePoint k) (B := V) v.left
    ((Over.w v).trans rfl)
  have hv : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.map σ x = v := by
    apply Over.OverMorphism.ext
    have hx : x.left = 𝟙 _ := by simpa [etalePoint] using Over.w x
    change x.left ≫ v.left = v.left
    rw [hx, Category.id_comp]
  refine ⟨F.obj.map σ.op z, ?_⟩
  rw [← hv, ← (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber_w σ x F.obj]
  rfl

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` are isomorphic to its stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`. -/
noncomputable def ΓIsoSheafFiberOfIsSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F ≅
      (pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.obj F :=
  let x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k) :=
    Over.homMk (𝟙 _) (by simp [etalePoint])
  (Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F ≪≫
    (LinearEquiv.ofBijective
      ((pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj).hom
      (bijective_toPresheafFiber_etalePoint_of_isSepClosed F x)).toModuleIso

end GlobalSections

section Flat

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Over a separably closed field `k`, the global sections of a flat étale sheaf of
`Λ`-modules on `Spec k` form a flat `Λ`-module: they are its stalk at a geometric point. -/
lemma flat_Γ_of_isSepClosed {F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F) :=
  ObjectProperty.prop_of_iso _ ((ΓIsoSheafFiberOfIsSepClosed F) ≪≫
    ((pointSmallEtale (𝟙 (Spec (.of k)))).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)).symm.app F).symm
    (((pointSmallEtale (𝟙 (Spec (.of k)))).ulift.{u + 1}).flat_sheafFiber_obj hF)

/-- Over a separably closed field `k`, an object of `D(Spec(k)_ét, Λ)` of Tor amplitude in
`[a, b]` has derived global sections of Tor amplitude in `[a, b]`: it is represented by a
complex of flat sheaves in degrees `[a, b]`, and the global sections functor is exact and
preserves flatness (`AlgebraicGeometry.Etale.flat_Γ_of_isSepClosed`). -/
lemma torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed {a b : ℤ}
    {L : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.torAmplitudeIn _ a b L) :
    _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a b
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hL
  let Γ := Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : CochainComplex.IsStrictlyGE ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ Γ.map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : CochainComplex.IsStrictlyLE ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ Γ.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  refine (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso ?_
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a b
      fun n ↦ flat_Γ_of_isSepClosed (hP n))
  exact (Γ.mapDerivedCategoryFactors.app P).symm ≪≫ Γ.mapDerivedCategory.mapIso e ≪≫
    (Functor.rightDerivedFunctorIsoMapDerivedCategory Γ).symm.app L

end Flat

section Duality

section

section Equivalence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u}) [(constantSheaf X.smallEtaleTopology A).IsEquivalence]

/-- If the constant sheaf functor `F : A ⥤ Sheaf X_ét A` is an equivalence of categories, the
global sections functor is a quasi-inverse of `F`, hence exact, and the derived global sections
`RΓ(X, -)` are the functor induced by `F⁻¹` on derived categories. -/
noncomputable def rightDerivedGlobalSectionsIsoMapDerivedCategoryInv :
    rightDerivedGlobalSections A X ≅
      (constantSheaf X.smallEtaleTopology A).inv.mapDerivedCategory :=
  let eΓ : Sheaf.Γ X.smallEtaleTopology A ≅ (constantSheaf X.smallEtaleTopology A).inv :=
    (constantSheafΓAdj _ _).rightAdjointUniq
      (constantSheaf X.smallEtaleTopology A).asEquivalence.toAdjunction
  have : PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology A) :=
    preservesFiniteLimits_of_natIso eΓ.symm
  have : PreservesFiniteColimits (Sheaf.Γ X.smallEtaleTopology A) :=
    preservesFiniteColimits_of_natIso eΓ.symm
  (Sheaf.Γ _ _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso eΓ

/-- If the constant sheaf functor `A ⥤ Sheaf X_ét A` is an equivalence of categories, the
derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)` are an equivalence of categories. -/
theorem isEquivalence_rightDerivedGlobalSections_of_isEquivalence :
    (rightDerivedGlobalSections A X).IsEquivalence :=
  Functor.isEquivalence_of_iso (rightDerivedGlobalSectionsIsoMapDerivedCategoryInv A X).symm

end Equivalence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
  [(constantSheaf X.smallEtaleTopology A).IsEquivalence]

end

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-sf-point`: The point, evaluated (evaluation at the point is an equivalence).

Let `k` be a separably closed field and `s = Spec k`. Evaluation at the geometric point, the
derived global sections `RΓ(s, -) : D(s_ét, Λ) ⥤ D(Λ)`, is an equivalence of categories; in
particular it is conservative. It restricts to the equivalence `Fib_s` of the blueprint between
the point category `D^b_c(s, Λ)` and the bounded derived category of finite `Λ`-modules. -/
instance isEquivalence_rightDerivedGlobalSections_of_isSepClosed :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).IsEquivalence :=
  isEquivalence_rightDerivedGlobalSections_of_isEquivalence _ _

end Duality

end AlgebraicGeometry.Etale
