/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.ScalarPullbackSingleTransposes
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceProof

/-! # Supported-source normalization of the scalar/pullback mate

## Main statements

- `diagonalSupported_pullbackScalarNormalization`: supported coefficient endpoints commute
  with geometric inverse image under the scalar mate.
- `upperStar_supportMap_comp_supported`: the underived supported-source square.

## Implementation details

- The derived statement is transposed through the scalar adjunction. The mate property of
  `Adjunction.pushHomOfComapIso` and `scalarRestrictionPullbackIso_inv_app_single` reduce
  both sides to the degree-zero functor applied to underived module maps.
- The underived square is transposed through the inverse-image adjunction. The ordinary
  exchange becomes the direct image of the unit endpoint adjoint followed by the conjugate
  composition comparison (`homEquiv_exchangeRight_app_comp`). The remaining identity is a
  formal consequence of `comapLowerStarIso_conjugate_square` (compatibility of the
  restriction comparisons with composition of direct images) and
  `coefficient_unitPull_square` (checked on underlying sheaves).
- Composites are compared as module maps rather than on underlying sheaves wherever
  possible: underlying-sheaf identities whose objects come from different module
  categories are only defeq after deep unfolding, which is very costly for the kernel.
- `coefficient_conjugate_square` takes the two proofs of the commutative square
  separately: the two supported pullbacks carry their own proofs, and identifying them
  inside the generic lemma keeps the kernel check cheap.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedUpper derivedScalars singlePullback
  scalarPullbackComparison

/-- Inverting a commutative square of isomorphisms around a fixed arrow. -/
private theorem inv_square {C : Type*} [Category C] {A B D E H K : C}
    (d : A ≅ B) (x : B ≅ D) (m : D ≅ E) (y : A ⟶ H) (n : H ≅ K) (s : K ≅ E)
    (h : d.hom ≫ x.hom ≫ m.hom = y ≫ n.hom ≫ s.hom) :
    x.inv ≫ d.inv ≫ y = m.hom ≫ s.inv ≫ n.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, reassoc_of% h]
  simp

/-- The adjoint transpose of an exchange morphism followed by a map, through the
conjugate of the exchanged isomorphism. -/
private theorem homEquiv_exchangeRight_app_comp {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} {RG : B' ⥤ B} {RG' : A' ⥤ A}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (aG : G ⊣ RG) (aG' : G' ⊣ RG')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') {K : A} {K' : A'} (ψ : G'.obj K ⟶ K') :
    aG.homEquiv _ _ ((Adjunction.exchangeRight af af' θ).app K ≫ Rf'.map ψ) =
      Rf.map (aG'.homEquiv _ _ ψ) ≫
        (conjugateEquiv (af.comp aG') (aG.comp af') θ.hom).app K' := by
  have hψ : G'.map (aG'.homEquiv _ _ ψ) ≫ aG'.counit.app K' = ψ := by
    simp [Adjunction.homEquiv_unit]
  generalize aG'.homEquiv _ _ ψ = φ at hψ ⊢
  subst hψ
  simp only [Adjunction.homEquiv_unit,
    Adjunction.exchangeRight_app, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Adjunction.comp_counit_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [← aG.unit_naturality_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  rw [← af'.unit_naturality_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  have hθ := θ.hom.naturality (Rf.map φ)
  simp only [Functor.comp_map] at hθ
  rw [reassoc_of% hθ]
  simp only [← Functor.map_comp_assoc, af.counit_naturality]

/-- The inverse-image adjoint of a restricted map out of a pulled-back restricted module is
the restriction of the adjoint, followed by the restriction/direct-image comparison. -/
theorem homEquiv_comapUpperStarIso_inv_app_comp
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S) {N : Modules T S}
    {N' : Modules T X} (φ : (CondensedRing.upperStar T f).obj N ⟶ N') :
    (CondensedRing.upperStarLowerStarAdjunction R f).homEquiv _ _
        ((CondensedRing.comapUpperStarIso a f).inv.app N ≫
          (Mod.comap (coefficientMap a X)).map φ) =
      (Mod.comap (coefficientMap a S)).map
          ((CondensedRing.upperStarLowerStarAdjunction T f).homEquiv _ _ φ) ≫
        (CondensedRing.comapLowerStarIso a f).hom.app N' := by
  have hu : (Mod.comap (coefficientMap a S)).map
        ((CondensedRing.upperStarLowerStarAdjunction T f).unit.app N) ≫
      (CondensedRing.comapLowerStarIso a f).hom.app ((CondensedRing.upperStar T f).obj N) =
      (CondensedRing.upperStarLowerStarAdjunction R f).unit.app
          ((Mod.comap (coefficientMap a S)).obj N) ≫
        (CondensedRing.lowerStar R f).map ((CondensedRing.comapUpperStarIso a f).inv.app N) := by
    have h := unit_mateEquiv (CondensedRing.upperStarLowerStarAdjunction T f)
      (CondensedRing.upperStarLowerStarAdjunction R f)
      (TwoSquare.mk _ _ _ _ (CondensedRing.comapUpperStarIso a f).inv) N
    rw [CondensedRing.comapUpperStarIso_mate] at h
    exact h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← hu, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1

/-- The ordinary exchange is the exchange morphism of the composition comparison. -/
theorem ordinaryExchange_eq_exchangeRight
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    ordinaryExchange Λ f f' hX hS h =
      Adjunction.exchangeRight (G := CondensedRing.upperStar Λ hS)
        (G' := CondensedRing.upperStar Λ hX) (CondensedRing.upperStarLowerStarAdjunction Λ f)
        (CondensedRing.upperStarLowerStarAdjunction Λ f')
        ((CondensedRing.upperStarComp Λ f' hS).symm ≪≫
          CondensedRing.upperStarCongr Λ h ≪≫ CondensedRing.upperStarComp Λ hX f) := by
  unfold ordinaryExchange
  rfl

/-- The underlying adjoint of a coefficient-unit pullback endpoint is the canonical
coefficient direct-image map. -/
theorem UnitPullEndpoint.homEquiv_iso_hom_hom
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {X S : Scheme.{u}} {p : X ⟶ S} (c : UnitPullEndpoint Λ p) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ p).homEquiv _ _) c.iso.hom).hom =
      condensedPushforwardHom Λ p := by
  rw [c.normalization, Adjunction.homEquiv_unit]
  rfl

/-- Inverting a composite of isomorphisms. -/
private theorem inv_square_three {C : Type*} [Category C] {A B D E F : C}
    (p : A ≅ B) (q : B ≅ D) (c : A ≅ E) (d : E ≅ F) (e : F ≅ D)
    (h : p.hom ≫ q.hom = c.hom ≫ d.hom ≫ e.hom) :
    q.inv ≫ p.inv ≫ c.hom = e.inv ≫ d.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, reassoc_of% h]
  simp

/-- The composition isomorphism of direct images commutes with the inverse restriction
comparisons. -/
@[reassoc]
theorem comapLowerStarIso_inv_app_comp_lowerStarComp
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules T X) :
    (CondensedRing.comapLowerStarIso a g).inv.app ((CondensedRing.lowerStar T f).obj N) ≫
        (Mod.comap (coefficientMap a Z)).map ((CondensedRing.lowerStarComp T f g).hom.app N) =
      (CondensedRing.lowerStar R g).map ((CondensedRing.comapLowerStarIso a f).hom.app N) ≫
        (CondensedRing.lowerStarComp R f g).hom.app ((Mod.comap (coefficientMap a X)).obj N) ≫
        (CondensedRing.comapLowerStarIso a (f ≫ g)).inv.app N := by
  rw [← cancel_mono ((CondensedRing.comapLowerStarIso a (f ≫ g)).hom.app N), Category.assoc,
    CondensedRing.comapLowerStarIso_hom_app_lowerStarComp, Iso.inv_hom_id_app_assoc]
  simp

/-- The inverse composition isomorphism of direct images commutes with the restriction
comparisons. -/
@[reassoc]
theorem comapLowerStarIso_inv_app_comp_lowerStarComp_inv
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules T X) :
    (CondensedRing.comapLowerStarIso a (f ≫ g)).inv.app N ≫
        (Mod.comap (coefficientMap a Z)).map ((CondensedRing.lowerStarComp T f g).inv.app N) ≫
        (CondensedRing.comapLowerStarIso a g).hom.app ((CondensedRing.lowerStar T f).obj N) =
      (CondensedRing.lowerStarComp R f g).inv.app ((Mod.comap (coefficientMap a X)).obj N) ≫
        (CondensedRing.lowerStar R g).map ((CondensedRing.comapLowerStarIso a f).inv.app N) :=
  inv_square_three ((Mod.comap (coefficientMap a Z)).mapIso
      ((CondensedRing.lowerStarComp T f g).app N))
    ((CondensedRing.comapLowerStarIso a (f ≫ g)).app N)
    ((CondensedRing.comapLowerStarIso a g).app _)
    ((CondensedRing.lowerStar R g).mapIso ((CondensedRing.comapLowerStarIso a f).app N))
    ((CondensedRing.lowerStarComp R f g).app _)
    (CondensedRing.comapLowerStarIso_hom_app_lowerStarComp R f g a N)

/-- Transport of direct images along an equality of morphisms commutes with the inverse
restriction comparisons. -/
@[reassoc]
theorem comapLowerStarIso_inv_app_comp_lowerStarCongr
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X Z : Scheme.{u}} {v w : X ⟶ Z} (e : v = w) (N : Modules T X) :
    (CondensedRing.comapLowerStarIso a v).inv.app N ≫
        (Mod.comap (coefficientMap a Z)).map ((CondensedRing.lowerStarCongr T e).hom.app N) =
      (CondensedRing.lowerStarCongr R e).hom.app ((Mod.comap (coefficientMap a X)).obj N) ≫
        (CondensedRing.comapLowerStarIso a w).inv.app N := by
  subst e
  simp [CondensedRing.lowerStarCongr]


/-- The conjugate of the composition comparison of a commutative square of inverse images
is the corresponding comparison of module direct images. -/
theorem conjugateEquiv_upperStarSquare_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {hX : X' ⟶ X} {hS : S' ⟶ S}
    (h : f' ≫ hS = hX ≫ f) (M : Modules Λ X') :
    (conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
          (CondensedRing.upperStarLowerStarAdjunction Λ hX))
        ((CondensedRing.upperStarLowerStarAdjunction Λ hS).comp
          (CondensedRing.upperStarLowerStarAdjunction Λ f'))
        ((CondensedRing.upperStarComp Λ f' hS).symm ≪≫ CondensedRing.upperStarCongr Λ h ≪≫
          CondensedRing.upperStarComp Λ hX f).hom).app M =
      (CondensedRing.lowerStarComp Λ hX f).hom.app M ≫
        (CondensedRing.lowerStarCongr Λ h.symm).hom.app M ≫
        (CondensedRing.lowerStarComp Λ f' hS).inv.app M := by
  have h₁ : conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ hX))
      (CondensedRing.upperStarLowerStarAdjunction Λ (hX ≫ f))
      (CondensedRing.upperStarComp Λ hX f).hom = (CondensedRing.lowerStarComp Λ hX f).hom :=
    congrArg Iso.hom (CondensedRing.conjugateIsoEquiv_upperStarComp Λ hX f)
  have h₂ : conjugateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ (hX ≫ f))
      (CondensedRing.upperStarLowerStarAdjunction Λ (f' ≫ hS))
      (CondensedRing.upperStarCongr Λ h).hom = (CondensedRing.lowerStarCongr Λ h.symm).hom := by
    rw [← CondensedRing.lowerStarCongr_symm]
    exact congrArg Iso.hom (CondensedRing.conjugateIsoEquiv_upperStarCongr Λ h)
  have h₃ : conjugateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ (f' ≫ hS))
      ((CondensedRing.upperStarLowerStarAdjunction Λ hS).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f'))
      (CondensedRing.upperStarComp Λ f' hS).inv = (CondensedRing.lowerStarComp Λ f' hS).inv :=
    congrArg Iso.inv (CondensedRing.conjugateIsoEquiv_upperStarComp Λ f' hS)
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp _ (CondensedRing.upperStarLowerStarAdjunction Λ (f' ≫ hS)),
    ← conjugateEquiv_comp _ (CondensedRing.upperStarLowerStarAdjunction Λ (hX ≫ f)),
    h₁, h₂, h₃]
  rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc]

/-- The conjugate composition comparison of a commutative square commutes with
restriction of scalars along the coefficient change. -/
theorem comapLowerStarIso_conjugate_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {hX : X' ⟶ X} {hS : S' ⟶ S} (h : f' ≫ hS = hX ≫ f) (N : Modules T X') :
    (CondensedRing.comapLowerStarIso a f).inv.app ((CondensedRing.lowerStar T hX).obj N) ≫
        (Mod.comap (coefficientMap a S)).map
          ((conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction T f).comp
              (CondensedRing.upperStarLowerStarAdjunction T hX))
            ((CondensedRing.upperStarLowerStarAdjunction T hS).comp
              (CondensedRing.upperStarLowerStarAdjunction T f'))
            ((CondensedRing.upperStarComp T f' hS).symm ≪≫ CondensedRing.upperStarCongr T h ≪≫
              CondensedRing.upperStarComp T hX f).hom).app N) ≫
        (CondensedRing.comapLowerStarIso a hS).hom.app ((CondensedRing.lowerStar T f').obj N) =
      (CondensedRing.lowerStar R f).map ((CondensedRing.comapLowerStarIso a hX).hom.app N) ≫
        (conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction R f).comp
            (CondensedRing.upperStarLowerStarAdjunction R hX))
          ((CondensedRing.upperStarLowerStarAdjunction R hS).comp
            (CondensedRing.upperStarLowerStarAdjunction R f'))
          ((CondensedRing.upperStarComp R f' hS).symm ≪≫ CondensedRing.upperStarCongr R h ≪≫
            CondensedRing.upperStarComp R hX f).hom).app
          ((Mod.comap (coefficientMap a X')).obj N) ≫
        (CondensedRing.lowerStar R hS).map ((CondensedRing.comapLowerStarIso a f').inv.app N) := by
  rw [conjugateEquiv_upperStarSquare_app, conjugateEquiv_upperStarSquare_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [comapLowerStarIso_inv_app_comp_lowerStarComp_assoc a hX f N,
    comapLowerStarIso_inv_app_comp_lowerStarCongr_assoc a h.symm N,
    comapLowerStarIso_inv_app_comp_lowerStarComp_inv a f' hS N]

/-- The coefficient change commutes with the adjoints of the coefficient-unit pullback
endpoints. -/
theorem coefficient_unitPull_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X X' : Scheme.{u}} {p : X' ⟶ X}
    (cR : UnitPullEndpoint R p) (cT : UnitPullEndpoint T p)
    (v : Semilinear a (Mod.regular (condensedRingObj R X)) (Mod.regular (condensedRingObj T X))
      (coefficientMap a X))
    (v' : Semilinear a (Mod.regular (condensedRingObj R X')) (Mod.regular (condensedRingObj T X'))
      (coefficientMap a X')) :
    v.hom ≫ (Mod.comap (coefficientMap a X)).map
        ((CondensedRing.upperStarLowerStarAdjunction T p).homEquiv _ _ cT.iso.hom) ≫
        (CondensedRing.comapLowerStarIso a p).hom.app (Mod.regular (condensedRingObj T X')) =
      (CondensedRing.upperStarLowerStarAdjunction R p).homEquiv _ _ cR.iso.hom ≫
        (CondensedRing.lowerStar R p).map v'.hom := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.comap_map_hom, CondensedRing.lowerStar_map_hom,
    CondensedRing.comapLowerStarIso_hom_app_hom, UnitPullEndpoint.homEquiv_iso_hom_hom,
    v.underlying, v'.underlying]
  erw [Category.comp_id]
  exact (condensedPushforwardHom_comp_map_coefficientMap a p).symm

/-- The transposed supported-source square for a commutative square of schemes: pushing
the coefficient map forward and then pulling back agrees with pulling back and then pushing
the primed coefficient map forward. -/
theorem coefficient_conjugate_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {hX : X' ⟶ X} {hS : S' ⟶ S} (h h₀ : f' ≫ hS = hX ≫ f)
    (cR : UnitPullEndpoint R hX) (cT : UnitPullEndpoint T hX)
    (v : Semilinear a (Mod.regular (condensedRingObj R X)) (Mod.regular (condensedRingObj T X))
      (coefficientMap a X))
    (v' : Semilinear a (Mod.regular (condensedRingObj R X')) (Mod.regular (condensedRingObj T X'))
      (coefficientMap a X')) :
    ((CondensedRing.lowerStar R f).map v.hom ≫
        (CondensedRing.comapLowerStarIso a f).inv.app (Mod.regular (condensedRingObj T X))) ≫
      (Mod.comap (coefficientMap a S)).map
        ((CondensedRing.lowerStar T f).map
            ((CondensedRing.upperStarLowerStarAdjunction T hX).homEquiv _ _ cT.iso.hom) ≫
          (conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction T f).comp
              (CondensedRing.upperStarLowerStarAdjunction T hX))
            ((CondensedRing.upperStarLowerStarAdjunction T hS).comp
              (CondensedRing.upperStarLowerStarAdjunction T f'))
            ((CondensedRing.upperStarComp T f' hS).symm ≪≫ CondensedRing.upperStarCongr T h ≪≫
              CondensedRing.upperStarComp T hX f).hom).app
            (Mod.regular (condensedRingObj T X'))) ≫
      (CondensedRing.comapLowerStarIso a hS).hom.app
        ((CondensedRing.lowerStar T f').obj (Mod.regular (condensedRingObj T X'))) =
    ((CondensedRing.lowerStar R f).map
          ((CondensedRing.upperStarLowerStarAdjunction R hX).homEquiv _ _ cR.iso.hom) ≫
        (conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction R f).comp
            (CondensedRing.upperStarLowerStarAdjunction R hX))
          ((CondensedRing.upperStarLowerStarAdjunction R hS).comp
            (CondensedRing.upperStarLowerStarAdjunction R f'))
          ((CondensedRing.upperStarComp R f' hS).symm ≪≫ CondensedRing.upperStarCongr R h₀ ≪≫
            CondensedRing.upperStarComp R hX f).hom).app
          (Mod.regular (condensedRingObj R X'))) ≫
      (CondensedRing.lowerStar R hS).map
        ((CondensedRing.lowerStar R f').map v'.hom ≫
          (CondensedRing.comapLowerStarIso a f').inv.app
            (Mod.regular (condensedRingObj T X'))) := by
  obtain rfl : h = h₀ := rfl
  have n₁ := (CondensedRing.comapLowerStarIso a f).inv.naturality
    (((CondensedRing.upperStarLowerStarAdjunction T hX).homEquiv _ _) cT.iso.hom)
  have n₂ := (conjugateEquiv ((CondensedRing.upperStarLowerStarAdjunction R f).comp
      (CondensedRing.upperStarLowerStarAdjunction R hX))
    ((CondensedRing.upperStarLowerStarAdjunction R hS).comp
      (CondensedRing.upperStarLowerStarAdjunction R f'))
    ((CondensedRing.upperStarComp R f' hS).symm ≪≫ CondensedRing.upperStarCongr R h ≪≫
      CondensedRing.upperStarComp R hX f).hom).naturality v'.hom
  simp only [Functor.comp_map] at n₁ n₂
  rw [Category.assoc, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ← reassoc_of% n₁, comapLowerStarIso_conjugate_square a h, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, coefficient_unitPull_square a cR cT v v',
    Functor.map_comp_assoc, reassoc_of% n₂]

/-- Naturality of the exact inverse-image single comparison. -/
@[reassoc]
theorem singlePullback_naturality (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) {M M' : Modules R S}
    (φ : M ⟶ M') :
    (derivedUpper R f).map ((DerivedCategory.singleFunctor (Modules R S) 0).map φ) ≫
        (singlePullback R f M').hom =
      (singlePullback R f M).hom ≫
        (DerivedCategory.singleFunctor (Modules R X) 0).map
          ((CondensedRing.upperStar R f).map φ) := by
  unfold derivedUpper singlePullback
  exact (Functor.singleFunctorCompLeftDerivedFunctorIso _).hom.naturality φ

/-- The underived supported-source square: restricting the pulled-back supported scalar
map and the supported pullback agree with the supported pullback followed by the primed
supported scalar map. -/
theorem upperStar_supportMap_comp_supported
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L₀ : ∀ X : Scheme.{u}, Modules R X) (L : ∀ X : Scheme.{u}, Modules T X)
    (m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X)
    (m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (s₀ : SourcePullback R g L₀ m₀P m₀W) (s : SourcePullback T g L mP mW)
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (c' : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      (coefficientMap a (ProjectiveLine Y')))
    (e : Endpoint a (source R Y) (source T Y) (supportMap a Y c.semilinear.hom).hom)
    (e' : Endpoint a (source R Y') (source T Y') (supportMap a Y' c'.semilinear.hom).hom) :
    (CondensedRing.upperStar R (baseW g)).map e.semilinear.hom ≫
      (CondensedRing.comapUpperStarIso a (baseW g)).inv.app (source T Y) ≫
      (Mod.comap (coefficientMap a (diagonalSurface Y'))).map s.supported.hom =
    s₀.supported.hom ≫ e'.semilinear.hom := by
  apply ((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_comapUpperStarIso_inv_app_comp,
    Adjunction.homEquiv_naturality_right, s.supported_normalization,
    s₀.supported_normalization]
  unfold sourcePullbackMap
  rw [ordinaryExchange_eq_exchangeRight, ordinaryExchange_eq_exchangeRight,
    homEquiv_exchangeRight_app_comp _ _ _
      (CondensedRing.upperStarLowerStarAdjunction T (baseP g)),
    homEquiv_exchangeRight_app_comp _ _ _
      (CondensedRing.upperStarLowerStarAdjunction R (baseP g))]
  rw [Mod.hom_ext _ _ e.semilinear.underlying, Mod.hom_ext _ _ e'.semilinear.underlying,
    supportMap, supportMap]
  exact coefficient_conjugate_square a s.geometry.diagonal_square s₀.geometry.diagonal_square
    s₀.endpoints.cP s.endpoints.cP c.semilinear c'.semilinear

/-- The inverse of the exact restriction/pullback comparison on a degree-zero module is
the ordinary restriction/pullback comparison, under the single comparisons. -/
@[reassoc]
theorem scalarRestrictionPullbackIso_inv_app_single
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S) (N : Modules T S) :
    (derivedUpper R f).map
        (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (scalarRestrictionPullbackIso a f).inv.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        (singlePullback T f N).hom =
    (singlePullback R f ((Mod.comap (coefficientMap a S)).obj N)).hom ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app N) ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app
        ((CondensedRing.upperStar T f).obj N) := by
  have h := exact_square_single (CondensedRing.upperStar R f) (CondensedRing.upperStar T f)
    (Mod.comap (coefficientMap a S)) (Mod.comap (coefficientMap a X))
    (CondensedRing.comapUpperStarIso a f) N
  unfold scalarRestrictionPullbackIso derivedUpper singlePullback
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [NatTrans.naturality_assoc]
  unfold CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    Functor.singleFunctorCompLeftDerivedFunctorIso
  simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  congr 1
  exact inv_square ((CondensedRing.derivedComapUpperStarIso a f).app _)
    ((CondensedRing.upperStar R f).mapDerivedCategory.mapIso
      (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).app N))
    (((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).app _) _
    (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).app _)
    ((DerivedCategory.singleFunctor (Modules R X) 0).mapIso
      ((CondensedRing.comapUpperStarIso a f).app N)) h

/-- Supported coefficient endpoints commute with geometric inverse image under the
scalar mate. The coefficient change is arbitrary; no positive line or diagonal class
occurs in the equation, and no diagram or trace compatibility is assumed. -/
theorem diagonalSupported_pullbackScalarNormalization
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L₀ : ∀ X : Scheme.{u}, Modules R X) (L : ∀ X : Scheme.{u}, Modules T X)
    (m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X)
    (m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (s₀ : SourcePullback R g L₀ m₀P m₀W) (s : SourcePullback T g L mP mW)
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (c' : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      (coefficientMap a (ProjectiveLine Y')))
    (e : Endpoint a (source R Y) (source T Y) (supportMap a Y c.semilinear.hom).hom)
    (e' : Endpoint a (source R Y') (source T Y') (supportMap a Y' c'.semilinear.hom).hom) :
    (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map e.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          s₀.supported.hom) ≫ e'.iso.hom := by
  unfold derivedScalars scalarPullbackComparison
  apply ((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a (diagonalSurface Y'))).homEquiv _ _).injective
  rw [mate_transpose, Adjunction.homEquiv_naturality_left, e'.normalization, e.normalization,
    Functor.map_comp, Functor.map_comp, Category.assoc,
    scalarRestrictionPullbackIso_inv_app_single_assoc, singlePullback_naturality_assoc]
  erw [← NatTrans.naturality]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [Functor.comp_map, ← Functor.map_comp_assoc, Category.assoc,
    upperStar_supportMap_comp_supported a g L₀ L m₀P m₀W mP mW s₀ s c c' e e']

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
