/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.CategoryTheory.ExactDegreeZero

public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.NormalizedEtaleOriginWitnesses
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Data.Finite.Defs
import Sheaf.AlgebraicGeometry.SupportedKummerScalarSource
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Derived scalar extension for a supported constant sheaf

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md,
paragraph 4; Stacks Project, Tags 07A6, 0D6D and 0G7E.
(blueprint: lem-geo-cartier-coeff-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The ordinary direct image of the constant rank-one module on a closed subscheme.
Source: Stacks Tag 03QP(1), used in the coefficient-extension comparison.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedConstantModule {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- Push forward the coefficient unit on `D`. The constant-sheaf adjunction sends the
generator `1` of `A` to the constant section `1` of `B`, with the A-action restricted
along `φ`; hence a constant section `a` goes to `φ a`.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def coefficientUnitModule {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantModule (A := A) i ⟶
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantModule (A := B) i) := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let x : (((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
      ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)))) :=
    (constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} B) hT).unit.app
      (ModuleCat.of B B) (1 : B)
  let h : ModuleCat.of A A ⟶
      ((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
        ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) :=
    ModuleCat.ofHom
      (Y := ((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
        ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))))
      (LinearMap.toSpanSingleton A
        (((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
          ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
              (ModuleCat.of B B)))) x)
  let k : (constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)) :=
    (constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A) hT).homEquiv _ _ |>.symm h
  exact (lowerStar (ModuleCat.{u + 1} A) i).map k ≫
    (lowerStarRestrictScalarsIso φ i).inv.app
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))

/-- The degree-zero derived object underlying `i_* A_D`.
Source: Stacks Tag 03QP(1), used in the coefficient-extension comparison.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedConstantDerived {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  SheafExactDegreeZero.scalarObj Z.smallEtaleTopology A (supportedConstantModule i)

/-- The degree-zero image of the specified direct-image coefficient unit, transported
by the canonical compatibility of exact restriction with the single functor.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def coefficientUnitDerived {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantDerived (A := A) i ⟶
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantDerived (A := B) i) :=
  SheafExactDegreeZero.scalarUnit Z.smallEtaleTopology φ
    (supportedConstantModule (A := A) i) (supportedConstantModule (A := B) i)
    (coefficientUnitModule φ i)

/-- The specified comparison is the adjunct of the actual direct-image coefficient unit.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedCoefficientComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology φ).obj
      (supportedConstantDerived (A := A) i) ⟶ supportedConstantDerived (A := B) i :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).homEquiv
        (supportedConstantDerived (A := A) i) (supportedConstantDerived (A := B) i)).symm
    (coefficientUnitDerived φ i)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private noncomputable def constantCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (D : Scheme.{u}) :
    (constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)) :=
  ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _).symm
      (ModuleCat.ofHom
        (Y := ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
            (ModuleCat.of B B))).obj.obj (op (Scheme.Etale.mk (𝟙 D))))
        (LinearMap.toSpanSingleton A _
        ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} B)
          (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of B B) (1 : B))))

private theorem constantCoefficientMap_generator_top
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (D : Scheme.{u}) (a : A) :
    (constantCoefficientMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
      ((toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.Etale.mk (𝟙 D))) a) =
      (toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
          (op (Scheme.Etale.mk (𝟙 D))) (φ a) := by
  let adj := constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal _ _)
  have h := (adj.homEquiv (ModuleCat.of A A)
    ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)))).apply_symm_apply
    (ModuleCat.ofHom
        (Y := ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
            (ModuleCat.of B B))).obj.obj (op (Scheme.Etale.mk (𝟙 D))))
        (LinearMap.toSpanSingleton A _
      ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} B)
        (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of B B) (1 : B))))
  have h' := congrArg (fun f ↦ f a) h
  change (constantCoefficientMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
    ((toSheafify D.smallEtaleTopology
      ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
        (op (Scheme.Etale.mk (𝟙 D))) a) =
    (φ a) • ((toSheafify D.smallEtaleTopology
      ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
        (op (Scheme.Etale.mk (𝟙 D))) (1 : B)) at h'
  rw [h', ← map_smul]
  congr 1
  simp only [smul_eq_mul, mul_one]

private noncomputable abbrev constantSection
    (A : Type (u + 1)) [CommRing A] (D : Scheme.{u}) (U : D.Etaleᵒᵖ) (a : A) :
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)).obj.obj U :=
  ((toSheafify D.smallEtaleTopology
    ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U) a

private theorem constantSheaf_ext_top
    {A : Type (u + 1)} [CommRing A] (D : Scheme.{u})
    {F : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f g : (constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A) ⟶ F)
    (h : f.hom.app (op (Scheme.Etale.mk (𝟙 D)))
        (constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1) =
      g.hom.app (op (Scheme.Etale.mk (𝟙 D)))
        (constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1)) : f = g := by
  apply ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv (ModuleCat.of A A) F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

private theorem coefficientUnitModule_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    coefficientUnitModule φ i =
      (lowerStar (ModuleCat.{u + 1} A) i).map (constantCoefficientMap φ D) := by
  unfold coefficientUnitModule
  change (lowerStar (ModuleCat.{u + 1} A) i).map (constantCoefficientMap φ D) ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem constantCoefficientMap_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (D : Scheme.{u}) :
    constantCoefficientMap (ψ.comp φ) D = constantCoefficientMap φ D ≫
      (Sheaf.restrictScalars D.smallEtaleTopology φ).map (constantCoefficientMap ψ D) ≫
      (Sheaf.restrictScalarsCompIso D.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} C)).obj
          (ModuleCat.of C C)) := by
  apply constantSheaf_ext_top D
  change (constantCoefficientMap (ψ.comp φ) D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
    (constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1) =
    (constantCoefficientMap ψ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
      ((constantCoefficientMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
        (constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1))
  rw [constantCoefficientMap_generator_top, constantCoefficientMap_generator_top,
    constantCoefficientMap_generator_top]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientUnitModule_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    coefficientUnitModule (ψ.comp φ) i = coefficientUnitModule φ i ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).map (coefficientUnitModule ψ i) ≫
      (Sheaf.restrictScalarsCompIso Z.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (supportedConstantModule (A := C) i) := by
  simp only [coefficientUnitModule_eq]
  rw [constantCoefficientMap_comp, Functor.map_comp, Functor.map_comp]
  rfl

attribute [local irreducible] coefficientUnitModule constantCoefficientMap
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientUnitDerived_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    coefficientUnitDerived (ψ.comp φ) i = coefficientUnitDerived φ i ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map (coefficientUnitDerived ψ i) ≫
      (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl).hom.app
        (supportedConstantDerived (A := C) i) := by
  unfold coefficientUnitDerived supportedConstantDerived
    SheafExactDegreeZero.scalarUnit SheafExactDegreeZero.scalarObj
  have hh := SheafExactDegreeZero.unit_comp
    (V := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} C))
    (W := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))
    (X := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Sheaf.restrictScalars Z.smallEtaleTopology ψ)
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (Sheaf.restrictScalars Z.smallEtaleTopology (ψ.comp φ))
    (Sheaf.restrictScalarsCompIso Z.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology (f := φ) (g := ψ) rfl) rfl
    (K := supportedConstantModule (A := A) i)
    (L := supportedConstantModule (A := B) i)
    (M := supportedConstantModule (A := C) i)
    (coefficientUnitModule φ i) (coefficientUnitModule ψ i)
    (coefficientUnitModule (ψ.comp φ) i) (coefficientUnitModule_comp φ ψ i)
  exact hh

private theorem constantCoefficientMap_id
    (A : Type (u + 1)) [CommRing A] (D : Scheme.{u}) :
    constantCoefficientMap (RingHom.id A) D =
      (AlgebraicGeometry.ProEtale.normalizedOriginRestrictionUnit D.smallEtaleTopology
        (RingHom.id A) rfl).inv.app
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)) := by
  apply constantSheaf_ext_top D
  change (constantCoefficientMap (RingHom.id A) D).hom.app
    (op (Scheme.Etale.mk (𝟙 D)))
      (constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1) =
    constantSection A D (op (Scheme.Etale.mk (𝟙 D))) 1
  exact constantCoefficientMap_generator_top (RingHom.id A) D 1

private theorem coefficientUnitModule_id
    (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    coefficientUnitModule (RingHom.id A) i =
      (AlgebraicGeometry.ProEtale.normalizedOriginRestrictionUnit Z.smallEtaleTopology
        (RingHom.id A) rfl).inv.app (supportedConstantModule (A := A) i) := by
  rw [coefficientUnitModule_eq, constantCoefficientMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientUnitDerived_id
    (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    coefficientUnitDerived (RingHom.id A) i =
      (Functor.mapDerivedCategoryNatIso
        (AlgebraicGeometry.ProEtale.normalizedOriginRestrictionUnit Z.smallEtaleTopology
          (RingHom.id A) rfl) ≪≫ Functor.mapDerivedCategoryIdIso _).inv.app
            (supportedConstantDerived (A := A) i) := by
  unfold coefficientUnitDerived supportedConstantDerived
    SheafExactDegreeZero.scalarUnit SheafExactDegreeZero.scalarObj
  have hh := SheafExactDegreeZero.unit_id
    (V := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Sheaf.restrictScalars Z.smallEtaleTopology (RingHom.id A))
    (AlgebraicGeometry.ProEtale.normalizedOriginRestrictionUnit Z.smallEtaleTopology
      (RingHom.id A) rfl) (supportedConstantModule (A := A) i)
    (coefficientUnitModule (RingHom.id A) i) (coefficientUnitModule_id A i)
  exact hh

private theorem adjunct_isIso
    {V W : Type*} [Category V] [Category W]
    {L : V ⥤ W} {R : W ⥤ V} (adj : L ⊣ R)
    {X : V} {Y : W} (η : X ⟶ R.obj Y)
    (h : ∀ N, Function.Bijective (fun f : Y ⟶ N ↦ η ≫ R.map f)) :
    IsIso ((adj.homEquiv X Y).symm η) := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  apply (Function.Bijective.of_comp_iff' (adj.homEquiv X N).bijective _).mp
  convert h N using 1
  funext g
  dsimp only [Function.comp_def]
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]

private theorem universalArrow_cancel
    {V W X : Type*} [Category V] [Category W] [Category X]
    (R : W ⥤ V) (S : X ⥤ W) (T : X ⥤ V) (e : S ⋙ R ≅ T)
    {K : V} {L : W} {M : X} (η : K ⟶ R.obj L) (θ : L ⟶ S.obj M)
    (hη : ∀ N, Function.Bijective (fun f : L ⟶ N ↦ η ≫ R.map f))
    (hηθ : ∀ N, Function.Bijective (fun f : M ⟶ N ↦
      (η ≫ R.map θ ≫ e.hom.app M) ≫ T.map f)) :
    ∀ N, Function.Bijective (fun f : M ⟶ N ↦ θ ≫ S.map f) := by
  intro N
  let outer : (L ⟶ S.obj N) → (K ⟶ T.obj N) :=
    fun f ↦ η ≫ R.map f ≫ e.hom.app N
  have ho : Function.Bijective outer := by
    convert ((e.app N).homToEquiv (Z := K)).bijective.comp (hη _) using 1
    funext f
    exact (Category.assoc _ _ _).symm
  apply (Function.Bijective.of_comp_iff' ho _).mp
  convert hηθ N using 1
  funext g
  dsimp only [outer, Function.comp_def]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality g
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  apply congrArg (η ≫ ·)
  apply congrArg (R.map θ ≫ ·)
  exact hn

private theorem adjunct_id
    {V : Type*} [Category V] {L R : V ⥤ V} (adj : L ⊣ R) (e : R ≅ 𝟭 V)
    (X : V) (η : X ⟶ R.obj X) (hη : η = e.inv.app X) :
    (adj.homEquiv X X).symm η = (Adjunction.leftAdjointIdIso adj e).hom.app X := by
  apply (adj.homEquiv X X).injective
  rw [Equiv.apply_symm_apply, hη]
  have hu := unit_conjugateEquiv_symm Adjunction.id adj e.inv X
  rw [Adjunction.homEquiv_unit]
  change e.inv.app X = adj.unit.app X ≫
    R.map (((conjugateEquiv Adjunction.id adj).symm e.inv).app X)
  change (𝟙 X) ≫ e.inv.app X = _ at hu
  simpa only [Category.id_comp] using hu

private theorem adjunct_comp
    {V W X : Type*} [Category V] [Category W] [Category X]
    {L₁ : V ⥤ W} {R₁ : W ⥤ V} {L₂ : W ⥤ X} {R₂ : X ⥤ W}
    {L₃ : V ⥤ X} {R₃ : X ⥤ V}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃)
    {K : V} {M : W} {N : X}
    (η : K ⟶ R₁.obj M) (θ : M ⟶ R₂.obj N) (ζ : K ⟶ R₃.obj N)
    (hζ : ζ = η ≫ R₁.map θ ≫ e.hom.app N) :
    L₂.map ((a.homEquiv K M).symm η) ≫ (b.homEquiv M N).symm θ =
      (Adjunction.leftAdjointCompIso a b c e).hom.app K ≫ (c.homEquiv K N).symm ζ := by
  let t := Adjunction.leftAdjointCompIso a b c e
  have hu := unit_conjugateEquiv_symm c (a.comp b) e.inv K
  change c.unit.app _ ≫ e.inv.app _ = (a.comp b).unit.app _ ≫
    (R₂ ⋙ R₁).map (t.hom.app _) at hu
  apply ((a.comp b).homEquiv K N).injective
  have hl : ((a.comp b).homEquiv K N)
      (L₂.map ((a.homEquiv K M).symm η) ≫ (b.homEquiv M N).symm θ) =
      η ≫ R₁.map θ := by
    rw [Adjunction.comp_homEquiv]
    change (a.homEquiv K (R₂.obj N)) ((b.homEquiv (L₁.obj K) N)
      (L₂.map ((a.homEquiv K M).symm η) ≫ (b.homEquiv M N).symm θ)) = _
    rw [b.homEquiv_naturality_left, Equiv.apply_symm_apply,
      a.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [hl]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu, Category.assoc]
  rw [← e.inv.naturality]
  rw [← Category.assoc, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, hζ]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem supportedResidue_isDerivedBaseChange
    (N : ℕ) (hN : 1 ≤ N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Sheaf.IsDerivedBaseChange (coefficientUnitDerived (supportedScalarMap N A hA) i) := by
  obtain ⟨ηD, ηZ, hηD, _, _, hη, _, _⟩ := supported_kummer_scalar_source Z N hN A hA i
  have he : ηD = constantCoefficientMap (supportedScalarMap N A hA) D := by
    apply constantSheaf_ext_top D
    exact (hηD (op (Scheme.Etale.mk (𝟙 D))) 1).trans
      (constantCoefficientMap_generator_top (supportedScalarMap N A hA) D 1).symm
  have hm : (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map
      ηD ≫
      (lowerStarCompRestrictScalarsIso (supportedScalarMap N A hA) i).inv.app
        (ordinaryFiniteConstant A D) =
      coefficientUnitModule (supportedScalarMap N A hA) i := by
    rw [he, coefficientUnitModule_eq]
    exact Category.comp_id _
  rw [hm] at hη
  unfold SupportedDerivedScalarUnit at hη
  exact hη

private theorem derivedBaseChange_cancel
    {R A B : Type (u + 1)} [CommRing R] [CommRing A] [CommRing B]
    (χ : R →+* A) (φ : A →+* B) (Z : Scheme.{u})
    {K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {L : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (η : K ⟶ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology χ).obj L)
    (θ : L ⟶ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj M)
    (hη : Sheaf.IsDerivedBaseChange η)
    (hηθ : Sheaf.IsDerivedBaseChange
      (η ≫ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology χ).map θ ≫
        (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl).hom.app M)) :
    Sheaf.IsDerivedBaseChange θ := by
  exact universalArrow_cancel
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology χ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology (φ.comp χ))
    (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl) η θ hη hηθ

private theorem coefficientUnitDerived_isDerivedBaseChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Sheaf.IsDerivedBaseChange (coefficientUnitDerived φ i) := by
  let N := ringChar A
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (CharP.char_ne_zero_of_finite A N)
  have hA : (N : A) = 0 := CharP.cast_eq_zero A (ringChar A)
  have hB : (N : B) = 0 := by
    rw [← map_natCast φ, hA, map_zero]
  let χ := supportedScalarMap N A hA
  have hχ : supportedScalarMap N B hB = φ.comp χ := by
    have hh : (supportedScalarMap N B hB).comp ULift.ringEquiv.symm.toRingHom =
        (φ.comp χ).comp ULift.ringEquiv.symm.toRingHom := Subsingleton.elim _ _
    ext x
    exact DFunLike.congr_fun hh x.down
  apply derivedBaseChange_cancel χ φ Z (coefficientUnitDerived χ i)
    (coefficientUnitDerived φ i) (supportedResidue_isDerivedBaseChange N hN A hA i)
  rw [← coefficientUnitDerived_comp, ← hχ]
  exact supportedResidue_isDerivedBaseChange N hN B hB i

private theorem supportedCoefficientComparison_isIso_of_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (h : Sheaf.IsDerivedBaseChange (coefficientUnitDerived φ i)) :
    IsIso (supportedCoefficientComparison φ i) := by
  exact adjunct_isIso (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)) (coefficientUnitDerived φ i) h

private theorem supportedCoefficientComparison_id
    (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedCoefficientComparison (RingHom.id A) i =
      (AlgebraicGeometry.ProEtale.normalizedOriginScalarUnit Z.smallEtaleTopology
        (RingHom.id A) rfl).hom.app (supportedConstantDerived (A := A) i) := by
  exact adjunct_id (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology (RingHom.id A)))
    (Functor.mapDerivedCategoryNatIso
      (AlgebraicGeometry.ProEtale.normalizedOriginRestrictionUnit Z.smallEtaleTopology
        (RingHom.id A) rfl) ≪≫ Functor.mapDerivedCategoryIdIso _)
    (supportedConstantDerived (A := A) i) (coefficientUnitDerived (RingHom.id A) i)
    (coefficientUnitDerived_id A i)

private theorem supportedCoefficientComparison_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology ψ).map
        (supportedCoefficientComparison φ i) ≫ supportedCoefficientComparison ψ i =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology
        φ ψ (ψ.comp φ) rfl).hom.app (supportedConstantDerived (A := A) i) ≫
          supportedCoefficientComparison (ψ.comp φ) i := by
  exact adjunct_comp
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology (ψ.comp φ)))
    (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl)
    (coefficientUnitDerived φ i) (coefficientUnitDerived ψ i)
    (coefficientUnitDerived (ψ.comp φ) i) (coefficientUnitDerived_comp φ ψ i)

/-- Derived scalar extension of the supported constant sheaf along finite coefficients is the
specified adjunct of the coefficient-unit map.  It is an isomorphism, natural in the coefficient
map, normalized to the identity coefficient map, and coherent under successive extensions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, paragraph 4; Stacks Project, Tags 07A6, 0D6D and 0G7E.
Proof:
1. The constant-sheaf adjunction determines the coefficient map by the image of 1
at the terminal etale object. Evaluating its unit proves that a maps to φ(a).
These formulas give the identity and composition laws for the ordinary units.
2. Put N = ringChar A, which is positive for a finite ring, including the zero ring.
Both A and B are killed by N. Apply lem-asd-supported-kummer-scalar-source to
ULift(ZMod N) → A and ULift(ZMod N) → B. Its generator normalization identifies
the ordinary maps with the coefficient units constructed here.
3. The map ULift(ZMod N) → B is the composite through A, by uniqueness of a ring
map from ZMod N. Cancel the universal arrow for ULift(ZMod N) → A from the one
for ULift(ZMod N) → B. This gives the unbounded derived universal property for
A → B; the adjunction and Yoneda then make its specified adjunct an isomorphism.
4. The exact degree-zero comparison preserves the ordinary identity and composition
laws, with the canonical derived restriction comparisons. The named interface
SheafExactDegreeZero keeps these constructions from unfolding their localization data.
5. Conjugation of adjunctions identifies the adjunct of the identity unit with
normalizedOriginScalarUnit and identifies composite adjuncts with
pbcFixedScalarExtensionComp. Thus the coefficient-unit composition law gives exactly
the displayed composition equation. Apply the universal-property argument to φ, ψ,
and ψ.comp φ.
(blueprint: lem-geo-cartier-coeff-extension) -/
theorem geoCartierCoeffExtension
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (φ : A →+* B) (ψ : B →+* C) :
    IsIso (supportedCoefficientComparison φ i) ∧
    IsIso (supportedCoefficientComparison ψ i) ∧
    IsIso (supportedCoefficientComparison (ψ.comp φ) i) ∧
    coefficientUnitDerived (ψ.comp φ) i = coefficientUnitDerived φ i ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map (coefficientUnitDerived ψ i) ≫
      (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl).hom.app
        (supportedConstantDerived (A := C) i) ∧
    supportedCoefficientComparison (RingHom.id A) i =
      (AlgebraicGeometry.ProEtale.normalizedOriginScalarUnit Z.smallEtaleTopology
        (RingHom.id A) rfl).hom.app (supportedConstantDerived (A := A) i) ∧
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology ψ).map
        (supportedCoefficientComparison φ i) ≫ supportedCoefficientComparison ψ i =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology
        φ ψ (ψ.comp φ) rfl).hom.app (supportedConstantDerived (A := A) i) ≫
          supportedCoefficientComparison (ψ.comp φ) i  := by
  exact ⟨supportedCoefficientComparison_isIso_of_universal φ i
      (coefficientUnitDerived_isDerivedBaseChange φ i),
    supportedCoefficientComparison_isIso_of_universal ψ i
      (coefficientUnitDerived_isDerivedBaseChange ψ i),
    supportedCoefficientComparison_isIso_of_universal (ψ.comp φ) i
      (coefficientUnitDerived_isDerivedBaseChange (ψ.comp φ) i),
    coefficientUnitDerived_comp φ ψ i, supportedCoefficientComparison_id A i,
    supportedCoefficientComparison_comp φ ψ i⟩

end AlgebraicGeometry.Etale
