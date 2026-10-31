/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Sites.FlatExtendScalars
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Finite-free scalar extension and the exceptional counit mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 1, counit-defined comparison.
(blueprint: lem-sf-finite-free-exceptional-mate)

Constant coefficients use module-valued sheaves, equivalently modules over the constant
ring sheaf by `constant_ring_module_sheaves`. The presentation below retains the universal
left-derived pair, its normalized scalar adjunction, and the specified basis coordinates.
No boundedness, nonzero rank, or nonzero ring condition is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w a b c d vA vB vC vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section Categorical
variable {CA : Type a} {CB : Type b} {DA : Type c} {DB : Type d}
  [Category.{vA} CA] [Category.{vB} CB] [Category.{vC} DA] [Category.{vD} DB]
  {TC : CA ⥤ CB} {UC : CB ⥤ CA} {TD : DA ⥤ DB} {UD : DB ⥤ DA}
  {FA : CA ⥤ DA} {GA : DA ⥤ CA} {FB : CB ⥤ DB} {GB : DB ⥤ CB}

/-- The representing isomorphism obtained from the successive scalar and given
adjunctions, transported along c. Source: blueprint finite-free-extension proof,
paragraph 1 (blueprint: lem-sf-finite-free-exceptional-mate). -/
@[irreducible] def finiteFreeExceptionalTheta (sC : TC ⊣ UC) (sD : TD ⊣ UD)
    (aA : FA ⊣ GA) (aB : FB ⊣ GB) (c : FA ⋙ TD ≅ TC ⋙ FB) :
    GB ⋙ UC ≅ UD ⋙ GA :=
  (sC.comp aB).rightAdjointUniq ((aA.comp sD).ofNatIsoLeft c)

/-- The counit mate, constructed without reference to a basis. Its component is
by definition the transpose of c inverse followed by scalar extension of the counit.
Source: blueprint finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate). -/
@[irreducible] def finiteFreeExceptionalMate (aA : FA ⊣ GA) (aB : FB ⊣ GB)
    (c : FA ⋙ TD ≅ TC ⋙ FB) : GA ⋙ TC ⟶ TD ⋙ GB :=
  (mateEquiv aA aB (TwoSquare.mk _ _ _ _ c.inv)).natTrans
/-- The successive representing Hom bijections, in their specified order.
Source: blueprint finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate). -/
def finiteFreeExceptionalHomMap (sC : TC ⊣ UC) (sD : TD ⊣ UD)
    (aA : FA ⊣ GA) (aB : FB ⊣ GB) (c : FA ⋙ TD ≅ TC ⋙ FB)
    (P : CA) (N : DB) (f : P ⟶ UC.obj (GB.obj N)) : P ⟶ GA.obj (UD.obj N) :=
  aA.homEquiv P _ (sD.homEquiv (FA.obj P) N
    (c.hom.app P ≫ (aB.homEquiv (TC.obj P) N).symm
      ((sC.homEquiv P (GB.obj N)).symm f)))

private theorem exceptionalTheta_hom (sC : TC ⊣ UC) (sD : TD ⊣ UD)
    (aA : FA ⊣ GA) (aB : FB ⊣ GB) (c : FA ⋙ TD ≅ TC ⋙ FB)
    (P : CA) (N : DB) (f : P ⟶ UC.obj (GB.obj N)) :
    f ≫ (finiteFreeExceptionalTheta sC sD aA aB c).hom.app N =
      finiteFreeExceptionalHomMap sC sD aA aB c P N f := by
  let a := sC.comp aB
  let b := (aA.comp sD).ofNatIsoLeft c
  unfold finiteFreeExceptionalTheta
  change f ≫ (a.rightAdjointUniq b).hom.app N = _
  have ht : b.homEquiv (UC.obj (GB.obj N)) N (a.counit.app N) =
      (a.rightAdjointUniq b).hom.app N := by
    apply (b.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (a.homEquiv_symm_rightAdjointUniq_hom_app b N).symm
  rw [← ht, ← b.homEquiv_naturality_left]
  change b.homEquiv P N ((a.homEquiv P N).symm f) = _
  simp only [a, b, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, Equiv.symm_trans_apply,
    finiteFreeExceptionalHomMap]
  rfl

private theorem exceptionalMate_counit (aA : FA ⊣ GA) (aB : FB ⊣ GB)
    (c : FA ⋙ TD ≅ TC ⋙ FB) (M : DA) :
    FB.map ((finiteFreeExceptionalMate aA aB c).app M) ≫
        aB.counit.app (TD.obj M) = c.inv.app (GA.obj M) ≫ TD.map (aA.counit.app M) := by
  unfold finiteFreeExceptionalMate
  exact mateEquiv_counit aA aB (TwoSquare.mk _ _ _ _ c.inv) M

private theorem exceptionalMate_unique (aA : FA ⊣ GA) (aB : FB ⊣ GB)
    (c : FA ⋙ TD ≅ TC ⋙ FB) (b' : GA ⋙ TC ⟶ TD ⋙ GB)
    (h : ∀ M, FB.map (b'.app M) ≫ aB.counit.app (TD.obj M) =
      c.inv.app (GA.obj M) ≫ TD.map (aA.counit.app M)) :
    b' = finiteFreeExceptionalMate aA aB c := by
  ext M
  apply (aB.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using
    (h M).trans (exceptionalMate_counit aA aB c M).symm

private theorem exceptionalMate_unit (sC : TC ⊣ UC) (sD : TD ⊣ UD)
    (aA : FA ⊣ GA) (aB : FB ⊣ GB) (c : FA ⋙ TD ≅ TC ⋙ FB) (M : DA) :
    sC.unit.app (GA.obj M) ≫ UC.map ((finiteFreeExceptionalMate aA aB c).app M) ≫
      (finiteFreeExceptionalTheta sC sD aA aB c).hom.app (TD.obj M) =
        GA.map (sD.unit.app M) := by
  rw [← Category.assoc, exceptionalTheta_hom sC sD aA aB c]
  unfold finiteFreeExceptionalHomMap
  dsimp only [Functor.id_obj]
  rw [← sC.homEquiv_unit]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, exceptionalMate_counit]
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.id_comp, sD.homEquiv_unit, sD.unit_naturality,
    aA.homEquiv_naturality_right]
  dsimp only [Functor.id_obj]
  rw [← aA.homEquiv_symm_id]
  rw [Equiv.apply_symm_apply, Category.id_comp]

end Categorical

/-- The finite-sum comparison with columns G of the standard inclusions.
Source: blueprint finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate). -/
@[irreducible] def finiteFreeExceptionalSumComparison
    {E : Type a} {F : Type b} [Category.{vA} E] [Category.{vB} F]
    [Preadditive E] [Preadditive F] [HasFiniteBiproducts E] [HasFiniteBiproducts F]
    (G : E ⥤ F) (r : ℕ) (M : E) :
    ⨁ (fun _ : Fin r ↦ G.obj M) ⟶ G.obj (⨁ (fun _ : Fin r ↦ M)) :=
  biproduct.desc (fun j : Fin r ↦ G.map (biproduct.ι (fun _ : Fin r ↦ M) j))

/-- The finite-sum comparison inverse has rows G of the standard projections.
Source: blueprint finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate). -/
@[irreducible] def finiteFreeExceptionalSumInverse
    {E : Type a} {F : Type b} [Category.{vA} E] [Category.{vB} F]
    [Preadditive E] [Preadditive F] [HasFiniteBiproducts E] [HasFiniteBiproducts F]
    (G : E ⥤ F) (r : ℕ) (M : E) :
    G.obj (⨁ (fun _ : Fin r ↦ M)) ⟶ ⨁ (fun _ : Fin r ↦ G.obj M) :=
  biproduct.lift (fun j : Fin r ↦ G.map (biproduct.π (fun _ : Fin r ↦ M) j))

/-- A presentation of the actual derived scalar functors and their canonical basis
coordinates. T and its counit form the universal left derived pair of sheafified tensor
extension; U is literally termwise exact restriction. The scalar adjunction is normalized
by the ordinary tensor unit on every complex. The basis columns are its unit followed
by multiplication by the basis element, fixing the coordinate isomorphism uniquely.
These are presentation data for the scalar functors in the statement, not an arbitrary
comparison or an additional invertibility hypothesis on the exceptional mate.
Source: Stacks 03CZ, 06YY, 07A6; blueprint finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate). -/
structure FiniteFreeExceptionalScalarPresentation
    {C : Type a} [Category.{vA} C] (J : GrothendieckTopology C)
    {A B : Type (max u a vA)} [CommRing A] [CommRing B] [Algebra A B]
    (r : ℕ) (basis : Module.Basis (Fin r) A B)
    [HasSheafify J (ModuleCat.{max u a vA} A)] [HasSheafify J (ModuleCat.{max u a vA} B)]
    [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} A))]
    [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} B))] where
  /-- The everywhere defined derived tensor extension. -/
  T : DerivedCategory (Sheaf J (ModuleCat.{max u a vA} A)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{max u a vA} B))
  /-- The universal cochain comparison. -/
  counit : DerivedCategory.Q ⋙ T ⟶
    (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA}
        (algebraMap A B))).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left-derived universal property fixes T up to its unique compatible isomorphism. -/
  universal : T.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{max u a vA} A)) (.up ℤ))
  /-- The scalar adjunction. -/
  adj : T ⊣ (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory
  /-- The scalar unit is induced by x mapping to 1 tensor x. -/
  unit_normalized : ∀ K : CochainComplex (Sheaf J (ModuleCat.{max u a vA} A)) ℤ,
    adj.unit.app (DerivedCategory.Q.obj K) ≫
      (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory.map (counit.app K) ≫
      (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryFactors.hom.app
        (((Sheaf.composeAndSheafify J
          (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA}
            (algebraMap A B))).mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (Sheaf.adjunction J
        (ModuleCat.extendRestrictScalarsAdj.{max u a vA, max u a vA, max u a vA}
          (algebraMap A B))).unit
        (.up ℤ)).app K)
  /-- The finite direct-sum coordinates, on all derived objects. -/
  coordinates : ∀ K : DerivedCategory (Sheaf J (ModuleCat.{max u a vA} A)),
    (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory.obj (T.obj K) ≅
      ⨁ (fun _ : Fin r ↦ K)
  /-- The j-th column is x mapping to b_j tensor x. -/
  column : ∀ (K : DerivedCategory (Sheaf J (ModuleCat.{max u a vA} A))) (j : Fin r),
    biproduct.ι (fun _ : Fin r ↦ K) j ≫ (coordinates K).inv =
      adj.unit.app K ≫ (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory.map
        (basis j • 𝟙 (T.obj K))

attribute [local instance] Abelian.hasFiniteBiproducts

section ScalarConstruction
variable {C : Type a} [Category.{vA} C] (J : GrothendieckTopology C)
  {A B : Type (max u a vA)} [CommRing A] [CommRing B] [Algebra A B]
  (r : ℕ) (basis : Module.Basis (Fin r) A B)
  [HasSheafify J (ModuleCat.{max u a vA} A)]
  [HasSheafify J (ModuleCat.{max u a vA} B)]
  [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} A))]
  [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} B))]

private def exceptionalRestrictedAlgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B ≃ₗ[A] (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' x y := Algebra.smul_def x y
  left_inv _ := rfl
  right_inv _ := rfl

omit [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} A))]
  [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a vA} B))] in
private theorem exceptionalOrdinaryBasis
    (F : Sheaf J (ModuleCat.{max u a vA} A)) :
    IsIso (biproduct.desc fun i : Fin r ↦
      (Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj
        (algebraMap A B))).unit.app F ≫
      (Sheaf.restrictScalars J (algebraMap A B)).map (basis i • 𝟙 _)) := by
  have : Module.Finite A B := Module.Finite.of_basis basis
  have : Module.Free A B := Module.Free.of_basis basis
  let φ := algebraMap A B
  let b' := basis.map (exceptionalRestrictedAlgebra (A := A) (B := B))
  -- `S ⊗_R F` is already a sheaf on sections, `S` being finite free
  have : PreservesLimits (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ) :=
    ModuleCat.preservesLimits_extendScalars_of_finite_projective φ
      (by rw [toAlgebra_algebraMap]; infer_instance)
      (by rw [toAlgebra_algebraMap]; infer_instance)
  have : PreservesLimitsOfSize.{vA, max a vA}
      (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ) :=
    preservesLimitsOfSize_shrink.{max a vA, max u a vA, vA, max u a vA}
      (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ)
  have : J.HasSheafCompose (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have hs : Presheaf.IsSheaf J
      (F.obj ⋙ ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ) :=
    ((sheafCompose J
      (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ)).obj F).property
  have : IsIso (toSheafify J
      (F.obj ⋙ ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ)) :=
    isIso_toSheafify _ hs
  -- the statement on sections
  have hU (U : Cᵒᵖ) : IsIso (biproduct.desc fun i ↦
      (ModuleCat.extendRestrictScalarsAdj.{max u a vA, max u a vA, max u a vA} φ).unit.app
        (F.obj.obj U) ≫
        (ModuleCat.restrictScalars.{max u a vA} φ).map
          (ModuleCat.restrictScalarsSelfVal φ (b' i) •
            𝟙 ((ModuleCat.extendScalars φ).obj (F.obj.obj U)))) :=
    ModuleCat.ExtendScalars.isIso_biproductDesc_unit_comp_map_smul φ b' (F.obj.obj U)
  -- the statement on underlying presheaves
  let t := Functor.whiskerRight (toSheafify J
    (F.obj ⋙ ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ))
      (ModuleCat.restrictScalars.{max u a vA} φ)
  let ψ (i : Fin r) :=
    ((ModuleCat.extendRestrictScalarsAdj.{max u a vA, max u a vA, max u a vA} φ).whiskerRight
      Cᵒᵖ).unit.app F.obj ≫
    Functor.whiskerRight ((basis i : B) •
      𝟙 (F.obj ⋙ ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ))
      (ModuleCat.restrictScalars.{max u a vA} φ)
  have hψ : IsIso (biproduct.desc ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    have : IsIso (biproduct.desc fun i ↦ ((CategoryTheory.evaluation _ _).obj U).map (ψ i)) :=
      hU U
    exact Functor.isIso_map_biproductDesc ((CategoryTheory.evaluation _ _).obj U) ψ
  have he : (biproduct.desc fun i ↦ (sheafToPresheaf _ _).map
      ((Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).unit.app F ≫
        (sheafCompose J
          (ModuleCat.restrictScalars.{max u a vA} (algebraMap A B))).map ((basis i : B) • 𝟙 _))) =
      biproduct.desc ψ ≫ t := by
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, Functor.map_comp]
    change ((Sheaf.adjunction _
        (ModuleCat.extendRestrictScalarsAdj.{max u a vA, max u a vA, max u a vA} φ)).unit.app
          F).hom ≫
        Functor.whiskerRight ((basis i : B) •
          𝟙 ((Sheaf.composeAndSheafify J (ModuleCat.extendScalars φ)).obj F)).hom
          (ModuleCat.restrictScalars.{max u a vA} φ) = _
    rw [Sheaf.adjunction_unit_app_hom]
    simp only [ψ, t, Category.assoc, ← Functor.whiskerRight_comp]
    congr 2
    change toSheafify _ _ ≫ ((basis i : B) • 𝟙 _) = ((basis i : B) • 𝟙 _) ≫ toSheafify _ _
    rw [Linear.comp_smul, Linear.smul_comp]
    erw [Category.comp_id]
  have : IsIso (biproduct.desc fun i ↦ (sheafToPresheaf _ _).map
      ((Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).unit.app F ≫
        (sheafCompose J
          (ModuleCat.restrictScalars.{max u a vA} (algebraMap A B))).map
            ((basis i : B) • 𝟙 _))) := by
    have : IsIso (biproduct.desc ψ ≫ t) := inferInstance
    rwa [← he] at this
  have := Functor.isIso_map_biproductDesc (sheafToPresheaf _ _) (φ := fun i ↦
      (Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).unit.app F ≫
        (sheafCompose J
          (ModuleCat.restrictScalars.{max u a vA} (algebraMap A B))).map ((basis i : B) • 𝟙 _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)


private theorem exceptionalRestrictionConservative :
    (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory.ReflectsIsomorphisms := by
  let U := Sheaf.restrictScalars J (algebraMap A B)
  have : U.ReflectsIsomorphisms := ⟨fun {M N} f _ ↦ by
    have : IsIso f.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      have : IsIso ((ModuleCat.restrictScalars (algebraMap A B)).map (f.hom.app V)) :=
        inferInstanceAs (IsIso (((sheafToPresheaf J _).map (U.map f)).app V))
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars (algebraMap A B))
    have : IsIso ((sheafToPresheaf J (ModuleCat B)).map f) := this
    exact isIso_of_reflects_iso _ (sheafToPresheaf J (ModuleCat B))⟩
  refine ⟨fun {M N} f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ U

private theorem exceptionalDerivedUnit
    {X : Type c} {Y : Type d} [Category.{vC} X] [Category.{vD} Y]
    [Abelian X] [Abelian Y] [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
    {E : X ⥤ Y} {U : Y ⥤ X} [E.Additive] [U.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) (P : CochainComplex X ℤ) :
    adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
  have hu : adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app P) := by
    simp only [Adjunction.onDerivedCategory, Adjunction.localization_unit_app]
    rfl
  change _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)
  rw [hu]
  simp only [Category.assoc]
  let e := E.mapDerivedCategoryFactors.app P
  let v := U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
    v.inv ≫ U.mapDerivedCategory.map e.inv ≫ U.mapDerivedCategory.map e.hom ≫ v.hom = _
  rw [← U.mapDerivedCategory.map_comp_assoc, e.inv_hom_id]
  erw [U.mapDerivedCategory.map_id]
  rw [Category.id_comp, v.inv_hom_id]
  exact Category.comp_id _

private theorem exceptionalDerivedBasis
    {X : Type c} {Y : Type d} [Category.{vC} X] [Category.{vD} Y]
    [Abelian X] [Abelian Y] [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
    {R : Type u} [Ring R] [Linear R Y]
    (r : ℕ) (coeff : Fin r → R) (E : X ⥤ Y) (U : Y ⥤ X)
    [E.Additive] [U.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U)
    (h : ∀ F, IsIso (biproduct.desc fun i : Fin r ↦ adj.unit.app F ≫
      U.map (coeff i • 𝟙 _))) (M : DerivedCategory X) :
    IsIso (biproduct.desc fun i : Fin r ↦ adj.onDerivedCategory.unit.app M ≫
      U.mapDerivedCategory.map (coeff i • 𝟙 _)) := by
  let d := adj.onDerivedCategory
  have hC (K : CochainComplex X ℤ) :
      IsIso (biproduct.desc fun i : Fin r ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _)) := by
    have (n : ℤ) : IsIso ((biproduct.desc fun i : Fin r ↦
        (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _)).f n) := by
      have e : (fun i : Fin r ↦ (HomologicalComplex.eval _ _ n).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
            (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _))) =
          fun i : Fin r ↦ adj.unit.app (K.X n) ≫ U.map (coeff i • 𝟙 _) := by
        funext i
        simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
          Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
          HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
        rfl
      have : IsIso (biproduct.desc fun i : Fin r ↦ (HomologicalComplex.eval _ _ n).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
            (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _))) := by
        rw [e]
        exact h (K.X n)
      exact Functor.isIso_map_biproductDesc (HomologicalComplex.eval _ _ n) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ (K : CochainComplex X ℤ) :
      IsIso (biproduct.desc fun i : Fin r ↦ d.unit.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategory.map (coeff i • 𝟙 _)) := by
    have := hC K
    have := Functor.isIso_biproductDesc_map DerivedCategory.Q
      (fun i : Fin r ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _))
    let z := U.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app K) ≪≫
      U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj K)
    refine isIso_biproductDesc_of_iso _ (fun i : Fin r ↦ DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map (coeff i • 𝟙 _)))
      (Iso.refl _) z (fun i ↦ ?_) inferInstance
    have hu : d.unit.app (DerivedCategory.Q.obj K) ≫ z.hom =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
      exact exceptionalDerivedUnit adj K
    have e₁ : (coeff i • 𝟙 (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K))) ≫
        E.mapDerivedCategoryFactors.hom.app K =
      E.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (coeff i • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj K)) := by
      rw [Functor.map_smul, Functor.map_id, Linear.smul_comp, Linear.comp_smul]
      simp
    have e₂ := U.mapDerivedCategoryFactors.hom.naturality
      (coeff i • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj K))
    dsimp only [Functor.comp_map] at e₂
    simp only [Functor.map_comp, Iso.refl_hom, Category.id_comp, Category.assoc]
    change d.unit.app _ ≫ U.mapDerivedCategory.map _ ≫
      U.mapDerivedCategory.map _ ≫ U.mapDerivedCategoryFactors.hom.app _ = _
    rw [← U.mapDerivedCategory.map_comp_assoc]
    change _ ≫ U.mapDerivedCategory.map
      ((coeff i • 𝟙 _) ≫ E.mapDerivedCategoryFactors.hom.app K) ≫ _ = _
    rw [e₁, U.mapDerivedCategory.map_comp,
      Category.assoc, e₂]
    simpa only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
        ((U.mapHomologicalComplex (.up ℤ)).map
          (coeff i • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj K)))) hu
  let e := DerivedCategory.Q.objObjPreimageIso M
  refine isIso_biproductDesc_of_iso _ _ e.symm
    ((E.mapDerivedCategory ⋙ U.mapDerivedCategory).mapIso e.symm) (fun i ↦ ?_)
    (hQ (DerivedCategory.Q.objPreimage M))
  have hu := d.unit.naturality e.inv
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hu
  simp only [Functor.comp_obj, Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map,
    Category.assoc]
  change d.unit.app M ≫ U.mapDerivedCategory.map (coeff i • 𝟙 _) ≫
    U.mapDerivedCategory.map (E.mapDerivedCategory.map e.inv) = _
  rw [← U.mapDerivedCategory.map_comp, Linear.smul_comp, Category.id_comp,
    ← Category.comp_id (E.mapDerivedCategory.map e.inv), ← Linear.comp_smul,
    U.mapDerivedCategory.map_comp]
  erw [reassoc_of% hu]

private theorem exceptionalScalarPresentation :
    Nonempty (FiniteFreeExceptionalScalarPresentation.{max u a vA, w, a, vA} J r basis) := by
  have : Module.Finite A B := Module.Finite.of_basis basis
  have : Module.Free A B := Module.Free.of_basis basis
  let φ := algebraMap A B
  have : PreservesLimits (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ) :=
    ModuleCat.preservesLimits_extendScalars_of_finite_projective φ
      (by rw [toAlgebra_algebraMap]; infer_instance)
      (by rw [toAlgebra_algebraMap]; infer_instance)
  let E := Sheaf.composeAndSheafify J
    (ModuleCat.extendScalars.{max u a vA, max u a vA, max u a vA} φ)
  let U := Sheaf.restrictScalars J φ
  let adj := Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj
    (algebraMap A B))
  have : E.Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  have : PreservesColimitsOfSize.{0, 0} E := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits E := inferInstance
  let d := adj.onDerivedCategory
  have hu (P : CochainComplex (Sheaf J (ModuleCat.{max u a vA} A)) ℤ) :
      d.unit.app (DerivedCategory.Q.obj P) ≫ U.mapDerivedCategory.map
        (E.mapDerivedCategoryFactors.hom.app P) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) :=
    exceptionalDerivedUnit adj P
  have hb (M : DerivedCategory (Sheaf J (ModuleCat.{max u a vA} A))) :
      IsIso (biproduct.desc fun i : Fin r ↦ d.unit.app M ≫
        U.mapDerivedCategory.map (basis i • 𝟙 _)) :=
    exceptionalDerivedBasis r (fun i ↦ basis i) E U adj
      (exceptionalOrdinaryBasis.{u, a, vA} J r basis) M
  exact ⟨{
    T := E.mapDerivedCategory
    counit := E.mapDerivedCategoryFactors.hom
    universal := Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ E.mapDerivedCategoryFactors
    adj := d
    unit_normalized := hu
    coordinates := fun M ↦ (asIso (biproduct.desc fun i : Fin r ↦
      d.unit.app M ≫ U.mapDerivedCategory.map (basis i • 𝟙 _))).symm
    column := fun M j ↦ biproduct.ι_desc _ j }⟩

end ScalarConstruction

section Sites
variable {C : Type a} {D : Type b} [Category.{vA} C] [Category.{vB} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {A B : Type (max u a b vA vB)} [CommRing A] [CommRing B] [Algebra A B]
  (r : ℕ) (basis : Module.Basis (Fin r) A B)
  [HasSheafify J (ModuleCat.{max u a b vA vB} A)] [HasSheafify J (ModuleCat.{max u a b vA vB} B)]
  [HasSheafify K (ModuleCat.{max u a b vA vB} A)] [HasSheafify K (ModuleCat.{max u a b vA vB} B)]
  [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a b vA vB} A))]
  [HasDerivedCategory.{w} (Sheaf J (ModuleCat.{max u a b vA vB} B))]
  [HasDerivedCategory.{w} (Sheaf K (ModuleCat.{max u a b vA vB} A))]
  [HasDerivedCategory.{w} (Sheaf K (ModuleCat.{max u a b vA vB} B))]

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The long signature compares four derived categories with explicit coefficient transports.
/-- Finite-free extension commutes with the right adjoints via the counit-defined mate.
The existential scalar presentations assert their existence, rather than assume it.
The first clause characterizes theta by the displayed chain of Hom bijections. The
second gives invertibility, the counit equation and its uniqueness, which also proves
basis independence. The final clauses specify the finite-sum comparison and its inverse.

Source: blueprint main-20261015, finite-free-extension proof, paragraph 1
(blueprint: lem-sf-finite-free-exceptional-mate).

Proof:
1. Construct exact extension by sheafifying ordinary module extension. The ordinary
   finite-basis theorem gives the scalar-unit columns objectwise, hence on complexes.
   Localize the exact adjunction and use its explicit unit formula to transport these
   columns to all derived objects. Restriction reflects isomorphisms objectwise on
   sheaves and, using homology, on derived categories.
2. Compose the scalar and given adjunctions and transport the left adjoint along c.
   The counit characterization of rightAdjointUniq gives the displayed Hom chain.
3. The mateEquiv definition transposes c inverse followed by T of the A-counit.
   Adjunction gives its counit identity, uniqueness, and naturality.
4. Trace U(b) after the scalar unit through the Hom chain. The triangle identity and
   naturality of the scalar unit give theta U(b) eta = GA(eta).
5. For each basis element use preservation of B-multiplication by GB, naturality of
   theta for multiplication, and the preceding unit calculation. The resulting column
   is GA of the corresponding basis inclusion.
6. Apply additivity to the finite-biproduct identities: the comparison with columns
   GA(iota_j) has inverse with rows GA(pi_j). Thus U(b), and then b by conservativity,
   is invertible. Empty sums prove the rank-zero case. The construction and its unique
   counit characterization involve no basis, so changing basis leaves the B-map unchanged.
-/
theorem finiteFreeExceptionalMate_isIso :
    ∃ (SC : FiniteFreeExceptionalScalarPresentation.{max u a b vA vB, w, a, vA}
        J r basis)
      (SD : FiniteFreeExceptionalScalarPresentation.{max u a b vA vB, w, b, vB}
        K r basis),
    ∀ (FA : DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} A)) ⥤
        DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A)))
      (GA : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} A)))
      (FB : DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} B)) ⥤
        DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} B)))
      (GB : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} B)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} B)))
      [FA.Additive] [GA.Additive] [FB.Additive] [GB.Additive]
      (aA : FA ⊣ GA) (aB : FB ⊣ GB) (c : FA ⋙ SD.T ≅ SC.T ⋙ FB)
    (multiplication : ∀ (a : B) (N : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} B))),
      GB.map (a • 𝟙 N) = a • 𝟙 (GB.obj N))
    (ρ : FB ⋙ (Sheaf.restrictScalars K (algebraMap A B)).mapDerivedCategory ≅
      (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory ⋙ FA)
    (normalization : ∀ P : DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} A)),
      (Sheaf.restrictScalars K (algebraMap A B)).mapDerivedCategory.map (c.hom.app P) ≫
        ρ.hom.app (SC.T.obj P) ≫ FA.map (SC.coordinates P).hom =
      (SD.coordinates (FA.obj P)).hom ≫
        finiteFreeExceptionalSumComparison FA r P),
    (∀ (P : DerivedCategory (Sheaf J (ModuleCat.{max u a b vA vB} A)))
      (N : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} B)))
      (f : P ⟶ ((Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory).obj (GB.obj N)),
      f ≫ (finiteFreeExceptionalTheta SC.adj SD.adj aA aB c).hom.app N =
        finiteFreeExceptionalHomMap SC.adj SD.adj aA aB c P N f) ∧
    IsIso (finiteFreeExceptionalMate aA aB c) ∧
    (∀ M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A)),
      FB.map ((finiteFreeExceptionalMate aA aB c).app M) ≫
        aB.counit.app (SD.T.obj M) = c.inv.app (GA.obj M) ≫ SD.T.map (aA.counit.app M)) ∧
    (∀ b' : GA ⋙ SC.T ⟶ SD.T ⋙ GB,
      (∀ M, FB.map (b'.app M) ≫ aB.counit.app (SD.T.obj M) =
        c.inv.app (GA.obj M) ≫ SD.T.map (aA.counit.app M)) →
      b' = finiteFreeExceptionalMate aA aB c) ∧
    (∀ M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A)),
      (SC.coordinates (GA.obj M)).inv ≫
        (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory.map
          ((finiteFreeExceptionalMate aA aB c).app M) ≫
        (finiteFreeExceptionalTheta SC.adj SD.adj aA aB c).hom.app (SD.T.obj M) ≫
        GA.map (SD.coordinates M).hom =
      finiteFreeExceptionalSumComparison GA r M) ∧
    (∀ M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A)),
      finiteFreeExceptionalSumComparison GA r M ≫
          finiteFreeExceptionalSumInverse GA r M =
        𝟙 _ ∧
      finiteFreeExceptionalSumInverse GA r M ≫
          finiteFreeExceptionalSumComparison GA r M =
        𝟙 _) := by
  obtain ⟨SC⟩ := exceptionalScalarPresentation.{max u a b vA vB, w, a, vA} J r basis
  obtain ⟨SD⟩ := exceptionalScalarPresentation.{max u a b vA vB, w, b, vB} K r basis
  refine ⟨SC, SD, ?_⟩
  intro FA GA FB GB _ _ _ _ aA aB c multiplication _ρ _normalization
  let UC := (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategory
  let UD := (Sheaf.restrictScalars K (algebraMap A B)).mapDerivedCategory
  let θ := finiteFreeExceptionalTheta SC.adj SD.adj aA aB c
  let β := finiteFreeExceptionalMate aA aB c
  have sums (M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A))) :
      finiteFreeExceptionalSumComparison GA r M ≫
          finiteFreeExceptionalSumInverse GA r M = 𝟙 _ ∧
      finiteFreeExceptionalSumInverse GA r M ≫
          finiteFreeExceptionalSumComparison GA r M = 𝟙 _ := by
    unfold finiteFreeExceptionalSumComparison finiteFreeExceptionalSumInverse
    exact ⟨(GA.mapBiproduct (fun _ : Fin r ↦ M)).inv_hom_id,
      (GA.mapBiproduct (fun _ : Fin r ↦ M)).hom_inv_id⟩
  have columns (M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A))) :
      (SC.coordinates (GA.obj M)).inv ≫ UC.map (β.app M) ≫
        θ.hom.app (SD.T.obj M) ≫ GA.map (SD.coordinates M).hom =
      finiteFreeExceptionalSumComparison GA r M := by
    apply biproduct.hom_ext'
    intro j
    have hm : (basis j • 𝟙 (SC.T.obj (GA.obj M))) ≫ β.app M =
        β.app M ≫ GB.map (basis j • 𝟙 (SD.T.obj M)) := by
      rw [multiplication]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      dsimp only [Functor.comp_obj]
      rw [Category.comp_id]
    have hn := θ.hom.naturality (basis j • 𝟙 (SD.T.obj M))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    change biproduct.ι _ j ≫ (SC.coordinates (GA.obj M)).inv ≫ UC.map (β.app M) ≫
      θ.hom.app (SD.T.obj M) ≫ GA.map (SD.coordinates M).hom = _
    rw [reassoc_of% (SC.column (GA.obj M) j), ← UC.map_comp_assoc, hm,
      UC.map_comp, Category.assoc, reassoc_of% hn]
    have hu : (SC.adj.unit.app (GA.obj M) ≫ UC.map (β.app M)) ≫
        θ.hom.app (SD.T.obj M) = GA.map (SD.adj.unit.app M) := by
      simpa only [Category.assoc] using exceptionalMate_unit SC.adj SD.adj aA aB c M
    rw [← Category.assoc, ← Category.assoc, hu]
    rw [← Category.assoc, ← GA.map_comp]
    have hd := SD.column M j
    rw [← hd]
    rw [← GA.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    unfold finiteFreeExceptionalSumComparison
    simp
  have hβ : IsIso β := by
    have : UC.ReflectsIsomorphisms :=
      exceptionalRestrictionConservative.{max u a b vA vB, w, a, vA} J
    have (M : DerivedCategory (Sheaf K (ModuleCat.{max u a b vA vB} A))) :
        IsIso (β.app M) := by
      have : IsIso (finiteFreeExceptionalSumComparison GA r M) :=
        ⟨⟨finiteFreeExceptionalSumInverse GA r M, (sums M).1, (sums M).2⟩⟩
      have : IsIso ((SC.coordinates (GA.obj M)).inv ≫ UC.map (β.app M) ≫
          θ.hom.app (SD.T.obj M) ≫ GA.map (SD.coordinates M).hom) := by
        rw [columns]
        infer_instance
      have : IsIso (UC.map (β.app M) ≫
          θ.hom.app (SD.T.obj M) ≫ GA.map (SD.coordinates M).hom) :=
        IsIso.of_isIso_comp_left (SC.coordinates (GA.obj M)).inv _
      have : IsIso (UC.map (β.app M)) :=
        IsIso.of_isIso_comp_right _
          (θ.hom.app (SD.T.obj M) ≫ GA.map (SD.coordinates M).hom)
      exact isIso_of_reflects_iso _ UC
    exact (NatTrans.isIso_iff_isIso_app β).2 (fun M ↦ inferInstance)
  exact ⟨exceptionalTheta_hom SC.adj SD.adj aA aB c, hβ,
    exceptionalMate_counit aA aB c, exceptionalMate_unique aA aB c, columns, sums⟩
end Sites
end CategoryTheory
