/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplexToSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # Signed assembly of a natural scalar-dual comparison

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X (section-hom-complexes)
and 08JJ (lemma-dual-perfect-complex), sign and degree-reversal conventions.
The arbitrary additive-functor assembly is the node's explicit agent-written argument.
(blueprint: lem-sfb-scalar-dual-signed-assembly).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def scalarCoordinates
    (R : Type u) [CommRing R] (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    (CochainComplex.moduleHomComplex F
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).X q ≅ ModuleCat.of R (Module.Dual R (F.X (-q))) := by
  let e : CochainComplex.HomComplex.Cochain F
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R)) q ≃ₗ[R] (F.X (-q) ⟶ ModuleCat.of R R) :=
    { CochainComplex.HomComplex.Cochain.toSingleEquiv (neg_add_cancel q) with
      map_smul' := by
        intro r z
        simp [CochainComplex.HomComplex.Cochain.toSingleEquiv] }
  exact (e.trans ModuleCat.homLinearEquiv).toModuleIso

private lemma scalarCoordinates_d
    (R : Type u) [CommRing R] (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    (CochainComplex.moduleHomComplex F
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).d q (q + 1) ≫ (scalarCoordinates R F (q + 1)).hom =
      (scalarCoordinates R F q).hom ≫ ModuleCat.ofHom
        (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((CochainComplex.HomComplex.δ q (q + 1) z).v (-(q + 1)) 0
    (neg_add_cancel (q + 1)) ≫ _).hom = _
  rw [CochainComplex.HomComplex.δ_v q (q + 1) rfl z (-(q + 1)) 0
    (neg_add_cancel (q + 1)) (-1) (-q) rfl (by omega)]
  simp [CochainComplex.singleFunctor_obj_d, Int.negOnePow_succ,
    scalarCoordinates, CochainComplex.HomComplex.Cochain.toSingleEquiv,
    LinearMap.dualMap]
  rfl

private noncomputable def scalarPrecomp
    {R : Type u} [CommRing R] {F G : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : F ⟶ G) :
    CochainComplex.moduleHomComplex G
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶
    CochainComplex.moduleHomComplex F
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) where
  f q := ModuleCat.ofHom
    { toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add q)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact CochainComplex.HomComplex.δ_ofHom_comp f z r

private lemma scalarPrecomp_coordinates
    {R : Type u} [CommRing R] {F G : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : F ⟶ G) (q : ℤ) :
    (scalarPrecomp f).f q ≫ (scalarCoordinates R F q).hom =
      (scalarCoordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add q)).v
    (-q) 0 (neg_add_cancel q) ≫ _).hom = _
  rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
  rfl

private lemma map_coordinate_square
    {D E : Type*} [Category D] [Category E] (T : D ⥤ E)
    {X₁ X₂ Y₁ Y₂ : D} {Z₁ Z₂ : E}
    (g : X₁ ⟶ X₂) (a : X₂ ⟶ Y₂) (b : X₁ ⟶ Y₁) (d : Y₁ ⟶ Y₂)
    (e : T.obj Y₂ ⟶ Z₂) (e' : T.obj Y₁ ⟶ Z₁) (h : Z₁ ⟶ Z₂)
    (hc : g ≫ a = b ≫ d) (hn : e' ≫ h = T.map d ≫ e) :
    T.map g ≫ (T.map a ≫ e) = (T.map b ≫ e') ≫ h := by
  rw [← Category.assoc, ← T.map_comp, hc, T.map_comp,
    Category.assoc, ← hn, ← Category.assoc]

set_option maxHeartbeats 600000 in
-- The six-clause assembly accumulates elaboration work across its component constructions.
/-- A supplied natural comparison with internal sheaf duals assembles uniquely into
signed cochain maps, naturally in the complex, preserving isomorphisms and reversed bounds.
Source: Stacks Project, sites-cohomology.tex, Tags 0A8X and 08JJ; the arbitrary additive
functor generalization is agent-written (blueprint: lem-sfb-scalar-dual-signed-assembly).

Proof:
1. Project a scalar Hom cochain of degree q onto its (-q,0) factor and identify R[0]^0
with R. Insert the functional in that factor and zero elsewhere for the inverse.
The other factors have zero target, so both composites are identities. The total Hom
formula gives tau_(q+1) d = -(-1)^q (d_F)^* tau_q.
2. Additivity of T implies T(0)=0 and T(-f)=-T(f), hence preservation of the two signs.
Its termwise prolongation is a complex since T carries d d=0 to T(d) T(d)=0.
3. Apply eta naturality to d_F^(-q-1). Multiply by -(-1)^q and use step 2 to obtain
the displayed coordinate differential equation. Precede eta by T(tau_q) to obtain
kappa. Step 1 gives the chain-map equation; equality of components gives uniqueness.
4. Scalar precomposition by a chain map has components (f^(-q))^* in these coordinates;
sheaf precomposition has components internal Hom(T(f^(-q)),1). Both commute with the
signed differentials by the chain-map equation of f. Eta naturality gives the square
with kappa. Precomposition preserves identities and reverses composition.
5. When the relevant eta are isomorphisms, the inverse components are
eta^(-1) followed by T(tau_q^(-1)). Multiplying the chain-map equation by these
inverses gives an inverse chain map. Localization preserves this isomorphism;
no derived functor of T is asserted or needed.
6. The identity on T(0) is T(1_0)=T(0)=0, so T carries zero objects to zero objects.
Outside [-b,-a], F^(-q) is zero, its scalar dual is zero, and internal Hom(0,B)=0.
Step 1 and preservation of zero objects give both vanishing statements. This also
covers a>b and the zero complex without extra endpoint or nonzero assumptions. -/
theorem scalarDual_signed_assembly
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] (B : Sheaf J CommRingCat.{u})
    (T : ModuleCat.{u} R ⥤ ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) [T.Additive]
    (η : ∀ V : ModuleCat.{u} R,
      T.obj (ModuleCat.of R (Module.Dual R V)) ⟶
        SheafOfModules.homObj (R := B) (T.obj V)
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
    (hη : ∀ {V W : ModuleCat.{u} R} (f : V ⟶ W),
      η W ≫ SheafOfModules.homObjMap (R := B) (T.map f) (𝟙 _) =
        T.map (ModuleCat.ofHom f.hom.dualMap) ≫ η V) :
    ∃ τ : ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ),
        (CochainComplex.moduleHomComplex F
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R R))).X q ≅ ModuleCat.of R (Module.Dual R (F.X (-q))),
      (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ)
          (z : (CochainComplex.moduleHomComplex F
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R))).X q),
        (τ F q).hom z = (z.v (-q) 0 (neg_add_cancel q) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of R R)).hom).hom) ∧
      (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ),
        (CochainComplex.moduleHomComplex F
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R R))).d q (q + 1) ≫ (τ F (q + 1)).hom =
          (τ F q).hom ≫ ModuleCat.ofHom
            (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap)) ∧
      ∃ κ : ∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
          (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.moduleHomComplex F
              ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R))) ⟶
            signedSheafDualComplex (R := B)
              ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
        (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ),
          @id (T.obj ((CochainComplex.moduleHomComplex F
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R))).X q) ⟶
            SheafOfModules.homObj (R := B) (T.obj (F.X (-q)))
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
            ((κ F).f q) = T.map (τ F q).hom ≫ η (F.X (-q))) ∧
        (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (κ' :
            (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (CochainComplex.moduleHomComplex F
                ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                  (ModuleCat.of R R))) ⟶
              signedSheafDualComplex (R := B)
                ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
                (SheafOfModules.unit
                  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))),
          (∀ q : ℤ, @id (T.obj ((CochainComplex.moduleHomComplex F
              ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R))).X q) ⟶
              SheafOfModules.homObj (R := B) (T.obj (F.X (-q)))
                (SheafOfModules.unit
                  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
              (κ'.f q) = T.map (τ F q).hom ≫ η (F.X (-q))) → κ' = κ F) ∧
        (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ),
          η (F.X (-q)) ≫
              (-q.negOnePow • SheafOfModules.homObjMap (R := B)
                (T.map (F.d (-(q + 1)) (-q))) (𝟙 _)) =
            T.map (ModuleCat.ofHom
              (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap)) ≫
                η (F.X (-(q + 1)))) ∧
        (∀ (F G : CochainComplex (ModuleCat.{u} R) ℤ) (f : F ⟶ G),
          ∃ g : CochainComplex.moduleHomComplex G
                ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                  (ModuleCat.of R R)) ⟶
              CochainComplex.moduleHomComplex F
                ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                  (ModuleCat.of R R)),
            ∃ h : signedSheafDualComplex (R := B)
                  ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
                  (SheafOfModules.unit
                    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ⟶
                signedSheafDualComplex (R := B)
                  ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
                  (SheafOfModules.unit
                    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
              (∀ q : ℤ, g.f q ≫ (τ F q).hom =
                (τ G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap) ∧
              (∀ q : ℤ, @id
                (SheafOfModules.homObj (R := B) (T.obj (G.X (-q)))
                    (SheafOfModules.unit
                      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ⟶
                  SheafOfModules.homObj (R := B) (T.obj (F.X (-q)))
                    (SheafOfModules.unit
                      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
                (h.f q) = SheafOfModules.homObjMap (R := B) (T.map (f.f (-q))) (𝟙 _)) ∧
              (T.mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫ κ F = κ G ≫ h) ∧
        (∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
          (∀ r : ℤ, IsIso (η (F.X r))) →
            IsIso (κ F) ∧ IsIso
              ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).map (κ F))) ∧
        (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
          (∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) →
            ∀ q : ℤ, q < -b ∨ -a < q →
              IsZero (((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (CochainComplex.moduleHomComplex F
                  ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                    (ModuleCat.of R R)))).X q) ∧
              IsZero ((signedSheafDualComplex (R := B)
                ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
                (SheafOfModules.unit
                  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).X q)) := by
  classical
  refine ⟨scalarCoordinates R, ?_, scalarCoordinates_d R, ?_⟩
  · intro F q z
    rfl
  · let H := fun F : CochainComplex (ModuleCat.{u} R) ℤ ↦
      CochainComplex.moduleHomComplex F
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
    let N := SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
    have hsign (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
        η (F.X (-q)) ≫
            (-q.negOnePow • SheafOfModules.homObjMap (R := B)
              (T.map (F.d (-(q + 1)) (-q))) (𝟙 _)) =
          T.map (ModuleCat.ofHom
            (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap)) ≫
              η (F.X (-(q + 1))) := by
      change η (F.X (-q)) ≫
          (-q.negOnePow • SheafOfModules.homObjMap (R := B)
            (T.map (F.d (-(q + 1)) (-q))) (𝟙 _)) =
        T.map (-q.negOnePow • ModuleCat.ofHom
          (F.d (-(q + 1)) (-q)).hom.dualMap) ≫ η (F.X (-(q + 1)))
      rw [T.map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp, hη]
    let κ (F : CochainComplex (ModuleCat.{u} R) ℤ) :
        (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj (H F) ⟶
          signedSheafDualComplex (R := B)
            ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) N :=
      { f := fun q ↦ T.map (scalarCoordinates R F q).hom ≫ η (F.X (-q))
        comm' := by
          intro q r hqr
          obtain rfl : r = q + 1 := hqr.symm
          simp only [signedSheafDualComplex, CochainComplex.of_d]
          change (T.map (scalarCoordinates R F q).hom ≫ η (F.X (-q))) ≫
              (-q.negOnePow • SheafOfModules.homObjMap (R := B)
                (T.map (F.d (-(q + 1)) (-q))) (𝟙 N)) =
            T.map ((H F).d q (q + 1)) ≫
              (T.map (scalarCoordinates R F (q + 1)).hom ≫ η (F.X (-(q + 1))))
          rw [Category.assoc, hsign, ← Category.assoc, ← T.map_comp,
            ← scalarCoordinates_d R, T.map_comp, Category.assoc] }
    refine ⟨κ, ?_, ?_, hsign, ?_, ?_, ?_⟩
    · intro F q
      rfl
    · intro F κ' hκ'
      apply HomologicalComplex.Hom.ext
      exact funext hκ'
    · intro F G f
      let h : signedSheafDualComplex (R := B)
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj G) N ⟶
          signedSheafDualComplex (R := B)
            ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) N :=
        { f := fun q ↦ SheafOfModules.homObjMap (R := B) (T.map (f.f (-q))) (𝟙 N)
          comm' := by
            intro q r hqr
            obtain rfl : r = q + 1 := hqr.symm
            simp only [signedSheafDualComplex, CochainComplex.of_d]
            simp only [Linear.comp_units_smul, Linear.units_smul_comp,
              SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
            have he := congrArg T.map (f.comm (-(q + 1)) (-q))
            simp only [T.map_comp] at he
            exact congrArg
              (fun t ↦ -q.negOnePow • SheafOfModules.homObjMap (R := B) t (𝟙 N))
              he.symm }
      refine ⟨scalarPrecomp f, h, scalarPrecomp_coordinates f, ?_, ?_⟩
      · intro q
        rfl
      · apply HomologicalComplex.Hom.ext
        funext q
        change T.map ((scalarPrecomp f).f q) ≫
            (T.map (scalarCoordinates R F q).hom ≫ η (F.X (-q))) =
          (T.map (scalarCoordinates R G q).hom ≫ η (G.X (-q))) ≫
            SheafOfModules.homObjMap (R := B) (T.map (f.f (-q))) (𝟙 N)
        exact map_coordinate_square T ((scalarPrecomp f).f q)
          (scalarCoordinates R F q).hom (scalarCoordinates R G q).hom
          (ModuleCat.ofHom (f.f (-q)).hom.dualMap) (η (F.X (-q))) (η (G.X (-q)))
          (SheafOfModules.homObjMap (R := B) (T.map (f.f (-q))) (𝟙 N))
          (scalarPrecomp_coordinates f q)
          (hη (V := F.X (-q)) (W := G.X (-q)) (f.f (-q)))
    · intro F hF
      have hcomp (q : ℤ) : IsIso ((κ F).f q) := by
        have : IsIso (η (F.X (-q))) := hF (-q)
        change IsIso (T.map (scalarCoordinates R F q).hom ≫ η (F.X (-q)))
        infer_instance
      have : ∀ q : ℤ, IsIso ((κ F).f q) := hcomp
      have hκ : IsIso (κ F) := HomologicalComplex.Hom.isIso_of_components _
      exact ⟨hκ, inferInstance⟩
    · intro F a b hF q hq
      have hz := hF (-q) (by omega)
      have hscalar : IsZero (ModuleCat.of R (Module.Dual R (F.X (-q)))) := by
        have : Subsingleton (F.X (-q)) := ModuleCat.subsingleton_of_isZero hz
        exact ModuleCat.isZero_of_subsingleton _
      refine ⟨T.map_isZero (hscalar.of_iso (scalarCoordinates R F q)), ?_⟩
      change IsZero (SheafOfModules.homObj (R := B) (T.obj (F.X (-q))) N)
      exact (((SheafOfModules.homFunctor B).flip.obj N).map_isZero
        (T.map_isZero hz).op)

end CategoryTheory
