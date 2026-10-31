/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedProjectionCoherenceData
public import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
/-! The associator half of the representative descent of tensor constraints.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YU and 07A4
(blueprint: lem-sfb-ringed-projection-associator-completion).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence
private theorem representativeArrow (X : RingedTensorCorner.{u, w})
    (P Q : CochainComplex X.mateModules ℤ)
    (hp : SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring P)
    (hq : SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring Q) :
    SheafOfModules.cochainTensorRepresentativeArrow X.topology X.ring (⟨P, hp⟩, ⟨Q, hq⟩) =
      (SheafOfModules.KFlatFixedTensor.representativeIso X.ring P Q
        hp.1 hq.1 hp.2 hq.2).hom := by
  unfold SheafOfModules.cochainTensorRepresentativeArrow
  change (𝟙 _) ≫ _ ≫ _ ≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients X.topology X.ring).map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  unfold SheafOfModules.KFlatFixedTensor.representativeIso
  rfl

private theorem transportRepresentative_app
    {C D : Type*} [Category C] [Category D]
    (S : C × C ⥤ D) (q : C ⥤ D) (T : D × D ⥤ D)
    {p p' : ObjectProperty C} (h : p = p')
    (r : (p.ι.prod p.ι) ⋙ S ≅ ((p.ι ⋙ q).prod (p.ι ⋙ q)) ⋙ T)
    (P Q : C) (hp : p P) (hq : p Q) (hp' : p' P) (hq' : p' Q) :
    let r' : (p'.ι.prod p'.ι) ⋙ S ≅ ((p'.ι ⋙ q).prod (p'.ι ⋙ q)) ⋙ T := h ▸ r
    r'.hom.app (⟨P, hp'⟩, ⟨Q, hq'⟩) = r.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) := by
  cases h
  rfl

private theorem transportAssociatorEquation
    {C : Type*} [Category C] (N S : C × C ⥤ C) (e : N ≅ S)
    {A B C' AB BC L R : C}
    (rAB : AB ⟶ N.obj (A, B)) (rBC : BC ⟶ N.obj (B, C'))
    (rL : L ⟶ N.obj (AB, C')) (rR : R ⟶ N.obj (A, BC))
    (f : L ⟶ R) (α : N.obj (N.obj (A, B), C') ⟶ N.obj (A, N.obj (B, C')))
    (h : rL ≫ N.map (Prod.mkHom rAB (𝟙 C')) ≫ α =
      f ≫ rR ≫ N.map (Prod.mkHom (𝟙 A) rBC)) :
    (rL ≫ e.hom.app (AB, C')) ≫
        S.map (Prod.mkHom (rAB ≫ e.hom.app (A, B)) (𝟙 C')) ≫
        S.map (Prod.mkHom (e.inv.app (A, B)) (𝟙 C')) ≫
        e.inv.app (N.obj (A, B), C') ≫ α ≫
        e.hom.app (A, N.obj (B, C')) ≫
        S.map (Prod.mkHom (𝟙 A) (e.hom.app (B, C'))) =
      f ≫ (rR ≫ e.hom.app (A, BC)) ≫
        S.map (Prod.mkHom (𝟙 A) (rBC ≫ e.hom.app (B, C'))) := by
  have hmap :
      S.map (Prod.mkHom (rAB ≫ e.hom.app (A, B)) (𝟙 C')) ≫
          S.map (Prod.mkHom (e.inv.app (A, B)) (𝟙 C')) =
        S.map (Prod.mkHom rAB (𝟙 C')) := by
    rw [← S.map_comp]
    congr 1
    apply Prod.hom_ext <;> simp [Category.assoc]
  simp only [Category.assoc]
  rw [← Category.assoc (S.map _) (S.map _), hmap]
  rw [← Category.assoc (e.hom.app _) (S.map _), ← e.hom.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  calc
    _ = (rL ≫ N.map (Prod.mkHom rAB (𝟙 C')) ≫ α) ≫
        e.hom.app (A, N.obj (B, C')) ≫
          S.map (Prod.mkHom (𝟙 A) (e.hom.app (B, C'))) := by
      simp only [Category.assoc]
    _ = (f ≫ rR ≫ N.map (Prod.mkHom (𝟙 A) rBC)) ≫
        e.hom.app (A, N.obj (B, C')) ≫
          S.map (Prod.mkHom (𝟙 A) (e.hom.app (B, C'))) := by rw [h]
    _ = f ≫ rR ≫
        (N.map (Prod.mkHom (𝟙 A) rBC) ≫ e.hom.app (A, N.obj (B, C'))) ≫
          S.map (Prod.mkHom (𝟙 A) (e.hom.app (B, C'))) := by
      simp only [Category.assoc]
    _ = f ≫ rR ≫ (e.hom.app (A, BC) ≫ S.map (Prod.mkHom (𝟙 A) rBC)) ≫
        S.map (Prod.mkHom (𝟙 A) (e.hom.app (B, C'))) := by rw [e.hom.naturality]
    _ = _ := by
      simp only [Category.assoc]
      rw [← S.map_comp]
      simp only [prod_comp, Category.id_comp]

set_option maxHeartbeats 2400000 in
-- Unfolding the representative comparison needs additional elaboration heartbeats.
/-- The associator obtained by conjugating the normalized derived associator `α` by the
comparison `e` between the fixed derived tensor and the recorded tensor is natural and
satisfies the representative equation of the recorded model.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YU and 07A4.

Proof: by `hassoc`, `assoc` is the composite of natural isomorphisms
`X.tensor ∘ (e⁻¹ × 1)`, `e⁻¹`, `α`, `e` and `X.tensor ∘ (1 × e)`, so naturality is
naturality of `α` and `e`. For the representative equation, the rigidity arrow
`cochainTensorRepresentativeArrow` is `KFlatFixedTensor.representativeIso` (both unfold to
the same descent comparison), so `he` says `a.representative(P,Q) = rep(P,Q) ≫ e(P,Q)` on
flat K-flat complexes, after transporting along `hflat`. Substitute this into the left
side; naturality of `e` in the first variable moves `X.tensor.map (rep(P,Q) ≫ e, 1)` past
`e(P⊗Q,T)`, the factors `e ≫ e⁻¹` cancel, and the left side becomes
`leftRepresentative(P,Q,T) ≫ α ≫ e ≫ X.tensor.map (1, e)`. The associator conjunct of
`hs` rewrites `leftRepresentative ≫ α` to `Q(α_ P Q T) ≫ rightRepresentative(P,Q,T)`,
and `α_` on cochain complexes is `totalAssociator`. Naturality of `e` in the second
variable then gives the right side. The flatness witnesses `hpq`, `hqt` are those of
`kFlat_total_tensor_model`.
(blueprint: lem-sfb-ringed-projection-associator-completion) -/
theorem ringedProjectionAssociatorCompletion
    (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X)
    (e : SheafOfModules.DerivedTensorConstraints.tensor X.ring ≅ X.tensor)
    (hflat : (fun P : CochainComplex X.mateModules ℤ =>
      P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat) =
      (fun P : CochainComplex X.mateModules ℤ =>
        P.IsKFlatIndependentCoefficients ∧
          ∀ n : ℤ, (P.X n).IsFlatOnSite))
    (he : let arep := hflat ▸ a.representative
      ∀ z : (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory ×
        (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory,
      SheafOfModules.cochainTensorRepresentativeArrow X.topology X.ring z ≫
        e.hom.app (DerivedCategory.Q.obj z.1.obj, DerivedCategory.Q.obj z.2.obj) =
      arep.hom.app z)
    (t : ∀ i j : ℤ, SheafOfModules.DerivedTensorConstraints.shiftedSource X.ring i j ≅
      SheafOfModules.DerivedTensorConstraints.shiftedTarget X.ring i j)
    (α : SheafOfModules.DerivedTensorConstraints.leftAssociated X.ring ≅
      SheafOfModules.DerivedTensorConstraints.rightAssociated X.ring)
    (σ : SheafOfModules.DerivedTensorConstraints.tensor X.ring ≅
      SheafOfModules.DerivedTensorConstraints.swapped X.ring)
    (assoc : ∀ E F G : X.mateDerived,
      X.tensor.obj (X.tensor.obj (E, F), G) ≅ X.tensor.obj (E, X.tensor.obj (F, G)))
    (hassoc : ∀ E F G, assoc E F G =
      X.tensor.mapIso (Iso.prod (asIso (e.inv.app (E, F))) (Iso.refl G)) ≪≫
        asIso (e.inv.app ((SheafOfModules.DerivedTensorConstraints.tensor X.ring).obj
          (E, F), G)) ≪≫ α.app ((E, F), G) ≪≫
        asIso (e.hom.app (E, (SheafOfModules.DerivedTensorConstraints.tensor X.ring).obj
          (F, G))) ≪≫
        X.tensor.mapIso (Iso.prod (Iso.refl E) (asIso (e.hom.app (F, G)))))
    (hs : SheafOfModules.DerivedTensorConstraints.IsNormalized X.ring t α σ) :
    (∀ {E E' F F' G G' : X.mateDerived} (x : E ⟶ E') (y : F ⟶ F') (z : G ⟶ G'),
      X.tensor.map (Prod.mkHom (X.tensor.map (Prod.mkHom x y)) z) ≫
          (assoc E' F' G').hom =
        (assoc E F G).hom ≫ X.tensor.map (Prod.mkHom x (X.tensor.map (Prod.mkHom y z)))) ∧
      (∀ (P Q T : CochainComplex X.mateModules ℤ)
        (hp : X.mateFlat P) (hq : X.mateFlat Q) (ht : X.mateFlat T),
        ∃ (hpq : X.mateFlat (total X P Q)) (hqt : X.mateFlat (total X Q T)),
          a.representative.hom.app (⟨total X P Q, hpq⟩, ⟨T, ht⟩) ≫
              X.tensor.map (Prod.mkHom (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
                (𝟙 (DerivedCategory.Q.obj T))) ≫ (assoc _ _ _).hom =
            DerivedCategory.Q.map (totalAssociator X P Q T).hom ≫
              a.representative.hom.app (⟨P, hp⟩, ⟨total X Q T, hqt⟩) ≫
              X.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
                (a.representative.hom.app (⟨Q, hq⟩, ⟨T, ht⟩)))) := by
  classical
  let N := SheafOfModules.DerivedTensorConstraints.tensor X.ring
  let D := X.mateDerived
  let γ : ((X.tensor.prod (𝟭 D)) ⋙ X.tensor) ≅
      CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod X.tensor) ⋙ X.tensor :=
    Functor.isoWhiskerRight (NatIso.prod e.symm (Iso.refl (𝟭 D))) X.tensor ≪≫
      Functor.isoWhiskerLeft (N.prod (𝟭 D)) e.symm ≪≫ α ≪≫
      Functor.isoWhiskerLeft (CategoryTheory.prod.associator D D D)
        (Functor.isoWhiskerLeft ((𝟭 D).prod N) e ≪≫
          Functor.isoWhiskerRight (NatIso.prod (Iso.refl (𝟭 D)) e) X.tensor)
  have hγ (E F G : D) : (assoc E F G).hom = γ.hom.app ((E, F), G) := by
    rw [hassoc]
    rfl
  constructor
  · intro E E' F F' G G' x y z
    rw [hγ, hγ]
    exact γ.hom.naturality (Prod.mkHom (Prod.mkHom x y) z)
  · intro P Q T hp hq ht
    let p : SheafOfModules.DerivedTensorConstraints.Model X.ring :=
      ⟨P, (congrFun hflat P).mp hp⟩
    let q : SheafOfModules.DerivedTensorConstraints.Model X.ring :=
      ⟨Q, (congrFun hflat Q).mp hq⟩
    let r : SheafOfModules.DerivedTensorConstraints.Model X.ring :=
      ⟨T, (congrFun hflat T).mp ht⟩
    have hrep (A B : CochainComplex X.mateModules ℤ)
        (ha : X.mateFlat A) (hb : X.mateFlat B) :
        a.representative.hom.app (⟨A, ha⟩, ⟨B, hb⟩) =
          (SheafOfModules.KFlatFixedTensor.representativeIso X.ring A B
            ((congrFun hflat A).mp ha).1 ((congrFun hflat B).mp hb).1
            ((congrFun hflat A).mp ha).2 ((congrFun hflat B).mp hb).2).hom ≫
            e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) := by
      have hh := he (⟨A, (congrFun hflat A).mp ha⟩, ⟨B, (congrFun hflat B).mp hb⟩)
      rw [representativeArrow] at hh
      rw [transportRepresentative_app
        (SheafOfModules.cochainTensorTotal X.topology X.ring ⋙ DerivedCategory.Q)
        DerivedCategory.Q X.tensor hflat a.representative A B ha hb] at hh
      exact hh.symm
    let pq := SheafOfModules.DerivedTensorConstraints.totalModel X.ring p q
    let qr := SheafOfModules.DerivedTensorConstraints.totalModel X.ring q r
    have hpq : X.mateFlat (total X P Q) := (congrFun hflat _).mpr pq.property
    have hqt : X.mateFlat (total X Q T) := (congrFun hflat _).mpr qr.property
    refine ⟨hpq, hqt, ?_⟩
    have hn := congrArg
      (fun m ↦ (SheafOfModules.DerivedTensorConstraints.leftRepresentative X.ring p q r).hom ≫ m)
      (congrArg Iso.hom (hs.2.1 p q r))
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc] at hn
    simp only [SheafOfModules.DerivedTensorConstraints.leftRepresentative,
      SheafOfModules.DerivedTensorConstraints.rightRepresentative,
      SheafOfModules.DerivedTensorConstraints.representative,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
      Category.assoc] at hn
    simp only [hrep (total X P Q) T hpq ht, hrep P Q hp hq,
      hrep P (total X Q T) hp hqt, hrep Q T hq ht]
    simp only [hassoc, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, asIso_hom, Category.assoc]
    have hcalc := transportAssociatorEquation N X.tensor e _ _ _ _ _ _ hn
    simp only [Category.assoc] at hcalc
    convert hcalc using 1 <;> rfl
end SheafOfModules.ProjectionCoherence
