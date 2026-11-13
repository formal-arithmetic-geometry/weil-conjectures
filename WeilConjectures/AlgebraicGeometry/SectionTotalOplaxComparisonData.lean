/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.AlgebraicGeometry.SectionCochainTensorComparison
public import WeilConjectures.AlgebraicGeometry.SectionOrdinaryOplaxNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # The actual internal total oplax arrow in section modules

All tensors are relative to the pulled-back coefficient ring. The totalization is the
existing signed direct-sum total, including its infinite degreewise sums. The helpers
name existing functors and canonical comparisons; the final proposition records their
specified-map equalities before and after homotopy quotient and localization.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- The actual mate oplax structure agrees with the canonical composite structure. -/
theorem totalInternalOplax_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullOplax Λ f = (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal :=
  internalPullOplax_eq_canonical Λ f

/-- The actual internal pullback applied termwise. -/
@[reducible] def totalInternalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (internalModules Λ Y) ℤ ⥤ CochainComplex (internalModules Λ X) ℤ :=
  retainedCochainFunctor (CondensedRing.upperStar Λ f)
/-- The specified ringed pullback applied termwise. -/
@[reducible] def totalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (modules Λ Y) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  retainedCochainFunctor (pullback Λ f)
/-- The unchanged canonical monoidal structure on the retained termwise pullback.

This is the existing monoidal structure, expressed in the retained functor interface. -/
instance totalSectionPullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).Monoidal := by
  change ((pullback Λ f).mapHomologicalComplex (.up ℤ)).Monoidal
  infer_instance

/-- The fixed internal-section equivalence applied termwise. -/
@[reducible] def totalSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  cochainSectionEquivalence Λ X
/-- The specified total comparison, with its cochain tensor type recorded explicitly.

This is the existing uniquely normalized comparison, with no new choice of data. -/
@[irreducible] def totalTensorComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (totalSectionEquivalence Λ X).obj (P ⊗ Q) ≅
      (totalSectionEquivalence Λ X).obj P ⊗ (totalSectionEquivalence Λ X).obj Q :=
  cochainTensorComparison Λ X P Q

/-- The termwise lift of the fixed adjunction-mate operation comparison. -/
@[irreducible] def termwisePullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj P) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) :=
  (NatIso.mapHomologicalComplex (pullComparison Λ f) (.up ℤ)).app P

/-- The total of the actual internal adjunction-mate oplax map. Its inverse is the
summed lax map. The existing mapBifunctorComparison uses the canonical left-adjoint
coproduct comparison, and is the forward map of mapCochainComplexμIso.symm. -/
@[irreducible] def actualInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalInternalPull Λ f).obj (P ⊗ Q) ≅
      (totalInternalPull Λ f).obj P ⊗ (totalInternalPull Λ f).obj Q :=
  letI := CondensedRing.monoidal_upperStar Λ f
  asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q)

private theorem termwise_naturality
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive F]
    (I : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (L : E ⥤ F)
    [I.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [L.PreservesZeroMorphisms]
    (h : I ⋙ G ≅ H ⋙ L) {A B : CochainComplex C ℤ} (a : A ⟶ B) :
    (G.mapHomologicalComplex (.up ℤ)).map ((I.mapHomologicalComplex (.up ℤ)).map a) ≫
        (NatIso.mapHomologicalComplex h (.up ℤ)).hom.app B =
      (NatIso.mapHomologicalComplex h (.up ℤ)).hom.app A ≫
        (L.mapHomologicalComplex (.up ℤ)).map ((H.mapHomologicalComplex (.up ℤ)).map a) := by
  simpa only [Functor.mapHomologicalComplex, Functor.comp_obj, Functor.comp_map] using
    (NatIso.mapHomologicalComplex h (.up ℤ)).hom.naturality a

/-- Naturality of the fixed termwise operation comparison in its cached functor types. -/
theorem termwisePullComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ B) :
    (totalSectionEquivalence Λ X).map ((totalInternalPull Λ f).map a) ≫
        (termwisePullComparison Λ f B).hom =
      (termwisePullComparison Λ f A).hom ≫
        (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) := by
    simpa only [termwisePullComparison, Iso.app_hom, totalInternalPull, totalSectionPull,
      totalSectionEquivalence, cochainSectionEquivalence] using
      termwise_naturality (CondensedRing.upperStar Λ f) (equivalence Λ X).functor
        (equivalence Λ Y).functor (pullback Λ f) (pullComparison Λ f) a

/-- Naturality of the actual internal signed-total oplax comparison. -/
theorem actualInternalTotalIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A A' B B' : CochainComplex (internalModules Λ Y) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
    (totalInternalPull Λ f).map (a ⊗ₘ b) ≫ (actualInternalTotalIso Λ f A' B').hom =
      (actualInternalTotalIso Λ f A B).hom ≫
        ((totalInternalPull Λ f).map a ⊗ₘ (totalInternalPull Λ f).map b) := by
    let _ := CondensedRing.monoidal_upperStar Λ f
    unfold actualInternalTotalIso
    simp only [asIso_hom]
    change (totalInternalPull Λ f).map
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (.up ℤ)) ≫ _ =
      _ ≫ HomologicalComplex.mapBifunctorMap
        ((totalInternalPull Λ f).map a) ((totalInternalPull Λ f).map b)
        (curriedTensor _) (.up ℤ)
    simpa only [totalInternalPull] using
      HomologicalComplex.mapBifunctorComparison_naturality
        (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) a b

/-- The signed total of the specified ringed adjunction-mate tensor map. Its inverse
is the sum of the ordinary inverse maps, the construction used by the ringed
cochain comparison of lem-pur-cochain-pullback-tensor-coherence. -/
@[irreducible] def sectionTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj (P ⊗ Q) ≅
      (totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q where
  hom := Functor.OplaxMonoidal.δ (totalSectionPull Λ f) P Q
  inv := Functor.LaxMonoidal.μ (totalSectionPull Λ f) P Q
  hom_inv_id := Functor.Monoidal.δ_μ (totalSectionPull Λ f) P Q
  inv_hom_id := Functor.Monoidal.μ_δ (totalSectionPull Λ f) P Q

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] totalComparison ordinaryTensorComparison ordinaryUnitComparison

section ExplicitConjugation

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  (F : A ⥤ B) (G : C ⥤ B) {x y : A} {u v : C} {w t : B}
  (p : x ≅ y) (r : G.obj u ≅ F.obj x) (i : u ≅ v) (c : G.obj v ≅ w) (e : w ≅ t)

/-- The forward and reverse conjugation paths are inverse. -/
theorem sectionConjugation_hom_inv_id :
    (F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom) ≫
      (e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom) = 𝟙 _ := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, ← F.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- The reverse and forward conjugation paths are inverse. -/
theorem sectionConjugation_inv_hom_id :
    (e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom) ≫
      (F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom) = 𝟙 _ := by
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The same five-factor isomorphism with its two maps stored explicitly.

. -/
def sectionConjugationIso : F.obj y ≅ t where
  hom := F.map p.inv ≫ r.inv ≫ G.map i.hom ≫ c.hom ≫ e.hom
  inv := e.inv ≫ c.inv ≫ G.map i.inv ≫ r.hom ≫ F.map p.hom
  hom_inv_id := sectionConjugation_hom_inv_id F G p r i c e
  inv_hom_id := sectionConjugation_inv_hom_id F G p r i c e

end ExplicitConjugation

/-- Conjugate the actual internal total by the fixed operation and signed-total
comparisons. Both the source and target transports are explicit. -/
@[irreducible] def conjugatedInternalTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj P ⊗ (totalSectionEquivalence Λ Y).obj Q) ≅
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) ⊗
        (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj Q) :=
  sectionConjugationIso (totalSectionPull Λ f) (totalSectionEquivalence Λ X)
    (totalTensorComparison Λ Y P Q) (termwisePullComparison Λ f (P ⊗ Q))
    (actualInternalTotalIso Λ f P Q)
    (totalTensorComparison Λ X ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q))
    (tensorIso (termwisePullComparison Λ f P) (termwisePullComparison Λ f Q))

/-- The fixed equivalence on the ring complex in degree zero. -/
@[irreducible] def totalUnitComparison (X : Scheme.{u}) :
    (totalSectionEquivalence Λ X).obj (internalCochainUnit Λ X) ≅
      sectionCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (equivalence Λ X).functor (.up ℤ) 0).app
      (𝟙_ (internalModules Λ X)) ≪≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).mapIso (ordinaryUnitComparison Λ X)

/-- The total internal unit, induced by the specified ordinary unit in degree zero. -/
@[irreducible] def actualInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (internalCochainUnit Λ Y) ⟶
      internalCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (CondensedRing.upperStar Λ f)
    (.up ℤ) 0).hom.app (𝟙_ (internalModules Λ Y)) ≫
    (HomologicalComplex.single (internalModules Λ X) (.up ℤ) 0).map
      (normalizationInternalUnit Λ f)

/-- The ringed total unit, induced by ordinary scalar multiplication in degree zero. -/
@[irreducible] def sectionTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (sectionCochainUnit Λ Y) ⟶
      sectionCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (pullback Λ f) (.up ℤ) 0).hom.app
      (𝟙_ (modules Λ Y)) ≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).map (normalizationSectionUnit Λ f)

/-- Conjugate the actual internal unit by the same fixed operation comparisons. -/
def conjugatedInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (sectionCochainUnit Λ Y) ⟶
      sectionCochainUnit Λ X :=
  (totalSectionPull Λ f).map (totalUnitComparison Λ Y).inv ≫
    (termwisePullComparison Λ f (internalCochainUnit Λ Y)).inv ≫
    (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
    (totalUnitComparison Λ X).hom

/-- The forward projection is the specified signed sum-total comparison. -/
theorem actualInternalTotalIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (actualInternalTotalIso Λ f P Q).hom =
      (letI := CondensedRing.monoidal_upperStar Λ f
       HomologicalComplex.mapBifunctorComparison
         (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q) := by
  unfold actualInternalTotalIso
  rfl

/-- The forward field retains the original native oplax tensorator. -/
theorem sectionTotalIso_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (sectionTotalIso Λ f P Q).hom = Functor.OplaxMonoidal.δ (totalSectionPull Λ f) P Q := by
  unfold sectionTotalIso
  rfl

/-- The specified section sum-total comparison, without its inverse data. -/
theorem sectionTotalIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (sectionTotalIso Λ f P Q).hom =
      HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (.up ℤ) P Q := by
  unfold sectionTotalIso
  rfl

/-- The specified degree-zero unit is the native cochain oplax unit. -/
theorem sectionTotalUnit_η {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sectionTotalUnit Λ f = Functor.OplaxMonoidal.η (totalSectionPull Λ f) := by
  unfold sectionTotalUnit normalizationSectionUnit
  rfl

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
