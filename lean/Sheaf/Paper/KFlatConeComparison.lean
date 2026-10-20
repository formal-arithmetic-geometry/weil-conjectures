/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.EqToHom
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# The two-resolution tensor augmentation square

Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YS, 06YT and 06YU
(blueprint: lem-pur-kflat-cone-comparison).

The tensor model is supplied with its natural representative comparison, as in
`wf_site_derived_tensor_descent`. No choice of a bare derived tensor object is made.
All auxiliary names below package the objects and maps of this one comparison square.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Prod MonoidalCategory

namespace SheafOfModules.KFlatConeComparison

section

variable {C : Type*} [Category C] [Abelian C]
  (F : C ⥤ C ⥤ C) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ A B : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor A B F (.up ℤ)]

open CochainComplex CochainComplex.HomComplex

/-- Simultaneous morphism formula for the totalized bifunctor.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
theorem uncurry_map_eq {X Y : CochainComplex C ℤ × CochainComplex C ℤ}
    (f : X ⟶ Y) :
    (CategoryTheory.Functor.uncurry.obj F.map₂CochainComplex).map f =
      HomologicalComplex.mapBifunctorMap f.1 f.2 F (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap f.1 (𝟙 X.2) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 Y.1) f.2 _ _ = _
  simp only [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  congr 1
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id]

/-- Totalization of an additive bifunctor with simultaneous action on morphisms.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def totalBifunctor :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj X := HomologicalComplex.mapBifunctor X.1 X.2 F (.up ℤ)
  map f := HomologicalComplex.mapBifunctorMap f.1 f.2 F (.up ℤ)
  map_id X := by
    rw [← uncurry_map_eq F]
    exact (CategoryTheory.Functor.uncurry.obj F.map₂CochainComplex).map_id X
  map_comp f g := by
    rw [← uncurry_map_eq F, ← uncurry_map_eq F, ← uncurry_map_eq F]
    exact (CategoryTheory.Functor.uncurry.obj F.map₂CochainComplex).map_comp f g

private lemma tensorCone₁_naturality {A B A' B' K K' : CochainComplex C ℤ}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (k : K ⟶ K')
    (h : f ≫ b = a ≫ g)
    (ht : HomologicalComplex.mapBifunctorMap f (𝟙 K) F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap b k F (.up ℤ) =
      HomologicalComplex.mapBifunctorMap a k F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap g (𝟙 K') F (.up ℤ)) :
    mappingCone.map _ _ (HomologicalComplex.mapBifunctorMap a k F (.up ℤ))
        (HomologicalComplex.mapBifunctorMap b k F (.up ℤ)) ht ≫
        (mapBifunctorMappingCone₁Iso g K' F).inv =
      (mapBifunctorMappingCone₁Iso f K F).inv ≫
        HomologicalComplex.mapBifunctorMap (mappingCone.map f g a b h) k F (.up ℤ) := by
  apply (Cocycle.equivHom _ _).injective
  ext : 1
  rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1)]
  constructor
  · ext n m hnm p q hpq
    obtain rfl : m = n - 1 := by omega
    dsimp at hpq
    simp [mappingCone.map, mapBifunctorMappingCone₁Iso.inv,
      Cochain.comp_v _ _ (add_zero (-1)) n (n - 1) (n - 1) (by omega) (by omega),
      mapBifunctorMappingCone₁Iso.ι_ι₁_assoc _ _ _ p q n hpq (n - 1) (by omega) (p - 1)
        (by omega),
      mapBifunctorMappingCone₁Iso.ι_ι₁ _ _ _ p q n hpq (n - 1) (by omega) (p - 1) (by omega),
      NatTrans.naturality_assoc]
    simp only [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp,
      mappingCone.inl_v_desc_f, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  · ext n p q hpq
    simp [mappingCone.map, mapBifunctorMappingCone₁Iso.inv, NatTrans.naturality_assoc]
    simp only [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp,
      mappingCone.inr_f_desc_f, HomologicalComplex.comp_f]

/-- Total tensor of two complexes concentrated in degree zero.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
@[irreducible] noncomputable def totalSingleIso (L M : C) :
    HomologicalComplex.mapBifunctor
      ((HomologicalComplex.single C (.up ℤ) 0).obj L)
      ((HomologicalComplex.single C (.up ℤ) 0).obj M) F (.up ℤ) ≅
      (HomologicalComplex.single C (.up ℤ) 0).obj ((F.obj L).obj M) :=
  mapBifunctorSingle₁Iso F L ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (F.obj L) (.up ℤ) 0).app M

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private lemma ordinaryTensor_naturality {L M L' M' : C} (l : L ⟶ L') (m : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single C (.up ℤ) 0).map l)
        ((HomologicalComplex.single C (.up ℤ) 0).map m) F (.up ℤ) ≫ (totalSingleIso F L' M').hom =
      (totalSingleIso F L M).hom ≫ (HomologicalComplex.single C (.up ℤ) 0).map
        ((F.map l).app M ≫ (F.obj L').map m) := by
  unfold totalSingleIso
  rw [← cancel_epi ((mapBifunctorSingle₁Iso F L
    ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (F.obj L) (.up ℤ) 0).app M).inv)]
  rw [Iso.inv_hom_id_assoc]
  rw [← cancel_mono ((mapBifunctorSingle₁Iso F L'
    ((HomologicalComplex.single C (.up ℤ) 0).obj M') ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (F.obj L') (.up ℤ) 0).app M').inv)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [Iso.trans_inv, Iso.app_inv, HomologicalComplex.comp_f, Category.assoc,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      mapBifunctorSingle₁Iso_inv_f, HomologicalComplex.single_map_f_self]
    simp only [HomologicalComplex.ι_mapBifunctorMap,
      HomologicalComplex.single_map_f_self, CategoryTheory.Functor.map_comp,
      NatTrans.comp_app, Category.assoc]
    simp only [NatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      ← NatTrans.comp_app_assoc]
    simp only [Iso.inv_hom_id_assoc, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
      Category.assoc, NatTrans.naturality_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      ((F.obj L).obj M) n hn).eq_of_src _ _

end

section

variable {C : Type*} [Category C] [Abelian C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [∀ A B : CochainComplex C ℤ,
    HomologicalComplex.HasMapBifunctor A B (curriedTensor C) (.up ℤ)]

/-- Signed transposition of a total tensor complex.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
@[irreducible] noncomputable def totalSwap (K L : CochainComplex C ℤ) :
    HomologicalComplex.mapBifunctor K L (curriedTensor C) (.up ℤ) ≅
      HomologicalComplex.mapBifunctor L K (curriedTensor C) (.up ℤ) := by
  let T := curriedTensor C
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => β_ (K.X p) (L.X q)) (by
        intro q q' _
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' _
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

set_option backward.isDefEq.respectTransparency false in
private lemma totalSwap_ι (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor K L (curriedTensor C) (.up ℤ) p q n h ≫
        (totalSwap K L).hom.f n =
      (p * q).negOnePow • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor L K (curriedTensor C) (.up ℤ) q p n
          (by change q + p = n; omega)) := by
  simp [mul_comm, totalSwap, HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom]

private lemma totalSwap_naturality {A B K D : CochainComplex C ℤ}
  (a : A ⟶ B) (b : K ⟶ D) :
  HomologicalComplex.mapBifunctorMap a b (curriedTensor C) (.up ℤ) ≫ (totalSwap B D).hom =
    (totalSwap A K).hom ≫ HomologicalComplex.mapBifunctorMap b a (curriedTensor C) (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  dsimp at hpq
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [totalSwap_ι]
  conv_rhs => rw [← Category.assoc, totalSwap_ι]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  congr 1
  dsimp only [curriedTensor_obj_map, curriedTensor_map_app]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc, whisker_exchange_assoc]

private lemma totalCone₂Swap_naturality
    {A B A' B' K K' : CochainComplex C ℤ}
    (k : K ⟶ K') (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g)
    (ht : HomologicalComplex.mapBifunctorMap (𝟙 K) f (curriedTensor C) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap k b (curriedTensor C) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap k a (curriedTensor C) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K') g (curriedTensor C) (.up ℤ)) :
    CochainComplex.mappingCone.map _ _
        (HomologicalComplex.mapBifunctorMap k a (curriedTensor C) (.up ℤ))
        (HomologicalComplex.mapBifunctorMap k b (curriedTensor C) (.up ℤ)) ht ≫
        ((CochainComplex.mapBifunctorMappingCone₂Iso K' g (curriedTensor C)).symm ≪≫
          totalSwap K' (CochainComplex.mappingCone g)).hom =
      ((CochainComplex.mapBifunctorMappingCone₂Iso K f (curriedTensor C)).symm ≪≫
          totalSwap K (CochainComplex.mappingCone f)).hom ≫
        HomologicalComplex.mapBifunctorMap (CochainComplex.mappingCone.map f g a b h)
          k (curriedTensor C) (.up ℤ) := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc,
    CochainComplex.mapBifunctorMappingCone₂Iso_inv_naturality]
  rw [Category.assoc, totalSwap_naturality, Category.assoc]

end

variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max u v})

/-- The existing module-sheaf category. Source: Stacks 06YP
(blueprint: lem-pur-kflat-cone-comparison). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{max u v, max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Degree-zero embedding. Source: Stacks 06YU
(blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable abbrev single := HomologicalComplex.single (Modules R) (.up ℤ) (0 : ℤ)

@[irreducible] noncomputable local instance moduleMonoidal :
    MonoidalCategory (Modules R) :=
  SheafOfModules.monoidalCategory R
local instance : MonoidalPreadditive (Modules R) := by
  unfold moduleMonoidal
  exact SheafOfModules.cochainModulesPreadditive R
noncomputable local instance moduleSymmetric : SymmetricCategory (Modules R) := by
  unfold moduleMonoidal
  exact SheafOfModules.symmetricCategory R

/-- The existing sheaf tensor bifunctor. Source: Stacks 06YM
(blueprint: lem-pur-kflat-cone-comparison). -/
@[reducible] noncomputable def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  curriedTensor (Modules R)

noncomputable local instance uniformTotal (A B : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasMapBifunctor A B (curriedTensor (Modules R)) (.up ℤ) :=
  by unfold moduleMonoidal; infer_instance

/-- The existing total tensor bifunctor. Source: Stacks 06YM
(blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  totalBifunctor (curriedTensor (Modules R))

set_option backward.isDefEq.respectTransparency false in
private theorem total_eq_uncurry : total R =
    CategoryTheory.Functor.uncurry.obj
      ((curriedTensor (Modules R)).map₂CochainComplex) := by
  refine CategoryTheory.Functor.ext (F := total R)
    (G := CategoryTheory.Functor.uncurry.obj
      ((curriedTensor (Modules R)).map₂CochainComplex)) (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (uncurry_map_eq (C := Modules R) (curriedTensor (Modules R)) f).symm

/-- The resolving class of the cited descent theorem, on complexes.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
def resolving : ObjectProperty (CochainComplex (Modules R) ℤ) := fun P =>
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
      (J := J) (R := R) (P.X n)

/-- The two augmented bounded-above flat K-flat resolutions, with all hypotheses.
Source: Stacks 06YP, 06YS, 06YT (blueprint: lem-pur-kflat-cone-comparison). -/
structure Pair where
  L : Modules R
  M : Modules R
  P : CochainComplex (Modules R) ℤ
  K : CochainComplex (Modules R) ℤ
  q : P ⟶ (single R).obj L
  ε : K ⟶ (single R).obj M
  q_quasiIso : QuasiIso q
  ε_quasiIso : QuasiIso ε
  P_bounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)
  K_bounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)
  P_resolving : resolving R P
  K_resolving : resolving R K

variable {R}

/-- Morphisms of both augmented resolutions, allowing maps of L and M as well.
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
structure Hom (r s : Pair R) where
  l : r.L ⟶ s.L
  m : r.M ⟶ s.M
  p : r.P ⟶ s.P
  k : r.K ⟶ s.K
  q_comm : p ≫ s.q = r.q ≫ (single R).map l
  ε_comm : k ≫ s.ε = r.ε ≫ (single R).map m

variable (R)

/-- Canonical identification of the lower-right vertex with (L tensor M)[0].
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def ordinaryIso (L M : Modules R) :
    (total R).obj ((single R).obj L, (single R).obj M) ≅
      (single R).obj (((tensor R).obj L).obj M) :=
  totalSingleIso (curriedTensor (Modules R)) L M

/-- Koszul symmetry, induced by sheaf braiding and signed total-complex transposition.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def swap (K L : CochainComplex (Modules R) ℤ) :
    (total R).obj (K, L) ≅ (total R).obj (L, K) := by
  exact totalSwap K L

/-- Canonical map of cones from a commuting square, for the stated Y plus X[1] convention.
Source: Stacks 05RU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def coneMap {A B A' B' : CochainComplex (Modules R) ℤ}
    {f : A ⟶ B} {g : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ g = f ≫ b) : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  CochainComplex.mappingCone.map f g a b h.symm

/-- Restriction of Q times Q to the resolving complexes of tensor descent.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
@[reducible] noncomputable def localizationPair [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι ⋙ DerivedCategory.Q).prod ((resolving R).ι ⋙ DerivedCategory.Q)

/-- Total tensor followed by Q on the same resolving class.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
@[reducible] noncomputable def resolvedTensor [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q

/-- The resolved pair as an object of the resolving product category.
Source: Stacks 06YS (blueprint: lem-pur-kflat-cone-comparison). -/
abbrev resolvedPair (r : Pair R) : (resolving R).FullSubcategory ×
    (resolving R).FullSubcategory :=
  (⟨r.P, r.P_resolving⟩, ⟨r.K, r.K_resolving⟩)

section

variable [HasDerivedCategory.{w} (Modules R)]

/-- The canonical derived-to-ordinary map in a model with its natural representative iso.
This is the tensor augmentation roof, not an arbitrary morphism or a choice from existence.
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
@[irreducible] noncomputable def comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
      DerivedCategory.Q.obj ((single R).obj r.M)) ⟶
        DerivedCategory.Q.obj ((single R).obj (((tensor R).obj r.L).obj r.M)) :=
  letI := r.q_quasiIso
  letI := r.ε_quasiIso
  (T.mapIso ((asIso (DerivedCategory.Q.map r.q)).prod
    (asIso (DerivedCategory.Q.map r.ε)))).inv ≫
    ρ.inv.app (resolvedPair R r) ≫ DerivedCategory.Q.map ((total R).map (r.q ×ₘ r.ε)) ≫
      DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom

end

set_option backward.defeqAttrib.useBackward true


private lemma coneMap_eq {A B A' B' : CochainComplex (Modules R) ℤ}
    {f : A ⟶ B} {g : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ g = f ≫ b) :
    coneMap R a b h = CochainComplex.mappingCone.map f g a b h.symm := by
  rfl

private lemma acyclic_of_iso {A B : CochainComplex (Modules R) ℤ} (e : A ≅ B)
    (h : B.Acyclic) : A.Acyclic := by
  intro i
  exact (exactAt_iff_of_quasiIsoAt e.hom i).2 (h i)

private lemma total_map {A B A' B' : CochainComplex (Modules R) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    (total R).map (f ×ₘ g) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (Modules R)) (.up ℤ) := by
  rfl

private lemma tensorMap_comp {A B C D E G : CochainComplex (Modules R) ℤ}
    (f : A ⟶ B) (g : C ⟶ D) (f' : B ⟶ E) (g' : D ⟶ G) :
    (total R).map (f ×ₘ g) ≫ (total R).map (f' ×ₘ g') =
      (total R).map ((f ≫ f') ×ₘ (g ≫ g')) :=
  ((total R).map_comp (f ×ₘ g) (f' ×ₘ g')).symm

@[irreducible] private noncomputable def leftIso (r : Pair R) :
    CochainComplex.mappingCone ((total R).map (r.q ×ₘ 𝟙 r.K)) ≅
      (total R).obj (CochainComplex.mappingCone r.q, r.K) := by
  exact (CochainComplex.mapBifunctorMappingCone₁Iso r.q r.K (curriedTensor (Modules R))).symm

@[irreducible] private noncomputable def topIso (r : Pair R) :
    CochainComplex.mappingCone ((total R).map (𝟙 r.P ×ₘ r.ε)) ≅
      (total R).obj (CochainComplex.mappingCone r.ε, r.P) := by
  exact (CochainComplex.mapBifunctorMappingCone₂Iso r.P r.ε (curriedTensor (Modules R))).symm ≪≫
    swap R r.P (CochainComplex.mappingCone r.ε)

private lemma leftIso_inr (r : Pair R) :
    CochainComplex.mappingCone.inr ((total R).map (r.q ×ₘ 𝟙 r.K)) ≫ (leftIso R r).hom =
      (total R).map (CochainComplex.mappingCone.inr r.q ×ₘ 𝟙 r.K) := by
  unfold leftIso
  exact CochainComplex.mapBifunctorMappingCone₁Iso.inr_inv r.q r.K (curriedTensor (Modules R))

private lemma topIso_inr (r : Pair R) :
    CochainComplex.mappingCone.inr ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (topIso R r).hom =
      (total R).map (𝟙 r.P ×ₘ CochainComplex.mappingCone.inr r.ε) ≫
        (swap R r.P (CochainComplex.mappingCone r.ε)).hom := by
  unfold topIso
  exact CochainComplex.mapBifunctorMappingCone₂Iso.inr_inv_assoc r.P r.ε
    (curriedTensor (Modules R)) (swap R r.P (CochainComplex.mappingCone r.ε)).hom

private lemma quasiIso_top (r : Pair R) : QuasiIso ((total R).map (𝟙 r.P ×ₘ r.ε)) := by
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  apply acyclic_of_iso R (topIso R r)
  change (HomologicalComplex.mapBifunctor (CochainComplex.mappingCone r.ε) r.P
    (curriedTensor (Modules R)) (.up ℤ)).Acyclic
  unfold moduleMonoidal
  exact r.P_resolving.1 _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic r.ε).1
    r.ε_quasiIso)

private lemma quasiIso_left (r : Pair R) : QuasiIso ((total R).map (r.q ×ₘ 𝟙 r.K)) := by
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  apply acyclic_of_iso R (leftIso R r)
  change (HomologicalComplex.mapBifunctor (CochainComplex.mappingCone r.q) r.K
    (curriedTensor (Modules R)) (.up ℤ)).Acyclic
  unfold moduleMonoidal
  exact r.K_resolving.1 _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic r.q).1
    r.q_quasiIso)

private lemma swap_naturality {A B C D : CochainComplex (Modules R) ℤ}
    (a : A ⟶ B) (b : C ⟶ D) :
    (total R).map (a ×ₘ b) ≫ (swap R B D).hom =
      (swap R A C).hom ≫ (total R).map (b ×ₘ a) := by
  change HomologicalComplex.mapBifunctorMap a b (curriedTensor (Modules R)) (.up ℤ) ≫
      (totalSwap B D).hom =
    (totalSwap A C).hom ≫
      HomologicalComplex.mapBifunctorMap b a (curriedTensor (Modules R)) (.up ℤ)
  exact totalSwap_naturality (C := Modules R) a b

private lemma leftIso_naturality {r s : Pair R} (f : Hom r s)
  (h : (total R).map (f.p ×ₘ f.k) ≫ (total R).map (s.q ×ₘ 𝟙 s.K) =
    (total R).map (r.q ×ₘ 𝟙 r.K) ≫
      (total R).map ((single R).map f.l ×ₘ f.k)) :
  coneMap R ((total R).map (f.p ×ₘ f.k))
      ((total R).map ((single R).map f.l ×ₘ f.k)) h ≫ (leftIso R s).hom =
    (leftIso R r).hom ≫
      (total R).map (coneMap R f.p ((single R).map f.l) f.q_comm ×ₘ f.k) := by
  rw [coneMap_eq, coneMap_eq]
  unfold leftIso
  exact tensorCone₁_naturality (C := Modules R) (curriedTensor (Modules R))
    r.q s.q f.p ((single R).map f.l) f.k f.q_comm.symm h.symm

set_option maxHeartbeats 60000 in
-- Matching the two cone comparisons requires the simultaneous tensor-map formula.
private lemma topIso_naturality {r s : Pair R} (f : Hom r s)
    (h : ((total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k)) ≫
        (total R).map (𝟙 s.P ×ₘ s.ε) =
      (total R).map (𝟙 r.P ×ₘ r.ε) ≫
        (total R).map (f.p ×ₘ (single R).map f.m)) :
    coneMap R ((total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k))
        ((total R).map (f.p ×ₘ (single R).map f.m)) h ≫ (topIso R s).hom =
      (topIso R r).hom ≫
        (total R).map (coneMap R f.k ((single R).map f.m) f.ε_comm ×ₘ f.p) := by
  have hc : (total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k) =
      (total R).map (f.p ×ₘ f.k) := by
    simp only [tensorMap_comp R, Category.comp_id, Category.id_comp]
  simp only [hc] at h ⊢
  rw [coneMap_eq, coneMap_eq]
  unfold topIso swap
  exact totalCone₂Swap_naturality (C := Modules R) f.p r.ε s.ε f.k
    ((single R).map f.m) f.ε_comm.symm h.symm

private lemma ordinary_naturality {L M L' M' : Modules R} (l : L ⟶ L') (m : M ⟶ M') :
  (total R).map ((single R).map l ×ₘ (single R).map m) ≫ (ordinaryIso R L' M').hom =
    (ordinaryIso R L M).hom ≫ (single R).map
      (((curriedTensor (Modules R)).map l).app M ≫
        ((curriedTensor (Modules R)).obj L').map m) := by
  unfold ordinaryIso
  exact ordinaryTensor_naturality (C := Modules R) (curriedTensor (Modules R)) l m


private theorem square (r : Pair R) :
    (total R).map (r.q ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 _ ×ₘ r.ε) =
      (total R).map (𝟙 r.P ×ₘ r.ε) ≫ (total R).map (r.q ×ₘ 𝟙 _) := by
  simp only [tensorMap_comp R, Category.id_comp, Category.comp_id]

private theorem top_square {r s : Pair R} (f : Hom r s) :
    (total R).map (f.p ×ₘ f.k) ≫ (total R).map (𝟙 s.P ×ₘ s.ε) =
      (total R).map (𝟙 r.P ×ₘ r.ε) ≫
        (total R).map (f.p ×ₘ (single R).map f.m) := by
  simp only [tensorMap_comp R, Category.comp_id, Category.id_comp, f.ε_comm]

private theorem left_square {r s : Pair R} (f : Hom r s) :
    (total R).map (f.p ×ₘ f.k) ≫ (total R).map (s.q ×ₘ 𝟙 s.K) =
      (total R).map (r.q ×ₘ 𝟙 r.K) ≫
        (total R).map ((single R).map f.l ×ₘ f.k) := by
  simp only [tensorMap_comp R, Category.comp_id, Category.id_comp, f.q_comm]

section

variable [HasDerivedCategory.{w} (Modules R)]

private noncomputable def representativeIso
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    DerivedCategory.Q.obj ((total R).obj (r.P, r.K)) ≅
      T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
        DerivedCategory.Q.obj ((single R).obj r.M)) := by
  have := r.q_quasiIso
  have := r.ε_quasiIso
  exact ρ.app (resolvedPair R r) ≪≫
    T.mapIso ((asIso (DerivedCategory.Q.map r.q)).prod
      (asIso (DerivedCategory.Q.map r.ε)))

private theorem representative_comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    (representativeIso R T ρ r).hom ≫ comparison R T ρ r =
      DerivedCategory.Q.map ((total R).map (r.q ×ₘ r.ε)) ≫
        DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom := by
  have := r.q_quasiIso
  have := r.ε_quasiIso
  simp only [representativeIso, comparison, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.app_hom, Iso.hom_inv_id_app_assoc]


private theorem representative_naturality
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) {r s : Pair R} (f : Hom r s) :
    DerivedCategory.Q.map ((total R).map (f.p ×ₘ f.k)) ≫
        (representativeIso R T ρ s).hom =
      (representativeIso R T ρ r).hom ≫
        T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
          DerivedCategory.Q.map ((single R).map f.m)) := by
  have := r.q_quasiIso
  have := r.ε_quasiIso
  have := s.q_quasiIso
  have := s.ε_quasiIso
  let ff : resolvedPair R r ⟶ resolvedPair R s :=
    (ObjectProperty.homMk (X := (resolvedPair R r).1)
      (Y := (resolvedPair R s).1) f.p) ×ₘ
    (ObjectProperty.homMk (X := (resolvedPair R r).2)
      (Y := (resolvedPair R s).2) f.k)
  have hn := ρ.hom.naturality ff
  change DerivedCategory.Q.map ((total R).map (f.p ×ₘ f.k)) ≫
      ρ.hom.app (resolvedPair R s) =
    ρ.hom.app (resolvedPair R r) ≫
      T.map (DerivedCategory.Q.map f.p ×ₘ DerivedCategory.Q.map f.k) at hn
  change DerivedCategory.Q.map ((total R).map (f.p ×ₘ f.k)) ≫
      (ρ.hom.app (resolvedPair R s) ≫
        T.map (DerivedCategory.Q.map s.q ×ₘ DerivedCategory.Q.map s.ε)) =
    (ρ.hom.app (resolvedPair R r) ≫
      T.map (DerivedCategory.Q.map r.q ×ₘ DerivedCategory.Q.map r.ε)) ≫ _
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, prod_comp, f.q_comm, f.ε_comm]

private noncomputable def derivedIso
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    DerivedCategory.Q.obj ((total R).obj (r.P, (single R).obj r.M)) ≅
      T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
        DerivedCategory.Q.obj ((single R).obj r.M)) := by
  have := quasiIso_top R r
  exact (asIso (DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)))).symm ≪≫
    representativeIso R T ρ r

private lemma derivedIso_normalization
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (derivedIso R T ρ r).hom =
      ρ.hom.app (resolvedPair R r) ≫
        T.map (DerivedCategory.Q.map r.q ×ₘ DerivedCategory.Q.map r.ε) := by
  have := quasiIso_top R r
  simp only [derivedIso, representativeIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, Iso.app_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.prod_hom]

private lemma derivedIso_comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    (derivedIso R T ρ r).hom ≫ comparison R T ρ r =
      DerivedCategory.Q.map ((total R).map (r.q ×ₘ 𝟙 _)) ≫
        DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom := by
  have := quasiIso_top R r
  rw [← cancel_epi (DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)))]
  rw [← Category.assoc, derivedIso_normalization]
  change (representativeIso R T ρ r).hom ≫ _ = _
  rw [representative_comparison]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  simp only [tensorMap_comp R, Category.id_comp, Category.comp_id]

private lemma derivedIso_naturality
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) {r s : Pair R} (f : Hom r s) :
    DerivedCategory.Q.map ((total R).map (f.p ×ₘ (single R).map f.m)) ≫
        (derivedIso R T ρ s).hom =
      (derivedIso R T ρ r).hom ≫
        T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
          DerivedCategory.Q.map ((single R).map f.m)) := by
  have := quasiIso_top R r
  rw [← cancel_epi (DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)))]
  have hnorm (t : Pair R) :
      DerivedCategory.Q.map ((total R).map (𝟙 t.P ×ₘ t.ε)) ≫
        (derivedIso R T ρ t).hom = (representativeIso R T ρ t).hom := by
    exact derivedIso_normalization R T ρ t
  calc
    _ = DerivedCategory.Q.map ((total R).map (f.p ×ₘ f.k)) ≫
        (representativeIso R T ρ s).hom := by
      simpa only [CategoryTheory.Functor.map_comp, Category.assoc, hnorm] using
        congrArg (fun z ↦ DerivedCategory.Q.map z ≫ (derivedIso R T ρ s).hom)
          (top_square R f).symm
    _ = (representativeIso R T ρ r).hom ≫ _ := representative_naturality R T ρ f
    _ = _ := by rw [← hnorm, Category.assoc]

private lemma comparison_naturality
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) {r s : Pair R} (f : Hom r s) :
    T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
        DerivedCategory.Q.map ((single R).map f.m)) ≫ comparison R T ρ s =
      comparison R T ρ r ≫ DerivedCategory.Q.map ((single R).map
        (((tensor R).map f.l).app r.M ≫ ((tensor R).obj s.L).map f.m)) := by
  rw [← cancel_epi (derivedIso R T ρ r).hom]
  rw [← Category.assoc, ← derivedIso_naturality R T ρ f, Category.assoc,
    derivedIso_comparison, ← Category.assoc (derivedIso R T ρ r).hom, derivedIso_comparison]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  have hs : (total R).map (f.p ×ₘ (single R).map f.m) ≫
      (total R).map (s.q ×ₘ 𝟙 ((single R).obj s.M)) =
      (total R).map (r.q ×ₘ 𝟙 ((single R).obj r.M)) ≫
        (total R).map ((single R).map f.l ×ₘ (single R).map f.m) := by
    simp only [tensorMap_comp R, Category.id_comp, Category.comp_id, f.q_comm]
  rw [← Category.assoc, hs, Category.assoc, ordinary_naturality, Category.assoc]

/-- The complete two-resolution augmentation comparison, including natural cone isomorphisms
and the normalization identifying the right arrow with the canonical tensor augmentation roof.
The parameter ρ is the natural representative comparison of the derived tensor model supplied
by `lem-weil-pbc-site-derived-tensor-descent`; thus the assertion applies to any such model.

Source: Stacks Project, Tags 06YM, 06YP, 06YS, 06YT, 06YU and Definition 05RU
(blueprint: lem-pur-kflat-cone-comparison).

Proof: bifunctoriality gives the square. The cones of q and ε are acyclic by
`lem-pur-quasi-iso-cone-acyclic`. K-flatness makes Cone(ε) tensor P and Cone(q) tensor K
acyclic. The signed tensor-cone isomorphisms of `lem-pc-tensor-mapping-cone-iso`, followed
in the top case by Koszul symmetry, identify these with the top and left cones; the
cone criterion proves both quasi-isomorphisms. Their inclusions and naturality follow
from the same signed formulas. Tensor descent identifies Q(P tensor K) with the derived
tensor; composing ρ with T(Qq,Qε) identifies it with L derived-tensor M. Invert the top
arrow to obtain e. Bifunctoriality then cancels the top arrow in the augmentation roof,
so the right arrow is precisely the canonical comparison. If the bottom arrow is a
quasi-isomorphism, cohomology and two-out-of-three make the right arrow invertible.
Naturality of tensor, cones and ρ gives all morphism-of-resolution compatibilities. -/
theorem augmentation_square
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) :
    ∃ (topCone : ∀ r : Pair R,
        CochainComplex.mappingCone ((total R).map (𝟙 r.P ×ₘ r.ε)) ≅
          (total R).obj (CochainComplex.mappingCone r.ε, r.P))
      (leftCone : ∀ r : Pair R,
        CochainComplex.mappingCone ((total R).map (r.q ×ₘ 𝟙 r.K)) ≅
          (total R).obj (CochainComplex.mappingCone r.q, r.K))
      (e : ∀ r : Pair R,
        DerivedCategory.Q.obj ((total R).obj (r.P, (single R).obj r.M)) ≅
          T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
            DerivedCategory.Q.obj ((single R).obj r.M))),
      ∀ r : Pair R,
        (total R).map (r.q ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 _ ×ₘ r.ε) =
          (total R).map (𝟙 r.P ×ₘ r.ε) ≫ (total R).map (r.q ×ₘ 𝟙 _) ∧
        QuasiIso ((total R).map (𝟙 r.P ×ₘ r.ε)) ∧
        QuasiIso ((total R).map (r.q ×ₘ 𝟙 r.K)) ∧
        CochainComplex.mappingCone.inr ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (topCone r).hom =
          (total R).map (𝟙 r.P ×ₘ CochainComplex.mappingCone.inr r.ε) ≫
            (swap R r.P (CochainComplex.mappingCone r.ε)).hom ∧
        CochainComplex.mappingCone.inr ((total R).map (r.q ×ₘ 𝟙 r.K)) ≫ (leftCone r).hom =
          (total R).map (CochainComplex.mappingCone.inr r.q ×ₘ 𝟙 r.K) ∧
        DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (e r).hom =
          ρ.hom.app (resolvedPair R r) ≫
            T.map (DerivedCategory.Q.map r.q ×ₘ DerivedCategory.Q.map r.ε) ∧
        (e r).hom ≫ comparison R T ρ r =
          DerivedCategory.Q.map ((total R).map (r.q ×ₘ 𝟙 _)) ≫
            DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom ∧
        (QuasiIso ((total R).map (𝟙 ((single R).obj r.L) ×ₘ r.ε)) →
          IsIso (comparison R T ρ r)) ∧
        ∀ (s : Pair R) (f : Hom r s),
          (∃ (ht : (total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k) ≫
                (total R).map (𝟙 s.P ×ₘ s.ε) =
              (total R).map (𝟙 r.P ×ₘ r.ε) ≫
                (total R).map (f.p ×ₘ (single R).map f.m))
            (hl : (total R).map (f.p ×ₘ f.k) ≫ (total R).map (s.q ×ₘ 𝟙 s.K) =
              (total R).map (r.q ×ₘ 𝟙 r.K) ≫
                (total R).map ((single R).map f.l ×ₘ f.k)),
            coneMap R ((total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k))
                ((total R).map (f.p ×ₘ (single R).map f.m)) ht ≫ (topCone s).hom =
              (topCone r).hom ≫
                (total R).map (coneMap R f.k ((single R).map f.m) f.ε_comm ×ₘ f.p) ∧
            coneMap R ((total R).map (f.p ×ₘ f.k))
                ((total R).map ((single R).map f.l ×ₘ f.k)) hl ≫ (leftCone s).hom =
              (leftCone r).hom ≫
                (total R).map (coneMap R f.p ((single R).map f.l) f.q_comm ×ₘ f.k)) ∧
          DerivedCategory.Q.map ((total R).map (f.p ×ₘ (single R).map f.m)) ≫ (e s).hom =
            (e r).hom ≫ T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
              DerivedCategory.Q.map ((single R).map f.m)) ∧
          T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
              DerivedCategory.Q.map ((single R).map f.m)) ≫ comparison R T ρ s =
            comparison R T ρ r ≫ DerivedCategory.Q.map ((single R).map
              (((tensor R).map f.l).app r.M ≫ ((tensor R).obj s.L).map f.m)) := by
  classical
  refine ⟨topIso R, leftIso R, derivedIso R T ρ, fun r ↦ ?_⟩
  refine ⟨square R r, quasiIso_top R r, quasiIso_left R r,
    topIso_inr R r, leftIso_inr R r, derivedIso_normalization R T ρ r,
    derivedIso_comparison R T ρ r, ?_, ?_⟩
  · intro hb
    have := quasiIso_top R r
    have := quasiIso_left R r
    have hi : QuasiIso ((total R).map (𝟙 r.P ×ₘ r.ε) ≫
        (total R).map (r.q ×ₘ 𝟙 ((single R).obj r.M))) := by
      rw [← square R r]
      infer_instance
    have := quasiIso_of_comp_left ((total R).map (𝟙 r.P ×ₘ r.ε))
      ((total R).map (r.q ×ₘ 𝟙 ((single R).obj r.M)))
    have he := derivedIso_comparison R T ρ r
    have hf : comparison R T ρ r = (derivedIso R T ρ r).inv ≫
        DerivedCategory.Q.map ((total R).map (r.q ×ₘ 𝟙 _)) ≫
          DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [hf]
    infer_instance
  · intro s f
    refine ⟨?_, derivedIso_naturality R T ρ f, comparison_naturality R T ρ f⟩
    have ht : (total R).map (f.p ×ₘ 𝟙 r.K) ≫
        (total R).map (𝟙 s.P ×ₘ f.k) ≫ (total R).map (𝟙 s.P ×ₘ s.ε) =
        (total R).map (𝟙 r.P ×ₘ r.ε) ≫
          (total R).map (f.p ×ₘ (single R).map f.m) := by
      simpa only [tensorMap_comp R, Category.id_comp, Category.comp_id]
        using top_square R f
    exact ⟨ht, left_square R f, topIso_naturality R f ht,
      leftIso_naturality R f (left_square R f)⟩

end

end SheafOfModules.KFlatConeComparison
