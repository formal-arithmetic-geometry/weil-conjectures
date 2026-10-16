/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Naturality of the injective-resolution computation

Source: Stacks Project, Tag 0156, Lemma 13.20.1.
(blueprint: lem-sp-derived-injective-resolution-naturality).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- A commuting square of quasi-isomorphisms induces a quasi-isomorphism on cones.
Source: Stacks Project, Tag 014A (five lemma for distinguished triangles)
(blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. Localize the morphism of mapping-cone triangles. Its first two components
are isomorphisms, hence so is its third component. Localization reflects
quasi-isomorphisms. -/
theorem quasiIso_map_of_quasiIso
    {K L I J : CochainComplex C ℤ} (f : K ⟶ L) (g : I ⟶ J)
    (a : K ⟶ I) (b : L ⟶ J) (h : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] : QuasiIso (map f g a b h) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
  let φ := DerivedCategory.Q.mapTriangle.map (triangleMap f g a b h)
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ φ
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (by change IsIso (DerivedCategory.Q.map a); infer_instance)
    (by change IsIso (DerivedCategory.Q.map b); infer_instance)

end CochainComplex.mappingCone

namespace CochainComplex.Plus

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual mapping cone in the category of bounded-below cochain complexes. -/
noncomputable def mappingCone {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus C :=
  ⟨CochainComplex.mappingCone f.hom, by
    obtain ⟨n, hn⟩ := K.property
    obtain ⟨m, hm⟩ := L.property
    exact ⟨min (n - 1) m,
      CochainComplex.isStrictlyGE_mappingCone f.hom n m _ (by omega) (by omega)⟩⟩

/-- A strictly commuting square gives the specified map between bounded-below cones. -/
noncomputable def mappingConeMap
    {K L I J : CochainComplex.Plus C} (f : K ⟶ L) (g : I ⟶ J)
    (a : K ⟶ I) (b : L ⟶ J) (h : f ≫ b = a ≫ g) :
    mappingCone f ⟶ mappingCone g :=
  ObjectProperty.homMk (CochainComplex.mappingCone.map f.hom g.hom a.hom b.hom
    (congrArg (fun k ↦ k.hom) h))

/-- A square of quasi-isomorphisms remains a quasi-isomorphism on bounded-below cones. -/
theorem mappingConeMap_quasiIso [HasDerivedCategory C]
    {K L I J : CochainComplex.Plus C} (f : K ⟶ L) (g : I ⟶ J)
    (a : K ⟶ I) (b : L ⟶ J) (h : f ≫ b = a ≫ g)
    [QuasiIso a.hom] [QuasiIso b.hom] : QuasiIso (mappingConeMap f g a b h).hom :=
  CochainComplex.mappingCone.quasiIso_map_of_quasiIso f.hom g.hom a.hom b.hom
    (congrArg (fun k ↦ k.hom) h)

/-- Mapping cones form a functor on arrows of bounded-below complexes. -/
noncomputable def mappingConeFunctor :
    ComposableArrows (CochainComplex.Plus C) 1 ⥤ CochainComplex.Plus C where
  obj f := mappingCone (f.map' 0 1)
  map φ := mappingConeMap _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  map_id f := by
    apply ObjectProperty.hom_ext
    exact CochainComplex.mappingCone.map_id _
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    exact CochainComplex.mappingCone.map_comp _ _ _ _ _
      (congrArg (fun k ↦ k.hom) (ComposableArrows.naturality' φ 0 1)) _ _
      (congrArg (fun k ↦ k.hom) (ComposableArrows.naturality' ψ 0 1))

/-- Cones of maps between termwise injective complexes are termwise injective. -/
theorem mappingCone_injective
    {I J : CochainComplex.Plus C} (g : I ⟶ J)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (n : ℤ) :
    Injective ((mappingCone g).obj.X n) :=
  Injective.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod g.hom n (n + 1) rfl).symm
    inferInstance

end CochainComplex.Plus

namespace CategoryTheory.Functor

variable {B : Type u} [Category.{v} B] [Abelian B] [EnoughInjectives B]
variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable [HasDerivedCategory B] [HasDerivedCategory C]
variable (G : B ⥤ C) [G.Additive]

/-- The canonical unit computation on injective complexes is natural for chain maps.
Source: Stacks Project, Tag 0156 (blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. Apply naturality of the derived-functor unit and invert its two components.
Apply cohomology and then the natural comparisons from derived to complex cohomology. -/
theorem homologyRightDerivedFunctorPlusObjQIsoOfInjective_naturality
    {I J : CochainComplex.Plus B}
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (g : I ⟶ J) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g)) ≫
        (G.homologyRightDerivedFunctorPlusObjQIsoOfInjective J n).hom =
      (G.homologyRightDerivedFunctorPlusObjQIsoOfInjective I n).hom ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map g.hom) n := by
  have hu := G.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient B).map g)
  dsimp only [Functor.comp_map] at hu
  have hinv :
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) ≫
          CategoryTheory.inv (G.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient B).obj J)) =
        CategoryTheory.inv (G.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient B).obj I)) ≫
          DerivedCategory.Plus.Qh.map
            (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map g)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hu.symm
  dsimp only [homologyRightDerivedFunctorPlusObjQIsoOfInjective,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  rw [← Functor.map_comp_assoc, hinv, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  have h₁ := (DerivedCategory.homologyFunctorFactorsh C n).hom.naturality
    (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map g)).hom
  have h₂ := (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.naturality
    ((G.mapHomologicalComplex (.up ℤ)).map g.hom)
  dsimp only [Functor.comp_map] at h₁ h₂
  erw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (_ ≫ ·) h₂

/-- Compute the whole derived object through a specified injective resolution.
The comparison is the mapped augmentation followed by the inverse derived unit. -/
noncomputable def rightDerivedFunctorPlusResolutionIso
    {K I : CochainComplex.Plus B} (a : K ⟶ I) [QuasiIso a.hom]
    [∀ n : ℤ, Injective (I.obj.X n)] :
    G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Qh.obj
        (G.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient B).obj I)) := by
  have : IsIso (DerivedCategory.Plus.Q.map a) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso a.hom›)
  exact G.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map a)) ≪≫
    (asIso (G.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient B).obj I))).symm

/-- Naturality holds already in the bounded-below derived category, before cohomology. -/
@[reassoc]
theorem rightDerivedFunctorPlusResolutionIso_naturality
    {K L I J : CochainComplex.Plus B} (a : K ⟶ I) (b : L ⟶ J)
    [QuasiIso a.hom] [QuasiIso b.hom]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (f : K ⟶ L) (g : I ⟶ J) (h : a ≫ g = f ≫ b) :
    G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (G.rightDerivedFunctorPlusResolutionIso b).hom =
      (G.rightDerivedFunctorPlusResolutionIso a).hom ≫
        DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map g)) := by
  dsimp only [rightDerivedFunctorPlusResolutionIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, asIso_inv]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← h,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a) ≫ ·)
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (G.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient B).map g)).symm

/-- The cone of a square of specified injective resolutions computes the whole
right derived object on its source cone, with the inverse-unit normalization.
Source: Stacks Project, Tags 014A and 0156
(blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. The cone map is a quasi-isomorphism by the distinguished-triangle five
lemma. Its target cone is bounded below and its terms are finite biproducts of
injectives. Apply the proved specified-resolution comparison to this cone map. -/
noncomputable def rightDerivedFunctorPlusConeResolutionIso
    {K L I J : CochainComplex.Plus B} (f : K ⟶ L) (g : I ⟶ J)
    (a : K ⟶ I) (b : L ⟶ J) (h : f ≫ b = a ≫ g)
    [QuasiIso a.hom] [QuasiIso b.hom]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] :
    G.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (CochainComplex.Plus.mappingCone f)) ≅
      DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient B).obj (CochainComplex.Plus.mappingCone g))) := by
  have : QuasiIso (CochainComplex.Plus.mappingConeMap f g a b h).hom :=
    CochainComplex.Plus.mappingConeMap_quasiIso f g a b h
  have (n : ℤ) : Injective ((CochainComplex.Plus.mappingCone g).obj.X n) :=
    CochainComplex.Plus.mappingCone_injective g n
  exact G.rightDerivedFunctorPlusResolutionIso
    (CochainComplex.Plus.mappingConeMap f g a b h)

/-- A whole diagram of specified injective resolutions computes the derived
functor naturally. This applies to all cutoffs of a truncation tower at once.
Source: Stacks Project, Tag 0156
(blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. At each object use the mapped augmentation followed by the inverse unit.
The diagram's augmentation naturality square and the proved derived-object
naturality theorem give the required square for each indexing morphism. -/
noncomputable def rightDerivedFunctorPlusResolutionNatIso
    {D : Type*} [Category* D] (K I : D ⥤ CochainComplex.Plus B) (a : K ⟶ I)
    [∀ d : D, QuasiIso (a.app d).hom]
    [∀ (d : D) (n : ℤ), Injective (((I.obj d).obj).X n)] :
    K ⋙ DerivedCategory.Plus.Q ⋙ G.rightDerivedFunctorPlus ≅
      I ⋙ HomotopyCategory.Plus.quotient B ⋙ G.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh :=
  NatIso.ofComponents (fun d ↦ G.rightDerivedFunctorPlusResolutionIso (a.app d))
    (fun f ↦ G.rightDerivedFunctorPlusResolutionIso_naturality _ _
      (K.map f) (I.map f) (a.naturality f).symm)

/-- A whole diagram of interval cones of specified injective resolutions computes
its derived image naturally, including all commuting maps between intervals.
Source: Stacks Project, Tags 014A and 0156
(blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. Apply the cone functor to the diagram of augmentation squares. The
five lemma makes every cone augmentation a quasi-isomorphism. The target cones
are termwise injective and bounded below. Apply the proved natural comparison
for a whole diagram of specified injective resolutions to these cone diagrams. -/
noncomputable def rightDerivedFunctorPlusConeResolutionNatIso
    {D : Type*} [Category* D]
    (K I : D ⥤ ComposableArrows (CochainComplex.Plus B) 1) (a : K ⟶ I)
    [∀ d : D, QuasiIso ((a.app d).app 0).hom]
    [∀ d : D, QuasiIso ((a.app d).app 1).hom]
    [∀ (d : D) (n : ℤ), Injective ((((I.obj d).obj 0).obj).X n)]
    [∀ (d : D) (n : ℤ), Injective ((((I.obj d).obj 1).obj).X n)] :
    K ⋙ CochainComplex.Plus.mappingConeFunctor ⋙
        DerivedCategory.Plus.Q ⋙ G.rightDerivedFunctorPlus ≅
      I ⋙ CochainComplex.Plus.mappingConeFunctor ⋙ HomotopyCategory.Plus.quotient B ⋙
        G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh := by
  let F := CochainComplex.Plus.mappingConeFunctor (C := B)
  let τ := Functor.whiskerRight a F
  have (d : D) : QuasiIso (τ.app d).hom := by
    change QuasiIso (CochainComplex.Plus.mappingConeMap _ _
      ((a.app d).app 0) ((a.app d).app 1)
      (ComposableArrows.naturality' (a.app d) 0 1)).hom
    exact CochainComplex.Plus.mappingConeMap_quasiIso _ _
      ((a.app d).app 0) ((a.app d).app 1)
      (ComposableArrows.naturality' (a.app d) 0 1)
  have (d : D) (n : ℤ) : Injective (((I ⋙ F).obj d).obj.X n) := by
    change Injective ((CochainComplex.Plus.mappingCone ((I.obj d).map' 0 1)).obj.X n)
    exact CochainComplex.Plus.mappingCone_injective
      (I := (I.obj d).obj 0) (J := (I.obj d).obj 1) _ n
  exact G.rightDerivedFunctorPlusResolutionNatIso (K ⋙ F) (I ⋙ F) τ

/-- Compute derived cohomology through a specified quasi-isomorphism to injectives. -/
noncomputable def homologyRightDerivedFunctorPlusResolutionIso
    {K I : CochainComplex.Plus B} (a : K ⟶ I) [QuasiIso a.hom]
    [∀ n : ℤ, Injective (I.obj.X n)] (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj I.obj).homology n := by
  have : IsIso (DerivedCategory.Plus.Q.map a) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso a.hom›)
  exact (DerivedCategory.Plus.homologyFunctor C n).mapIso
    (G.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map a))) ≪≫
      G.homologyRightDerivedFunctorPlusObjQIsoOfInjective I n

/-- A commuting square of specified injective resolutions gives a commuting
cohomology comparison square, without choosing arbitrary cohomology isomorphisms.
Source: Stacks Project, Tag 0156 (blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. The specified augmentation square becomes a square under localization,
the derived functor and cohomology. Follow it by the naturality square for the
inverse unit on injective complexes. Functoriality combines these two squares. -/
theorem homologyRightDerivedFunctorPlusResolutionIso_naturality
    {K L I J : CochainComplex.Plus B} (a : K ⟶ I) (b : L ⟶ J)
    [QuasiIso a.hom] [QuasiIso b.hom]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (f : K ⟶ L) (g : I ⟶ J) (h : a ≫ g = f ≫ b) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
        (G.homologyRightDerivedFunctorPlusResolutionIso b n).hom =
      (G.homologyRightDerivedFunctorPlusResolutionIso a n).hom ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map g.hom) n := by
  dsimp only [homologyRightDerivedFunctorPlusResolutionIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← h, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    homologyRightDerivedFunctorPlusObjQIsoOfInjective_naturality]
  simp only [Category.assoc]

end CategoryTheory.Functor
