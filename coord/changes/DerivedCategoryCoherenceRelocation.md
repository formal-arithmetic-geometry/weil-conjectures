# Derived-category coherence lemma relocation

## Reason

The returned delivery duplicated nine existing generic coherence lemmas. Reuse their
existing declarations by moving them, with unchanged statements, proofs and visibility,
from `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars` to its existing public
dependency `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
Both modules are unclaimed. This makes the generic API available to finite-coefficient
pro-etale users without importing the incompatible fixed-coefficient pro-etale API.
Directly importing the old source into the item fails with `environment already contains
AlgebraicGeometry.ProEtale.«term(_)_*[_]»` because the coefficient APIs collide.
No new declaration, mathematical statement, definition or global instance is introduced.
No target statement review is reopened. No public import is changed.

After moving the declarations, the original `RestrictScalars` fails against the changed
dependency with nine `has already been declared` errors (the first at line 103 for
`CategoryTheory.Functor.mapHomologicalComplexCompIso_refl_hom_app`). The adapted file
removes exactly the relocated sections and compiles. The second reader reproduced this
counterfactual with `lcompile.py`; the sections moved are byte-identical. The surrounding
local instance attribute remains in the old file and is scoped by a new closed
`DerivedCoherence` section in the destination.

## Old

The following block is in `CategoryTheory.Functor` in `RestrictScalars`:

```lean
section Factors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composition isomorphism `Functor.mapHomologicalComplexCompIso` of the identity
isomorphism of `F ⋙ G` is the identity. -/
lemma mapHomologicalComplexCompIso_refl_hom_app {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app K = 𝟙 _ := by
  ext n
  simp
  rfl

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The form of `Functor.mapDerivedCategoryCompIso_fac` in which the comparison isomorphism
`Functor.mapHomologicalComplexCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factors (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fac, mapHomologicalComplexCompIso_refl_hom_app]
  simp

/-- The form of `Functor.mapDerivedCategoryCompIso_fach` in which the comparison isomorphism
`Functor.mapHomotopyCategoryCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factorsh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fach, mapHomotopyCategoryCompIso_refl_hom_app (F := F) (G := G)]
  simp

end Factors

section Coherence

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

variable (C) in
/-- On the image of an object of the homotopy category, the isomorphism
`Functor.mapDerivedCategoryIdIso` is the factorization `Functor.mapDerivedCategoryFactorsh` of
the identity functor. -/
lemma mapDerivedCategoryIdIso_hom_app_Qh_obj (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app K := by
  have h := congr_app (congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at h
  have hq : DerivedCategory.Qh.map ((mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K) =
      𝟙 (((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) := by
    rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
    exact DerivedCategory.Qh.map_id _
  refine (Category.comp_id _).symm.trans (h.trans ?_)
  rw [hq]
  -- the identities are those of objects which agree only up to unfolding `𝟭 C`
  erw [Category.id_comp, Category.comp_id]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The left unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_id_comp :
    (mapDerivedCategoryCompIso (𝟭 C) F).hom ≫
        Functor.whiskerRight (mapDerivedCategoryIdIso C).hom F.mapDerivedCategory =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K),
    mapDerivedCategoryIdIso_hom_app_Qh_obj, Category.assoc]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh (𝟭 C) F K).trans
    (Category.id_comp _).symm

/-- The right unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_comp_id :
    (mapDerivedCategoryCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryIdIso D).hom =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      F.mapDerivedCategoryFactorsh.hom.app K =
      (𝟭 D).mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        (mapDerivedCategoryIdIso D).hom.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryIdIso D).hom.naturality _).symm
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K), Category.assoc, hnat,
    mapDerivedCategoryIdIso_hom_app_Qh_obj]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh F (𝟭 D) K).trans
    (Category.id_comp _).symm

variable (G : D ⥤ E) (H : E ⥤ E') [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The associativity law for `Functor.mapDerivedCategoryCompIso`: the two ways of comparing
`D(F ⋙ G ⋙ H)` with `D(F) ⋙ D(G) ⋙ D(H)` agree. -/
lemma mapDerivedCategoryCompIso_assoc :
    (mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).hom =
      (mapDerivedCategoryCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (mapDerivedCategoryCompIso F G).hom H.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (mapDerivedCategoryCompIso G H).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K)) =
      (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (mapDerivedCategoryCompIso G H).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryCompIso G H).hom.naturality _).symm
  rw [← cancel_mono (H.mapDerivedCategory.map (G.mapDerivedCategory.map
      (F.mapDerivedCategoryFactors.hom.app K)) ≫
    H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))]
  trans (F ⋙ G ⋙ H).mapDerivedCategoryFactors.hom.app K
  · rw [Category.assoc, reassoc_of% hnat,
      mapDerivedCategoryCompIso_hom_app_factors G H
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
    exact mapDerivedCategoryCompIso_hom_app_factors F (G ⋙ H) K
  · symm
    rw [Category.assoc]
    simp only [← Functor.map_comp_assoc]
    rw [mapDerivedCategoryCompIso_hom_app_factors F G K]
    exact mapDerivedCategoryCompIso_hom_app_factors (F ⋙ G) H K

end Coherence

section Whisker

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the first
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerRight {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (mapDerivedCategoryNatIso (isoWhiskerRight e G)).hom ≫ (mapDerivedCategoryCompIso F' G).hom =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatIso e).hom G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← Functor.map_comp_assoc, mapDerivedCategoryNatIso_fac, Functor.map_comp_assoc,
    mapDerivedCategoryFactors_hom_naturality, mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the second
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerLeft (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {G G' : D ⥤ E} [G.Additive]
    [G'.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategoryNatIso (isoWhiskerLeft F e)).hom ≫ (mapDerivedCategoryCompIso F G').hom =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryNatIso e).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← reassoc_of% ((mapDerivedCategoryNatIso e).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app K)), mapDerivedCategoryNatIso_fac,
    mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

end Whisker
```

## New

The same block, verbatim, is in `CategoryTheory.Functor` in
`MapDerivedCategoryMate`, wrapped as follows; it is removed from `RestrictScalars`,
which already publicly imports `MapDerivedCategoryMate`:

```lean
section DerivedCoherence

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composition isomorphism `Functor.mapHomologicalComplexCompIso` of the identity
isomorphism of `F ⋙ G` is the identity. -/
lemma mapHomologicalComplexCompIso_refl_hom_app {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app K = 𝟙 _ := by
  ext n
  simp
  rfl

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The form of `Functor.mapDerivedCategoryCompIso_fac` in which the comparison isomorphism
`Functor.mapHomologicalComplexCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factors (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fac, mapHomologicalComplexCompIso_refl_hom_app]
  simp

/-- The form of `Functor.mapDerivedCategoryCompIso_fach` in which the comparison isomorphism
`Functor.mapHomotopyCategoryCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factorsh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fach, mapHomotopyCategoryCompIso_refl_hom_app (F := F) (G := G)]
  simp

end Factors

section Coherence

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

variable (C) in
/-- On the image of an object of the homotopy category, the isomorphism
`Functor.mapDerivedCategoryIdIso` is the factorization `Functor.mapDerivedCategoryFactorsh` of
the identity functor. -/
lemma mapDerivedCategoryIdIso_hom_app_Qh_obj (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app K := by
  have h := congr_app (congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at h
  have hq : DerivedCategory.Qh.map ((mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K) =
      𝟙 (((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) := by
    rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
    exact DerivedCategory.Qh.map_id _
  refine (Category.comp_id _).symm.trans (h.trans ?_)
  rw [hq]
  -- the identities are those of objects which agree only up to unfolding `𝟭 C`
  erw [Category.id_comp, Category.comp_id]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The left unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_id_comp :
    (mapDerivedCategoryCompIso (𝟭 C) F).hom ≫
        Functor.whiskerRight (mapDerivedCategoryIdIso C).hom F.mapDerivedCategory =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K),
    mapDerivedCategoryIdIso_hom_app_Qh_obj, Category.assoc]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh (𝟭 C) F K).trans
    (Category.id_comp _).symm

/-- The right unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_comp_id :
    (mapDerivedCategoryCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryIdIso D).hom =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      F.mapDerivedCategoryFactorsh.hom.app K =
      (𝟭 D).mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        (mapDerivedCategoryIdIso D).hom.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryIdIso D).hom.naturality _).symm
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K), Category.assoc, hnat,
    mapDerivedCategoryIdIso_hom_app_Qh_obj]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh F (𝟭 D) K).trans
    (Category.id_comp _).symm

variable (G : D ⥤ E) (H : E ⥤ E') [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The associativity law for `Functor.mapDerivedCategoryCompIso`: the two ways of comparing
`D(F ⋙ G ⋙ H)` with `D(F) ⋙ D(G) ⋙ D(H)` agree. -/
lemma mapDerivedCategoryCompIso_assoc :
    (mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).hom =
      (mapDerivedCategoryCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (mapDerivedCategoryCompIso F G).hom H.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (mapDerivedCategoryCompIso G H).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K)) =
      (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (mapDerivedCategoryCompIso G H).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryCompIso G H).hom.naturality _).symm
  rw [← cancel_mono (H.mapDerivedCategory.map (G.mapDerivedCategory.map
      (F.mapDerivedCategoryFactors.hom.app K)) ≫
    H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))]
  trans (F ⋙ G ⋙ H).mapDerivedCategoryFactors.hom.app K
  · rw [Category.assoc, reassoc_of% hnat,
      mapDerivedCategoryCompIso_hom_app_factors G H
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
    exact mapDerivedCategoryCompIso_hom_app_factors F (G ⋙ H) K
  · symm
    rw [Category.assoc]
    simp only [← Functor.map_comp_assoc]
    rw [mapDerivedCategoryCompIso_hom_app_factors F G K]
    exact mapDerivedCategoryCompIso_hom_app_factors (F ⋙ G) H K

end Coherence

section Whisker

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the first
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerRight {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (mapDerivedCategoryNatIso (isoWhiskerRight e G)).hom ≫ (mapDerivedCategoryCompIso F' G).hom =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatIso e).hom G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← Functor.map_comp_assoc, mapDerivedCategoryNatIso_fac, Functor.map_comp_assoc,
    mapDerivedCategoryFactors_hom_naturality, mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the second
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerLeft (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {G G' : D ⥤ E} [G.Additive]
    [G'.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategoryNatIso (isoWhiskerLeft F e)).hom ≫ (mapDerivedCategoryCompIso F G').hom =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryNatIso e).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← reassoc_of% ((mapDerivedCategoryNatIso e).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app K)), mapDerivedCategoryNatIso_fac,
    mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

end Whisker

end DerivedCoherence
```

## Users

Checked all nine moved names with the source-based downstream scan. The only existing
lexical user outside the source module is `RawFixedDerivedComparisonNaturality`, whose
unchanged source compiles against the delivered set (41.0 s). Other direct importers
are listed to make the scope clear. Existing importers of `RestrictScalars` retain the
same declarations through its unchanged public import. All signatures and visibility
are unchanged; there are no new global instances or attributes.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate | unclaimed | Receives the nine existing generic declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars | unclaimed | Forced removal of exactly the relocated sections; imports and other declarations unchanged. |
| Sheaf.Paper.ProfinitePointPullback | B4 | Uses generic coherence through a proof-only import. |
| Sheaf.AlgebraicGeometry.RawFixedDerivedComparisonNaturality | unclaimed | Existing lexical user; unchanged source compiled against the delivered set. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Direct importer of the generic module; no interface used here changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange | unclaimed | Direct importer of the generic module; no interface used here changes. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Direct importer of RestrictScalars; declarations remain re-exported. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Direct importer of RestrictScalars; declarations remain re-exported. |

## Status

landed 20261015T172915-L-557856 2026-10-15 (merge of deliver/B4/Sheaf.Paper.ProfinitePointPullback)
