/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.SingleAdjunctionComparison
public import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.PullbackConstantModule
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.CategoryTheory.SectionsAdjunctionComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Derived sections over a geometric point, with adjunction normalization

Source: Stacks Project, sites-cohomology.tex, Tag 07A6, and etale-cohomology.tex,
Tags 04JQ and 0F0F (blueprint: lem-kun-geometric-point-derived-sections-adjunction).

The integer-module encoding and the actual stalk are those of the dependency
`GeometricPointDerivedConstants`. All derived inverse images and constants below are
termwise exact functors. The adjunctions are transported from the existing canonical
left-derived adjunctions through their canonical exact-functor identifications.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Register the additivity supplied by the normalized geometric-point equivalence.
Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable instance geometricPointSectionsStalkAdditive
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] : (geometricPointStalk Ω).Additive :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).stalkAdditive

/-- The normalized constant/stalk adjunction, whose unit is the canonical constant germ.
Its counit is uniquely determined by that normalization, so this choice selects no
arbitrary map. Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsStalkAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    geometricPointConstants Ω ⊣ geometricPointStalk Ω :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).adjunction

/-- The canonical constant-section adjunction with termwise derived constants on the left.
Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantAdjunction (Z : Scheme.{u}) :
    (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).ofNatIsoLeft
    (constantSheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical derived inverse/direct-image adjunction, with the exact termwise inverse
image on the left. Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).ofNatIsoLeft
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical pullback-of-constants comparison, descended termwise.
Source: Stacks Tags 07A6 and 0F0F, and `lem-kun-pullback-constant`
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointConstants Ω).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ≅
      (constantSheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (geometricPointConstants Ω)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)

/-- The specified natural isomorphism of right adjoints. It is constructed by composing
constant/stalk with inverse/direct image, transporting the left adjoint through the
canonical constants comparison, and applying uniqueness of right adjoints.
Source: Stacks Tag 07A6 and the pushforward-composition proof following it
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointDerivedSectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
        (geometricPointStalk Ω).mapDerivedCategory ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  Adjunction.normalizedDerivedRightAdjointIso (geometricPointSectionsStalkAdjunction Ω)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
    (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)

/-- The actual global-section-to-germ map at the identity geometric point. The lift
only reindexes the same pointed-neighbourhood colimit, as in the dependency's stalk.
Source: Stacks Tags 040R and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGerm
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G ⟶ (geometricPointStalk Ω).obj G :=
  (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of Ω)))).hom.app G ≫
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (ULift.up (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _))) G.obj

/-- The augmentation identification `H⁰(S_D Rh_* G[0]) ≅ S(h_* G)`.
It uses exactness of the stalk and the canonical zeroth-right-derived comparison.
Source: Stacks Tags 05TD and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapSingleRightDerivedH0Iso
    (geometricPointStalk Ω) G

/-- The canonical augmentation identification `H⁰(RΓ_Z G[0]) ≅ Γ_Z G`.
Source: Stacks Tag 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  (Sheaf.Γ Z.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).singleRightDerivedH0Iso G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem point_germ_normalization
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] [HasWeakSheafify J A] [HasTerminal C]
    (Φ : J.Point) [HasColimitsOfSize A]
    {T : C} (hT : IsTerminal T) (x : Φ.fiber.obj T)
    (adj : constantSheaf J A ⊣ Φ.sheafFiber)
    (hu : ∀ M, adj.unit.app M =
      Φ.toPresheafFiber T x ((Functor.const _).obj M) ≫
        Φ.presheafFiber.map (toSheafify J ((Functor.const _).obj M)))
    (G : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app G ≫
        Φ.toPresheafFiber T x G.obj =
      ((constantSheafΓAdj J A).rightAdjointUniq adj).hom.app G := by
  let a := constantSheafΓAdj J A
  let b := constantSheafAdj J A hT
  let M := (Sheaf.Γ J A).obj G
  have hc := a.rightAdjointUniq_hom_app_counit b G
  have hc' := congrArg (fun f ↦
    (toSheafify J ((Functor.const _).obj M)).app (op T) ≫ f.hom.app (op T)) hc
  have hb : (toSheafify J ((Functor.const _).obj (G.obj.obj (op T)))).app (op T) ≫
      (b.counit.app G).hom.app (op T) = 𝟙 _ := by
    simp [b, constantSheafAdj_counit_app, ← NatTrans.comp_app]
  have hg : (toSheafify J ((Functor.const _).obj M)).app (op T) ≫
      (a.counit.app G).hom.app (op T) =
        (Sheaf.ΓNatIsoSheafSections J A hT).hom.app G := by
    have hn := congr_app (toSheafify_naturality J
      ((Functor.const _).map ((a.rightAdjointUniq b).hom.app G))) (op T) |>.symm
    change (toSheafify J ((Functor.const _).obj M)).app (op T) ≫
        ((constantSheaf J A).map ((a.rightAdjointUniq b).hom.app G)).hom.app (op T) =
      (a.rightAdjointUniq b).hom.app G ≫
        (toSheafify J ((Functor.const _).obj (G.obj.obj (op T)))).app (op T) at hn
    change (toSheafify J ((Functor.const _).obj M)).app (op T) ≫
      (((constantSheaf J A).map ((a.rightAdjointUniq b).hom.app G)).hom.app (op T) ≫
        (b.counit.app G).hom.app (op T)) = _ at hc'
    rw [← Category.assoc, hn, Category.assoc, hb] at hc'
    erw [Category.comp_id] at hc'
    exact hc'.symm
  rw [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom]
  simp only [conjugateEquiv_apply_app, Iso.refl_hom,
    NatTrans.id_app]
  rw [hu]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change _ = (Φ.toPresheafFiber T x ((Functor.const _).obj M) ≫
    Φ.presheafFiber.map (toSheafify J _)) ≫ Φ.presheafFiber.map (a.counit.app G).hom
  rw [Category.assoc, Φ.toPresheafFiber_naturality_assoc,
    Φ.toPresheafFiber_naturality, ← Category.assoc, hg]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionsGerm_eq_rightAdjointUniq
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    geometricPointSectionsGerm Ω G =
      ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).rightAdjointUniq
          (geometricPointSectionsStalkAdjunction Ω)).hom.app G := by
  apply point_germ_normalization
    (Spec (.of Ω)).smallEtaleTopology
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1})
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of Ω)))
    (ULift.up (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _)))
    (geometricPointSectionsStalkAdjunction Ω) _ G
  intro M
  have hu : (geometricPointSectionsStalkAdjunction Ω).unit =
      (geometricPointConstantGerm Ω).hom :=
    (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).unit_eq
  rw [hu]
  let Φ := (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}
  change (Φ.presheafFiberConstIso M).inv ≫
    Φ.presheafFiber.map (toSheafify _ _) = _
  have ht : (Φ.presheafFiberConstIso M).inv =
      Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (ULift.up (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _)))
          ((Functor.const _).obj M) := by
    apply (cancel_mono (Φ.presheafFiberConstIso M).hom).1
    rw [Iso.inv_hom_id]
    exact (Φ.toPresheafFiber_presheafFiberConstIso_hom M _ _).symm
  rw [ht]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem germ_ordinary_comparison
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    geometricPointSectionsGerm Ω ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) ≫
      ((((geometricPointSectionsStalkAdjunction Ω).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)).ofNatIsoLeft
          (Scheme.upperStarConstantSheafIso
            (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)).rightAdjointUniq
            (constantSheafΓAdj Z.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).hom.app G =
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).hom.app G := by
  rw [sectionsGerm_eq_rightAdjointUniq]
  simpa only [lowerStarCompGlobalSectionsIso, Sheaf.ΓNatIsoSheafSections,
    Scheme.upperStarConstantSheafIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] using
    Adjunction.sections_comparison
      (constantSheafΓAdj _ _) (constantSheafAdj _ _ terminalIsTerminal)
      (geometricPointSectionsStalkAdjunction Ω)
      (constantSheafΓAdj _ _) (constantSheafAdj _ _ terminalIsTerminal)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h) G


/-- The natural right-adjoint comparison has the specified counit identity and is inverse
to the global-section-to-germ map in degree zero. Source: Stacks Tag 07A6, the subsequent
pushforward-composition proof, and Tags 04JQ, 0F0F and 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction).

Proof:
1. Apply the counit characterization of `rightAdjointUniq` to the transported
   composite adjunction. Expand its counit and cancel the two constants comparisons.
2. The constant-section and constant/evaluation adjunctions identify the section
   counit evaluated at the terminal object with the global-section comparison.
   The normalized point unit is the constant germ. Naturality of the map into
   the point colimit therefore identifies the actual section-to-germ map with
   the unique comparison from the sections right adjoint to the stalk right adjoint.
3. `lem-kun-sections-adjunction-comparison` shows that the ordinary composite
   right-adjoint comparison, preceded by this germ map, is the pushforward/sections
   isomorphism. The constants isomorphism is the prescribed `upperStarConstantSheafIso`.
4. `lem-kun-right-derived-single-counit` computes the canonical derived counits on
   the single-object augmentations. `lem-kun-single-adjunction-comparison` then
   identifies the derived comparison on these augmentations with the single of
   the ordinary comparison. This only uses exactness of the left adjoints and stalk.
5. `lem-kun-right-derived-single-h0` identifies the zeroth homology of each augmentation
   with inverse to the canonical zeroth-derived isomorphism, also after applying
   the exact stalk functor. Apply zeroth homology to Step 4, cancel the augmentation
   isomorphisms, and use naturality of the single/homology identification.
   Step 3 gives the required degree-zero normalization. -/
theorem geometricPoint_derivedSections_adjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (∀ E : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      (geometricPointSectionsConstantsIso Ω h).hom.app
          (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
            (geometricPointStalk Ω).mapDerivedCategory).obj E) ≫
        (constantSheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory.map
            ((geometricPointDerivedSectionsIso Ω h).hom.app E) ≫
        (geometricPointSectionsConstantAdjunction Z).counit.app E =
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory.map
          ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.counit.app
            ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor.obj E)) ≫
        (geometricPointSectionsImageAdjunction Ω h).counit.app E) ∧
    (∀ G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)),
      geometricPointSectionsGerm Ω ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) ≫
        (geometricPointSectionsImageH0Iso Ω h G).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).map
          ((geometricPointDerivedSectionsIso Ω h).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≫
        (geometricPointSectionsGlobalH0Iso Z G).hom =
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).hom.app G) := by
  constructor
  · intro E
    exact Adjunction.normalizedDerivedRightAdjointIso_counit
      (geometricPointSectionsStalkAdjunction Ω)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
      (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h) E
  · intro G
    let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
    let S := geometricPointStalk Ω
    let R := lowerStar A h
    let T := Sheaf.Γ Z.smallEtaleTopology A
    let H := DerivedCategory.homologyFunctor A 0
    let c := ((((geometricPointSectionsStalkAdjunction Ω).comp
      (upperStarLowerStarAdjunction A h)).ofNatIsoLeft
        (Scheme.upperStarConstantSheafIso A h)).rightAdjointUniq
          (constantSheafΓAdj Z.smallEtaleTopology A)).hom.app G
    let f := (geometricPointDerivedSectionsIso Ω h).hom.app
      ((DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology A) 0).obj G)
    have hs := Adjunction.normalizedDerivedRightAdjointIso_h0.{
      u + 2, u + 2, u + 2, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (L := geometricPointConstants Ω) (S := S) (U := upperStar A h) (R := R)
      (K := constantSheaf Z.smallEtaleTopology A) (T := T)
      (geometricPointSectionsStalkAdjunction Ω) (upperStarLowerStarAdjunction A h)
      (constantSheafΓAdj Z.smallEtaleTopology A) (Scheme.upperStarConstantSheafIso A h) G
    have hz : (geometricPointSectionsImageH0Iso Ω h G).inv ≫ H.map f ≫
        (geometricPointSectionsGlobalH0Iso Z G).hom = c := by
      delta geometricPointSectionsImageH0Iso geometricPointSectionsGlobalH0Iso
      dsimp only [f]
      delta geometricPointDerivedSectionsIso
      exact hs
    exact (congrArg (fun k ↦ geometricPointSectionsGerm Ω (R.obj G) ≫ k) hz).trans
      (germ_ordinary_comparison Ω h G)

end AlgebraicGeometry.Etale
