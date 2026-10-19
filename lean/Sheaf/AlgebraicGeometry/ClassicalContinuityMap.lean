/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.AlgebraicGeometry.EtaleComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Sheaf.RingTheory.IndEtaleSmallIndex

/-! # Continuity maps and classical pro-étale sheaves

Source: current blueprint, sec-proetale-coefficients/sk-def-pe-classical-definition,
`sk-def-pe-classical-definition-continuity-map.md`, clauses 1--4 and final paragraph
(blueprint: det-pe-classical-definition-continuity-map).

The index categories and section values live in the common larger universe `u + 1`.
Module coefficients use the intrinsic constant-ring module category of the recorded
small pro-étale site, with the same coefficient lift as `Scheme.proEtaleDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An affine étale presentation with an affine vertex in the pro-étale site.
The universal property is taken in all schemes over `X`, not just in the site.
Source: current blueprint, continuity-map detail, clause 1
(blueprint: det-pe-classical-definition-continuity-map). -/
structure AffinePresentation (X : Scheme.{u}) (I : Type (u + 1))
    [SmallCategory I] [IsCofiltered I] where
  diagram : I ⥤ X.ProEt
  affine : ∀ i : I, IsAffine (diagram.obj i).left
  etale : ∀ i : I, Etale (diagram.obj i).hom
  cone : Cone diagram
  affineVertex : IsAffine cone.pt.left
  isLimit : IsLimit ((Scheme.ProEt.forget X).mapCone cone)

/-- Restriction of a presheaf to the stages of a presentation, contravariantly.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionDiagram {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) : Iᵒᵖ ⥤ C :=
  P.diagram.op ⋙ F

/-- The restriction cocone, obtained functorially from the projection cone.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionCocone {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) :
    Cocone (sectionDiagram P F) :=
  F.mapCocone P.cone.op

/-- The canonical map out of the chosen colimit, retaining the presentation.
Source: current blueprint, continuity-map detail, clause 2; Stacks, Categories, Tag 002F
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def continuityMap {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C)
    [HasColimit (sectionDiagram P F)] :
    colimit (sectionDiagram P F) ⟶ F.obj (op P.cone.pt) :=
  colimit.desc (sectionDiagram P F) (sectionCocone P F)

/-- The displayed formula on representatives of the colimit.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map).
Proof: the defining factorization equation of `colimit.desc`, applied to the restriction
cocone, gives the projection restriction on each summand. -/
theorem continuityMap_ι {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C)
    [HasColimit (sectionDiagram P F)] (i : I) :
    colimit.ι (sectionDiagram P F) (op i) ≫ continuityMap P F =
      F.map (P.cone.π.app i).op := by
  exact colimit.ι_desc (sectionCocone P F) (op i)

/-- Naturality of the continuity map in the sheaf (in fact in any presheaf).
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map).
Proof: precompose with every coprojection. Both composites become the restriction map
along `u_i` followed by the component of the sheaf morphism. They agree by naturality;
the colimit universal property gives equality. -/
theorem continuityMap_natural {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] {F G : X.ProEtᵒᵖ ⥤ C} (α : F ⟶ G)
    [HasColimit (sectionDiagram P F)] [HasColimit (sectionDiagram P G)] :
    colimMap (G := sectionDiagram P F) (F := sectionDiagram P G)
      (Functor.whiskerLeft P.diagram.op α) ≫ continuityMap P G =
      continuityMap P F ≫ α.app (op P.cone.pt) := by
  apply colimit.hom_ext
  intro i
  obtain ⟨i⟩ := i
  simp [continuityMap, sectionCocone, sectionDiagram, α.naturality]

/-- A set sheaf is classical when every affine presentation gives a bijective map.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassical {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), Function.Bijective (continuityMap P F.obj)

/-- Set-sheaf classicality is invariant under isomorphism.
Source: current blueprint, continuity-map proof, third paragraph
(blueprint: det-pe-classical-definition-continuity-map).
Proof: naturality identifies the continuity maps through the component bijections of
an isomorphism and the colimit isomorphism induced by its stage components. Apply the
same construction to its inverse to see that these identifications are bijective. -/
theorem isClassical_iso_iff {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))} (e : F ≅ G) :
    IsClassical F ↔ IsClassical G := by
  have h {F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))}
      (e : F ≅ G) (hF : IsClassical F) : IsClassical G := by
    intro I _ _ P
    have hmap := continuityMap_natural P e.hom.hom
    have : IsIso (continuityMap P F.obj) :=
      (CategoryTheory.isIso_iff_bijective _).mpr (hF P)
    have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft P.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    have : IsIso (e.hom.hom.app (op P.cone.pt)) := by infer_instance
    have : IsIso (continuityMap P G.obj) := by
      apply (isIso_comp_left_iff
        (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
      rw [hmap]
      infer_instance
    exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance
  exact ⟨h e, h e.symm⟩

section Modules

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

variable (F : ringedSiteModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))))

/-- Sections with scalars restricted along the constant-section sheafification unit.
This is a presheaf of modules over the lifted discrete coefficient ring itself.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleSectionPresheaf : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} Λ) := by
  let M := PresheafOfModules.restrictScalarsObj F.val
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  exact
    { obj := M.obj
      map f := M.map f
      map_id U := by ext x; exact congrArg (fun g ↦ g x) (M.map_id U)
      map_comp f g := by ext x; exact congrArg (fun h ↦ h x) (M.map_comp f g) }

/-- The linear continuity map, taking the colimit in coefficient modules.
Its scalar action is restriction along the canonical constant-section maps.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleContinuityMap {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I) :
    colimit (sectionDiagram P (moduleSectionPresheaf Λ F)) ⟶
      (moduleSectionPresheaf Λ F).obj (op P.cone.pt) :=
  continuityMap P (moduleSectionPresheaf Λ F)

/-- Classicality of intrinsic constant-ring module sheaves.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalModule : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), IsIso (moduleContinuityMap Λ F P)

/-- Module classicality agrees with classicality of the underlying set sheaf.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map).
Proof: filtered module colimits have the corresponding set colimits as underlying sets:
every element comes from a stage and equality is witnessed at a common later stage.
Under this comparison the two continuity maps agree on every coprojection. A linear
map is invertible precisely when its underlying function is bijective. -/
theorem isClassicalModule_iff :
    IsClassicalModule Λ F ↔
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget AddCommGrpCat.{u + 1})).obj ((SheafOfModules.toSheaf _).obj F)) := by
  let V := forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
  have h (I : Type (u + 1)) [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I) :
      IsIso (moduleContinuityMap Λ F P) ↔
        Function.Bijective (continuityMap P (moduleSectionPresheaf Λ F ⋙ V)) := by
    rw [← CategoryTheory.isIso_iff_bijective]
    have heq :
        (preservesColimitIso V (sectionDiagram P (moduleSectionPresheaf Λ F))).inv ≫
          V.map (moduleContinuityMap Λ F P) =
            continuityMap P (moduleSectionPresheaf Λ F ⋙ V) := by
      exact preservesColimitIso_inv_comp_desc V
        (sectionDiagram P (moduleSectionPresheaf Λ F))
        (sectionCocone P (moduleSectionPresheaf Λ F))
    rw [← heq, isIso_comp_left_iff]
    exact (isIso_iff_of_reflects_iso _ V).symm
  constructor
  · intro hF I _ _ P
    exact (h I P).mp (hF P)
  · intro hF I _ _ P
    exact (h I P).mpr (hF P)

private theorem isClassicalModule_iso_iff
    (G : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1, u} Λ))))) (e : F ≅ G) :
    IsClassicalModule Λ F ↔ IsClassicalModule Λ G := by
  rw [isClassicalModule_iff, isClassicalModule_iff]
  exact isClassical_iso_iff
    ((SheafOfModules.toSheaf _ ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso e)

end Modules

/-- Classical cochain complexes have classical cohomology module sheaves in every degree.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalCochainComplex {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : CochainComplex
      (ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1, u} Λ))))) ℤ) : Prop :=
  ∀ q : ℤ, IsClassicalModule Λ (K.homology q)

/-- Classicality of the recorded intrinsic derived category, using its cohomology sheaves.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalComplex {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : Scheme.proEtaleDerivedCategory X Λ) : Prop :=
  ∀ q : ℤ, IsClassicalModule Λ
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj K)

/-- The cochain and derived formulations agree under the recorded localization functor.
Source: current blueprint, continuity-map detail, clause 4; Stacks, Tag 05RT
(blueprint: det-pe-classical-definition-continuity-map).
Proof: `DerivedCategory.homologyFunctorFactors` identifies each cohomology sheaf of
`Q.obj K` with the corresponding cochain cohomology sheaf. Apply the underlying-set
comparison and isomorphism invariance to each degree; the resulting equivalences give
the equivalence of the predicates quantified over all integers. -/
theorem isClassicalComplex_Q_iff {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : CochainComplex
      (ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1, u} Λ))))) ℤ) :
    IsClassicalComplex Λ
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K) ↔
        IsClassicalCochainComplex Λ K := by
  apply forall_congr'
  intro q
  exact isClassicalModule_iso_iff Λ _ _
    ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard _) q).app K)

/-- Classicality depends only on the derived isomorphism class.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map).
Proof: apply each cohomology functor to the given isomorphism. Its components and inverse
identify the restriction diagrams and continuity cocones. The induced colimit maps are
inverse linear isomorphisms, so invertibility of each continuity map is preserved. -/
theorem isClassicalComplex_iso_iff {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    {K L : Scheme.proEtaleDerivedCategory X Λ} (e : K ≅ L) :
    IsClassicalComplex Λ K ↔ IsClassicalComplex Λ L := by
  apply forall_congr'
  intro q
  exact isClassicalModule_iso_iff Λ _ _
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).mapIso e)

set_option backward.defeqAttrib.useBackward true in
private noncomputable def affineGlobalSectionsIsColimit
    {J : Type*} [Category J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] [IsAffine c.pt] :
    IsColimit (Scheme.Γ.mapCocone c.op) := by
  let α : D ≅ (D.op ⋙ Scheme.Γ).rightOp ⋙ Scheme.Spec :=
    NatIso.ofComponents (fun j ↦ (D.obj j).isoSpec)
      (fun f ↦ (Scheme.isoSpec_hom_naturality (D.map f)).symm)
  have hs : IsLimit (Scheme.Spec.mapCone (coneRightOpOfCocone (Scheme.Γ.mapCocone c.op))) := by
    refine IsLimit.equivOfNatIsoOfIso α c _ ?_ hc
    refine Cone.ext c.pt.isoSpec ?_
    intro j
    exact (Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj j) (c.π.app j)).symm
  exact isColimitOfConeRightOpOfCocone (D.op ⋙ Scheme.Γ)
    (isLimitOfReflects Scheme.Spec hs)

set_option backward.defeqAttrib.useBackward true in
/-- Presentable affine site objects are exactly the affine ind-étale subsite objects.
Source: current blueprint, continuity-map detail, final paragraph; recorded
`proAffineEtale_Spec_iff` and `Scheme.AffineProEt`
(blueprint: det-pe-classical-definition-continuity-map).
Proof, following steps 7--9 of the node:
1. Write `X = Spec R` and each affine stage as `Spec B_i`, using
   `def-weil-affine-spectrum`. The structure and transition maps give a filtered
   diagram of `R`-algebras. By `lem-weil-pbc-etale-ring-map-iff-etale-affine`, its
   terms are finitely presented étale algebras.
2. Forget the relative limit to schemes. Identify every affine stage and the vertex
   naturally with the spectrum of its global sections. Reflect the transported limit
   through the fully faithful Spec functor and take opposites. This proves that the
   global-sections cocone is a ring colimit, without choosing another ring colimit.
   The structure maps commute by the equations for morphisms over X, so they exhibit
   the vertex structure map as ind-étale with index in universe `u + 1`.
3. Apply `lem-pe-ind-etale-small-index` to obtain a universe-u presentation. The
   recorded `RingHom.IndEtale.iff_ind_etale` and `proAffineEtale_iff_appTop` give
   `proAffineEtale` of the vertex; cancel its isomorphism to U. Conversely, unfold
   the recorded `proAffineEtale` presentation and enlarge its index to `u + 1`.
   Its affine étale stages lift to objects of the site. The forgetful functor from
   schemes over X reflects this limit because a cofiltered index is connected.
   The resulting presentation has vertex U itself. -/
theorem affinePresentation_iff {X : Scheme.{u}} [IsAffine X] (U : X.ProEt) :
    (∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsCofiltered I)
      (P : AffinePresentation X I), Nonempty (P.cone.pt ≅ U)) ↔ proAffineEtale U.hom := by
  constructor
  · rintro ⟨I, _, _, P, ⟨e⟩⟩
    have : IsAffine P.cone.pt.left := P.affineVertex
    have (i : I) : IsAffine (P.diagram.obj i).left := P.affine i
    let V := Scheme.ProEt.forget X ⋙ Over.forget X
    let D := P.diagram ⋙ V
    let c := V.mapCone P.cone
    let F := D.op ⋙ Scheme.Γ
    let t : (Functor.const Iᵒᵖ).obj Γ(X, ⊤) ⟶ F :=
      { app i := (P.diagram.obj i.unop).hom.appTop
        naturality {i j} a := by
          dsimp [F, D, V]
          rw [Category.id_comp, ← Scheme.Hom.comp_appTop]
          congr 1
          exact (MorphismProperty.Over.w (P.diagram.map a.unop)).symm }
    have (i : I) : IsAffine (D.obj i) := P.affine i
    have : IsAffine c.pt := P.affineVertex
    have hc : IsLimit c := isLimitOfPreserves (Over.forget X) P.isLimit
    have hring : MorphismProperty.ind.{u + 1} CommRingCat.etale.{u}
        P.cone.pt.hom.appTop := by
      refine ⟨Iᵒᵖ, inferInstance, inferInstance, F, t,
        (Scheme.Γ.mapCocone c.op).ι, affineGlobalSectionsIsColimit D c hc, ?_⟩
      intro i
      refine ⟨?_, ?_⟩
      · have := P.etale i.unop
        change RingHom.Etale (P.diagram.obj i.unop).hom.appTop.hom
        exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)
          (X := (P.diagram.obj i.unop).left) (Y := X)
          (f := (P.diagram.obj i.unop).hom)).mp (P.etale i.unop)
      · change (P.diagram.obj i.unop).hom.appTop ≫
            (P.cone.π.app i.unop).left.appTop = P.cone.pt.hom.appTop
        rw [← Scheme.Hom.comp_appTop, MorphismProperty.Over.w]
        rfl
    have hp : proAffineEtale P.cone.pt.hom := by
      apply (proAffineEtale_iff_appTop (X := P.cone.pt.left) (Y := X)).mpr
      rw [RingHom.IndEtale.iff_ind_etale]
      exact CommRingCat.ind_etale_small_index _ hring
    have he : e.hom.left ≫ U.hom = P.cone.pt.hom := MorphismProperty.Over.w e.hom
    rw [← he] at hp
    exact (MorphismProperty.cancel_left_of_respectsIso (P := proAffineEtale)
      e.hom.left U.hom).mp hp
  · intro h
    have hU := h.isAffine
    change MorphismProperty.pro.{u}
      (@Etale ⊓ MorphismProperty.ofObjectProperty (IsAffine ·) ⊤) U.hom at h
    have hlarge : MorphismProperty.pro.{u + 1}
        (@Etale ⊓ MorphismProperty.ofObjectProperty (IsAffine ·) ⊤) U.hom :=
      MorphismProperty.pro_of_univLE.{u, u + 1} _ h
    obtain ⟨I, _, _, D, t, s, hs, hts⟩ := hlarge
    have haff (i : I) : IsAffine (D.obj i) := (hts i).1.2.1
    have het (i : I) : Etale (t.app i) := (hts i).1.1
    let E : I ⥤ X.ProEt := MorphismProperty.Over.lift' D t
      (fun i ↦ inferInstanceAs (WeaklyEtale (t.app i))) (fun _ ↦ trivial)
    let c : Cone E :=
      { pt := U
        π :=
          { app i := MorphismProperty.Over.homMk (s.app i) (hts i).2
            naturality {i j} a := by
              apply MorphismProperty.Over.Hom.ext
              change s.app j = s.app i ≫ D.map a
              simpa using s.naturality a } }
    refine ⟨I, inferInstance, inferInstance,
      { diagram := E
        affine := haff
        etale := het
        cone := c
        affineVertex := hU
        isLimit := ?_ }, ⟨Iso.refl _⟩⟩
    have : IsConnected I := IsCofiltered.isConnected I
    exact isLimitOfReflects (Over.forget X) hs

end AlgebraicGeometry.ProEtale
