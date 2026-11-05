/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization
import all WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport
import all WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # The open pullback square evaluated on a direct-image representative

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-counit-homotopy-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option linter.unusedVariables false

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Termwise tensor restriction comparison on the homotopy categories.
Source: Stacks Project, Tags 08DW and 08HY.
(blueprint: def-pc-open-pinned-single-tensor-restriction-iso). -/
noncomputable def openPinnedHomotopyTensorRestrictionIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) :=
  by
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    letI := schemeOpenRestriction_additive X U
    letI := schemeOpenRestriction_additive X' U'
    refine Functor.mapHomotopyCategoryCompIso
      (openPinnedTensorRestrictionIso k U U' j hj) (.up ℤ) ≪≫ ?_
    exact (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j)) (.up ℤ)).symm

private theorem targetHomotopyComparison
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    {F : C ⥤ D} {G R : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [H.Additive]
    (e : G ≅ R) (a : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P ≫
        (Functor.mapHomotopyCategoryCompIso
          (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app K) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

section
variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

section
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

/-- The target-open leg of the derived counit composition calculation.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle).
Proof: naturality of the open-pullback comparison moves the counit for k
past its component. The factorization equation of leftDerivedUnique identifies
that comparison followed by the exact restriction factor with the counit for
U' inclusion followed by the localized underived open tensor comparison.
The selected composition comparison factors the successive counits through
its composite counit. Combine these two equations and functoriality of Qh.
This uses no source open or commuting square, and applies to every complex,
including zero complexes and the empty open. -/
private theorem open_pinned_target_counit_triangle
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X' U').hom.app
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) =
    (pinnedPullbackComposition.{u, w} U'.ι k).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) := by
  have : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
  let E : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) (.up ℤ) :=
    ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ)).obj P
  let e := openPinnedTensorOpenIso X' U'
  let q := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))
  let v := (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app E
  let vi := (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app E
  have ho := openCounit.{u, w} X' U' E
  have hi := mappedHomotopyInvHom e E q
  have ho' := targetOpenFactor
    ((singleComplexOpenPullbackIso X' U').inv.app (DerivedCategory.Qh.obj E))
    ((singleComplexOpenPullbackIso X' U').hom.app (DerivedCategory.Qh.obj E))
    ((pinnedPullbackCounit.{u, w} U'.ι).app E)
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app E)
    (q.map v) (q.map vi)
    ((singleComplexOpenPullbackIso X' U').inv_hom_id_app (DerivedCategory.Qh.obj E)) ho hi
  have hc := compositionCounit.{u, w} U'.ι k P
  have ht := targetHomotopyComparison e
    (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm P
  have hg := congrArg q.map ht
  simp only [q.map_comp] at hg
  have hn := (singleComplexOpenPullbackIso X' U').hom.naturality
    ((pinnedPullbackCounit.{u, w} k).app P)
  exact targetTriangleAlgebra _ _ _ _ _ _ _ _ _ _ _ hn.symm ho' hc hg

end

/-- Coherence of the underived localized comparison factors.
Source: Stacks Project, Tags 08DW and 08HY; the explicitly constructed tensor comparisons.
Proof: expand the restriction comparison into its four factors: the inverse
open comparison for U', the inverse target composition comparison, the source
composition comparison along hj, and the open comparison for U. The target
homotopy comparison is the inverse of the lift of the first two factors, so
these cancel. The last two factors are the source comparison. For an arbitrary
morphism f and an equality j ≫ U.ι = f, equality induction identifies the
composition comparison along that equality with the comparison at j ≫ U.ι
precomposed by equality transport. This induction generalizes f first, rather
than trying to eliminate the equality of two fixed composites. Apply this at
hj. Lifting additive functors to complexes and then to the homotopy quotient
preserves composition, inverses, and equality transport, giving the displayed
identity for every P. This argument uses only functor identities; it applies to
empty and top opens and zero complexes without any extra hypothesis.
(blueprint: lem-pc-open-pinned-tensor-counit-transport-coherence) -/
private theorem open_pinned_tensor_comparison_coherence
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (openPinnedHomotopyTargetCompositionIso k U').hom.app P ≫
      (openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P =
    eqToHom (congrArg (fun f ↦
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P) hj).symm ≫
      (openPinnedHomotopySourceCompositionIso U j).hom.app P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht : ∀ (f : U'.toScheme ⟶ X) (h : j ≫ U.ι = f),
      (Scheme.Modules.tensorPullbackCompositionIso j U.ι f h).hom =
        eqToHom (congrArg Scheme.Modules.tensorPullback h).symm ≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).hom := by
    intro f h
    cases h
    simp only [eqToHom_refl, Category.id_comp]
  have hb :
      (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm).inv ≫
        (openPinnedTensorRestrictionIso k U U' j hj).hom =
      eqToHom (congrArg Scheme.Modules.tensorPullback hj).symm ≫
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm).inv := by
    simp only [openPinnedTensorRestrictionIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [ht _ hj]
    simp only [Category.assoc, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_hom]
  have := schemeOpenRestriction_additive X U
  have := schemeOpenRestriction_additive X' U'
  exact lift_comparison
    (fun f : U'.toScheme ⟶ X ↦ Scheme.Modules.tensorPullback f)
    (Scheme.Modules.tensorPullback k) (schemeOpenRestriction X' U')
    (schemeOpenRestriction X U) (Scheme.Modules.tensorPullback j) hj _ _ _ P hb

/-- Transport and termwise tensor composition in a commuting open square.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-tensor-counit-transport).
Proof: the source and target homotopy comparison isomorphisms are the two
termwise paths from tensor pullback along the composite to restriction
followed by tensor pullback. Expand openPinnedTensorRestrictionIso into its
four factors. The target comparison cancels its inverse composition and
inverse open tensor comparison, leaving the source comparison, with transport
along hj. The functor from additive functors to homotopy functors preserves
these compositions and inverses, as does Qh. The counit family respects
transport along equality of scheme morphisms by equality induction. Combine
that transport identity with the termwise comparison identity. No derived
composition comparison, derived open-pullback comparison, or flatness of P
is used. Empty opens and zero complexes obey the same functor identities. -/
private theorem open_pinned_tensor_counit_transport
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact transport_counit_comparison
    (fun f : U'.toScheme ⟶ X ↦ (derivedPullback.{u, w} f).obj (DerivedCategory.Qh.obj P))
    (fun f ↦ ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P)
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)))
    (fun f ↦ (pinnedPullbackCounit.{u, w} f).app P) hj _ _ _
    (open_pinned_tensor_comparison_coherence k U U' j hj P)

end

/-- The pinned counit restriction equation for an arbitrary homotopy complex.
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction).
Proof: expand the two composition comparisons in the restricted coefficient.
Their left-derived factorization equations identify their composites with the
pinned counits with the localized underived tensor composition comparisons.
The open-pullback comparison is leftDerivedUnique, so its factorization equation
identifies the open counit with the exact restriction factorization followed by
the underived open tensor comparison. Substituting these identities cancels the
inverse open and composition comparisons. What remains is the image in the
homotopy category of the four factors of openPinnedTensorRestrictionIso.
One can check these equalities on K-flat resolutions, where the counits are
invertible, and descend by their left-derived universal property. No flatness
of P is needed, and empty opens and zero complexes use the same identities. -/
private theorem open_pinned_counit_homotopy_restriction
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    singleComplexRestrictedCoefficient k (DerivedCategory.Qh.obj P)
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) (𝟙 _) U U' j hj ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P)  := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht := open_pinned_target_counit_triangle.{u, w} k U' P
  have hs := open_pinned_source_counit_triangle.{u, w} U j P
  have hc := open_pinned_tensor_counit_transport.{u, w} k U U' j hj P
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at ht hs hc
  have ht' := congrArg (fun f ↦ f ≫ DerivedCategory.Qh.map
    ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P)) ht
  simp only [Category.assoc] at ht'
  have h := counit_path_glue
    ((derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
      (DerivedCategory.Qh.obj P)))
    ((pinnedPullbackComposition.{u, w} j U.ι).hom.app (DerivedCategory.Qh.obj P))
    (eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj))
    ((pinnedPullbackComposition.{u, w} U'.ι k).app (DerivedCategory.Qh.obj P))
    _ _ _ _ _ _ _ ht' hc hs
  simpa only [singleComplexRestrictedCoefficient, pinnedPullbackComposition, Iso.app_inv,
    CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc] using h

section
attribute [local irreducible] singleComplexOpenPullbackIso Functor.mapHomotopyCategory
  Functor.mapDerivedCategory openPinnedHomotopyTensorRestrictionIso
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory

/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).

Proof: Put P = F_h(I), let v be the homotopy tensor adjunction counit at I,
 and write t for the homotopy tensor restriction isomorphism. Apply
 open_pinned_counit_homotopy_restriction to P and the restricted square. Its identity
 input contributes only an identity map, so its left side is S(Qh(P)) followed by
 rX(epsilon_f(P)), the target restriction factorization at the homotopy pullback of
 P, and Qh(t.hom(P)). Its right side is Lf0 of the source restriction factorization
 followed by epsilon_f0(rY_h(P)). Precompose both sides with Lf0 of the inverse
 source restriction factorization, and postcompose both sides with Qh(t.inv(P)).
 Functoriality and the inverse identities cancel the source factorization and the
 pair t.hom, t.inv. Next postcompose with Qh(rX_h(v)). Naturality of the target
 restriction factorization at v identifies its composite with this arrow with
 rX(Qh(v)) followed by the restriction factorization at I. Finally combine the two
 Qh images on the right by functoriality. This gives precisely the asserted
 equality. No derived unit or derived-adjunction counit occurs. All cancellations
 are of isomorphisms, so empty opens and zero complexes require no exceptions. -/
private theorem singleComplexOpen_restricted_counit_cancellation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by
  classical
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have h := open_pinned_counit_homotopy_restriction.{u, w} f V (f ⁻¹ᵁ V)
    (f ∣_ V) (morphismRestrict_ι f V)
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ) |>.obj I)
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at h
  let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let rY := schemeOpenRestriction Y V
  let P := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
    (.up ℤ)).obj I
  let v := ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)).counit.app I
  have hn := rX.mapDerivedCategoryFactorsh.hom.naturality v
  dsimp only [Functor.comp_map] at hn
  have h' := cancel_restriction_counit
    ((derivedPullback (f ∣_ V)).mapIso (rY.mapDerivedCategoryFactorsh.app P))
    (singleComplexRestrictedCoefficient f (DerivedCategory.Qh.obj P)
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P)) (𝟙 _) V (f ⁻¹ᵁ V)
      (f ∣_ V) (morphismRestrict_ι f V))
    _ _ (DerivedCategory.Qh.mapIso
      ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).app P)) _ _ _ _ h hn
  clear h hn
  have hs := remove_mapped_identity rX.mapDerivedCategory
    ((derivedPullback f).obj (DerivedCategory.Qh.obj P))
    ((derivedPullback (f ∣_ V)).map
      ((singleComplexOpenPullbackIso Y V).inv.app (DerivedCategory.Qh.obj P)))
    ((singleComplexOpenPinnedComposition (f ∣_ V) V.ι).hom.app (DerivedCategory.Qh.obj P))
    (eqToHom (congrArg
      (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj P)) (morphismRestrict_ι f V)))
    ((singleComplexOpenPinnedComposition (f ⁻¹ᵁ V).ι f).inv.app (DerivedCategory.Qh.obj P))
    ((singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).hom.app
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P)))
  have he := congrArg (fun s ↦
    ((derivedPullback (f ∣_ V)).mapIso (rY.mapDerivedCategoryFactorsh.app P)).inv ≫ s ≫
      rX.mapDerivedCategory.map ((pinnedPullbackCounit f).app P) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map v) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I) hs
  have hmain := he.symm.trans h'
  simpa only [Functor.id_obj, singleComplexOpenPinnedComposition,
    pinnedPullbackCounit, Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom,
    Category.assoc, Functor.map_comp] using hmain

end

end

/-- Derived compatibility before the sectionwise mate identity.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-counit-homotopy-factorization).

Proof: The pinned Hom equivalence identifies pullback of the right-derived unit
followed by the derived counit with the left-derived counit followed by localization
of the homotopy counit. Move that unit across the five-factor pullback square by
naturality. Apply open_pinned_counit_homotopy_restriction to the direct-image
homotopy complex, and cancel the target restriction and tensor restriction
isomorphisms. Naturality of the source restriction factorization moves localization
of the homotopy counit through restriction. Functoriality of Qh then joins the
inverse tensor comparison and restricted homotopy counit into the displayed arrow.
This calculation does not identify that arrow with the restricted-morphism counit;
that is the separate sectionwise mate identity. It uses no inverse of the derived
unit, so applies also to unbounded complexes, empty opens and the zero complex. -/
theorem singleComplexOpen_pullback_counit_homotopy_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by
  have h₁ := singleComplexOpen_unit_square_factorization f V I
  have h₂ := singleComplexOpen_restricted_counit_cancellation f V I
  exact Eq.trans h₁ h₂

end AlgebraicGeometry
