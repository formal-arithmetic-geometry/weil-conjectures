/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! # Reflection of an exceptional coefficient mate through the site comparison

Source: current blueprint reduction-exceptional, site/coefficient compatibility;
parent lem-pur-finite-coefficient-adjoint-comparisons, steps 7--8 and 12--13.
(blueprint: lem-pur-normalized-change-site-reflection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

private theorem plus_of_comparison
    (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : DerivedCategory.TStructure.t.plus ((nu B T).obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  intro i hi
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff _ a).1 ha i hi)

/-- The site-comparison counit at a constructible finite-Tor object is invertible. -/
private theorem normalizedSiteCounit_isIso
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K.obj) :=
  ((ProEtale.DerivedCategory.plusEtaleOrigin_iff K.obj).mp
    K.property.plusEtaleOrigin).2

/-- The coefficient change of the comparison counit, expressed in etale coordinates. -/
private def normalizedSiteChangeMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K : D A T) :
    (Etale.scalarExtension φ T).obj ((rnu A T).obj K) ⟶
      (rnu B T).obj ((tensor φ T).obj K) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app _ ≫
    (rnu B T).map ((ProEtale.pbcComparisonReduction T φ).inv.app _ ≫
      (tensor φ T).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K))

/-- Boundedness of coefficient change makes its site-comparison identification invertible. -/
private theorem normalizedSiteChangeMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K : (ctf A T).FullSubcategory)
    (hK : ctf B T ((tensor φ T).obj K.obj)) :
    IsIso (normalizedSiteChangeMap φ T K.obj) := by
  have := normalizedSiteCounit_isIso A T K
  let e := (ProEtale.pbcComparisonReduction T φ).symm.app ((rnu A T).obj K.obj) ≪≫
    (tensor φ T).mapIso
      (asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K.obj))
  have hb : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ T).obj ((rnu A T).obj K.obj)) := by
    apply plus_of_comparison B T
    exact DerivedCategory.TStructure.t.plus.prop_of_iso e.symm hK.plus
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} B) T _ hb
  unfold normalizedSiteChangeMap
  infer_instance

/-- The ordinary etale coefficient mate used by the site transport. -/
private def normalizedEtaleMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (K : D A Y) :=
  (etaleAdjunction B c).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse φ c
        ((etaleUpper A c).obj ((rnu A Y).obj K)) ≫
      (Etale.scalarExtension φ Y).map
        ((etaleAdjunction A c).counit.app ((rnu A Y).obj K)))

/-- Transport the etale coefficient mate through the coefficient/site square. -/
private def normalizedTransportMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (K : D A Y) :
    (tensor φ X).obj ((upper A c).obj K) ⟶
      (upper B c).obj ((tensor φ Y).obj K) :=
  (ProEtale.pbcComparisonReduction X φ).hom.app
      ((etaleUpper A c).obj ((rnu A Y).obj K)) ≫
    (nu B X).map (normalizedEtaleMate φ c K ≫
      (etaleUpper B c).map (normalizedSiteChangeMap φ Y K))

/-- The boundary identifications of the transported mate are invertible. -/
private theorem normalizedTransportMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (K : (ctf A Y).FullSubcategory)
    (hK : ctf B Y ((tensor φ Y).obj K.obj))
    (he : IsIso (normalizedEtaleMate φ c K.obj)) :
    IsIso (normalizedTransportMate φ c K.obj) := by
  have := normalizedSiteChangeMap_isIso φ Y K hK
  unfold normalizedTransportMate
  infer_instance

/-- The exceptional object has its specified, rather than chosen, etale antecedent. -/
private def normalizedUpperWitness
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) (dA : AdjointDatum A c)
    (K : (ctf A Y).FullSubcategory) :
    Scheme.FixedEtaleOriginWitness X A
      ⟨(upper A c).obj K.obj, (dA.upper_preserves K.obj K.property).plus⟩ :=
  ⟨⟨(etaleUpper A c).obj ((rnu A Y).obj K.obj), dA.etaleBound K.obj K.property⟩,
    Iso.refl _⟩

/-- At the canonical upper witness the boundary isomorphism cancels from the projection. -/
private theorem normalizedProjection_upper
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (dA : AdjointDatum A c) (K : (ctf A Y).FullSubcategory)
    (hB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj ((etaleUpper A c).obj ((rnu A Y).obj K.obj)))) :
    projectionAtWitness φ c
        ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩
        (normalizedUpperWitness c dA K) hB ≫
      (lower B c).map ((ProEtale.pbcComparisonReduction X φ).hom.app
        ((etaleUpper A c).obj ((rnu A Y).obj K.obj))) =
    (tensor φ Y).map ((ProEtale.compactSupportSiteComparison A c).hom.app
        ⟨(etaleUpper A c).obj ((rnu A Y).obj K.obj), dA.etaleBound K.obj K.property⟩) ≫
      (ProEtale.pbcComparisonReduction Y φ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          ((etaleUpper A c).obj ((rnu A Y).obj K.obj))) ≫
      (nu B Y).map (Etale.ExceptionalCoefficients.compactSupportMap φ c
        ((etaleUpper A c).obj ((rnu A Y).obj K.obj))) ≫
      (ProEtale.compactSupportSiteComparison B c).inv.app
        ⟨(Etale.scalarExtension φ X).obj
          ((etaleUpper A c).obj ((rnu A Y).obj K.obj)), hB⟩ := by
  dsimp only [projectionAtWitness, normalizedUpperWitness, upper, Functor.comp_obj,
    Iso.refl_hom, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The site-change map is the transpose of the scalar change of the site counit. -/
private theorem normalizedSiteChangeMap_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K : D A T) :
    (nu B T).map (normalizedSiteChangeMap φ T K) ≫
        (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).counit.app
          ((tensor φ T).obj K) =
      (ProEtale.pbcComparisonReduction T φ).inv.app ((rnu A T).obj K) ≫
        (tensor φ T).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K) := by
  exact (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).homEquiv _ _
    |>.symm_apply_apply _

/-- Expand only the target counit of the transported mate, before using the projection. -/
private theorem normalizedTransportMate_transpose
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (dB : AdjointDatum B c) (K : D A Y)
    (hK : ctf B Y ((tensor φ Y).obj K))
    (hN : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj ((etaleUpper A c).obj ((rnu A Y).obj K)))) :
    (lower B c).map (normalizedTransportMate φ c K) ≫ dB.counit ⟨_, hK⟩ =
      (lower B c).map ((ProEtale.pbcComparisonReduction X φ).hom.app
        ((etaleUpper A c).obj ((rnu A Y).obj K))) ≫
      (ProEtale.compactSupportSiteComparison B c).hom.app
        ⟨(Etale.scalarExtension φ X).obj ((etaleUpper A c).obj ((rnu A Y).obj K)), hN⟩ ≫
      (nu B Y).map (Etale.ExceptionalCoefficients.comparisonInverse φ c
        ((etaleUpper A c).obj ((rnu A Y).obj K))) ≫
      (nu B Y).map ((Etale.scalarExtension φ Y).map
        ((etaleAdjunction A c).counit.app ((rnu A Y).obj K))) ≫
      (ProEtale.pbcComparisonReduction Y φ).inv.app ((rnu A Y).obj K) ≫
      (tensor φ Y).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K) := by
  let L := (rnu A Y).obj K
  let M := (Etale.scalarExtension φ Y).obj L
  let N := (Etale.scalarExtension φ X).obj ((etaleUpper A c).obj L)
  let H := (etaleUpper B c).obj ((rnu B Y).obj ((tensor φ Y).obj K))
  let z := normalizedSiteChangeMap φ Y K
  let t : N ⟶ H := normalizedEtaleMate φ c K ≫ (etaleUpper B c).map z
  have hn := (ProEtale.compactSupportSiteComparison B c).hom.naturality
    (ObjectProperty.homMk t :
      (⟨N, hN⟩ : DerivedCategory.Plus _) ⟶
        ⟨H, dB.etaleBound _ hK⟩)
  change (lower B c).map ((nu B X).map t) ≫
      (ProEtale.compactSupportSiteComparison B c).hom.app ⟨H, _⟩ =
    (ProEtale.compactSupportSiteComparison B c).hom.app ⟨N, hN⟩ ≫
      (nu B Y).map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map t)
    at hn
  have he :
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map t ≫
          (etaleAdjunction B c).counit.app ((rnu B Y).obj ((tensor φ Y).obj K)) =
        Etale.ExceptionalCoefficients.comparisonInverse φ c ((etaleUpper A c).obj L) ≫
          (Etale.scalarExtension φ Y).map ((etaleAdjunction A c).counit.app L) ≫ z := by
    have he0 := (etaleAdjunction B c).homEquiv _ _ |>.symm_apply_apply
      (Etale.ExceptionalCoefficients.comparisonInverse φ c ((etaleUpper A c).obj L) ≫
        (Etale.scalarExtension φ Y).map ((etaleAdjunction A c).counit.app L))
    change (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      (normalizedEtaleMate φ c K) ≫ (etaleAdjunction B c).counit.app M = _ at he0
    have hz := (etaleAdjunction B c).counit.naturality z
    simp only [Functor.comp_map, Functor.id_map] at hz
    dsimp only [t]
    erw [Functor.map_comp, Category.assoc, hz, ← Category.assoc, he0, Category.assoc]
  dsimp only [normalizedTransportMate, upper, Functor.comp_obj, AdjointDatum.counit]
  rw [Functor.map_comp, dB.counit_normalization ⟨_, hK⟩]
  simp only [Category.assoc]
  change _ ≫ (lower B c).map ((nu B X).map t) ≫ _ = _
  erw [reassoc_of% hn, ← Functor.map_comp_assoc, he]
  simp only [Functor.map_comp, Category.assoc]
  erw [normalizedSiteChangeMap_counit φ Y K]

private theorem compactSupport_comparisonInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (φ : A →+* B) (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Etale.ExceptionalCoefficients.compactSupportMap φ c M ≫
      Etale.ExceptionalCoefficients.comparisonInverse φ c M = 𝟙 _ := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (Etale.properFiniteCoefficientExtension φ c.g).1
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  have h : IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ c M) := by
    unfold Etale.ExceptionalCoefficients.compactSupportMap
    infer_instance
  simp only [Etale.ExceptionalCoefficients.comparisonInverse, dif_pos h,
    IsIso.hom_inv_id]

/-- Projection normalization identifies the transported mate's counit transpose. -/
private theorem normalizedTransportMate_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (dA : AdjointDatum A c) (dB : AdjointDatum B c)
    (hY : ∀ K, ctf A Y K → ctf B Y ((tensor φ Y).obj K))
    (hb : ∀ (K : (ctf A X).FullSubcategory)
      (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
      DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj w.complex.obj))
    (q : (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
      (ctf A X).ι ⋙ tensor φ X ⋙ lower B c)
    (hq : ∀ (K : (ctf A X).FullSubcategory)
      (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
      q.hom.app K = projectionAtWitness φ c K w (hb K w))
    (K : (ctf A Y).FullSubcategory) :
    (lower B c).map (normalizedTransportMate φ c K.obj) ≫
        dB.counit ⟨(tensor φ Y).obj K.obj, hY K.obj K.property⟩ =
      q.inv.app ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩ ≫
        (tensor φ Y).map (dA.counit K) := by
  let P : (ctf A X).FullSubcategory :=
    ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩
  let w := normalizedUpperWitness c dA K
  have hN : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj
        ((etaleUpper A c).obj ((rnu A Y).obj K.obj))) := hb P w
  have hp := normalizedProjection_upper φ c dA K hN
  have hq0 : q.hom.app P = projectionAtWitness φ c P w hN := hq P w
  rw [← hq0] at hp
  have hd := (ProEtale.pbcComparisonReduction Y φ).hom.naturality
    ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj))
  change (tensor φ Y).map ((nu A Y).map
      ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj))) ≫
      (ProEtale.pbcComparisonReduction Y φ).hom.app ((rnu A Y).obj K.obj) =
    (ProEtale.pbcComparisonReduction Y φ).hom.app _ ≫
      (nu B Y).map ((Etale.scalarExtension φ Y).map
        ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj))) at hd
  apply (cancel_epi (q.hom.app P)).1
  simp only [P, upper, Functor.comp_obj, Iso.hom_inv_id_app_assoc]
  erw [normalizedTransportMate_transpose φ c dB K.obj (hY K.obj K.property) hN]
  erw [reassoc_of% hp]
  dsimp only [upper, Functor.comp_obj]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [← Functor.map_comp_assoc, compactSupport_comparisonInverse]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% hd]
  simp only [Iso.hom_inv_id_app_assoc]
  dsimp only [AdjointDatum.counit]
  rw [dA.counit_normalization K, Functor.map_comp, Functor.map_comp]

/-- An ambient map with the normalized coefficient counit equation is invertible
if its ordinary etale counterpart is invertible. This is a pointwise transport
statement; it constructs neither a coefficient comparison nor an adjunction.

Source: parent lem-pur-finite-coefficient-adjoint-comparisons, steps 7--8 and 12--13;
current blueprint reduction-exceptional, site/coefficient compatibility.
(blueprint: lem-pur-normalized-change-site-reflection).

Proof: let L = Rnu_Y K. The comparison counit at K is invertible because K has
bounded etale origin. The same holds at its scalar extension by hY. Write delta
for pbcComparisonReduction. Set e = delta_Y(L).symm followed by tensor of the
comparison counit at K; thus e identifies nu_B(scalar L) with tensor K. Set
z = unit_B(scalar L) followed by Rnu_B(e); this identifies scalar L with
Rnu_B(tensor K). Both arrows are isomorphisms. Use the scalar
site square to identify scalar extension of nu_X(etaleUpper_A L) with
nu_X(scalar extension of etaleUpper_A L), and use the invertible comparison unit
at scalar extension of L to identify the target with
nu_X(etaleUpper_B(scalar extension of L)). All needed lower bounds follow from
dA.etaleBound, dB.etaleBound and the supplied tensor bounds. The conjugated map is
delta_X(etaleUpper_A L).hom followed by nu_B of the etale mate, followed by
nu_B(etaleUpper_B(z.hom)). Expand dA.counit_normalization and
dB.counit_normalization. Naturality of the site counit, scalar/site comparison and
compact-support site comparison, together with the two comparison-adjunction
triangle identities, shows that the conjugated map has precisely hm as counit
transpose. The projection normalization fixes the compact-support comparison at
the retained origin of upper_A K; naturality removes the chosen origin witness.
Injectivity of the dB adjunction transpose identifies m with this conjugated map.
The middle map is the exact comparison inverse image of the etale mate, hence is
invertible by he. The two boundary maps are isomorphisms, so m is invertible.
Proof irrelevance removes differences between lower-bound witnesses. This argument
uses arbitrary finite coefficient rings and works for zero inputs and empty schemes. -/
theorem normalized_change_site_reflection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (φ : A →+* B) (c : Compactification f)
    (dA : AdjointDatum A c) (dB : AdjointDatum B c)
    (hX : ∀ K, ctf A X K → ctf B X ((tensor φ X).obj K))
    (hY : ∀ K, ctf A Y K → ctf B Y ((tensor φ Y).obj K))
    (hb : ∀ (K : (ctf A X).FullSubcategory)
      (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
      DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj w.complex.obj))
    (q : (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
      (ctf A X).ι ⋙ tensor φ X ⋙ lower B c)
    (hq : ∀ (K : (ctf A X).FullSubcategory)
      (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
      q.hom.app K = projectionAtWitness φ c K w (hb K w))
    (K : (ctf A Y).FullSubcategory)
    (m : (tensor φ X).obj ((upper A c).obj K.obj) ⟶
      (upper B c).obj ((tensor φ Y).obj K.obj))
    (hm : (lower B c).map m ≫
        dB.counit ⟨(tensor φ Y).obj K.obj, hY K.obj K.property⟩ =
      q.inv.app ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩ ≫
        (tensor φ Y).map (dA.counit K))
    (he : IsIso ((etaleAdjunction B c).homEquiv _ _
      (Etale.ExceptionalCoefficients.comparisonInverse φ c
          ((etaleUpper A c).obj ((rnu A Y).obj K.obj)) ≫
        (Etale.scalarExtension φ Y).map
          ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj))))) :
    IsIso m := by
  let n := normalizedTransportMate φ c K.obj
  have hn := normalizedTransportMate_counit φ c dA dB hY hb q hq K
  have hmn : m = n := by
    let P : (ctf B X).FullSubcategory :=
      ⟨_, hX _ (dA.upper_preserves K.obj K.property)⟩
    let Q : (ctf B Y).FullSubcategory := ⟨_, hY K.obj K.property⟩
    have h : (ObjectProperty.homMk m :
        P ⟶ (restrict (upper B c) dB.upper_preserves).obj Q) =
        ObjectProperty.homMk n := by
      apply (dB.adjunction.homEquiv P Q).symm.injective
      apply ObjectProperty.hom_ext
      change (lower B c).map m ≫ dB.counit Q =
        (lower B c).map n ≫ dB.counit Q
      exact hm.trans hn.symm
    exact congrArg (fun t ↦ t.hom) h
  rw [hmn]
  exact normalizedTransportMate_isIso φ c K (hY K.obj K.property) he

end AlgebraicGeometry.FiniteCoefficientAdjoints
