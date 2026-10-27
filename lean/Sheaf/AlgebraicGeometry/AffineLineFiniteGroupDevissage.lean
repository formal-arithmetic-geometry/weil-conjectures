module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.KummerRootLineComputation
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.MvPolynomial.Equiv
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Finite primary coefficients on the geometric affine line

Source: current blueprint, sec-six-functors-basics/sk-prop-a1-kummer,
Coefficients and Degrees 0 and 1, with finite-primary cardinality devissage
(blueprint: lem-pur-affine-line-finite-group-devissage).

The two helper constructions only assemble existing functors and adjunction units.
In particular the comparison is the canonical constants map, without a primitive-root
choice or a choice of an isomorphism of its endpoints.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Derived sections of a constant abelian sheaf placed in degree zero, functorial in
its coefficient group. Source: blueprint sk-prop-a1-kummer, Coefficients and Degrees 0 and 1
(blueprint: lem-pur-affine-line-finite-group-devissage). -/
def abelianConstantsDerivedSections (X : Scheme.{u}) :
    AddCommGrpCat.{u + 1} ⥤ DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    DerivedCategory.Plus.singleFunctor _ 0) ⋙
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus

/-- The canonical map from coefficients in degree zero to derived sections of their
constant sheaf: the derived constant-sheaf/sections adjunction unit, followed by the
canonical compatibility of exact constants with the degree-zero single functor.
Source: blueprint sk-prop-a1-kummer, Coefficients and Degrees 0 and 1
(blueprint: lem-pur-affine-line-finite-group-devissage). -/
def abelianDerivedConstants (X : Scheme.{u}) :
    DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u + 1} 0 ⟶
      X.abelianConstantsDerivedSections :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).derivedPlus.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        |>.mapDerivedCategoryPlusSingleFunctor 0).hom
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AffineSpace

open Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma constants_unit (X : Scheme.{u}) [ConnectedSpace X]
    (B : AddCommGrpCat.{u + 1}) :
    IsIso ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app B) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale X
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  have hu : IsIso (adj.unit.app B) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    simp only [adj, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp]
    change Function.Bijective ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj B)).app (Opposite.op (Scheme.Etale.mk (𝟙 X))))
    exact X.bijective_toSheafify_app_terminal B
  have hf := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}) adj B
  have : IsIso ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app B ≫
      ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightAdjointUniq adj).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B)) := by
    rw [hf]
    exact hu
  exact IsIso.of_isIso_comp_right _
    (((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightAdjointUniq adj).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cyclic_vanishing (k : Type u) [Field k] [IsAlgClosed k]
    (m : ℕ) (hm : 1 ≤ m) (hinv : IsUnit (m : k)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((constantSheaf
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod m)))) q) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero (m : k) := ⟨hinv.ne_zero⟩
  obtain ⟨ζ, hζ, -⟩ := (IsSepClosed.exists_isPrimitiveRoot.{u, u} k m).2.2
  let ζu : kˣ := (hζ.isUnit (by omega)).unit
  have hζu : IsPrimitiveRoot ζu m :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa only [ζu, IsUnit.unit_spec] using hζ)
  have hm' : IsUnit (m : Γ(KummerLine.curve k true, ⊤)) := by
    simpa using hinv.map (KummerLine.scalar k true)
  have hz := (KummerLine.kummer_root_line_computation k m hm hinv ζu hζu hm').choose_spec.2.2.2.1
    false q (by simpa using hq)
  let := hz
  let θ := (KummerLine.curve k false).constantZModIsoRootsOfUnitySheaf m
    (KummerLine.structureMap k false) hζ
  have hc : Subsingleton (Sheaf.H ((KummerLine.curve k false).constantZMod m) q) :=
    ⟨fun x y ↦ ((Sheaf.functorH _ q).mapIso θ).addCommGroupIsoToAddEquiv.injective
      (hz.elim _ _)⟩
  let e : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ≅ KummerLine.curve k false :=
    AffineSpace.SpecIso _ (.of k) ≪≫ Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv.toCommRingCatIso.symm.op
  let F := (KummerLine.curve k false).constantZMod m
  let := hc
  have hc' : Subsingleton (Sheaf.H ((e.hom)^*[AddCommGrpCat.{u + 1}].obj F) q) :=
    (Etale.cohomologyMap_bijective e.hom F q).2.subsingleton
  let c := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} e.hom).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod m)))
  refine ⟨fun x y ↦
    ((Sheaf.functorH _ q).mapIso c.symm).addCommGroupIsoToAddEquiv.injective ?_⟩
  exact hc'.elim _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma finite_vanishing (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) (hinv : IsUnit (ell : k))
    (B : AddCommGrpCat.{u + 1}) [Finite B] (a : ℕ)
    (hB : ∀ b : B, (ell ^ a) • b = 0) :
    (Sheaf.Γ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightAcyclic
      ((constantSheaf (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj B) := by
  classical
  let X := AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' B
  let E : B ≃+ ((i : ι) → ULift.{u + 1} (ZMod (n i))) :=
    (e.trans (DirectSum.addEquivProd _)).trans
      (AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift.symm)
  have hdvd (i : ι) : n i ∣ ell ^ a := by
    have h := congrArg (fun x ↦ (E x i).down)
      (hB (E.symm (Function.update 0 i 1)))
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using h
  have hi (i : ι) : IsUnit (n i : k) := by
    obtain ⟨d, hd⟩ := hdvd i
    apply isUnit_of_dvd_unit (show (n i : k) ∣ (ell : k) ^ a from ?_) (hinv.pow a)
    exact ⟨(d : k), by simpa only [Nat.cast_pow, Nat.cast_mul] using congrArg (Nat.cast : ℕ → k) hd⟩
  let f (i : ι) : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} (ZMod (n i)))
  let eB : B ≅ ⨁ f := E.toAddCommGrpIso ≪≫ (AddCommGrpCat.biproductIsoPi f).symm
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 X)))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  intro q
  let H := C ⋙ G.rightDerived (q + 1)
  have hz (i : ι) : IsZero (H.obj (f i)) := by
    have hv := cyclic_vanishing k (n i) (by have := hn i; omega) (hi i) (q + 1)
      (by omega)
    have hv' := (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology
      (MorphismProperty.Over.mkIdTerminal @Etale X) (q + 1) (C.obj (f i))).1 hv
    exact hv'.of_iso ((NatIso.rightDerived (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{u + 1} (MorphismProperty.Over.mkIdTerminal @Etale X))
        (q + 1)).app (C.obj (f i)))
  have hzsum : IsZero (⨁ fun i ↦ H.obj (f i)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply biproduct.hom_ext
    intro i
    exact (hz i).eq_of_tgt _ _
  exact hzsum.of_iso (H.mapIso eB ≪≫ H.mapBiproduct f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma derived_constants_iso (X : Scheme.{u}) [ConnectedSpace X]
    (B : AddCommGrpCat.{u + 1})
    (hB : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightAcyclic
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B)) :
    IsIso (X.abelianDerivedConstants.app B) := by
  let L := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let R := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let adj := constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have (M : AddCommGrpCat.{u + 1}) : IsIso (adj.unit.app M) := constants_unit X M
  let S : CochainComplex.Plus AddCommGrpCat.{u + 1} :=
    ⟨(CochainComplex.singleFunctor _ 0).obj B, 0, inferInstance⟩
  let K := (HomotopyCategory.Plus.quotient _).obj S
  let LS := L.mapCochainComplexPlus.obj S
  have hLS (n : ℤ) : R.rightAcyclic (LS.obj.X n) := by
    by_cases hn : n = 0
    · subst n
      exact R.rightAcyclic.prop_of_iso
        (L.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B)).symm hB
    · exact R.rightAcyclic.prop_of_isZero (L.map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 B n hn))
  have hR : IsIso (R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K)) :=
    R.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic LS hLS
  have hu : IsIso (adj.mapHomotopyCategoryPlus.unit.app K) := by
    have : IsIso ((HomotopyCategory.Plus.ι _).map
        (adj.mapHomotopyCategoryPlus.unit.app K)) := by
      rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
      change IsIso ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj S.obj))
      rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app S.obj).f n) := by
        rw [Adjunction.mapHomologicalComplex_unit_app_f]
        infer_instance
      have : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app S.obj) :=
        HomologicalComplex.Hom.isIso_of_components _
      exact Functor.map_isIso _ _
    exact isIso_of_fully_faithful (HomotopyCategory.Plus.ι _) _
  have hunit : IsIso (adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K)) := by
    have : IsIso (adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K)) := by
      rw [adj.derivedPlus_unit_app_fac K]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K))
  let e : (DerivedCategory.Plus.singleFunctor _ 0).obj B ≅ DerivedCategory.Plus.Qh.obj K :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app B ≪≫
        (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u + 1}).symm.app S.obj)
  have : IsIso (adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj B)) :=
    (NatTrans.isIso_app_iff_of_iso adj.derivedPlus.unit e).mpr hunit
  dsimp only [Scheme.abelianDerivedConstants, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- Finite-primary devissage on the geometric affine line, including the specified
constants map and coefficient naturality. Source: current blueprint sk-prop-a1-kummer,
Coefficients and Degrees 0 and 1
(blueprint: lem-pur-affine-line-finite-group-devissage).

Proof:
1. On every connected scheme, the constants unit is invertible by the computation of
   global sections of constant sheaves. Transport along uniqueness of right adjoints
   identifies that unit with the unit for the specified global-sections functor.
2. For any positive m invertible in k, choose a primitive m-th root and apply the Kummer
   root computation at false. The roots-of-unity trivialization transfers positive-degree
   vanishing to ZMod m. The affine-space/Spec-polynomial isomorphism and the canonical
   constant-sheaf pullback comparison transfer it to the stated affine line.
3. Mathlib's finite abelian-group structure theorem writes B as a finite sum of ZMod n_i.
   Applying the exponent hypothesis to each coordinate shows n_i divides ell^a, hence n_i
   is invertible in k. The additive higher-derived functors preserve this finite sum, so
   all positive derived sections vanish. The empty sum includes the zero coefficient group.
4. Apply the acyclic-complex comparison to the constant single complex B_C[0]. The derived
   adjunction unit factors as the termwise constants unit followed by that comparison, so
   the actual specified constants map is invertible. Its homology identifies derived
   sections with B in degree zero and zero in every other degree.
5. Naturality is the naturality equation of abelianDerivedConstants itself. The exponent
   hypothesis makes Multiplicative B an ell-group, so Mathlib's p-group cardinality theorem
   gives the final order assertion. No freeness over ZMod (ell^a) is used. -/
theorem affineLine_finiteGroup_devissage (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) (hell : Nat.Prime ell) (hinv : IsUnit (ell : k))
    (B : AddCommGrpCat.{u + 1}) [Finite B] (a : ℕ) (ha : 1 ≤ a)
    (hB : ∀ b : B, (ell ^ a) • b = 0) :
    IsIso ((AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).abelianDerivedConstants.app B) ∧
    IsIso ((constantSheafΓAdj
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).smallEtaleTopology
      AddCommGrpCat.{u + 1}).unit.app B) ∧
    (∀ q : ℤ, q ≠ 0 → IsZero
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).abelianConstantsDerivedSections.obj B))) ∧
    (∀ (B' : AddCommGrpCat.{u + 1}) [Finite B'] (a' : ℕ), 1 ≤ a' →
      (∀ b : B', (ell ^ a') • b = 0) → ∀ f : B ⟶ B',
      (DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u + 1} 0).map f ≫
          (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).abelianDerivedConstants.app B' =
        (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).abelianDerivedConstants.app B ≫
          (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))).abelianConstantsDerivedSections.map f) ∧
    (∃ b : ℕ, Nat.card B = ell ^ b) := by
  classical
  let X := AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))
  have : ConnectedSpace X := inferInstance
  have hu : IsIso (X.abelianDerivedConstants.app B) :=
    derived_constants_iso X B (finite_vanishing k ell hinv B a (by
      have _ := ha
      exact hB))
  refine ⟨hu, constants_unit X B, ?_, ?_, ?_⟩
  · intro q hq
    have hz : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u + 1} 0).obj B)) := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q h
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q h
    exact hz.of_iso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      (asIso (X.abelianDerivedConstants.app B))).symm
  · intro B' _ a' _ _ f
    exact X.abelianDerivedConstants.naturality f
  · have : Fact ell.Prime := ⟨hell⟩
    have hp : IsPGroup ell (Multiplicative B) :=
      isPGroup_iff_pow_pow_eq_one.mpr fun b ↦ ⟨a, by
        apply Multiplicative.toAdd.injective
        exact hB b.toAdd⟩
    obtain ⟨b, hb⟩ := hp.exists_card_eq
    exact ⟨b, (Nat.card_congr Multiplicative.ofAdd).trans hb⟩

end AlgebraicGeometry.AffineSpace
