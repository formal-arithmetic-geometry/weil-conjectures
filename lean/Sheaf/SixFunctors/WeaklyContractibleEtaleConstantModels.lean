/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization

/-! # Trivializing a common etale constant model on a weakly contractible object

Source: Stacks Project, proetale.tex, Tag 09C6; sites.tex, Tag 090K.
(blueprint: lem-sfb-wcontractible-etale-constant-models)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

private theorem sectionOfCover
    {X : Scheme.{u}} {W V : X.ProEt} (p : V ⟶ W)
    (hp : Sieve.generate (Presieve.singleton p) ∈ ProEt.topology X W)
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    ∃ s : W ⟶ V, s ≫ p = 𝟙 W := by
  let J := ProEt.topology X
  have hepi : Epi (J.uliftYoneda.{u + 1}.map p) := by
    constructor
    intro Z a b hab
    apply J.uliftYonedaEquiv.injective
    have heq : Z.obj.map p.op (J.uliftYonedaEquiv a) =
        Z.obj.map p.op (J.uliftYonedaEquiv b) := by
      rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality, hab]
    apply Sheaf.isSeparated Z W _ hp
    rintro T f ⟨_, g, _, ⟨⟩, rfl⟩
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (Z.obj.map g.op) heq
  obtain ⟨s, hs⟩ := hW (J.uliftYoneda.{u + 1}.map p)
    ((Sheaf.isLocallySurjective_iff_epi _).mpr hepi) ⟨𝟙 W⟩
  exact ⟨s.down, congrArg ULift.down hs⟩

private noncomputable def comparisonConstantDerivedIso
    (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (E : _root_.DerivedCategory (ModuleCat.{u + 1} R)) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E :=
  ((Functor.mapDerivedCategoryCompIso _ _).app E).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarConstantSheafIso R X)).app E

private noncomputable def etaleConstantDerivedIso
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : _root_.DerivedCategory (ModuleCat.{u + 1} R)) :
    (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E) ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E :=
  ((Functor.mapDerivedCategoryCompIso _ _).app E).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (constantSheafCompUpperStarIso R f)).app E

private noncomputable def modelOnFactorization
    (R : Type (u + 1)) [CommRing R] {X V Y : Scheme.{u}}
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (E : _root_.DerivedCategory (ModuleCat.{u + 1} R))
    (v : V ⟶ X) (t : Y ⟶ V) (f : Y ⟶ X) (hfac : t ≫ v = f)
    (e : (upperStar (ModuleCat.{u + 1} R) v).mapDerivedCategory.obj L ≅
      (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E) :
    (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) ≅
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E := by
  subst f
  let A := ModuleCat.{u + 1} R
  let c := ProEtale.comparisonUpperStar A Y
  let ep : (upperStar A (t ≫ v)).mapDerivedCategory.obj L ≅
      (constantSheaf Y.smallEtaleTopology A).mapDerivedCategory.obj E :=
    (Functor.mapDerivedCategoryNatIso (upperStarComp A t v)).app L ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app L ≪≫
      (upperStar A t).mapDerivedCategory.mapIso e ≪≫ etaleConstantDerivedIso R t E
  exact ((Functor.mapDerivedCategoryCompIso _ _).app L).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso A (t ≫ v))).app L ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app L ≪≫
    c.mapDerivedCategory.mapIso ep ≪≫ comparisonConstantDerivedIso R Y E

private theorem singleProjectionIso {D : Type*} [Category D] [HasZeroMorphisms D]
    {I : Type*} (G : I → D) [HasProduct G] (i : I)
    (h : ∀ j, j ≠ i → IsZero (G j)) : IsIso (Pi.π G i) := by
  classical
  let q : G i ⟶ ∏ᶜ G := Pi.lift (fun j ↦ if e : i = j then eqToHom (congrArg G e) else 0)
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply Pi.hom_ext
    intro j
    by_cases e : j = i
    · subst j
      simp [q]
    · exact (h j e).eq_of_tgt _ _
  · simp [q]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem clopenDerivedModels
    (R : Type (u + 1)) [CommRing R] {Y : Scheme.{u}}
    {I : Type u} [Finite I] {V : I → Scheme.{u}} (j : ∀ i, V i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i k ↦ Disjoint (Set.range (j i).base) (Set.range (j k).base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (K H : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (e : ∀ i, (ProEtale.upperStar (ModuleCat.{u + 1} R) (j i)).mapDerivedCategory.obj K ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} R) (j i)).mapDerivedCategory.obj H) :
    Nonempty (K ≅ H) := by
  classical
  let A := ModuleCat.{u + 1} R
  let U := fun i ↦ ProEtale.upperStar A (j i)
  let S := fun i ↦ ProEtale.lowerStar A (j i)
  have (i : I) : PreservesFiniteColimits (S i) :=
    ProEtale.preservesFiniteColimits_lowerStar_of_isClosed_range A (j i) (hclosed i)
  let adj := fun i ↦ (ProEtale.upperStarLowerStarAdjunction A (j i)).mapDerivedCategoryAdjunction
  have hcov : Presieve.ofArrows V j ∈ proetalePrecoverage Y :=
    zariskiPrecoverage_le_proetalePrecoverage _
      ((ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ Set.mem_iUnion.mp (hcover.ge (Set.mem_univ x)), fun i ↦ inferInstance⟩)
  have hjoint : JointlyReflectIsomorphisms U := by
    constructor
    intro F G f hf
    apply ProEtale.isIso_of_isIso_localizationRestriction A f j hcov
    intro i
    have : IsIso ((U i).map f) := hf i
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction A (j i) inferInstance) f).mp this
  have hdjoint := Functor.jointlyReflectIsomorphisms_mapDerivedCategory hjoint
  let η (M) : M ⟶ ∏ᶜ (fun i ↦ (S i).mapDerivedCategory.obj
      ((U i).mapDerivedCategory.obj M)) := Pi.lift (fun i ↦ (adj i).unit.app M)
  have hη (M) : IsIso (η M) := by
    apply (hdjoint.isIso_iff _).mpr
    intro i
    let D := (U i).mapDerivedCategory
    let Gi := fun k ↦ (S k).mapDerivedCategory.obj ((U k).mapDerivedCategory.obj M)
    have hz (k : I) (hki : k ≠ i) : IsZero (D.obj (Gi k)) :=
      ProEtale.isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_lowerStar
        (j k) (j i) (hdisj hki) _
    have : IsIso (Pi.π (fun k ↦ D.obj (Gi k)) i) := singleProjectionIso _ i hz
    have : IsIso (D.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    have hc : IsIso ((adj i).counit.app ((U i).mapDerivedCategory.obj M)) := by
      infer_instance
    have hu : IsIso (D.map ((adj i).unit.app M)) := by
      rw [← isIso_comp_right_iff _ ((adj i).counit.app _)]
      change IsIso ((U i).mapDerivedCategory.map ((adj i).unit.app M) ≫
        (adj i).counit.app ((U i).mapDerivedCategory.obj M))
      have heq : (U i).mapDerivedCategory.map ((adj i).unit.app M) ≫
          (adj i).counit.app ((U i).mapDerivedCategory.obj M) = 𝟙 _ :=
        (adj i).left_triangle_components M
      rw [heq]
      infer_instance
    rw [← isIso_comp_right_iff _ (D.map (Pi.π Gi i)), ← D.map_comp]
    have heq : η M ≫ Pi.π Gi i = (adj i).unit.app M := Pi.lift_π _ _
    rw [heq]
    exact hu
  have : IsIso (η K) := hη K
  have : IsIso (η H) := hη H
  exact ⟨asIso (η K) ≪≫ Pi.mapIso (fun i ↦ (S i).mapDerivedCategory.mapIso (e i)) ≪≫
    (asIso (η H)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Etale local identifications with a fixed algebraic complex become a global
identification on any affine weakly contractible pro-etale object.

Source: Stacks Project, proetale.tex, proof of Tag 09C6; sites.tex, Tag 090K.
(blueprint: lem-sfb-wcontractible-etale-constant-models)

Proof. Geometric inverse image preserves constant module sheaves, naturally in
linear maps, hence preserves constant complexes after passing to derived categories.
The etale/pro-etale comparison commutes with pullback and restriction. Pull the given
etale cover back to W. Its restrictions therefore identify the comparison pullback
with the constant E on every member. Since W is affine, refine this cover by finitely
many affine etale maps U_j to W. They are pro-etale objects over X: etale maps are
weakly etale, and weakly etale maps compose. Their finite disjoint union U is affine
and pro-etale over X, and the representable map h_U to h_W is an epimorphism, since
its components form a covering family. Weak contractibility gives a section of this
map; subcanonicity identifies it with a scheme section s of U to W. On each clopen
component j_i, direct image is exact. The derived adjunction units give a map from
any derived object K to the finite product of j_i* j_i^* K. Each restriction of this
map is an isomorphism: the off-diagonal terms are zero by disjointness and the
remaining term is an isomorphism by the adjunction triangle identity. Restrictions
jointly reflect isomorphisms, so the unit map is an isomorphism. These product
identifications assemble the local isomorphisms on U_j. Pulling the result back along s
gives the required one on W, because its composite with U to W is the identity.
The same construction permits disconnected W. For empty W both objects are zero.
Neither coefficient finiteness nor perfectness of E is needed. -/
theorem etale_constant_models_on_weaklyContractible
    (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (E : _root_.DerivedCategory (ModuleCat.{u + 1} R))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (hlocal : ∀ i : 𝒰.I₀, Nonempty
      ((upperStar (ModuleCat.{u + 1} R) (𝒰.f i)).mapDerivedCategory.obj L ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology
          (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E))
    (W : X.ProEt) [IsAffine W.left]
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    Nonempty
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) W.hom).mapDerivedCategory.obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) ≅
        (constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E)
    := by
  classical
  let A := ModuleCat.{u + 1} R
  let P := 𝒰.pullback₁ W.hom
  have : QuasiCompactCover P.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (P.f i).isOpenMap)
  have : CompactSpace ((𝟭 Scheme.{u}).obj W.left) :=
    inferInstanceAs (CompactSpace W.left)
  obtain ⟨𝒱, φ, hfin, hφ⟩ := QuasiCompactCover.exists_hom.{u, u} P
  have : Finite 𝒱.I₀ := hfin
  have : Finite 𝒱.cover.I₀ := hfin
  let V := 𝒱.cover.X
  let v := 𝒱.cover.f
  let q : (∐ V) ⟶ W.left := Sigma.desc v
  have : ∀ i, Etale (v i) := fun i ↦ 𝒱.map_prop i
  have : Etale q := IsZariskiLocalAtSource.sigmaDesc (fun i ↦ 𝒱.map_prop i)
  have : Surjective q := Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range
  let T : X.ProEt := ProEt.mk (q ≫ W.hom)
  let p : T ⟶ W := MorphismProperty.Over.homMk q rfl
  have hp : Sieve.generate (Presieve.singleton p) ∈ ProEt.topology X W := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    apply etalePrecoverage_le_proetalePrecoverage
    change Presieve.singleton q ∈ precoverage @AlgebraicGeometry.Etale W.left
    rw [singleton_mem_precoverage_iff]
    exact ⟨q.surjective, inferInstance⟩
  obtain ⟨s, hs⟩ := sectionOfCover p hp hW
  have hs' : s.left ≫ q = 𝟙 W.left := congrArg (fun f ↦ f.left) hs
  let N := (ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj L
  let c := fun Y : Scheme.{u} ↦ constantSheaf (ProEt.topology Y) A
  let K := (ProEtale.upperStar A (q ≫ W.hom)).mapDerivedCategory.obj N
  let H := (c (∐ V)).mapDerivedCategory.obj E
  have hjclosed (i : 𝒱.I₀) : IsClosed (Set.range (Sigma.ι V i).base) := by
    have he : (Set.range (Sigma.ι V i).base)ᶜ =
        ⋃ j : {j : 𝒱.I₀ // j ≠ i}, Set.range (Sigma.ι V j.1).base := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_range, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq x
        refine ⟨⟨j, ?_⟩, y, hy⟩
        rintro rfl
        exact hx ⟨y, hy⟩
      · rintro ⟨⟨j, hji⟩, y, hy⟩ ⟨z, hz⟩
        have h := (sigmaι_eq_iff V j i y z).mp (hy.trans hz.symm)
        exact hji (Sigma.mk.inj_iff.mp h).1
    exact isOpen_compl_iff.mp (he ▸ isOpen_iUnion
      (fun j ↦ (Sigma.ι V j.1).isOpenEmbedding.isOpen_range))
  have hjdisj : Pairwise fun i k ↦
      Disjoint (Set.range (Sigma.ι V i).base) (Set.range (Sigma.ι V k).base) := by
    intro i k hik
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have h := (sigmaι_eq_iff V i k x y).mp (hx.trans hy.symm)
    exact hik (Sigma.mk.inj_iff.mp h).1
  have hjcover : ⋃ i, Set.range (Sigma.ι V i).base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  have e (i : 𝒱.I₀) :
      (ProEtale.upperStar A (Sigma.ι V i)).mapDerivedCategory.obj K ≅
        (ProEtale.upperStar A (Sigma.ι V i)).mapDerivedCategory.obj H := by
    let t : V i ⟶ 𝒰.X (φ.s₀ i) := φ.h₀ i ≫ 𝒰.pullbackHom W.hom (φ.s₀ i)
    have ht : t ≫ 𝒰.f (φ.s₀ i) = v i ≫ W.hom := by
      simp only [t, Category.assoc, Cover.pullbackHom_map]
      rw [← Category.assoc, φ.w₀]
    let ei := modelOnFactorization R L E (𝒰.f (φ.s₀ i)) t (v i ≫ W.hom) ht
      (hlocal (φ.s₀ i)).some
    have hi : Sigma.ι V i ≫ (q ≫ W.hom) = v i ≫ W.hom := by
      rw [← Category.assoc, Sigma.ι_desc]
    let ec : (c (∐ V) ⋙ ProEtale.upperStar A (Sigma.ι V i)) ≅ c (V i) :=
      ProEtale.constantSheafCompUpperStarIso A (Sigma.ι V i)
    exact ((Functor.mapDerivedCategoryCompIso _ _).app N).symm ≪≫
      (Functor.mapDerivedCategoryNatIso
        (ProEtale.upperStarComp A (Sigma.ι V i) (q ≫ W.hom)).symm).app N ≪≫
      (Functor.mapDerivedCategoryNatIso (ProEtale.upperStarCongr A hi)).app N ≪≫
      ei ≪≫ ((Functor.mapDerivedCategoryNatIso ec).app E).symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app E
  obtain ⟨eT⟩ := clopenDerivedModels R (Sigma.ι V) hjclosed hjdisj hjcover K H e
  let es := (ProEtale.upperStar A s.left).mapDerivedCategory.mapIso eT
  have hcomp : s.left ≫ (q ≫ W.hom) = W.hom := by
    rw [← Category.assoc, hs', Category.id_comp]
  exact ⟨((Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarCongr A hcomp)).app N).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp A s.left (q ≫ W.hom))).app N ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app N ≪≫ es ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).app E).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.constantSheafCompUpperStarIso A s.left)).app E⟩

end AlgebraicGeometry.Etale
