/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.PUnit

/-!
# Tensor and unbounded derived calculus for a finite clopen partition

Source: Stacks Project, derived.tex, Tags 015F and 05RU; sites-modules.tex, Tag 0GMW;
sites-cohomology.tex, Tags 06YN, 06YS, 0G7D and 06YU; finite-component application
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

All restrictions are the sectionwise functors of the module-gluing node. Tensor products
and their constraints are the existing sheafification and K-flat localization constructions.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  DerivedCategory.Q Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

namespace AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor

/-- The recorded module category, with a coefficient universe containing the small site.
Source: Stacks 03D7 (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

/-- Restrict commutative rings by the same site composition as `clopenRingRestriction`.
Source: Stacks 04TR (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)

/-- The module restriction of the recorded gluing theorem, without changing its data.
Source: Stacks 04TR (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenModuleRestriction j
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)

/-- Exactness of component restriction, including the unbounded case.
Source: Stacks 015F and 04TR (blueprint: lem-pur-finite-product-derived-tensor-calculus).
Proof: identify the component site with the slice at the open immersion. Restriction
preserves kernels and sheafified cokernels by the exact module-gluing equivalence;
equivalently sheaf exactness is local on this slice. No exactness of sections is used. -/
theorem restriction_exact {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) ∧
      PreservesFiniteColimits (restriction.{t, u} j R) := by
  let : (restriction.{t, u} j R).IsLeftAdjoint := by
    unfold restriction clopenModuleRestriction
    infer_instance
  let S := ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
    RingCat.{max u (t + 1)})).obj ((rings.{t, u} j).obj R))
  let V := SheafOfModules.toSheaf.{max u (t + 1)} S
  have : PreservesFiniteLimits (restriction.{t, u} j R ⋙ V) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf _ ⋙
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
        AddCommGrpCat.{max u (t + 1)} (topology Y) (topology X))
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ V, inferInstance⟩

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) := (restriction_exact j R).1

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteColimits (restriction.{t, u} j R) := (restriction_exact j R).2

/-- Additivity is the already recorded sectionwise restriction additivity.
Source: Stacks 04TR (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance restrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (restriction.{t, u} j R).Additive :=
  clopenModuleRestriction_additive j _

/-- Standard localization in the fixed module universe, with no boundedness restriction.
Source: Stacks 05RU (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  HasDerivedCategory.standard (Modules.{t, u} R)

/-- Degreewise restriction followed by localization at quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  (restriction.{t, u} j R).mapDerivedCategory

/-- The existing native K-flat derived tensor, with its prescribed constraints.
Source: Stacks 0FPT (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance derivedMonoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (Modules.{t, u} R)) :=
  RingedDerivedNative.monoidal.{t + 1, t, u} (topology X) R

/-- Its existing Koszul symmetry.
Source: Stacks 0FPT (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
instance derivedSymmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (Modules.{t, u} R)) :=
  RingedDerivedNative.symmetric.{t + 1, t, u} (topology X) R

/-- The pure tensor in the existing localization tensor of module sheaves.
Source: Stacks 0GMW (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def pure {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : Modules.{t, u} R) (U : X.ProEtᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (F ⊗ H).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R).obj)).unit.app (F.val ⊗ H.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) F H).inv.val).app U)
    (x ⊗ₜ[R.obj.obj U] y)

/-- The inverse tensorator of a braided restriction functor.
Source: Stacks 0GMW (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def tensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (restriction.{t, u} j R).Braided) (F H : Modules.{t, u} R) :
    (restriction.{t, u} j R).obj (F ⊗ H) ≅
      (restriction.{t, u} j R).obj F ⊗ (restriction.{t, u} j R).obj H :=
  letI := h
  (Functor.Monoidal.μIso (restriction.{t, u} j R) F H).symm

/-- The inverse tensorator on the prescribed native derived tensors.
Source: Stacks 06YU, 0FPT (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      exact (@Functor.Monoidal.μIso _ _ (derivedMonoidal.{t, u} R) _ _
        (derivedMonoidal.{t, u} ((rings.{t, u} j).obj R))
        (derivedRestriction.{t, u} j R) h.toMonoidal K L).symm

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

private def coordinateTransport {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] {i k : J} (h : i = k) : D i ⥤ D k := by
  subst k
  exact 𝟭 _

private def coordinateInsertion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] (i : J) : D i ⥤ ∀ k, D k := by
  classical
  exact Functor.pi' (fun k ↦ if h : i = k then coordinateTransport D h
    else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))

private def coordinateProjection {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : 𝟭 (∀ k, D k) ⟶ Pi.eval D i ⋙ coordinateInsertion D i := by
  classical
  apply NatTrans.pi'
  intro k
  change Pi.eval D k ⟶ Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose))
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).inv
  · exact 0

private def coordinateInclusion {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, HasZeroObject (D i)] [∀ i, HasZeroMorphisms (D i)]
    (i : J) : Pi.eval D i ⋙ coordinateInsertion D i ⟶ 𝟭 (∀ k, D k) := by
  classical
  apply NatTrans.pi'
  intro k
  change (Pi.eval D i ⋙
    (if h : i = k then coordinateTransport D h
      else (Functor.const _).obj (show D k from HasZeroObject.zero.choose)))
      ⟶ Pi.eval D k
  by_cases h : i = k
  · subst k
    simpa only [dite_true, coordinateTransport] using
      (Functor.rightUnitor (Pi.eval D i)).hom
  · exact 0

private def coordinateBicone {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    Bicone (fun i ↦ Pi.eval D i ⋙ coordinateInsertion D i) := by
  classical
  refine
    { pt := 𝟭 _
      π := coordinateProjection D
      ι := coordinateInclusion D
      ι_π := ?_ }
  intro i k
  by_cases h : i = k
  · subst k
    simp only [dite_true, eqToHom_refl]
    apply NatTrans.ext
    funext M l
    by_cases hl : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, coordinateInsertion,
        coordinateTransport, NatTrans.pi', Functor.pi', Pi.eval]
    · have hz : IsZero ((coordinateInsertion D i).obj (M i) l) := by
        simpa only [coordinateInsertion, Functor.pi'_obj, dif_neg hl, Functor.const_obj_obj]
          using (HasZeroObject.zero (C := D l)).choose_spec
      exact hz.eq_of_src _ _
  · simp only [dif_neg h]
    apply NatTrans.ext
    funext M l
    by_cases hi : i = l
    · subst l
      simp [coordinateProjection, coordinateInclusion, NatTrans.pi', Ne.symm h]
      rfl
    · simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
      rfl

private theorem coordinateBicone_total {J : Type*} [Fintype J] (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)] :
    ∑ i, (coordinateBicone D).π i ≫ (coordinateBicone D).ι i = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext M k
  rw [NatTrans.app_sum]
  have he {S : Finset J} (f : J → ∀ i, M i ⟶ M i) :
      (∑ i ∈ S, f i) k = ∑ i ∈ S, f i k := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS => simp [Finset.sum_insert hi]
  rw [he]
  change (∑ i, (coordinateProjection D i).app M k ≫
    (coordinateInclusion D i).app M k) = 𝟙 (M k)
  rw [Finset.sum_eq_single k]
  · simp [coordinateProjection, coordinateInclusion, NatTrans.pi',
      coordinateTransport]
  · intro i _ hi
    simp [coordinateProjection, coordinateInclusion, NatTrans.pi', hi]
  · simp

private theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
      (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙ e i),
        b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  classical
  let := Fintype.ofFinite J
  let s := coordinateInsertion D
  let e (i : J) := s i ⋙ E.inverse
  have hs (i : J) : s i ⋙ Pi.eval D i ≅ 𝟭 _ := by
    dsimp only [s, coordinateInsertion]
    refine Functor.pi'CompEval _ i ≪≫ ?_
    simpa only [dite_true, coordinateTransport] using (Iso.refl (𝟭 (D i)))
  have hz (i k : J) (h : k ≠ i) (M : D i) : IsZero ((s i).obj M k) := by
    simpa [s, coordinateInsertion, Ne.symm h] using (HasZeroObject.zero (C := D k)).choose_spec
  refine ⟨e, ?_, ?_, ⟨s, fun i ↦ ⟨rfl, ⟨hs i⟩, hz i⟩⟩, ?_, ?_⟩
  · intro i
    exact ⟨Functor.associator (s i) E.inverse (E.functor ⋙ Pi.eval D i) ≪≫
      Functor.isoWhiskerLeft (s i) ((Functor.associator E.inverse E.functor (Pi.eval D i)).symm ≪≫
        Functor.isoWhiskerRight E.counitIso (Pi.eval D i) ≪≫ Functor.leftUnitor _) ≪≫ hs i⟩
  · intro i k hik M
    exact IsZero.of_iso (hz k i hik M) (Pi.isoApp (E.counitIso.app ((s k).obj M)) i)
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ (C ⥤ C) :=
      (Functor.whiskeringLeft C (∀ i, D i) (∀ i, D i)).obj E.functor ⋙
        (Functor.whiskeringRight C (∀ i, D i) C).obj E.inverse
    have : H.Additive := inferInstance
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    let b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i) :=
      { pt := 𝟭 _
        π i := E.unitIso.hom ≫ b'.π i
        ι i := b'.ι i ≫ E.unitIso.inv
        ι_π i k := by
          change (b'.ι i ≫ E.unitIso.inv) ≫ (E.unitIso.hom ≫ b'.π k) = _
          rw [Category.assoc, Iso.inv_hom_id_assoc]
          exact b'.ι_π i k }
    refine ⟨b, rfl, ⟨isBilimitOfTotal b ?_⟩⟩
    change ∑ i, (E.unitIso.hom ≫ b'.π i) ≫ (b'.ι i ≫ E.unitIso.inv) = 𝟙 _
    have ht' : ∑ i, b'.π i ≫ b'.ι i = 𝟙 (E.functor ⋙ E.inverse) := ht
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id] using
      congrArg (fun f ↦ E.unitIso.hom ≫ f ≫ E.unitIso.inv) ht'
  · let H : ((∀ i, D i) ⥤ ∀ i, D i) ⥤ ((∀ i, D i) ⥤ C) :=
      (Functor.whiskeringRight _ _ _).obj E.inverse
    let b' := H.mapBicone (coordinateBicone D)
    have ht : ∑ i, b'.π i ≫ b'.ι i = 𝟙 b'.pt := by
      change ∑ i, H.map _ ≫ H.map _ = 𝟙 _
      simp only [← H.map_comp, ← H.map_sum, coordinateBicone_total, H.map_id]
    exact ⟨b', rfl, ⟨isBilimitOfTotal b' ht⟩⟩

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

private def tupleComplex : (∀ i, CochainComplex (B i) ℤ) ⥤ CochainComplex A ℤ where
  obj P :=
    { X n := G.obj (fun i ↦ (P i).X n)
      d n m := G.map (fun i ↦ (P i).d n m)
      shape n m h := by
        have he : (fun i ↦ (P i).d n m) = (fun i ↦ (0 : (P i).X n ⟶ (P i).X m)) := by
          funext i
          exact (P i).shape n m h
        rw [he, hzero]
      d_comp_d' n m k _ _ := by
        rw [← G.map_comp]
        have he : (fun i ↦ (P i).d n m ≫ (P i).d m k) =
            (fun i ↦ (0 : (P i).X n ⟶ (P i).X k)) := by
          funext i
          exact (P i).d_comp_d n m k
        change G.map (fun i ↦ (P i).d n m ≫ (P i).d m k) = 0
        rw [he, hzero] }
  map f :=
    { f n := G.map (fun i ↦ (f i).f n)
      comm' n m _ := by
        rw [← G.map_comp, ← G.map_comp]
        congr 1
        funext i
        exact (f i).comm n m }
  map_id P := by
    ext n
    exact G.map_id _
  map_comp f g := by
    ext n
    exact G.map_comp _ _

private def tupleUnit : 𝟭 (CochainComplex A ℤ) ≅
    Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ)) ⋙ tupleComplex G hzero :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ η.app (P.X n)) (by
      intro n m _
      exact (η.hom.naturality (P.d n m)).symm)) (by
    intro P Q f
    ext n
    exact η.hom.naturality (f.f n))

private def tupleCounit : tupleComplex G hzero ⋙
    Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ Pi.isoMk (fun i ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Pi.eval _ i).mapIso (ε.app (fun k ↦ (P k).X n))) (by
      intro n m _
      exact (congrFun (ε.hom.naturality (fun k ↦ (P k).d n m)) i).symm))) (by
    intro P Q f
    funext i
    ext n
    exact congrFun (ε.hom.naturality (fun k ↦ (f k).f n)) i)

private def tupleEquivalence : CochainComplex A ℤ ≌ (∀ i, CochainComplex (B i) ℤ) :=
  CategoryTheory.Equivalence.mk _ _ (tupleUnit r G hzero η) (tupleCounit r G hzero ε)

include G hzero η ε in
private theorem derivedPi_isEquivalence
    (hr : JointlyReflectIsomorphisms r) :
    (Functor.pi' (fun i ↦ (r i).mapDerivedCategory)).IsEquivalence := by
  let rc := Functor.pi' (fun i ↦ (r i).mapHomologicalComplex (.up ℤ))
  let rd := Functor.pi' (fun i ↦ (r i).mapDerivedCategory)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Wi := MorphismProperty.pi (fun i ↦ HomologicalComplex.quasiIso (B i) (.up ℤ))
  let Qi := Functor.pi (fun i ↦ (DerivedCategory.Q : CochainComplex (B i) ℤ ⥤ _))
  let E := tupleEquivalence r G hzero η ε
  have hd := Functor.jointlyReflectIsomorphisms_mapDerivedCategory hr
  have hrc {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
      W f ↔ Wi (rc.map f) := by
    change QuasiIso f ↔
      ∀ i, QuasiIso (((r i).mapHomologicalComplex (.up ℤ)).map f)
    change QuasiIso f ↔ ∀ i, QuasiIso _
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso A f]
    simp_rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    rw [hd.isIso_iff]
    exact forall_congr' fun i ↦
      NatIso.isIso_map_iff (r i).mapDerivedCategoryFactors f
  have hinv : Wi.IsInvertedBy (E.inverse ⋙ DerivedCategory.Q) := by
    intro P Q f hf
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mpr
    apply (hrc (E.inverse.map f)).mpr
    intro i
    let e := (Pi.eval _ i).mapIso (E.counitIso.app P)
    let e' := (Pi.eval _ i).mapIso (E.counitIso.app Q)
    have hn : ((r i).mapHomologicalComplex (.up ℤ)).map (E.inverse.map f) ≫ e'.hom =
        e.hom ≫ f i := congrFun (E.counitIso.hom.naturality f) i
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk e e' hn.symm)).mpr (hf i)
  let Gd := Localization.lift (E.inverse ⋙ DerivedCategory.Q) hinv Qi
  let α : DerivedCategory.Q ⋙ rd ≅ rc ⋙ Qi :=
    NatIso.pi' (fun i ↦ (r i).mapDerivedCategoryFactors)
  let β : (E.inverse ⋙ DerivedCategory.Q) ⋙ rd ≅ Qi :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso Qi ≪≫ Functor.leftUnitor Qi
  let γ : (rc ⋙ Qi) ⋙ Gd ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft rc (Localization.fac (E.inverse ⋙ DerivedCategory.Q) hinv Qi) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q
  let : Localization.Lifting DerivedCategory.Q W (rc ⋙ Qi) rd := ⟨α⟩
  exact Localization.isEquivalence DerivedCategory.Q W Qi Wi (rc ⋙ Qi) rd
    (E.inverse ⋙ DerivedCategory.Q) Gd γ β

end DerivedPi

private theorem moduleGluing
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ E : Modules.{t, u} R ≌ ∀ i, Modules.{t, u} ((rings (j i)).obj R),
      E.functor = Functor.pi' (fun i ↦ restriction (j i) R) := by
  classical
  obtain ⟨n, ⟨a⟩⟩ := Finite.exists_equiv_fin I
  let e := a.symm
  let S := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  have hde : Pairwise (fun i k : Fin n ↦
      Disjoint (Set.range (j (e i))) (Set.range (j (e k)))) := by
    intro i k hik
    exact hd (fun h ↦ hik (e.injective h))
  have hce : ∀ x : X, ∃ i : Fin n, x ∈ Set.range (j (e i)) := by
    intro x
    obtain ⟨i, hi⟩ := hc x
    exact ⟨e.symm i, by rw [e.apply_symm_apply]; exact hi⟩
  obtain ⟨G, η, ε, _⟩ := clopen_ringed_module_gluing.{t, max u (t + 1), u, 0,
    max u (t + 1), max u (t + 1), 0, 0}
    X (Fin n) (fun i ↦ Y (e i)) (fun i ↦ j (e i)) hde hce S
    (by intro U a b; exact @mul_comm (R.obj.obj U) inferInstance a b)
  let E₀ := CategoryTheory.Equivalence.mk _ G η ε
  let T := Pi.equivalenceOfEquiv (fun i ↦ Modules.{t, u} ((rings (j i)).obj R)) e
  let r := Functor.pi' (fun i ↦ restriction (j i) R)
  let h : (E₀.trans T).functor ≅ r :=
    Functor.associator r T.inverse T.functor ≪≫
      Functor.isoWhiskerLeft r T.counitIso ≪≫ Functor.rightUnitor r
  exact ⟨(E₀.trans T).changeFunctor h, rfl⟩

private theorem emptyDerived (X : Scheme.{t}) [IsEmpty X]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Nonempty (DerivedCategory (Modules.{t, u} R) ≌ Discrete PUnit) := by
  classical
  obtain ⟨E, he⟩ := moduleGluing X PEmpty.{1} (fun i ↦ PEmpty.elim i)
    (fun i ↦ PEmpty.elim i) (by intro i; exact PEmpty.elim i)
    (fun x ↦ isEmptyElim x) R
  have hz (M : Modules.{t, u} R) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply E.functor.map_injective
    funext i
    exact PEmpty.elim i
  have hD (K : DerivedCategory (Modules.{t, u} R)) : IsZero K :=
    (DerivedCategory.isZero_iff K).mpr (fun n ↦ hz _)
  apply (equiv_punit_iff_unique _).mpr
  exact ⟨⟨HasZeroObject.zero.choose⟩,
    fun K L ↦ ⟨{ default := 0, uniq := fun f ↦ (hD K).eq_of_src f 0 }⟩⟩

/-- The unbounded derived equivalence, insertion identities, cohomology and detection.
Source: Stacks 015F, 05RU and finite-product localization
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 1-3 and 12): apply the exact module equivalence and its sectionwise
product inverse degreewise, including differentials and homotopies. Cohomology commutes
with exact restriction, so quasi-isomorphisms are detected componentwise. The finite
product of the localization functors is a localization at the component quasi-isomorphisms;
descend the inverse through it. Descend the module unit, counit and triangle equations
using the faithful natural-transformation clause of localization. Cone matrices and
shifts commute with the additive exact functors, proving triangulatedness. Zero insertion
and its projection identities descend the same way; their finite bilimit bicone has
vertex the identity. Thus the inverse is naturally the finite sum of inserted components.
The equivalence detects zero objects and isomorphisms. An empty site has only zero
modules, hence zero complexes and a terminal derived category. For an empty partition
the covering condition forces the scheme empty. No nonempty-index hypothesis is used. -/
theorem finite_clopen_derived_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∃ E : DerivedCategory (Modules.{t, u} R) ≌
        (∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R))),
      E.functor = Functor.pi' (fun i ↦ derivedRestriction (j i) R) ∧
      (∀ i, (derivedRestriction.{t, u} (j i) R).IsTriangulated) ∧
      (∀ i (m : ℤ), Nonempty
        (derivedRestriction (j i) R ⋙ DerivedCategory.homologyFunctor _ m ≅
          DerivedCategory.homologyFunctor _ m ⋙ restriction (j i) R)) ∧
      (∀ K : DerivedCategory (Modules.{t, u} R),
        IsZero K ↔ ∀ i, IsZero ((derivedRestriction.{t, u} (j i) R).obj K)) ∧
      (∀ (K L : DerivedCategory (Modules.{t, u} R)) (f : K ⟶ L),
        IsIso f ↔ ∀ i, IsIso ((derivedRestriction.{t, u} (j i) R).map f)) ∧
      (∃ e : ∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ⥤
          DerivedCategory (Modules.{t, u} R),
        (∀ i, Nonempty (e i ⋙ derivedRestriction (j i) R ≅ 𝟭 _)) ∧
        (∀ i k, i ≠ k → ∀ K, IsZero ((e k ⋙ derivedRestriction (j i) R).obj K)) ∧
        (∃ s : ∀ i, DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ⥤
            (∀ k, DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))),
          ∀ i, e i = s i ⋙ E.inverse ∧
            Nonempty (s i ⋙ Pi.eval
              (fun k ↦ DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))) i ≅ 𝟭 _) ∧
            (∀ k, k ≠ i → ∀ K, IsZero ((s i).obj K k))) ∧
        (∃ b : Bicone (fun i ↦ derivedRestriction (j i) R ⋙ e i),
          b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
        (∃ b : Bicone (fun i ↦ Pi.eval
            (fun k ↦ DerivedCategory (Modules.{t, u} ((rings (j k)).obj R))) i ⋙ e i),
          b.pt = E.inverse ∧ Nonempty b.IsBilimit)) ∧
      (∀ i, IsEmpty (Y i) → Nonempty
        (DerivedCategory (Modules.{t, u} ((rings.{t, u} (j i)).obj R)) ≌ Discrete PUnit)) ∧
      (IsEmpty I → IsEmpty X ∧ Nonempty
        (DerivedCategory (Modules.{t, u} R) ≌ Discrete PUnit)) := by
  classical
  obtain ⟨E₀, hE₀⟩ := moduleGluing X I Y j hdisjoint hcover R
  have hA : E₀.functor.Additive := by
    constructor
    intro M N f g
    rw [hE₀]
    funext i
    exact (restriction (j i) R).map_add
  let := hA
  have hr : JointlyReflectIsomorphisms (fun i ↦ restriction (j i) R) := by
    constructor
    intro M N f hf
    have : IsIso (E₀.functor.map f) := by
      rw [hE₀]
      exact (isIso_pi_iff _).mpr hf
    exact isIso_of_reflects_iso f E₀.functor
  have hD := derivedPi_isEquivalence (fun i ↦ restriction (j i) R) E₀.inverse
    (fun M N ↦ E₀.inverse.map_zero M N)
    (by simpa only [hE₀] using E₀.unitIso)
    (by simpa only [hE₀] using E₀.counitIso) hr
  let := hD
  let rd := Functor.pi' (fun i ↦ derivedRestriction (j i) R)
  let E := rd.asEquivalence
  have hd := Functor.jointlyReflectIsomorphisms_mapDerivedCategory hr
  have : E.functor.Additive := by
    constructor
    intro M N f g
    funext i
    exact (derivedRestriction (j i) R).map_add
  obtain ⟨e, he, hz, hs, hb, hc⟩ := equivalenceCoordinateDecomposition
    (fun i ↦ DerivedCategory (Modules.{t, u} ((rings (j i)).obj R))) E
  refine ⟨E, rfl, (fun _ ↦ inferInstance), ?_, (fun _ ↦ hd.isZero_iff), ?_, ?_, ?_, ?_⟩
  · intro i n
    exact ⟨((restriction (j i) R).mapDerivedCategoryHomologyFunctorIso n).symm⟩
  · intro K L f
    exact hd.isIso_iff f
  · exact ⟨e, he, hz, hs, hb, hc⟩
  · intro i hi
    let := hi
    exact emptyDerived (Y i) _
  · intro hi
    have hX : IsEmpty X := ⟨fun x ↦ hi.false (hcover x).choose⟩
    let := hX
    exact ⟨hX, emptyDerived X R⟩

/-- Ordinary and total tensor comparisons, flatness and K-flatness, and the normalized
symmetric monoidal derived restriction. Each `Braided` structure contains invertible
tensorators and unit comparison, their naturality, associativity, both unit diagrams,
and the symmetry diagram; the tensor products are the existing ones on both sides.
Source: Stacks 0GMW, 06YN, 06YS, 0G7D, 06YU and 0FPT
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 4-9): the bilinear universal property constructs the restriction
tensorator. Its inverse is obtained by gluing the component bilinear maps. Both
composites fix pure tensors, so they are identities. Reassociation, exchange and unit
multiplication agree on generators. Restriction is left adjoint to zero insertion,
hence preserves the sums over p+q=n. Apply the tensorator on each summand: both
differentials send x tensor y to dx tensor y + (-1)^p x tensor dy. This gives the natural
chain isomorphism below. Test exact tensoring first by restriction and then by exact
zero insertion to obtain both directions of flatness. Test K-flatness against arbitrary
acyclic complexes, using restriction in one direction and insertion in the other.
Choose flat-term K-flat resolutions. Their restrictions are again such resolutions.
The K-flat localization equivalence and its unique natural-transformation extension
clause descend the chain tensorator and its inverse to all derived morphisms. The
representative square below fixes this descent to the native K-flat tensor models.
Associativity, units and Koszul symmetry descend because their diagrams agree on pure
triple tensors and degree (p,q) generators, with the same sign (-1)^(pq). Empty and zero
categories have unique maps and satisfy all these formulas. -/
theorem finite_clopen_tensor_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ F : Modules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          ((restriction.{t, u} (j i) R).obj F)) ∧
    (∀ P : CochainComplex (Modules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    ∀ i, ∃ (h : (restriction.{t, u} (j i) R).Braided)
      (c : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          (restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ) ≅
        (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).prod
          ((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ))) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R))
      (d : (derivedRestriction.{t, u} (j i) R).Braided),
      (∀ (F H : Modules.{t, u} R) (U : (Y i).ProEt) (x : F.val.obj
          (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((tensorComparison (j i) R h F H).hom.val.app (op U))
          (pure R F H _ x y) =
        pure ((rings.{t, u} (j i)).obj R) ((restriction.{t, u} (j i) R).obj F)
          ((restriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ) (p q n : ℤ) (hpq : p + q = n)
        (U : (Y i).ProEt)
        (x : (P.X p).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (((c.hom.app (P, Q)).f n).val.app (op U))
          (coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq _ x y) =
        coefficientTensorGenerator.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
          p q n hpq (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
        (hiP : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P))
        (_hiQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)),
        (derivedRestriction.{t, u} (j i) R).map
            (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology X) R P Q
              (Or.inl hP)).hom ≫
          (derivedTensorComparison (j i) R d (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj Q)).hom ≫
          ((restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app Q) =
        (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app
            ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
          DerivedCategory.Q.map (c.hom.app (P, Q)) ≫
          (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology (Y i))
            ((rings.{t, u} (j i)).obj R)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
            (Or.inl hiP)).hom) := by
  sorry

open SheafOfModules.SuccessiveDerivedQuotient

/-- The already defined universal coefficient-extension presentations on this site.
Source: Stacks 06YY (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev Presentations (X : Scheme.{t}) :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    Presentation.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (J := topology X) a

/-- Apply the existing normalized scalar compositor to the restricted ring maps.
The final equality transport is only functoriality of ring restriction.
Source: Stacks 0D6D (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def scalarComposite {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} Y) (N : Normalization (J := topology Y) p)
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) (b : S ⟶ T) :
    (p ((rings.{t, u} j).map a)).derived ⋙ (p ((rings.{t, u} j).map b)).derived ≅
      (p ((rings.{t, u} j).map (a ≫ b))).derived :=
  N.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b) ≪≫
    eqToIso (congrArg (fun f ↦ (p f).derived) ((rings.{t, u} j).map_comp a b).symm)

/-- Lift an ordinary coefficient/restriction comparison degreewise to homotopy categories.
Source: Stacks 015F and 06YY (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def scalarHomotopyComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y)
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (c : (p a).ordinary ⋙ restriction.{t, u} j S ≅
      restriction.{t, u} j R ⋙ (q ((rings.{t, u} j).map a)).ordinary) :
    (p a).ordinary.mapHomotopyCategory (.up ℤ) ⋙
        (restriction.{t, u} j S).mapHomotopyCategory (.up ℤ) ≅
      (restriction.{t, u} j R).mapHomotopyCategory (.up ℤ) ⋙
        (q ((rings.{t, u} j).map a)).ordinary.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso c (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- Coefficient extension is identified componentwise as an S_i-linear natural
isomorphism, with its canonical K-flat normalization and compatibility with composites.
The conclusion quantifies over arbitrary presentations of the existing universal
left-derived functors and their normalized compositors; their existence is the recorded
successive-derived-quotient theorem. Thus no scalar-extension data is assumed beyond
what those dependency theorems already construct.

Source: Stacks 06YT, 06YY, 0G7D, 05V4 and 0D6D
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 10-12): on a K-flat flat-term representative P, ordinary extension
computes derived extension by lem-pur-derived-change-of-rings. Restriction commutes with
ordinary extension by the sheafified formula p tensor s maps to r(p) tensor r(s);
in the scalar-first convention this is s tensor p. The restricted complex is K-flat
with flat terms by the tensor calculus. Descend this natural chain isomorphism and its
inverse along the K-flat localization equivalence. The universal counits give exactly
the representative square below; uniqueness extends it to every derived morphism.
For R to S to T, tensor cancellation shows P tensor_R S is still flat-term K-flat.
The existing normalized compositor is represented by (p tensor s) tensor t mapping
to p tensor psi(s)t. Restricting before or after this formula gives the same section;
descent proves the displayed composition square. Identity maps are included, with the
unit formula p tensor a mapping to a p. No flatness of the ring maps is needed. Thus
finite quotient reductions and every completed-to-finite projection are special cases,
using the coefficient identifications of the module-gluing node. For empty and zero
components every comparison is the unique morphism, and the same formulas apply. -/
theorem finite_clopen_scalar_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)) :
    ∀ (p : Presentations.{t, u} X) (N : Normalization (J := topology X) p)
      (q : ∀ i, Presentations.{t, u} (Y i)) (Ni : ∀ i, Normalization (J := topology (Y i)) (q i)),
    ∃ (c : ∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
        (p a).ordinary ⋙ restriction.{t, u} (j i) S ≅
          restriction.{t, u} (j i) R ⋙ (q i ((rings.{t, u} (j i)).map a)).ordinary)
      (γ : ∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
        (p a).derived ⋙ derivedRestriction.{t, u} (j i) S ≅
          derivedRestriction.{t, u} (j i) R ⋙ (q i ((rings.{t, u} (j i)).map a)).derived),
      (∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (M : Modules.{t, u} R) (U : (Y i).ProEt)
        (s : S.obj.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (x : M.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((c i a).hom.app M).val.app (op U)
          (sectionTensor (p a) M _ s x) =
        sectionTensor (q i ((rings.{t, u} (j i)).map a))
          ((restriction.{t, u} (j i) R).obj M) (op U) s x) ∧
      (∀ i {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (P : CochainComplex (Modules.{t, u} R) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (P.X n)),
        (derivedRestriction.{t, u} (j i) S).map
            ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (restriction.{t, u} (j i) S).mapDerivedCategoryFactorsh.hom.app
            (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          DerivedCategory.Qh.map
            ((scalarHomotopyComparison (j i) p (q i) a (c i a)).hom.app
              ((HomotopyCategory.quotient _ _).obj P)) =
        (γ i a).hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q i ((rings.{t, u} (j i)).map a)).derived.map
            ((restriction.{t, u} (j i) R).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q i ((rings.{t, u} (j i)).map a)).counit.app
            (((restriction.{t, u} (j i) R).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P))) ∧
      (∀ i {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
        (a : R ⟶ S) (b : S ⟶ T) (K : DerivedCategory (Modules.{t, u} R)),
        (derivedRestriction.{t, u} (j i) T).map ((N.derived a b).hom.app K) ≫
          (γ i (a ≫ b)).hom.app K =
        (γ i b).hom.app ((p a).derived.obj K) ≫
          (q i ((rings.{t, u} (j i)).map b)).derived.map ((γ i a).hom.app K) ≫
          (scalarComposite (j i) (q i) (Ni i) a b).hom.app
            ((derivedRestriction.{t, u} (j i) R).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor
