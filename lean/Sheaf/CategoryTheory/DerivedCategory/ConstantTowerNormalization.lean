/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.DiagramKFlatReplacements
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Category.ULift

/-!
# The representative normalization of the derived constant-tower comparison

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The auxiliary maps below merely spell out the canonical localization identifications.
Strict towers are indexed by `ℕᵒᵖ`, with level `n` representing the paper's level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB u


open CategoryTheory CategoryTheory.Limits

-- Avoid expanding covering multicospans when forgetting commutative ring structures.
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl


-- Computation on a resolving class is invariant under the chosen universal pair.
private theorem counit_iso_on_resolving
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (E : A ⥤ B) [E.Additive] (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (s : P ⟶ K), p P ∧ QuasiIso s)
    (hinv : ∀ {P Q : CochainComplex A ℤ} (s : P ⟶ Q),
      p P → p Q → QuasiIso s → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s))
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (K : CochainComplex A ℤ) (hK : p K) : IsIso (ε.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, p K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X), Y ∈ P ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := res K
    exact ⟨q.obj Y, q.map s, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hmap : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → W s → IsIso (F.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨N, hN, rfl⟩ hs
    obtain ⟨s, rfl⟩ := q.map_surjective s
    have hs := hinv s hK hN ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs)
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map s)))
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hs)
  obtain ⟨hpw, D, δ, hD, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hmap
  let : F.HasPointwiseLeftDerivedFunctor W := hpw
  let : D.IsLeftDerivedFunctor δ W := hD
  let α := (Functor.associator q DerivedCategory.Qh D).hom ≫ Functor.whiskerLeft q δ
  have hα := pointwise_precomp_full q DerivedCategory.Qh F D δ
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor D δ W)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ D ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv D ≫ α ≫ j.hom
  have hβ := pointwise_change_iso D i j α hα
  let : D.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  have := hcomp (q.obj K) ⟨K, hK, rfl⟩
  have : IsIso (β.app K) := by dsimp [β, α]; infer_instance
  let e := Functor.leftDerivedUnique L D β ε (HomologicalComplex.quasiIso A (.up ℤ))
  have he : e.hom.app (DerivedCategory.Q.obj K) ≫ ε.app K = β.app K := by
    simp [e]
  have : IsIso (e.hom.app (DerivedCategory.Q.obj K) ≫ ε.app K) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Q.obj K)) (ε.app K)


-- Extend the quotient of two invertible counits, then use resolutions for uniqueness.
private theorem comparison_from_resolutions
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uB} [Category.{vB} D]
    (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (s : P ⟶ K), p P ∧ QuasiIso s)
    (U V : DerivedCategory A ⥤ D) (H : CochainComplex A ℤ ⥤ D)
    (η : DerivedCategory.Q ⋙ U ⟶ H) (θ : DerivedCategory.Q ⋙ V ⟶ H)
    (hη : ∀ P, p P → IsIso (η.app P)) (hθ : ∀ P, p P → IsIso (θ.app P)) :
    ∃! b : U ≅ V, ∀ P, p P → b.hom.app (DerivedCategory.Q.obj P) ≫ θ.app P =
      η.app P := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let i := DerivedCategory.quotientCompQhIso A
  let η' : q ⋙ (Q ⋙ U) ⟶ H := Functor.whiskerRight i.hom U ≫ η
  let θ' : q ⋙ (Q ⋙ V) ⟶ H := Functor.whiskerRight i.hom V ≫ θ
  have hη' (K : CochainComplex A ℤ) (hK : p K) : IsIso (η'.app K) := by
    have := hη K hK
    dsimp [η']
    infer_instance
  have hθ' (K : CochainComplex A ℤ) (hK : p K) : IsIso (θ'.app K) := by
    have := hθ K hK
    dsimp [θ']
    infer_instance
  let P : HomotopyCategory A (.up ℤ) → Prop := fun X ↦ p X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X), P Y ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨N, s, hN, hs⟩ := res K
    exact ⟨q.obj N, q.map s, hN,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let α (X : HomotopyCategory A (.up ℤ)) (hX : P X) :
      (Q ⋙ U).obj X ⟶ (Q ⋙ V).obj X :=
    letI := hθ' X.as hX
    η'.app X.as ≫ inv (θ'.app X.as)
  have hα : ∀ (X Y : HomotopyCategory A (.up ℤ)) (hX : P X) (hY : P Y) (s : X ⟶ Y),
      (Q ⋙ U).map s ≫ α Y hY = α X hX ≫ (Q ⋙ V).map s := by
    intro X Y hX hY s
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have := hθ' K hX
    have := hθ' N hY
    change (q ⋙ Q ⋙ U).map f ≫ (η'.app N ≫ inv (θ'.app N)) =
      (η'.app K ≫ inv (θ'.app K)) ≫ (q ⋙ Q ⋙ V).map f
    apply (cancel_mono (θ'.app N)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [θ'.naturality f]
    simp only [IsIso.inv_hom_id_assoc]
    exact η'.naturality f
  have hU : W.IsInvertedBy (Q ⋙ U) := by
    intro X Y s hs
    have := Localization.inverts Q W s hs
    exact U.map_isIso (Q.map s)
  obtain ⟨γ, hγ⟩ := exists_natTrans_from_resolvingClass W P hres (Q ⋙ U) (Q ⋙ V) hU α hα
  have hγiso (X : HomotopyCategory A (.up ℤ)) : IsIso (γ.app X) := by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    have := Localization.inverts Q W s hs
    have : IsIso ((Q ⋙ U).map s) := hU s hs
    have : IsIso ((Q ⋙ V).map s) := V.map_isIso (Q.map s)
    have := hη' Y.as hY
    have := hθ' Y.as hY
    have : IsIso (γ.app Y) := by rw [hγ Y hY]; dsimp [α]; infer_instance
    have he : γ.app X = inv ((Q ⋙ U).map s) ≫ γ.app Y ≫ (Q ⋙ V).map s := by
      rw [← γ.naturality s]
      simp
    rw [he]
    infer_instance
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  let b : U ≅ V := Localization.liftNatIso Q W (Q ⋙ U) (Q ⋙ V) U V (asIso γ)
  have hb (X : HomotopyCategory A (.up ℤ)) : b.hom.app (Q.obj X) = γ.app X := by
    simp [b]
  have hnorm (K : CochainComplex A ℤ) (hK : p K) :
      b.hom.app (DerivedCategory.Q.obj K) ≫ θ.app K = η.app K := by
    have := hθ' K hK
    apply (cancel_epi (U.map (i.hom.app K))).1
    rw [← Category.assoc, b.hom.naturality (i.hom.app K), Category.assoc]
    change b.hom.app (Q.obj (q.obj K)) ≫ θ'.app K = η'.app K
    rw [hb, hγ (q.obj K) hK]
    change (η'.app K ≫ inv (θ'.app K)) ≫ θ'.app K = η'.app K
    simp
  refine ⟨b, hnorm, ?_⟩
  intro c hc
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  obtain ⟨N, s, hN, hs⟩ := res K
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) := inferInstance
  have he : c.hom.app (DerivedCategory.Q.obj N) = b.hom.app (DerivedCategory.Q.obj N) := by
    have := hθ N hN
    apply (cancel_mono (θ.app N)).1
    rw [hc N hN, hnorm N hN]
  apply (cancel_epi (U.map (DerivedCategory.Q.map s))).1
  rw [c.hom.naturality, b.hom.naturality, he]


-- The inverse of Mathlib's transpose on complexes of functors.
private def diagramComplex
    {A I : Type*} [Category A] [HasZeroMorphisms A] [Category I]
    (M : I ⥤ CochainComplex A ℤ) : CochainComplex (I ⥤ A) ℤ where
  X n := M ⋙ HomologicalComplex.eval A (.up ℤ) n
  d n m :=
    { app := fun j ↦ (M.obj j).d n m
      naturality := fun j k a ↦ (M.map a).comm n m }
  shape n m h := by ext j; exact (M.obj j).shape n m h
  d_comp_d' n m k _ _ := by ext j; exact (M.obj j).d_comp_d n m k

private def diagramAugmentation
    {A I : Type*} [Category A] [HasZeroMorphisms A] [Category I]
    {M : I ⥤ CochainComplex A ℤ} {K : CochainComplex (I ⥤ A) ℤ}
    (p : M ⟶ K.asFunctor) : diagramComplex M ⟶ K where
  f n :=
    { app := fun j ↦ (p.app j).f n
      naturality := fun j k a ↦ congrArg (fun g ↦ g.f n) (p.naturality a) }
  comm' n m _ := by ext j; exact (p.app j).comm n m


private def ringedResolvingClass
    {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{u})
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) : Prop :=
  CochainComplex.IsAcyclicTensorKFlat (R := R) P ∧
    ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)

private theorem ringed_resolution
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    (R : Sheaf T CommRingCat.{u})
    (K : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ P, ∃ s : P ⟶ K, ringedResolvingClass R P ∧ QuasiIso s := by
  obtain ⟨P, s, hk, hf, hs, _⟩ := CochainComplex.exists_diagram_isKFlatResolution T R
    ((Functor.const (Discrete PUnit.{u + 1})).obj K)
  exact ⟨P.obj ⟨PUnit.unit⟩, s.app ⟨PUnit.unit⟩,
    ⟨hk ⟨PUnit.unit⟩, hf ⟨PUnit.unit⟩⟩, hs ⟨PUnit.unit⟩⟩

private theorem ringed_tower_resolution
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    (R : Sheaf T CommRingCat.{u})
    (K : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ P, ∃ s : P ⟶ K,
      (∀ j : ℕᵒᵖ, ringedResolvingClass R (P.asFunctor.obj j)) ∧ QuasiIso s := by
  obtain ⟨P, s, hk, hf, hs, _⟩ := CochainComplex.exists_diagram_isKFlatResolution T R
    (AsSmall.down ⋙ K.asFunctor : AsSmall.{u} ℕᵒᵖ ⥤ _)
  let N := AsSmall.up ⋙ P
  let t : N ⟶ K.asFunctor := Functor.whiskerLeft AsSmall.up s
  let a := diagramAugmentation t
  refine ⟨diagramComplex N, a, ?_, ?_⟩
  · intro j
    exact ⟨hk (AsSmall.up.obj j), hf (AsSmall.up.obj j)⟩
  · apply (HomologicalComplex.quasiIso_iff_evaluation a).2
    intro j
    exact hs (AsSmall.up.obj j)

private theorem ringed_pullback_inverts
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (T' : GrothendieckTopology D)
    (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
    (f : CategoryTheory.RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    {P Q : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ} (s : P ⟶ Q)
    (hP : ringedResolvingClass R P) (hQ : ringedResolvingClass R Q) (hs : QuasiIso s) :
    QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s) := by
  exact CochainComplex.diagram_pullback_quasiIso T T' R S f E adj
    ((Functor.const (Discrete PUnit.{u + 1})).map s)
    (fun _ ↦ hP.1) (fun _ ↦ hQ.1) (fun _ ↦ hP.2) (fun _ ↦ hQ.2)
    (fun _ ↦ hs) ⟨PUnit.unit⟩

private theorem ringed_tower_pullback_inverts
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (T' : GrothendieckTopology D)
    (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
    (f : CategoryTheory.RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    {P Q : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ} (s : P ⟶ Q)
    (hP : ∀ j : ℕᵒᵖ, ringedResolvingClass R (P.asFunctor.obj j))
    (hQ : ∀ j : ℕᵒᵖ, ringedResolvingClass R (Q.asFunctor.obj j)) (hs : QuasiIso s) :
    QuasiIso ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj E).mapHomologicalComplex (.up ℤ)).map s) := by
  let a := (HomologicalComplex.complexOfFunctorsToFunctorToComplex).map s
  have hh := CochainComplex.diagram_pullback_quasiIso T T' R S f E adj
    (Functor.whiskerLeft (AsSmall.down : AsSmall.{u} ℕᵒᵖ ⥤ ℕᵒᵖ) a)
    (fun j ↦ (hP (AsSmall.down.obj j)).1) (fun j ↦ (hQ (AsSmall.down.obj j)).1)
    (fun j ↦ (hP (AsSmall.down.obj j)).2) (fun j ↦ (hQ (AsSmall.down.obj j)).2)
    (fun j ↦ (HomologicalComplex.quasiIso_iff_evaluation s).1 hs (AsSmall.down.obj j))
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro j
  exact hh (AsSmall.up.obj j)

namespace CategoryTheory.Functor

section Identifications

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (E : A ⥤ B) [E.Additive]

/-- Termwise pullback of a constant complex is the constant complex of its pullback.
Source: the constant-tower subargument, Step 1; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This is `compConstIso` applied to complexes, not an independently chosen comparison. -/
def constantTowerComplexComparison :
    E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (compConstIso ℕᵒᵖ E) (ComplexShape.up ℤ)

/-- The constant tower of the chosen ordinary counit, transported to strict tower complexes.
Source: the constant-tower subargument, Steps 1--2; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
The factors are associators, exact constant-functor localization, and the termwise comparison. -/
def constantTowerDerivedSourceCounit
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (L ⋙ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory) ⟶
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  (associator _ _ _).inv ≫
    whiskerRight ε _ ≫ (associator _ _ _).hom ≫
    whiskerLeft _ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategoryFactors.hom ≫
    (associator _ _ _).inv ≫
    whiskerRight (constantTowerComplexComparison E).hom DerivedCategory.Q ≫
    (associator _ _ _).hom

/-- The chosen tower counit at a constant representative, with its source localized.
Source: the constant-tower subargument, Steps 1--2; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
Only the canonical factorization of the exact constant functor is inserted. -/
def constantTowerDerivedTargetCounit
    (L : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ L ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) :
    DerivedCategory.Q ⋙ ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ L) ⟶
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  (associator _ _ _).inv ≫
    whiskerRight (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom L ≫
    (associator _ _ _).hom ≫
    whiskerLeft ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)) τ


omit [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] in
private theorem constantTowerDerivedSourceCounit_isIso
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex A ℤ) [IsIso (ε.app P)] :
    IsIso ((constantTowerDerivedSourceCounit E L ε).app P) := by
  dsimp [constantTowerDerivedSourceCounit]
  infer_instance

omit [HasDerivedCategory.{wB} B] in
private theorem constantTowerDerivedTargetCounit_isIso
    (L : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ L ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex A ℤ)
    [IsIso (τ.app (((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).obj P))] :
    IsIso ((constantTowerDerivedTargetCounit E L τ).app P) := by
  dsimp [constantTowerDerivedTargetCounit]
  infer_instance

/-- The type of comparison isomorphisms between the two canonical derived tower functors.
Source: the constant-tower subargument, Step 1; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This transparent type uses the exact constant functors, with no chosen comparison. -/
def ConstantTowerDerivedComparison
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)) :=
  L ⋙ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ≅
    (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ Lt

/-- The representative counit equation and its inverse formula, with canonical transports.
Source: the constant-tower subargument, Steps 2 and 5; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This transparent predicate packages parallel arrows; it supplies no comparison data. -/
def IsConstantTowerRepresentativeNormalized
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (b : ConstantTowerDerivedComparison L Lt)
    (P : CochainComplex A ℤ) : Prop :=
  b.hom.app (DerivedCategory.Q.obj P) ≫
      (constantTowerDerivedTargetCounit E Lt τ).app P =
    (constantTowerDerivedSourceCounit E L ε).app P ∧
  ∃ t : ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ Lt).obj
        (DerivedCategory.Q.obj P) ≅
      (((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)).obj P,
    t.hom = (constantTowerDerivedTargetCounit E Lt τ).app P ∧
    b.hom.app (DerivedCategory.Q.obj P) =
      (constantTowerDerivedSourceCounit E L ε).app P ≫ t.inv

/-- Unique comparison normalized on a specified representative class.
Source: Stacks Tag 06XN and the constant-tower subargument, Steps 2--6
(blueprint: lem-cbc-derived-constant-tower-normalization).
This is the explicit existence-and-uniqueness quantifier over the comparison type,
with no additional hypothesis or data. Packaging it avoids repeating concrete
module-sheaf instance comparisons when the representative equation is specialized. -/
def HasUniqueConstantTowerNormalizedComparison
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (W : CochainComplex A ℤ → Prop) : Prop :=
  ∃! b : ConstantTowerDerivedComparison L Lt,
    ∀ P : CochainComplex A ℤ, W P →
      IsConstantTowerRepresentativeNormalized E L ε Lt τ b P


private theorem constantTowerComparison_of_resolving
    (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (s : P ⟶ K), p P ∧ QuasiIso s)
    (hinv : ∀ {P Q : CochainComplex A ℤ} (s : P ⟶ Q),
      p P → p Q → QuasiIso s → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map s))
    (pt : CochainComplex (ℕᵒᵖ ⥤ A) ℤ → Prop)
    (rest : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (s : P ⟶ K), pt P ∧ QuasiIso s)
    (hinvt : ∀ {P Q : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (s : P ⟶ Q),
      pt P → pt Q → QuasiIso s →
        QuasiIso ((((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (.up ℤ)).map s))
    (hconst : ∀ P : CochainComplex A ℤ, p P →
      pt (((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).obj P))
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [Lt.IsLeftDerivedFunctor τ (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))] :
    HasUniqueConstantTowerNormalizedComparison E L ε Lt τ p := by
  let Et := (whiskeringRight ℕᵒᵖ A B).obj E
  have hε (P : CochainComplex A ℤ) (hP : p P) : IsIso (ε.app P) :=
    counit_iso_on_resolving E p res hinv L ε P hP
  have hτ (P : CochainComplex A ℤ) (hP : p P) :
      IsIso (τ.app (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj P)) :=
    counit_iso_on_resolving Et pt rest hinvt Lt τ _ (hconst P hP)
  let η := Functor.constantTowerDerivedSourceCounit E L ε
  let θ := Functor.constantTowerDerivedTargetCounit E Lt τ
  have hη (P : CochainComplex A ℤ) (hP : p P) : IsIso (η.app P) := by
    have := hε P hP
    exact Functor.constantTowerDerivedSourceCounit_isIso E L ε P
  have hθ (P : CochainComplex A ℤ) (hP : p P) : IsIso (θ.app P) := by
    have := hτ P hP
    exact Functor.constantTowerDerivedTargetCounit_isIso E Lt τ P
  obtain ⟨b, hb, huniq⟩ := comparison_from_resolutions p res
    (L ⋙ (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory)
    ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ Lt) _ η θ hη hθ
  refine ⟨b, ?_, ?_⟩
  · intro P hP
    have := hθ P hP
    refine ⟨hb P hP, asIso (θ.app P), rfl, ?_⟩
    exact (IsIso.eq_comp_inv (θ.app P)).2 (hb P hP)
  · intro c hc
    exact huniq c (fun P hP ↦ (hc P hP).1)


end Identifications

end CategoryTheory.Functor

namespace CategoryTheory.RingedToposMorphism

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {T : GrothendieckTopology C} {T' : GrothendieckTopology D}
  (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
  [HasDerivedCategory.{wA}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wB}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]

/-- The unique constant-tower comparison with its K-flat representative normalization.
Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The adjunction identifies `E` with inverse image followed by extension of scalars,
exactly as in `CochainComplex.diagram_pullback_quasiIso`. The two universal pairs are
arbitrary. The last existential packages the invertible transported tower counit;
its inverse gives precisely the displayed formula in the node.

Proof:
1. Towers are abelian levelwise, so the constant functors are exact. Use their
   `mapDerivedCategoryFactors` and `constantTowerComplexComparison` to identify the
   two representative targets (lem-weil-tower-category-levelwise-abelian and
   lem-weil-pbc-exact-functor-derived-factorization).
2. The diagram K-flat replacement theorem supplies resolutions, both for complexes
   and for strict towers, and pullback inverts quasi-isomorphisms in these classes.
   Apply `leftDerived_from_resolvingClass`; uniqueness of universal pairs transports
   its invertible counits to the chosen pairs. A constant K-flat flat-term complex
   belongs to the tower resolving class. Form the component by the inverse tower
   counit after the constant ordinary counit.
3. Counit naturality and cancellation of the tower counit prove naturality of these
   components on the full resolving class.
4. Use the right calculus of fractions and `exists_natTrans_from_resolvingClass`
   to extend to all complexes. For a resolution P → X, the extended component is
   conjugate to the component at P, so is invertible.
5. Lift the resulting natural isomorphism along localization (the liftNatIso clause
   of lem-weil-pbc-localization-universal-property). Its components satisfy the
   normalization, and cancellation gives the asserted inverse formula.
6. Any second normalized isomorphism agrees on resolving representatives, hence on
   all complexes by resolutions and naturality. Localization's `natTrans_ext` then
   gives equality on the derived category, proving uniqueness. -/
theorem existsUnique_derivedConstantTowerComparison
    (f : RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    (L : DerivedCategory (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Lt.IsLeftDerivedFunctor τ (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Functor.HasUniqueConstantTowerNormalizedComparison.{u + 1, u, u + 1, u,
        wA, wB, wTA, wTB}
      (A := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
      (B := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)) E L ε Lt τ
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) := by
  exact Functor.constantTowerComparison_of_resolving E (ringedResolvingClass R)
    (ringed_resolution T R) (ringed_pullback_inverts T T' R S f E adj)
    (fun P ↦ ∀ j : ℕᵒᵖ, ringedResolvingClass R (P.asFunctor.obj j))
    (ringed_tower_resolution T R) (ringed_tower_pullback_inverts T T' R S f E adj)
    (fun P hP _ ↦ hP) L ε Lt τ

end CategoryTheory.RingedToposMorphism
