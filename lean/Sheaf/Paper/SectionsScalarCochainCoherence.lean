/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Cochain sections and scalar extension for compatible ring towers

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CZ and 03CY.
(blueprint: lem-weil-sections-scalar-cochain-coherence)

Scalar extension is sheafified sectionwise tensor. The existence statement fixes its
objects and maps, and fixes every comparison by its values on pure tensors. No data
is chosen from this theorem. Mathlib puts the scalar factor first in scalar extension;
thus its `a ⊗ n` denotes the statement's `n ⊗ a`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe uC vC r uD vD uE vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.SectionsScalarCochain

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]

/-- The dependency's module-sheaf category for a commutative ring sheaf.
Source: Stacks 03D7 (blueprint: lem-weil-sections-scalar-cochain-coherence). -/
abbrev modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Termwise application with additivity supplied explicitly, without a local instance
in the statement. Source: Stacks 03EK
(blueprint: lem-weil-sections-scalar-cochain-coherence). -/
abbrev onComplexes {D : Type uD} {E : Type uE} [Category.{vD} D] [Category.{vE} E] [Preadditive D]
    [Preadditive E] (F : D ⥤ E) (hF : F.Additive) :
    CochainComplex D ℤ ⥤ CochainComplex E ℤ :=
  letI := hF
  F.mapHomologicalComplex (.up ℤ)

/-- Evaluation at the terminal object, with scalars restricted through lambda.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-cochain-coherence). -/
abbrev sections (s : C) (R : Sheaf J CommRingCat.{r}) (A : CommRingCat.{r})
    (lam : A →+* R.obj.obj (op s)) : modules R ⥤ ModuleCat.{r} A :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op s) ⋙
    ModuleCat.restrictScalars lam

/-- Termwise sections of unbounded cochains.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-cochain-coherence). -/
abbrev G (s : C) (R : Sheaf J CommRingCat.{r}) (A : CommRingCat.{r})
    (lam : A →+* R.obj.obj (op s)) :=
  (sections s R A lam).mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary scalar extension; the scalar is the first tensor factor.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-cochain-coherence). -/
abbrev t {A B : CommRingCat.{r}} (f : A ⟶ B) :=
  (ModuleCat.extendScalars f.hom).mapHomologicalComplex (.up ℤ)

/-- A pure tensor in ordinary scalar extension, with the module action fixed before
elaborating the coefficient; this includes the identity ring map.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-cochain-coherence). -/
def ordinaryPure {A B : CommRingCat.{r}} (f : A ⟶ B)
    (N : ModuleCat.{r} A) (b : B) (n : N) : (ModuleCat.extendScalars f.hom).obj N :=
  b ⊗ₜ[A,f.hom] n

/-- The actual sheafification-unit pure tensor, transported only across the specified
object equality of the scalar-extension functor. No arbitrary pairing is supplied.
Source: Stacks 03EK, 03CY
(blueprint: lem-weil-sections-scalar-cochain-coherence). -/
def pure {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (E : modules R ⥤ modules S) (e : ∀ M, E.obj M = SheafOfModules.changeOfRings f M)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    (E.obj M).val.obj W :=
  Eq.ndrec (motive := fun N : modules S ↦ (N.val.obj W : Type r))
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf f M).presheaf).app W
      (a ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)) (e M).symm

private theorem cochain_triple_value (s : C)
    (R : Fin 4 ⥤ Sheaf J CommRingCat.{r}) (A : Fin 4 ⥤ CommRingCat.{r})
    (lam : ∀ i, A.obj i →+* (R.obj i).obj.obj (op s))
    (E : ∀ {i j : Fin 4}, (i ⟶ j) → modules (R.obj i) ⥤ modules (R.obj j))
    (e : ∀ {i j : Fin 4} (f : i ⟶ j) M,
      (E f).obj M = SheafOfModules.changeOfRings (R.map f) M)
    (add : ∀ {i j : Fin 4} (f : i ⟶ j), (E f).Additive)
    (theta : ∀ {i j : Fin 4} (f : i ⟶ j),
      G s (R.obj i) (A.obj i) (lam i) ⋙ t.{r, r} (A.map f) ⟶
      onComplexes (E f) (add f) ⋙ G s (R.obj j) (A.obj j) (lam j))
    (a : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
      t.{r, r} (A.map f) ⋙ t.{r, r} (A.map g) ≅ t.{r, r} (A.map (f ≫ g)))
    (htheta : ∀ {i j : Fin 4} (f : i ⟶ j)
      (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ)
      (n : (K.X q).val.obj (op s)) (b : A.obj j),
      ((theta f).app K).f q (b ⊗ₜ[A.obj i,(A.map f).hom] n) =
        pure (R.map f) (E f) (e f) (K.X q) (op s) (lam j b) n)
    (hordinary : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
      (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ) (q : ℤ)
      (n : N.X q) (b : A.obj j) (c : A.obj k),
      ((a f g).hom.app N).f q
        (c ⊗ₜ[A.obj j,(A.map g).hom] (b ⊗ₜ[A.obj i,(A.map f).hom] n)) =
      (A.map g b * c) ⊗ₜ[A.obj i,(A.map (f ≫ g)).hom] n)
    {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ)
    (n : (K.X q).val.obj (op s)) (b : A.obj j) (c : A.obj k) (d : A.obj l) :
    (((t.{r, r} (A.map h)).map
      ((a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ≫
      (a (f ≫ g) h).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K) ≫
      (theta ((f ≫ g) ≫ h)).app K).f q)
        (d ⊗ₜ[A.obj k,(A.map h).hom]
          (c ⊗ₜ[A.obj j,(A.map g).hom] (b ⊗ₜ[A.obj i,(A.map f).hom] n))) =
    pure (R.map ((f ≫ g) ≫ h)) (E ((f ≫ g) ≫ h)) (e ((f ≫ g) ≫ h))
      (K.X q) (op s) (lam l (A.map (g ≫ h) b * A.map h c * d)) n := by
  simp only [t, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ModuleCat.comp_apply]
  erw [ModuleCat.ExtendScalars.map_tmul, hordinary, hordinary, htheta]
  have he : A.map h (A.map g b * c) * d =
      A.map (g ≫ h) b * A.map h c * d := by
    rw [map_mul]
    exact congrArg (fun z ↦ z * A.map h c * d)
      (ConcreteCategory.congr_hom (A.map_comp g h) b).symm
  exact congrArg (fun z : A.obj l ↦
    pure (R.map ((f ≫ g) ≫ h)) (E ((f ≫ g) ≫ h)) (e ((f ≫ g) ≫ h))
      (K.X q) (op s) (lam l z) n) he

private theorem generic_routes
    (D : Fin 4 → Type uD) (H : Fin 4 → Type uE)
    [∀ i, Category.{vD} (D i)] [∀ i, Category.{vE} (H i)]
    (GG : ∀ i, D i ⥤ H i)
    (EE : ∀ {i j : Fin 4}, (i ⟶ j) → D i ⥤ D j)
    (TT : ∀ {i j : Fin 4}, (i ⟶ j) → H i ⥤ H j)
    (theta : ∀ {i j : Fin 4} (f : i ⟶ j),
          GG i ⋙ TT f ⟶
            EE f ⋙ GG j)
        (u : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
          EE f ⋙ EE g ≅
            EE (f ≫ g))
        (a : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
          TT f ⋙ TT g ≅ TT (f ≫ g))
    (hc : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
      (K : D i),
      (TT g).map ((theta f).app K) ≫
          (theta g).app ((EE f).obj K) ≫
          (GG k).map ((u f g).hom.app K) =
        (a f g).hom.app ((GG i).obj K) ≫
          (theta (f ≫ g)).app K)
    (hf : ∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
      (K : D i),
      (EE h).map ((u f g).hom.app K) ≫
          (u (f ≫ g) h).hom.app K =
        (u g h).hom.app ((EE f).obj K) ≫
          (u f (g ≫ h)).hom.app K)
    {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (K : D i)
    (v : _) (hv : v ∈ [(TT h).map ((TT g).map ((theta f).app K)) ≫
              (TT h).map
                ((theta g).app ((EE f).obj K)) ≫
              (theta h).app ((EE g).obj
                ((EE f).obj K)) ≫
              (GG l).map
                ((EE h).map ((u f g).hom.app K)) ≫
              (GG l).map ((u (f ≫ g) h).hom.app K),
            (TT h).map ((TT g).map ((theta f).app K)) ≫
              (TT h).map
                ((theta g).app ((EE f).obj K)) ≫
              (theta h).app ((EE g).obj
                ((EE f).obj K)) ≫
              (GG l).map
                ((u g h).hom.app ((EE f).obj K)) ≫
              (GG l).map ((u f (g ≫ h)).hom.app K),
            (TT h).map ((TT g).map ((theta f).app K)) ≫
              (a g h).hom.app ((GG j).obj
                ((EE f).obj K)) ≫
              (theta (g ≫ h)).app ((EE f).obj K) ≫
              (GG l).map ((u f (g ≫ h)).hom.app K),
            (TT h).map
                ((a f g).hom.app ((GG i).obj K)) ≫
              (TT h).map ((theta (f ≫ g)).app K) ≫
              (theta h).app ((EE (f ≫ g)).obj K) ≫
              (GG l).map ((u (f ≫ g) h).hom.app K),
            (TT h).map
                ((a f g).hom.app ((GG i).obj K)) ≫
              (a (f ≫ g) h).hom.app ((GG i).obj K) ≫
              (theta ((f ≫ g) ≫ h)).app K]) : v =
        (TT h).map
            ((a f g).hom.app ((GG i).obj K)) ≫
          (a (f ≫ g) h).hom.app ((GG i).obj K) ≫
          (theta ((f ≫ g) ≫ h)).app K := by
      have hbase :
          (TT h).map ((TT g).map ((theta f).app K)) ≫
            (TT h).map
              ((theta g).app ((EE f).obj K)) ≫
            (theta h).app ((EE g).obj
              ((EE f).obj K)) ≫
            (GG l).map
              ((EE h).map ((u f g).hom.app K)) ≫
            (GG l).map ((u (f ≫ g) h).hom.app K) =
          (TT h).map
            ((a f g).hom.app ((GG i).obj K)) ≫
          (a (f ≫ g) h).hom.app ((GG i).obj K) ≫
          (theta ((f ≫ g) ≫ h)).app K := by
        have hn := (theta h).naturality ((u f g).hom.app K)
        dsimp only [Functor.comp_obj, Functor.comp_map] at hn
        rw [← reassoc_of% hn]
        have hp := congrArg (fun z ↦ (TT h).map z) (hc f g K)
        simp only [Functor.map_comp] at hp
        calc
          _ = (TT h).map
                ((a f g).hom.app ((GG i).obj K)) ≫
              (TT h).map ((theta (f ≫ g)).app K) ≫
              (theta h).app ((EE (f ≫ g)).obj K) ≫
              (GG l).map ((u (f ≫ g) h).hom.app K) := by
            simpa only [Category.assoc] using congrArg
              (fun z ↦ z ≫
                (theta h).app ((EE (f ≫ g)).obj K) ≫
                (GG l).map ((u (f ≫ g) h).hom.app K)) hp
          _ = _ := by rw [hc (f ≫ g) h K]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hbase
      · have hp := congrArg
          (fun z ↦ (GG l).map z) (hf f g h K)
        simp only [Functor.map_comp] at hp
        rw [← hp]
        exact hbase
      · rw [← reassoc_of% (hc g h ((EE f).obj K))]
        have hp := congrArg
          (fun z ↦ (GG l).map z) (hf f g h K)
        simp only [Functor.map_comp] at hp
        rw [← hp]
        exact hbase
      · rw [hc (f ≫ g) h K]
      · rfl

section ProofConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def presheafExtension {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :
    modules R ⥤ PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj :=
    { obj := SheafOfModules.changeOfRingsPresheaf f
      map := fun v ↦
        { app := fun W ↦ (ModuleCat.extendScalars (f.hom.app W).hom).map (v.val.app W)
          naturality := SheafOfModules.changeOfRingsHom_naturality f _ v }
      map_id := fun M ↦ by
        ext W : 1
        exact (ModuleCat.extendScalars (f.hom.app W).hom).map_id _
      map_comp := fun v w ↦ by
        ext W : 1
        exact (ModuleCat.extendScalars (f.hom.app W).hom).map_comp _ _ }

private def extension {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :
    modules R ⥤ modules S where
  obj := SheafOfModules.changeOfRings f
  map {M _N} v := SheafOfModules.changeOfRingsHom f M v
  map_id M := (presheafExtension f ⋙ PresheafOfModules.sheafification (𝟙 _)).map_id M
  map_comp v w :=
    (presheafExtension f ⋙ PresheafOfModules.sheafification (𝟙 _)).map_comp v w

private theorem extension_obj {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) : (extension f).obj M = SheafOfModules.changeOfRings f M := rfl

private theorem extension_map {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    {M N : modules R} (v : M ⟶ N) : (extension f).map v =
      eqToHom (extension_obj f M) ≫ SheafOfModules.changeOfRingsHom f M v ≫
        eqToHom (extension_obj f N).symm := by
  rfl

private def pt {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    ((extension f).obj M).val.obj W :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf f M).presheaf).app W
    (a ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)

private theorem pt_def {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    pt f M W a x = pure f (extension f) (extension_obj f) M W a x := rfl

private theorem extension_ext {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) {H : modules S} {v w : (extension f).obj M ⟶ H}
    (h : ∀ W x, v.val.app W (pt f M W 1 x) = w.val.app W (pt f M W 1 x)) :
    v = w := by
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h W x

private theorem pt_map {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    {M N : modules R} (v : M ⟶ N) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    ((extension f).map v).val.app W (pt f M W a x) =
      pt f N W a (v.val.app W x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  let v' : SheafOfModules.changeOfRingsPresheaf f M ⟶
      SheafOfModules.changeOfRingsPresheaf f N :=
    { app := fun W ↦ (ModuleCat.extendScalars (f.hom.app W).hom).map (v.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality f _ v }
  exact (congrArg (fun t ↦ t.app W
    (a ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)) (adj.unit.naturality v')).symm

private def rawLift {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (H : modules S)
    (v : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj H) :
    SheafOfModules.changeOfRingsPresheaf f M ⟶ H.val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (f.hom.app W).hom (v.val.app W)
      naturality := by
        intro U V i
        apply ModuleCat.ExtendScalars.hom_ext
        intro x
        have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap f M i)
          (1 : S.obj.obj U) x
        change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (f.hom.app V).hom (v.val.app V)
            (SheafOfModules.changeOfRingsMap f M i
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)) =
          H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
            (f.hom.app U).hom (v.val.app U)
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x))
        change SheafOfModules.changeOfRingsMap f M i _ = _ at ht
        rw [ht, map_one]
        change (1 : S.obj.obj V) • (show H.val.obj V from v.val.app V (M.val.map i x)) =
          H.val.map i ((1 : S.obj.obj U) • (show H.val.obj U from v.val.app U x))
        simp only [one_smul]
        exact PresheafOfModules.naturality_apply v.val i x }

private def lift {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (H : modules S)
    (v : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj H) :
    (extension f).obj M ⟶ H :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).symm
    (rawLift f M H v)

private theorem lift_pt {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (H : modules S)
    (v : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj H)
    (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    (lift f M H v).val.app W (pt f M W a x) =
      a • (show H.val.obj W from v.val.app W x) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
      |>.apply_symm_apply (rawLift f M H v)
  exact congrArg (fun t ↦ t.app W (a ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)) h

private theorem pt_smul {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (W : Cᵒᵖ) (a b : S.obj.obj W) (x : M.val.obj W) :
    pt f M W (a * b) x = a • pt f M W b x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf f M)
  change η.app W (a • (b ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)) =
    a • η.app W (b ⊗ₜ[R.obj.obj W,(f.hom.app W).hom] x)
  exact (η.app W).hom.map_smul a _

private theorem pt_base {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (W : Cᵒᵖ) (a : R.obj.obj W) (x : M.val.obj W) :
    pt f M W 1 (a • x) = (f.hom.app W a) • pt f M W 1 x := by
  rw [← pt_smul, mul_one]
  let : Module (R.obj.obj W) (S.obj.obj W) :=
    Module.compHom (S.obj.obj W) (f.hom.app W).hom
  have ht : (1 : S.obj.obj W) ⊗ₜ[R.obj.obj W] (a • x) =
      f.hom.app W a ⊗ₜ[R.obj.obj W] x := by
    rw [TensorProduct.tmul_smul]
    change (f.hom.app W a * 1) ⊗ₜ[R.obj.obj W] x = _
    rw [mul_one]
  exact congrArg ((toSheafify J
    (SheafOfModules.changeOfRingsPresheaf f M).presheaf).app W) ht

private theorem pt_add {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) (W : Cᵒᵖ) (x y : M.val.obj W) :
    pt f M W 1 (x + y) = pt f M W 1 x + pt f M W 1 y := by
  unfold pt
  simp only [TensorProduct.tmul_add, map_add]

private instance extension_additive {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :
    (extension f).Additive where
  map_add {M N} v w := by
    apply extension_ext f M
    intro W x
    change ((extension f).map (v + w)).val.app W (pt f M W 1 x) =
      ((extension f).map v).val.app W (pt f M W 1 x) +
        ((extension f).map w).val.app W (pt f M W 1 x)
    rw [pt_map, pt_map, pt_map]
    exact pt_add f N W (v.val.app W x) (w.val.app W x)

private theorem pt_restrict {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (M : modules R) {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) :
    ((extension f).obj M).val.map i (pt f M U 1 x) = pt f M V 1 (M.val.map i x) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf f M)
  have h := PresheafOfModules.naturality_apply η i
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x)
  have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap f M i)
    (1 : S.obj.obj U) x
  change SheafOfModules.changeOfRingsMap f M i _ = _ at ht
  change η.app V (SheafOfModules.changeOfRingsMap f M i _) = _ at h
  rw [ht, map_one] at h
  exact h.symm

private def insert {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) (M : modules R) :
    M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj ((extension f).obj M) where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        (X := M.val.obj W)
        (Y := (ModuleCat.restrictScalars (f.hom.app W).hom).obj
          (((extension f).obj M).val.obj W))
        { toFun := fun x ↦ pt f M W 1 x
          map_add' := pt_add f M W
          map_smul' := pt_base f M W }
      naturality := by
        intro U V i
        ext x
        exact (pt_restrict f M i x).symm }

private theorem extension_ext2 {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (M : modules R) {H : modules T}
    {v w : (extension g).obj ((extension f).obj M) ⟶ H}
    (h : ∀ W x, v.val.app W (pt g _ W 1 (pt f M W 1 x)) =
      w.val.app W (pt g _ W 1 (pt f M W 1 x))) : v = w := by
  let res := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map g)
  have he : insert g ((extension f).obj M) ≫ res.map v =
      insert g ((extension f).obj M) ≫ res.map w := by
    apply extension_ext f M
    exact h
  apply extension_ext g
  intro W y
  exact congrArg (fun z ↦ z.val.app W y) he

attribute [local irreducible] extension pt rawLift lift

private def assocHom {R S T : Sheaf J CommRingCat.{r}} (f : R ⟶ S) (g : S ⟶ T)
    (M : modules R) : (extension g).obj ((extension f).obj M) ⟶
      (extension (f ≫ g)).obj M :=
  lift g ((extension f).obj M) ((extension (f ≫ g)).obj M)
    (lift f M ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map g)).obj
        ((extension (f ≫ g)).obj M)) (insert (f ≫ g) M))

private def assocInv {R S T : Sheaf J CommRingCat.{r}} (f : R ⟶ S) (g : S ⟶ T)
    (M : modules R) : (extension (f ≫ g)).obj M ⟶
      (extension g).obj ((extension f).obj M) :=
  lift (f ≫ g) M _ (insert f M ≫
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).map
      (insert g ((extension f).obj M)))

private theorem assocHom_pt {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (M : modules R) (W : Cᵒᵖ)
    (a : S.obj.obj W) (b : T.obj.obj W) (x : M.val.obj W) :
    (assocHom f g M).val.app W (pt g _ W b (pt f M W a x)) =
      pt (f ≫ g) M W (g.hom.app W a * b) x := by
  change (lift g ((extension f).obj M) ((extension (f ≫ g)).obj M)
    (lift f M ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map g)).obj
        ((extension (f ≫ g)).obj M)) (insert (f ≫ g) M))).val.app W _ = _
  rw [lift_pt]
  rw [lift_pt]
  change b • (g.hom.app W a • pt (f ≫ g) M W 1 x) = _
  rw [← mul_smul, ← pt_smul, mul_one, mul_comm]

private theorem assocInv_pt {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (M : modules R) (W : Cᵒᵖ)
    (b : T.obj.obj W) (x : M.val.obj W) :
    (assocInv f g M).val.app W (pt (f ≫ g) M W b x) =
      pt g _ W b (pt f M W 1 x) := by
  unfold assocInv
  rw [lift_pt]
  change b • pt g _ W 1 (pt f M W 1 x) = _
  rw [← pt_smul, mul_one]

private def associator {R S T : Sheaf J CommRingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) :
    extension f ⋙ extension g ≅ extension (f ≫ g) :=
  NatIso.ofComponents (fun M ↦
    { hom := assocHom f g M
      inv := assocInv f g M
      hom_inv_id := by
        apply extension_ext2 f g M
        intro W x
        change (assocInv f g M).val.app W
          ((assocHom f g M).val.app W (pt g _ W 1 (pt f M W 1 x))) =
            pt g _ W 1 (pt f M W 1 x)
        rw [assocHom_pt, map_one, one_mul, assocInv_pt]
      inv_hom_id := by
        apply extension_ext
        intro W x
        change (assocHom f g M).val.app W
          ((assocInv f g M).val.app W (pt (f ≫ g) M W 1 x)) = pt (f ≫ g) M W 1 x
        rw [assocInv_pt, assocHom_pt, map_one, one_mul] }) (by
    intro M N v
    apply extension_ext2 f g M
    intro W x
    change (assocHom f g N).val.app W
      (((extension g).map ((extension f).map v)).val.app W
        (pt g _ W 1 (pt f M W 1 x))) =
      ((extension (f ≫ g)).map v).val.app W
        ((assocHom f g M).val.app W (pt g _ W 1 (pt f M W 1 x)))
    rw [pt_map, pt_map, assocHom_pt, assocHom_pt, pt_map])

attribute [local irreducible] assocHom assocInv

private def identityInsert (R : Sheaf J CommRingCat.{r}) (M : modules R) :
    M ⟶ (extension (𝟙 R)).obj M where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun x ↦ pt (𝟙 R) M W 1 x
          map_add' := pt_add (𝟙 R) M W
          map_smul' := pt_base (𝟙 R) M W }
      naturality := by
        intro U V i
        ext x
        exact (pt_restrict (𝟙 R) M i x).symm }

private theorem identityInsert_apply (R : Sheaf J CommRingCat.{r}) (M : modules R)
    (W : Cᵒᵖ) (x : M.val.obj W) :
    (identityInsert R M).val.app W x = pt (𝟙 R) M W 1 x := rfl

attribute [local irreducible] identityInsert

private theorem unit_action (R : Sheaf J CommRingCat.{r}) (M : modules R)
    (W : Cᵒᵖ) (a : R.obj.obj W) (x : M.val.obj W) :
    (lift (𝟙 R) M M (𝟙 M)).val.app W (pt (𝟙 R) M W a x) = a • x := by
  exact lift_pt (𝟙 R) M M (𝟙 M) W a x

private def unitIso (R : Sheaf J CommRingCat.{r}) (M : modules R) :
    (extension (𝟙 R)).obj M ≅ M where
  hom := lift (𝟙 R) M M (𝟙 M)
  inv := identityInsert R M
  hom_inv_id := by
    apply extension_ext
    intro W x
    change (identityInsert R M).val.app W
      ((lift (𝟙 R) M M (𝟙 M)).val.app W (pt (𝟙 R) M W 1 x)) = pt (𝟙 R) M W 1 x
    exact (congrArg ((identityInsert R M).val.app W)
      ((unit_action R M W 1 x).trans (one_smul _ x))).trans
        (identityInsert_apply R M W x)
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    change (lift (𝟙 R) M M (𝟙 M)).val.app W ((identityInsert R M).val.app W x) = x
    exact (congrArg ((lift (𝟙 R) M M (𝟙 M)).val.app W)
      (identityInsert_apply R M W x)).trans
        ((unit_action R M W 1 x).trans (one_smul _ x))

private theorem unitIso_hom_apply (R : Sheaf J CommRingCat.{r}) (M : modules R)
    (W : Cᵒᵖ) (a : R.obj.obj W) (x : M.val.obj W) :
    (unitIso R M).hom.val.app W (pt (𝟙 R) M W a x) = a • x := unit_action R M W a x

private theorem unitIso_inv_apply (R : Sheaf J CommRingCat.{r}) (M : modules R)
    (W : Cᵒᵖ) (x : M.val.obj W) :
    (unitIso R M).inv.val.app W x = pt (𝟙 R) M W 1 x := identityInsert_apply R M W x

attribute [local irreducible] unitIso

private def unitor (R : Sheaf J CommRingCat.{r}) : extension (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (unitIso R) (by
    intro M N v
    apply extension_ext
    intro W x
    change (unitIso R N).hom.val.app W
      (((extension (𝟙 R)).map v).val.app W (pt (𝟙 R) M W 1 x)) =
        v.val.app W ((unitIso R M).hom.val.app W (pt (𝟙 R) M W 1 x))
    rw [pt_map, unitIso_hom_apply, unitIso_hom_apply, one_smul, one_smul])

private theorem unitor_hom (R : Sheaf J CommRingCat.{r}) (M : modules R) :
    (unitor R).hom.app M = (unitIso R M).hom := rfl

private theorem unitor_inv (R : Sheaf J CommRingCat.{r}) (M : modules R) :
    (unitor R).inv.app M = (unitIso R M).inv := rfl

attribute [local irreducible] unitor

private theorem associator_hom {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (M : modules R) :
    (associator f g).hom.app M = assocHom f g M := rfl

private theorem associator_inv {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (M : modules R) :
    (associator f g).inv.app M = assocInv f g M := rfl

attribute [local irreducible] associator

private def associatorAlong {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hh : f ≫ g = h) :
    extension f ⋙ extension g ≅ extension h :=
  hh ▸ associator f g

private theorem associatorAlong_hom_pt {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hh : f ≫ g = h)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (b : T.obj.obj W) (x : M.val.obj W) :
    ((associatorAlong f g h hh).hom.app M).val.app W (pt g _ W b (pt f M W a x)) =
      pt h M W (g.hom.app W a * b) x := by
  subst h
  change ((associator f g).hom.app M).val.app W _ = _
  rw [associator_hom]
  exact assocHom_pt f g M W a b x

private theorem associatorAlong_inv_pt {R S T : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hh : f ≫ g = h)
    (M : modules R) (W : Cᵒᵖ) (b : T.obj.obj W) (x : M.val.obj W) :
    ((associatorAlong f g h hh).inv.app M).val.app W (pt h M W b x) =
      pt g _ W b (pt f M W 1 x) := by
  subst h
  change ((associator f g).inv.app M).val.app W _ = _
  rw [associator_inv]
  exact assocInv_pt f g M W b x

private def unitorAlong (R : Sheaf J CommRingCat.{r}) (f : R ⟶ R) (hf : f = 𝟙 R) :
    extension f ≅ 𝟭 _ := hf.symm ▸ unitor R

private theorem unitorAlong_hom_pt (R : Sheaf J CommRingCat.{r})
    (f : R ⟶ R) (hf : f = 𝟙 R) (M : modules R) (W : Cᵒᵖ)
    (a : R.obj.obj W) (x : M.val.obj W) :
    ((unitorAlong R f hf).hom.app M).val.app W (pt f M W a x) = a • x := by
  subst f
  change ((unitor R).hom.app M).val.app W _ = _
  rw [unitor_hom]
  exact unitIso_hom_apply R M W a x

private theorem unitorAlong_inv_apply (R : Sheaf J CommRingCat.{r})
    (f : R ⟶ R) (hf : f = 𝟙 R) (M : modules R) (W : Cᵒᵖ) (x : M.val.obj W) :
    ((unitorAlong R f hf).inv.app M).val.app W x = pt f M W 1 x := by
  subst f
  change ((unitor R).inv.app M).val.app W x = _
  rw [unitor_inv]
  exact unitIso_inv_apply R M W x

attribute [local irreducible] associatorAlong unitorAlong

attribute [local irreducible] ModuleCat.extendScalarsComp ModuleCat.extendScalarsId

private def ordinaryDirect {A B D : CommRingCat.{r}} (f : A ⟶ B) (g : B ⟶ D) :
    ModuleCat.extendScalars.{r, r, r} f.hom ⋙ ModuleCat.extendScalars.{r, r, r} g.hom ≅
      ModuleCat.extendScalars.{r, r, r} (g.hom.comp f.hom) := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := (g.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  exact NatIso.ofComponents
    (fun N ↦ (TensorProduct.AlgebraTensorModule.cancelBaseChange A B D D N).toModuleIso) (by
      intro M N v
      apply ModuleCat.ExtendScalars.hom_ext
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul b n => rfl)

private def ordinaryAssociator {A B D : CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : f ≫ g = h) :
    ModuleCat.extendScalars.{r, r, r} f.hom ⋙ ModuleCat.extendScalars.{r, r, r} g.hom ≅
      ModuleCat.extendScalars.{r, r, r} h.hom :=
  hh ▸ ordinaryDirect f g

private theorem ordinaryAssociator_hom {A B D : CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : f ≫ g = h)
    (N : ModuleCat.{r} A) (b : B) (c : D) (n : N) :
    ((ordinaryAssociator f g h hh).hom.app N)
      (c ⊗ₜ[B,g.hom] (b ⊗ₜ[A,f.hom] n)) = (g b * c) ⊗ₜ[A,h.hom] n := by
  subst h
  rfl

private theorem ordinaryAssociator_inv {A B D : CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : f ≫ g = h)
    (N : ModuleCat.{r} A) (c : D) (n : N) :
    ((ordinaryAssociator f g h hh).inv.app N) (c ⊗ₜ[A,h.hom] n) =
      c ⊗ₜ[B,g.hom] ((1 : B) ⊗ₜ[A,f.hom] n) := by
  subst h
  rfl

private def ordinaryIdentity (A : CommRingCat.{r}) :
    ModuleCat.extendScalars.{r, r, r} (RingHom.id A) ≅ 𝟭 (ModuleCat.{r} A) :=
  NatIso.ofComponents (fun N ↦ (TensorProduct.lid A N).toModuleIso) (by
    intro M N v
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : A) • v x = v ((1 : A) • x)
    simp only [one_smul])

private def ordinaryUnitor (A : CommRingCat.{r}) (f : A ⟶ A) (hf : f = 𝟙 A) :
    ModuleCat.extendScalars.{r, r, r} f.hom ≅ 𝟭 _ :=
  hf.symm ▸ ordinaryIdentity A

private theorem ordinaryUnitor_hom (A : CommRingCat.{r}) (f : A ⟶ A) (hf : f = 𝟙 A)
    (N : ModuleCat.{r} A) (b : A) (n : N) :
    ((ordinaryUnitor A f hf).hom.app N) (ordinaryPure f N b n) = b • n := by
  subst f
  rfl

private theorem ordinaryUnitor_inv (A : CommRingCat.{r}) (f : A ⟶ A) (hf : f = 𝟙 A)
    (N : ModuleCat.{r} A) (n : N) :
    ((ordinaryUnitor A f hf).inv.app N) n = (1 : A) ⊗ₜ[A,f.hom] n := by
  subst f
  rfl

attribute [local irreducible] ordinaryAssociator ordinaryUnitor

private def comparisonInsert (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom) (M : modules R) :
    (sections s R A lamA).obj M ⟶ (ModuleCat.restrictScalars h.hom).obj
      ((sections s S B lamB).obj ((extension f).obj M)) :=
  ModuleCat.ofHom
    (X := (sections s R A lamA).obj M)
    (Y := (ModuleCat.restrictScalars h.hom).obj
      ((sections s S B lamB).obj ((extension f).obj M)))
    { toFun := fun n ↦ pt f M (op s) 1 n
      map_add' := pt_add f M (op s)
      map_smul' := by
        intro a n
        change pt f M (op s) 1 (lamA a • (show M.val.obj (op s) from n)) =
          lamB (h a) • pt f M (op s) 1 n
        have hc : f.hom.app (op s) (lamA a) = lamB (h a) :=
          RingHom.congr_fun compat a
        exact (pt_base f M (op s) (lamA a) n).trans
          (congrArg (fun z : S.obj.obj (op s) ↦ z • pt f M (op s) 1 n) hc) }

private theorem comparisonInsert_apply (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom) (M : modules R)
    (n : M.val.obj (op s)) :
    comparisonInsert s f h lamA lamB compat M n = pt f M (op s) 1 n := rfl

attribute [local irreducible] comparisonInsert

private def comparisonMap (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom) (M : modules R) :
    (ModuleCat.extendScalars h.hom).obj ((sections s R A lamA).obj M) ⟶
      (sections s S B lamB).obj ((extension f).obj M) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars h.hom
    (comparisonInsert s f h lamA lamB compat M)

private theorem comparisonMap_tmul (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom)
    (M : modules R) (b : B) (n : M.val.obj (op s)) :
    comparisonMap s f h lamA lamB compat M (b ⊗ₜ[A,h.hom] n) =
      pt f M (op s) (lamB b) n := by
  change b • comparisonInsert s f h lamA lamB compat M n = _
  rw [comparisonInsert_apply]
  change lamB b • pt f M (op s) 1 n = _
  rw [← pt_smul, mul_one]

attribute [local irreducible] comparisonMap

private def comparison (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom) :
    sections s R A lamA ⋙ ModuleCat.extendScalars h.hom ⟶
      extension f ⋙ sections s S B lamB where
  app M := comparisonMap s f h lamA lamB compat M
  naturality := by
    intro M N v
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    change comparisonMap s f h lamA lamB compat N
      ((ModuleCat.extendScalars h.hom).map
        ((sections s R A lamA).map v) ((1 : B) ⊗ₜ[A,h.hom] n)) =
      ((extension f).map v).val.app (op s)
        (comparisonMap s f h lamA lamB compat M ((1 : B) ⊗ₜ[A,h.hom] n))
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [comparisonMap_tmul, comparisonMap_tmul, map_one]
    exact (pt_map f v (op s) 1 n).symm

private theorem comparison_tmul (s : C) {R S : Sheaf J CommRingCat.{r}}
    {A B : CommRingCat.{r}} (f : R ⟶ S) (h : A ⟶ B)
    (lamA : A →+* R.obj.obj (op s)) (lamB : B →+* S.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lamA = lamB.comp h.hom)
    (M : modules R) (b : B) (n : M.val.obj (op s)) :
    ((comparison s f h lamA lamB compat).app M) (b ⊗ₜ[A,h.hom] n) =
      pt f M (op s) (lamB b) n := by
  exact comparisonMap_tmul s f h lamA lamB compat M b n

attribute [local irreducible] comparison

private theorem comparison_comp (s : C)
    {R S T : Sheaf J CommRingCat.{r}} {A B D : CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T) (hh : f ≫ g = h)
    (f' : A ⟶ B) (g' : B ⟶ D) (h' : A ⟶ D) (hh' : f' ≫ g' = h')
    (lA : A →+* R.obj.obj (op s)) (lB : B →+* S.obj.obj (op s))
    (lD : D →+* T.obj.obj (op s))
    (cF : (f.hom.app (op s)).hom.comp lA = lB.comp f'.hom)
    (cG : (g.hom.app (op s)).hom.comp lB = lD.comp g'.hom)
    (cH : (h.hom.app (op s)).hom.comp lA = lD.comp h'.hom)
    (M : modules R) :
    (ModuleCat.extendScalars g'.hom).map ((comparison s f f' lA lB cF).app M) ≫
        (comparison s g g' lB lD cG).app ((extension f).obj M) ≫
        (sections s T D lD).map ((associatorAlong f g h hh).hom.app M) =
      (ordinaryAssociator f' g' h' hh').hom.app ((sections s R A lA).obj M) ≫
        (comparison s h h' lA lD cH).app M := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul b n =>
    change ((associatorAlong f g h hh).hom.app M).val.app (op s)
      (((comparison s g g' lB lD cG).app ((extension f).obj M))
        ((ModuleCat.extendScalars g'.hom).map ((comparison s f f' lA lB cF).app M)
          ((1 : D) ⊗ₜ[B,g'.hom] (b ⊗ₜ[A,f'.hom] n)))) =
      ((comparison s h h' lA lD cH).app M)
        (((ordinaryAssociator f' g' h' hh').hom.app ((sections s R A lA).obj M))
          ((1 : D) ⊗ₜ[B,g'.hom] (b ⊗ₜ[A,f'.hom] n)))
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [comparison_tmul, comparison_tmul, associatorAlong_hom_pt,
      ordinaryAssociator_hom, comparison_tmul, map_one, mul_one, mul_one]
    exact congrArg (fun a ↦ pt h M (op s) a n) (RingHom.congr_fun cG b)

private theorem comparison_unit (s : C) (R : Sheaf J CommRingCat.{r}) (A : CommRingCat.{r})
    (f : R ⟶ R) (hf : f = 𝟙 R) (h : A ⟶ A) (hh : h = 𝟙 A)
    (lam : A →+* R.obj.obj (op s))
    (compat : (f.hom.app (op s)).hom.comp lam = lam.comp h.hom) (M : modules R) :
    (comparison s f h lam lam compat).app M ≫
        (sections s R A lam).map ((unitorAlong R f hf).hom.app M) =
      (ordinaryUnitor A h hh).hom.app ((sections s R A lam).obj M) := by
  subst h
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change ((unitorAlong R f hf).hom.app M).val.app (op s)
    (((comparison s f (𝟙 A) lam lam compat).app M)
      ((1 : A) ⊗ₜ[A,RingHom.id A] n)) = _
  rw [comparison_tmul, map_one, unitorAlong_hom_pt, one_smul]
  exact ((ordinaryUnitor_hom A (𝟙 A) rfl _ 1 n).trans (one_smul A n)).symm

private theorem extension_ext3 {R S T U : Sheaf J CommRingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) (M : modules R) {H : modules U}
    {v w : (extension h).obj ((extension g).obj ((extension f).obj M)) ⟶ H}
    (hp : ∀ W x, v.val.app W (pt h _ W 1 (pt g _ W 1 (pt f M W 1 x))) =
      w.val.app W (pt h _ W 1 (pt g _ W 1 (pt f M W 1 x)))) : v = w := by
  let res := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map h)
  have he : insert h _ ≫ res.map v = insert h _ ≫ res.map w := by
    apply extension_ext2 f g M
    exact hp
  apply extension_ext h
  intro W y
  exact congrArg (fun z ↦ z.val.app W y) he

private theorem ordinary_ext3 {A B D F : CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ F) (N : ModuleCat.{r} A)
    {P : ModuleCat.{r} F}
    {v w : (ModuleCat.extendScalars h.hom).obj
      ((ModuleCat.extendScalars g.hom).obj ((ModuleCat.extendScalars f.hom).obj N)) ⟶ P}
    (hp : ∀ (d : F) (c : D) (b : B) (n : N),
      v (d ⊗ₜ[D,h.hom] (c ⊗ₜ[B,g.hom] (b ⊗ₜ[A,f.hom] n))) =
        w (d ⊗ₜ[D,h.hom] (c ⊗ₜ[B,g.hom] (b ⊗ₜ[A,f.hom] n)))) : v = w := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul c z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add z z' hz hz' => simp only [TensorProduct.tmul_add, map_add, hz, hz']
    | tmul b n => exact hp 1 c b n

private theorem associator_four (R : Fin 4 ⥤ Sheaf J CommRingCat.{r})
    {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (M : modules (R.obj i)) :
    (extension (R.map h)).map
        ((associatorAlong (R.map f) (R.map g) (R.map (f ≫ g))
          (R.map_comp f g).symm).hom.app M) ≫
      (associatorAlong (R.map (f ≫ g)) (R.map h) (R.map ((f ≫ g) ≫ h))
        (R.map_comp (f ≫ g) h).symm).hom.app M =
    (associatorAlong (R.map g) (R.map h) (R.map (g ≫ h))
        (R.map_comp g h).symm).hom.app ((extension (R.map f)).obj M) ≫
      (associatorAlong (R.map f) (R.map (g ≫ h)) (R.map (f ≫ (g ≫ h)))
        (R.map_comp f (g ≫ h)).symm).hom.app M := by
  apply extension_ext3 (R.map f) (R.map g) (R.map h) M
  intro W x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [pt_map, associatorAlong_hom_pt, associatorAlong_hom_pt,
    associatorAlong_hom_pt, associatorAlong_hom_pt]
  simp only [map_one, one_mul]
  rfl

private theorem ordinaryAssociator_four (A : Fin 4 ⥤ CommRingCat.{r})
    {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (N : ModuleCat.{r} (A.obj i)) :
    (ModuleCat.extendScalars (A.map h).hom).map
        ((ordinaryAssociator (A.map f) (A.map g) (A.map (f ≫ g))
          (A.map_comp f g).symm).hom.app N) ≫
      (ordinaryAssociator (A.map (f ≫ g)) (A.map h) (A.map ((f ≫ g) ≫ h))
        (A.map_comp (f ≫ g) h).symm).hom.app N =
    (ordinaryAssociator (A.map g) (A.map h) (A.map (g ≫ h))
        (A.map_comp g h).symm).hom.app
          ((ModuleCat.extendScalars (A.map f).hom).obj N) ≫
      (ordinaryAssociator (A.map f) (A.map (g ≫ h)) (A.map (f ≫ (g ≫ h)))
        (A.map_comp f (g ≫ h)).symm).hom.app N := by
  apply ordinary_ext3 (A.map f) (A.map g) (A.map h)
  intro d c b n
  simp only [ModuleCat.comp_apply]
  erw [ModuleCat.ExtendScalars.map_tmul, ordinaryAssociator_hom,
    ordinaryAssociator_hom, ordinaryAssociator_hom, ordinaryAssociator_hom]
  congr 1
  simp only [map_mul, mul_assoc]
  have hc : A.map h (A.map g b) = A.map (g ≫ h) b :=
    (ConcreteCategory.congr_hom (A.map_comp g h) b).symm
  rw [hc]

attribute [-instance] extension_additive
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

private theorem moduleConstruction [EssentiallySmall.{r} C] (s : C)
    (R : Fin 4 ⥤ Sheaf J CommRingCat.{r}) (A : Fin 4 ⥤ CommRingCat.{r})
    (lam : ∀ i, A.obj i →+* (R.obj i).obj.obj (op s))
    (compat : ∀ {i j : Fin 4} (f : i ⟶ j),
      ((R.map f).hom.app (op s)).hom.comp (lam i) = (lam j).comp (A.map f).hom) (P : Prop)
    (k : ∀
    (E : ∀ {i j : Fin 4}, (i ⟶ j) → modules (R.obj i) ⥤ modules (R.obj j))
    (e : ∀ {i j : Fin 4} (f : i ⟶ j) M,
    (E f).obj M = SheafOfModules.changeOfRings (R.map f) M)
    (_add : ∀ {i j : Fin 4} (f : i ⟶ j), (E f).Additive)
    (_map_eq : ∀ {i j : Fin 4} (f : i ⟶ j) {M N : modules (R.obj i)} (v : M ⟶ N),
    (E f).map v = eqToHom (e f M) ≫
      SheafOfModules.changeOfRingsHom (R.map f) M v ≫ eqToHom (e f N).symm)
    (theta : ∀ {i j : Fin 4} (f : i ⟶ j),
    sections s (R.obj i) (A.obj i) (lam i) ⋙ (ModuleCat.extendScalars (A.map f).hom) ⟶
    E f ⋙ sections s (R.obj j) (A.obj j) (lam j))
    (u : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
    E f ⋙ E g ≅
    E (f ≫ g))
    (a : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
    (ModuleCat.extendScalars (A.map f).hom) ⋙ (ModuleCat.extendScalars (A.map g).hom) ≅
      (ModuleCat.extendScalars (A.map (f ≫ g)).hom))
    (m : ∀ i : Fin 4, E (𝟙 i) ≅ 𝟭 _)
    (mu : ∀ i : Fin 4, (ModuleCat.extendScalars (A.map (𝟙 i)).hom) ≅ 𝟭 _)
    (_p1 : ∀ {i j : Fin 4} (f : i ⟶ j) (M : modules (R.obj i))
               (n : M.val.obj (op s)) (b : A.obj j),
              ((theta f).app M) (b ⊗ₜ[A.obj i,(A.map f).hom] n) =
                pure (R.map f) (E f) (e f) M (op s) (lam j b) n)
    (_p2 : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
              (M : modules (R.obj i))  (W : Cᵒᵖ)
              (x : M.val.obj W) (b : (R.obj j).obj.obj W)
              (c : (R.obj k).obj.obj W),
              (((u f g).hom.app M)).val.app W
                (pure (R.map g) (E g) (e g) ((E f).obj M) W c
                  (pure (R.map f) (E f) (e f) M W b x)) =
                pure (R.map (f ≫ g)) (E (f ≫ g)) (e (f ≫ g)) M W
                  ((R.map g).hom.app W b * c) x)
    (_p3 : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
              (M : modules (R.obj i))  (W : Cᵒᵖ)
              (x : M.val.obj W) (c : (R.obj k).obj.obj W),
              (((u f g).inv.app M)).val.app W
                (pure (R.map (f ≫ g)) (E (f ≫ g)) (e (f ≫ g)) M W c x) =
                pure (R.map g) (E g) (e g) ((E f).obj M) W c
                  (pure (R.map f) (E f) (e f) M W 1 x))
    (_p4 : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
              (N : ModuleCat.{r} (A.obj i))
              (n : N) (b : A.obj j) (c : A.obj k),
              ((a f g).hom.app N)
                (c ⊗ₜ[A.obj j,(A.map g).hom] (b ⊗ₜ[A.obj i,(A.map f).hom] n)) =
                ((A.map g b * c) ⊗ₜ[A.obj i,(A.map (f ≫ g)).hom] n))
    (_p5 : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
              (N : ModuleCat.{r} (A.obj i))
              (n : N) (c : A.obj k),
              ((a f g).inv.app N) (c ⊗ₜ[A.obj i,(A.map (f ≫ g)).hom] n) =
                c ⊗ₜ[A.obj j,(A.map g).hom] ((1 : A.obj j) ⊗ₜ[A.obj i,(A.map f).hom] n))
    (_p6 : ∀ (i : Fin 4) (M : modules (R.obj i))
              (W : Cᵒᵖ) (x : M.val.obj W) (b : (R.obj i).obj.obj W),
              (((m i).hom.app M)).val.app W
                (pure (R.map (𝟙 i)) (E (𝟙 i)) (e (𝟙 i)) M W b x) = b • x)
    (_p7 : ∀ (i : Fin 4) (M : modules (R.obj i))
              (W : Cᵒᵖ) (x : M.val.obj W),
              (((m i).inv.app M)).val.app W x =
                pure (R.map (𝟙 i)) (E (𝟙 i)) (e (𝟙 i)) M W 1 x)
    (_p8 : ∀ (i : Fin 4) (N : ModuleCat.{r} (A.obj i))
              (n : N) (b : A.obj i),
              ((mu i).hom.app N) (ordinaryPure (A.map (𝟙 i)) N b n) = b • n)
    (_p9 : ∀ (i : Fin 4) (N : ModuleCat.{r} (A.obj i))
              (n : N), ((mu i).inv.app N) n =
                (1 : A.obj i) ⊗ₜ[A.obj i,(A.map (𝟙 i)).hom] n)
    (_p10 : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
              (M : modules (R.obj i)),
              ((ModuleCat.extendScalars (A.map g).hom)).map ((theta f).app M) ≫
                  (theta g).app ((E f).obj M) ≫
                  (sections s (R.obj k) (A.obj k) (lam k)).map ((u f g).hom.app M) =
                (a f g).hom.app ((sections s (R.obj i) (A.obj i) (lam i)).obj M) ≫
                  (theta (f ≫ g)).app M)
    (_p11 : ∀ (i : Fin 4) (M : modules (R.obj i)),
              (theta (𝟙 i)).app M ≫
                  (sections s (R.obj i) (A.obj i) (lam i)).map ((m i).hom.app M) =
                (mu i).hom.app ((sections s (R.obj i) (A.obj i) (lam i)).obj M))
    (_p12 : ∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
              (M : modules (R.obj i)),
              (E h).map ((u f g).hom.app M) ≫
                  (u (f ≫ g) h).hom.app M =
                (u g h).hom.app ((E f).obj M) ≫
                  (u f (g ≫ h)).hom.app M)
    (_p13 : ∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
              (N : ModuleCat.{r} (A.obj i)),
              ((ModuleCat.extendScalars (A.map h).hom)).map ((a f g).hom.app N) ≫ (a (f ≫ g)
                h).hom.app N =
                (a g h).hom.app (((ModuleCat.extendScalars (A.map f).hom)).obj N) ≫ (a f (g ≫
                  h)).hom.app N), P) : P := by
  apply k (fun {_ _} f ↦ extension (R.map f))
    (fun {_ _} f M ↦ extension_obj (R.map f) M)
    (fun {_ _} f ↦ extension_additive (R.map f))
    (fun {_ _} f {_M _N} v ↦ extension_map (R.map f) v)
    (fun {_ _} f ↦ comparison s (R.map f) (A.map f) (lam _) (lam _) (compat f))
    (fun {_ _ _} f g ↦
      associatorAlong (R.map f) (R.map g) (R.map (f ≫ g)) (R.map_comp f g).symm)
    (fun {_ _ _} f g ↦
      ordinaryAssociator (A.map f) (A.map g) (A.map (f ≫ g)) (A.map_comp f g).symm)
    (fun i ↦ unitorAlong (R.obj i) (R.map (𝟙 i)) (R.map_id i))
    (fun i ↦ ordinaryUnitor (A.obj i) (A.map (𝟙 i)) (A.map_id i))
  · intro i j f M n b
    exact (comparison_tmul s (R.map f) (A.map f) (lam i) (lam j) (compat f) M b n).trans
      (pt_def (R.map f) M (op s) (lam j b) n)
  · intro i j k f g M W x b c
    simpa only [← pt_def] using associatorAlong_hom_pt
      (R.map f) (R.map g) (R.map (f ≫ g)) (R.map_comp f g).symm M W b c x
  · intro i j k f g M W x c
    simpa only [← pt_def] using associatorAlong_inv_pt
      (R.map f) (R.map g) (R.map (f ≫ g)) (R.map_comp f g).symm M W c x
  · intro i j k f g N n b c
    exact ordinaryAssociator_hom _ _ _ _ N b c n
  · intro i j k f g N n c
    exact ordinaryAssociator_inv _ _ _ _ N c n
  · intro i M W x b
    simpa only [← pt_def] using unitorAlong_hom_pt
      (R.obj i) (R.map (𝟙 i)) (R.map_id i) M W b x
  · intro i M W x
    simpa only [← pt_def] using unitorAlong_inv_apply
      (R.obj i) (R.map (𝟙 i)) (R.map_id i) M W x
  · intro i N n b
    exact ordinaryUnitor_hom _ _ _ N b n
  · intro i N n
    exact ordinaryUnitor_inv _ _ _ N n
  · intro i j k f g M
    exact comparison_comp s (R.map f) (R.map g) (R.map (f ≫ g)) _
      (A.map f) (A.map g) (A.map (f ≫ g)) _ (lam i) (lam j) (lam k)
      (compat f) (compat g) (compat (f ≫ g)) M
  · intro i M
    exact comparison_unit s (R.obj i) (A.obj i) (R.map (𝟙 i)) (R.map_id i)
      (A.map (𝟙 i)) (A.map_id i) (lam i) (compat (𝟙 i)) M
  · intro i j k l f g h M
    exact associator_four R f g h M
  · intro i j k l f g h N
    exact ordinaryAssociator_four A f g h N


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false

/-- All balanced maps exist as natural chain maps, the scalar associators and action
units are natural chain isomorphisms, and their sections comparisons are coherent.
Source: Stacks 03EK, section-tensor-product; 03CZ, adjointness-tensor-restrict;
03CY, sheafification-presheaf-modules.
(blueprint: lem-weil-sections-scalar-cochain-coherence)

Proof plan (the node's eight steps):
1. The sectionwise scalar adjunction followed by the module-sheafification adjunction
   determines a map from an extension by its value on x tensor 1. Apply it repeatedly
   for iterated extensions, over every object, without asserting global generation.
2. The compatible lambdas make the sections pairing balanced and linear; ordinary
   tensor generation gives its naturality.
3. Extend the single and double insertions to obtain u and its displayed inverse.
   The adjunction proves the inverse equations and naturality.
4. Extend the identity to obtain the action unit with inverse insertion of 1.
   Ordinary tensors give the analogous module associators and units.
5. Apply these maps degreewise. Naturality at the differentials proves the chain
   equations for the maps and their inverses, and then naturality for chain maps.
6. On double ordinary pure tensors both comparison routes give the lambda-image
   of the product of transported coefficients. The identity case gives the action.
7. For the four-stage sheaf equation both routes agree on triple insertion; use
   the adjunction three times. The ordinary equation uses triple tensor generators.
8. Substitution gives the displayed common image for every three-comparison route.
   The binary equation and the two four-stage equations allow all reassociations.
   This uses no cancellation, flatness, exactness, or invertibility of theta. -/
theorem coherence [EssentiallySmall.{r} C] (s : C) (_hs : IsTerminal s)
    (R : Fin 4 ⥤ Sheaf J CommRingCat.{r}) (A : Fin 4 ⥤ CommRingCat.{r})
    (lam : ∀ i, A.obj i →+* (R.obj i).obj.obj (op s))
    (compat : ∀ {i j : Fin 4} (f : i ⟶ j),
      ((R.map f).hom.app (op s)).hom.comp (lam i) = (lam j).comp (A.map f).hom) :
    ∃ (E : ∀ {i j : Fin 4} (_f : i ⟶ j), modules (R.obj i) ⥤ modules (R.obj j))
      (e : ∀ {i j : Fin 4} (f : i ⟶ j) M,
        (E f).obj M = SheafOfModules.changeOfRings (R.map f) M)
      (add : ∀ {i j : Fin 4} (f : i ⟶ j), (E f).Additive),
      (∀ {i j : Fin 4} (f : i ⟶ j) {M N : modules (R.obj i)} (v : M ⟶ N),
        (E f).map v = eqToHom (e f M) ≫
          SheafOfModules.changeOfRingsHom (R.map f) M v ≫ eqToHom (e f N).symm) ∧
      ∃ (theta : ∀ {i j : Fin 4} (f : i ⟶ j),
          G s (R.obj i) (A.obj i) (lam i) ⋙ t.{r, r} (A.map f) ⟶
            onComplexes (E f) (add f) ⋙ G s (R.obj j) (A.obj j) (lam j))
        (u : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
          onComplexes (E f) (add f) ⋙ onComplexes (E g) (add g) ≅
            onComplexes (E (f ≫ g)) (add (f ≫ g)))
        (a : ∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k),
          t.{r, r} (A.map f) ⋙ t.{r, r} (A.map g) ≅ t.{r, r} (A.map (f ≫ g)))
        (m : ∀ i : Fin 4, onComplexes (E (𝟙 i)) (add (𝟙 i)) ≅ 𝟭 _)
        (mu : ∀ i : Fin 4, t.{r, r} (A.map (𝟙 i)) ≅ 𝟭 _),
        (∀ {i j : Fin 4} (f : i ⟶ j) (K : CochainComplex (modules (R.obj i)) ℤ)
          (q : ℤ) (n : (K.X q).val.obj (op s)) (b : A.obj j),
          ((theta f).app K).f q (b ⊗ₜ[A.obj i,(A.map f).hom] n) =
            pure (R.map f) (E f) (e f) (K.X q) (op s) (lam j b) n) ∧
        (∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
          (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ) (W : Cᵒᵖ)
          (x : (K.X q).val.obj W) (b : (R.obj j).obj.obj W)
          (c : (R.obj k).obj.obj W),
          (((u f g).hom.app K).f q).val.app W
            (pure (R.map g) (E g) (e g) ((E f).obj (K.X q)) W c
              (pure (R.map f) (E f) (e f) (K.X q) W b x)) =
            pure (R.map (f ≫ g)) (E (f ≫ g)) (e (f ≫ g)) (K.X q) W
              ((R.map g).hom.app W b * c) x) ∧
        (∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
          (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ) (W : Cᵒᵖ)
          (x : (K.X q).val.obj W) (c : (R.obj k).obj.obj W),
          (((u f g).inv.app K).f q).val.app W
            (pure (R.map (f ≫ g)) (E (f ≫ g)) (e (f ≫ g)) (K.X q) W c x) =
            pure (R.map g) (E g) (e g) ((E f).obj (K.X q)) W c
              (pure (R.map f) (E f) (e f) (K.X q) W 1 x)) ∧
        (∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
          (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ) (q : ℤ)
          (n : N.X q) (b : A.obj j) (c : A.obj k),
          ((a f g).hom.app N).f q
            (c ⊗ₜ[A.obj j,(A.map g).hom] (b ⊗ₜ[A.obj i,(A.map f).hom] n)) =
            ((A.map g b * c) ⊗ₜ[A.obj i,(A.map (f ≫ g)).hom] n)) ∧
        (∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
          (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ) (q : ℤ)
          (n : N.X q) (c : A.obj k),
          ((a f g).inv.app N).f q (c ⊗ₜ[A.obj i,(A.map (f ≫ g)).hom] n) =
            c ⊗ₜ[A.obj j,(A.map g).hom] ((1 : A.obj j) ⊗ₜ[A.obj i,(A.map f).hom] n)) ∧
        (∀ (i : Fin 4) (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ)
          (W : Cᵒᵖ) (x : (K.X q).val.obj W) (b : (R.obj i).obj.obj W),
          (((m i).hom.app K).f q).val.app W
            (pure (R.map (𝟙 i)) (E (𝟙 i)) (e (𝟙 i)) (K.X q) W b x) = b • x) ∧
        (∀ (i : Fin 4) (K : CochainComplex (modules (R.obj i)) ℤ) (q : ℤ)
          (W : Cᵒᵖ) (x : (K.X q).val.obj W),
          (((m i).inv.app K).f q).val.app W x =
            pure (R.map (𝟙 i)) (E (𝟙 i)) (e (𝟙 i)) (K.X q) W 1 x) ∧
        (∀ (i : Fin 4) (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ) (q : ℤ)
          (n : N.X q) (b : A.obj i),
          ((mu i).hom.app N).f q (ordinaryPure (A.map (𝟙 i)) (N.X q) b n) = b • n) ∧
        (∀ (i : Fin 4) (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ) (q : ℤ)
          (n : N.X q), ((mu i).inv.app N).f q n =
            (1 : A.obj i) ⊗ₜ[A.obj i,(A.map (𝟙 i)).hom] n) ∧
        (∀ {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
          (K : CochainComplex (modules (R.obj i)) ℤ),
          (t.{r, r} (A.map g)).map ((theta f).app K) ≫
              (theta g).app ((onComplexes (E f) (add f)).obj K) ≫
              (G s (R.obj k) (A.obj k) (lam k)).map ((u f g).hom.app K) =
            (a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K) ≫
              (theta (f ≫ g)).app K) ∧
        (∀ (i : Fin 4) (K : CochainComplex (modules (R.obj i)) ℤ),
          (theta (𝟙 i)).app K ≫
              (G s (R.obj i) (A.obj i) (lam i)).map ((m i).hom.app K) =
            (mu i).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ∧
        (∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
          (K : CochainComplex (modules (R.obj i)) ℤ),
          (onComplexes (E h) (add h)).map ((u f g).hom.app K) ≫
              (u (f ≫ g) h).hom.app K =
            (u g h).hom.app ((onComplexes (E f) (add f)).obj K) ≫
              (u f (g ≫ h)).hom.app K) ∧
        (∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
          (N : CochainComplex (ModuleCat.{r} (A.obj i)) ℤ),
          (t.{r, r} (A.map h)).map ((a f g).hom.app N) ≫ (a (f ≫ g) h).hom.app N =
            (a g h).hom.app ((t.{r, r} (A.map f)).obj N) ≫ (a f (g ≫ h)).hom.app N) ∧
        (∀ {i j k l : Fin 4} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
          (K : CochainComplex (modules (R.obj i)) ℤ),
          ∀ v ∈ [
            (t.{r, r} (A.map h)).map ((t.{r, r} (A.map g)).map ((theta f).app K)) ≫
              (t.{r, r} (A.map h)).map
                ((theta g).app ((onComplexes (E f) (add f)).obj K)) ≫
              (theta h).app ((onComplexes (E g) (add g)).obj
                ((onComplexes (E f) (add f)).obj K)) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map
                ((onComplexes (E h) (add h)).map ((u f g).hom.app K)) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map ((u (f ≫ g) h).hom.app K),
            (t.{r, r} (A.map h)).map ((t.{r, r} (A.map g)).map ((theta f).app K)) ≫
              (t.{r, r} (A.map h)).map
                ((theta g).app ((onComplexes (E f) (add f)).obj K)) ≫
              (theta h).app ((onComplexes (E g) (add g)).obj
                ((onComplexes (E f) (add f)).obj K)) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map
                ((u g h).hom.app ((onComplexes (E f) (add f)).obj K)) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map ((u f (g ≫ h)).hom.app K),
            (t.{r, r} (A.map h)).map ((t.{r, r} (A.map g)).map ((theta f).app K)) ≫
              (a g h).hom.app ((G s (R.obj j) (A.obj j) (lam j)).obj
                ((onComplexes (E f) (add f)).obj K)) ≫
              (theta (g ≫ h)).app ((onComplexes (E f) (add f)).obj K) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map ((u f (g ≫ h)).hom.app K),
            (t.{r, r} (A.map h)).map
                ((a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ≫
              (t.{r, r} (A.map h)).map ((theta (f ≫ g)).app K) ≫
              (theta h).app ((onComplexes (E (f ≫ g)) (add (f ≫ g))).obj K) ≫
              (G s (R.obj l) (A.obj l) (lam l)).map ((u (f ≫ g) h).hom.app K),
            (t.{r, r} (A.map h)).map
                ((a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ≫
              (a (f ≫ g) h).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K) ≫
              (theta ((f ≫ g) ≫ h)).app K],
            v =
              (t.{r, r} (A.map h)).map
                  ((a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ≫
                (a (f ≫ g) h).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K) ≫
                (theta ((f ≫ g) ≫ h)).app K ∧
            ∀ (q : ℤ) (n : (K.X q).val.obj (op s))
              (b : A.obj j) (c : A.obj k) (d : A.obj l),
              (v.f q)
                (d ⊗ₜ[A.obj k,(A.map h).hom]
                  (c ⊗ₜ[A.obj j,(A.map g).hom] (b ⊗ₜ[A.obj i,(A.map f).hom] n))) =
                pure (R.map ((f ≫ g) ≫ h)) (E ((f ≫ g) ≫ h)) (e ((f ≫ g) ≫ h))
                  (K.X q) (op s) (lam l (A.map (g ≫ h) b * A.map h c * d)) n) := by
  apply moduleConstruction s R A lam compat
  intro md_E md_e md_add md_map_eq md_theta md_u md_a md_m md_mu
    md_p1 md_p2 md_p3 md_p4 md_p5 md_p6 md_p7 md_p8 md_p9
    md_p10 md_p11 md_p12 md_p13
  let E := @md_E
  let e := @md_e
  let add := @md_add
  let {i j : Fin 4} (_f : i ⟶ j) : (E _f).Additive := add _f
  let theta {i j : Fin 4} (f : i ⟶ j) :
      G s (R.obj i) (A.obj i) (lam i) ⋙ t.{r, r} (A.map f) ⟶
      onComplexes (E f) (add f) ⋙ G s (R.obj j) (A.obj j) (lam j) :=
    NatTrans.mapHomologicalComplex (md_theta f) (.up ℤ)
  let u {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k) :
      onComplexes (E f) (add f) ⋙ onComplexes (E g) (add g) ≅
      onComplexes (E (f ≫ g)) (add (f ≫ g)) :=
    NatIso.mapHomologicalComplex (md_u f g) (.up ℤ)
  let a {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k) :
      t.{r, r} (A.map f) ⋙ t.{r, r} (A.map g) ≅ t.{r, r} (A.map (f ≫ g)) :=
    NatIso.mapHomologicalComplex (md_a f g) (.up ℤ)
  let m (i : Fin 4) : onComplexes (E (𝟙 i)) (add (𝟙 i)) ≅ 𝟭 _ :=
    NatIso.mapHomologicalComplex (md_m i) (.up ℤ)
  let mu (i : Fin 4) : t.{r, r} (A.map (𝟙 i)) ≅ 𝟭 _ :=
    NatIso.mapHomologicalComplex (md_mu i) (.up ℤ)
  refine ⟨@E, @e, @add, @md_map_eq, @theta, @u, @a, m, mu, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i j f K q n b
    exact md_p1 f (K.X q) n b
  refine ⟨?_, ?_⟩
  · intro i j k f g K q W x b c
    exact md_p2 f g (K.X q) W x b c
  refine ⟨?_, ?_⟩
  · intro i j k f g K q W x c
    exact md_p3 f g (K.X q) W x c
  refine ⟨?_, ?_⟩
  · intro i j k f g N q n b c
    exact md_p4 f g (N.X q) n b c
  refine ⟨?_, ?_⟩
  · intro i j k f g N q n c
    exact md_p5 f g (N.X q) n c
  refine ⟨?_, ?_⟩
  · intro i K q W x b
    exact md_p6 i (K.X q) W x b
  refine ⟨?_, ?_⟩
  · intro i K q W x
    exact md_p7 i (K.X q) W x
  refine ⟨?_, ?_⟩
  · intro i N q n b
    exact md_p8 i (N.X q) n b
  refine ⟨?_, ?_⟩
  · intro i N q n
    exact md_p9 i (N.X q) n
  refine ⟨?_, ?_⟩
  · intro i j k f g K
    ext q : 1
    exact md_p10 f g (K.X q)
  refine ⟨?_, ?_⟩
  · intro i K
    ext q : 1
    exact md_p11 i (K.X q)
  refine ⟨?_, ?_⟩
  · intro i j k l f g h K
    ext q : 1
    exact md_p12 f g h (K.X q)
  refine ⟨?_, ?_⟩
  · intro i j k l f g h N
    ext q : 1
    exact md_p13 f g h (N.X q)
  intro i j k l f g h K v hv
  have heq : v =
      (t.{r, r} (A.map h)).map
        ((a f g).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K)) ≫
      (a (f ≫ g) h).hom.app ((G s (R.obj i) (A.obj i) (lam i)).obj K) ≫
      (theta ((f ≫ g) ≫ h)).app K := by
    apply HomologicalComplex.hom_ext
    intro q
    have hq := List.mem_map_of_mem (f := fun z ↦ z.f q) hv
    exact generic_routes
      (fun i ↦ modules (R.obj i)) (fun i ↦ ModuleCat.{r} (A.obj i))
      (fun i ↦ sections s (R.obj i) (A.obj i) (lam i))
      (@md_E) (fun f ↦ ModuleCat.extendScalars (A.map f).hom)
      (@md_theta) (@md_u) (@md_a) (@md_p10) (@md_p12)
      f g h (K.X q) (v.f q) hq
  refine ⟨heq, ?_⟩
  intro q n b c d
  rw [heq]
  exact cochain_triple_value s R A lam (@E) (@e) (@add) (@theta) (@a)
    (fun {_ _} f K q n b ↦ md_p1 f (K.X q) n b)
      (fun {_ _ _} f g N q n b c ↦ md_p4 f g (N.X q) n b c) f g h K q n b c d

end ProofConstruction
end CategoryTheory.SectionsScalarCochain
