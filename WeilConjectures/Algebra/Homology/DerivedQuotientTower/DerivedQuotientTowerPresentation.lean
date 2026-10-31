/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian

/-! # Universal derived quotient towers

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion), for the
ordinary reduction tower; sites-cohomology.tex, Tags 06YT and 06YS, and derived.tex,
Tag 06XN (dual assertion), for its universal K-flat homotopy presentation.
(blueprint: lem-weil-pbc-derived-quotient-tower-presentation).

The input maps are arbitrary compatible maps of commutative ring sheaves. The
augmentation is specified before deriving, by the sheafification image of `1 ⊗ m`.
Natural-number level `n` denotes the positive level `n+1` in the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r wA wT

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.DerivedQuotientTower

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The recorded category of modules over a commutative ring sheaf, forgetting
commutativity only. Source: Stacks 03EK
(blueprint: lem-weil-pbc-derived-quotient-tower-presentation). -/
abbrev Mod (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Ordinary scalar extension with the original scalar action retained.
Source: Stacks 03EK, 06YY
(blueprint: lem-weil-pbc-derived-quotient-tower-presentation). -/
abbrev reductionObj {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
    (changeOfRings q M)

/-- The actual local pure tensor in ordinary scalar extension, including the
sheafification unit. Source: Stacks 03EK, 06YY
(blueprint: lem-weil-pbc-derived-quotient-tower-presentation). -/
def tensorSection {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (reductionObj q M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (changeOfRingsPresheaf q M)).app U
        (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] m)

open MonoidalCategory

private abbrev ring (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

private abbrev coeff {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) : Mod R :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
    (unit (ring S))

private abbrev pre {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :=
  (PresheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).obj
      (changeOfRingsPresheaf q M)

private def preUnit {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    pre q M ⟶ (reductionObj q M).val :=
  (PresheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).unit.app
        (changeOfRingsPresheaf q M))

private instance preUnit_injective {R S : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (M : Mod R) : PresheafOfModules.IsLocallyInjective J (preUnit q M) := by
  change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J _)
  infer_instance

private instance preUnit_surjective {R S : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (M : Mod R) : PresheafOfModules.IsLocallySurjective J (preUnit q M) := by
  change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J _)
  infer_instance

private def lift {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M N : Mod R)
    (a : pre q M ⟶ N.val) : reductionObj q M ⟶ N :=
  ⟨(PresheafOfModules.homEquivOfIsLocallyBijective (preUnit q M) N.isSheaf).symm a⟩

omit [EssentiallySmall.{r} C] in
private theorem lift_fac {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M N : Mod R)
    (a : pre q M ⟶ N.val) : preUnit q M ≫ (lift q M N a).val = a :=
  (PresheafOfModules.homEquivOfIsLocallyBijective
    (preUnit q M) N.isSheaf).apply_symm_apply a

omit [EssentiallySmall.{r} C] in
private theorem reduction_ext {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (M N : Mod R) (f g : reductionObj q M ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U),
      f.val.app U (tensorSection q M U s m) =
        g.val.app U (tensorSection q M U s m)) : f = g := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (preUnit q M) N.isSheaf).injective
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => exact h U s m
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
private def coeffMap {R S S' : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (q' : R ⟶ S') (t : S' ⟶ S) (h : q' ≫ t = q) :
    coeff q' ⟶ coeff q where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (coeff q').val.obj U) (Y := (coeff q).val.obj U)
        { toFun := t.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro a s
            change t.hom.app U (q'.hom.app U a * (show S'.obj.obj U from s)) =
              q.hom.app U a * t.hom.app U (show S'.obj.obj U from s)
            rw [map_mul]
            have hh := congrArg (fun f : R ⟶ S ↦ f.hom.app U a) h
            exact congrArg (· * t.hom.app U s) hh }
      naturality := by
        intro U V i
        ext s
        exact ConcreteCategory.congr_hom (t.hom.naturality i) s }

set_option backward.isDefEq.respectTransparency false in
private def transition {R S S' : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (q' : R ⟶ S') (t : S' ⟶ S) (h : q' ≫ t = q)
    (M : Mod R) : reductionObj q' M ⟶ reductionObj q M :=
  lift q' M (reductionObj q M)
    ((presheafTensorIso q' M).hom ≫
      (coeffMap q q' t h).val ▷ M.val ≫
      (presheafTensorIso q M).inv ≫ preUnit q M)

private theorem transition_tensor {R S S' : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (q' : R ⟶ S') (t : S' ⟶ S) (h : q' ≫ t = q)
    (M : Mod R) (U : Cᵒᵖ) (s : S'.obj.obj U) (m : M.val.obj U) :
    (transition q q' t h M).val.app U (tensorSection q' M U s m) =
      tensorSection q M U (t.hom.app U s) m := by
  have hh := congrArg (fun f : pre q' M ⟶ (reductionObj q M).val ↦
    f.app U (s ⊗ₜ[R.obj.obj U, (q'.hom.app U).hom] m))
      (lift_fac q' M (reductionObj q M)
        ((presheafTensorIso q' M).hom ≫
          (coeffMap q q' t h).val ▷ M.val ≫
          (presheafTensorIso q M).inv ≫ preUnit q M))
  exact hh

private def extensionPre {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) :
    Mod R ⥤ PresheafOfModules.{r} (ring S).obj where
  obj := changeOfRingsPresheaf q
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (q.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality q _ f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    simp

private def extension {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) : Mod R ⥤ Mod S :=
  extensionPre q ⋙ PresheafOfModules.sheafification (𝟙 (ring S).obj)

private instance extension_additive {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) :
    (extension q).Additive := by
  have hscalar (U : Cᵒᵖ) : (ModuleCat.extendScalars (q.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (q.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification (𝟙 (ring S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).left_adjoint_additive
  have : (extensionPre q).Additive := by
    constructor
    intro M N f g
    ext U : 1
    exact (ModuleCat.extendScalars (q.hom.app U).hom).map_add (f := f.val.app U) (g := g.val.app U)
  exact inferInstanceAs ((extensionPre q) ⋙
    PresheafOfModules.sheafification (𝟙 (ring S).obj)).Additive

private def level {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) : Mod R ⥤ Mod R :=
  extension q ⋙ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)

private instance level_additive {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) :
    (level q).Additive := inferInstanceAs
  (extension q ⋙ restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).Additive

omit [EssentiallySmall.{r} C] in
private theorem level_tensor {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((level q).map f).val.app U (tensorSection q M U s m) =
      tensorSection q N U s (f.val.app U m) := by
  have hh := congrArg (fun g ↦ g.app U
    (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] m))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).unit.naturality
      ((extensionPre q).map f))
  change tensorSection q N U s (f.val.app U m) = _ at hh
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
private def oneTensor {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M.val ⟶ pre q M where
  app U := ModuleCat.ExtendRestrictScalarsAdj.Unit.map
    (q.hom.app U).hom (X := M.val.obj U)
  naturality := by
    intro U V i
    ext m
    change (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (q.hom.app V).hom] M.val.map i m =
      changeOfRingsMap q M i ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] m)
    rw [show changeOfRingsMap q M i _ = _ from
      Classical.choose_spec (exists_changeOfRingsMap q M i) 1 m, map_one]

private def ordinaryUnit {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M ⟶ reductionObj q M := ⟨oneTensor q M ≫ preUnit q M⟩

omit [EssentiallySmall.{r} C] in
private theorem ordinaryUnit_tensor {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U) :
    (ordinaryUnit q M).val.app U m = tensorSection q M U 1 m := rfl

private theorem transition_natural {R S S' : Sheaf J CommRingCat.{r}}
    (q : R ⟶ S) (q' : R ⟶ S') (t : S' ⟶ S) (h : q' ≫ t = q)
    {M N : Mod R} (f : M ⟶ N) :
    (level q').map f ≫ transition q q' t h N =
      transition q q' t h M ≫ (level q).map f := by
  apply reduction_ext q' M (reductionObj q N)
  intro U s m
  change (transition q q' t h N).val.app U
    (((level q').map f).val.app U (tensorSection q' M U s m)) =
      ((level q).map f).val.app U
        ((transition q q' t h M).val.app U (tensorSection q' M U s m))
  rw [level_tensor, transition_tensor, transition_tensor, level_tensor]

private def tower {R : Sheaf J CommRingCat.{r}}
    (S : ℕ → Sheaf J CommRingCat.{r}) (q : ∀ n : ℕ, R ⟶ S n)
    (t : ∀ n : ℕ, S (n + 1) ⟶ S n)
    (hq : ∀ n : ℕ, q (n + 1) ≫ t n = q n) : Mod R ⥤ (ℕᵒᵖ ⥤ Mod R) where
  obj M := Functor.ofOpSequence (X := fun n ↦ reductionObj (q n) M)
    (fun n ↦ transition (q n) (q (n + 1)) (t n) (hq n) M)
  map {M N} f := NatTrans.ofOpSequence (F := Functor.ofOpSequence
    (X := fun n ↦ reductionObj (q n) M)
    (fun n ↦ transition (q n) (q (n + 1)) (t n) (hq n) M))
    (G := Functor.ofOpSequence (X := fun n ↦ reductionObj (q n) N)
      (fun n ↦ transition (q n) (q (n + 1)) (t n) (hq n) N)) (fun n ↦ (level (q n)).map f) (by
    intro n
    simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
      (transition_natural (q n) (q (n + 1)) (t n) (hq n) f).symm)
  map_id M := by
    apply NatTrans.ext
    funext n
    exact (level (q n.unop)).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (level (q n.unop)).map_comp f g

private instance tower_additive {R : Sheaf J CommRingCat.{r}}
    (S : ℕ → Sheaf J CommRingCat.{r}) (q : ∀ n : ℕ, R ⟶ S n)
    (t : ∀ n : ℕ, S (n + 1) ⟶ S n)
    (hq : ∀ n : ℕ, q (n + 1) ≫ t n = q n) : (tower S q t hq).Additive where
  map_add {M N} {f g} := by
    apply NatTrans.ext
    funext n
    exact (level (q n.unop)).map_add (f := f) (g := g)

private def augmentation {R : Sheaf J CommRingCat.{r}}
    (S : ℕ → Sheaf J CommRingCat.{r}) (q : ∀ n : ℕ, R ⟶ S n)
    (t : ∀ n : ℕ, S (n + 1) ⟶ S n)
    (hq : ∀ n : ℕ, q (n + 1) ≫ t n = q n) :
    Functor.const ℕᵒᵖ ⟶ tower S q t hq where
  app M := NatTrans.ofOpSequence (fun n ↦ ordinaryUnit (q n) M) (by
    intro n
    simp only [Functor.const_obj_map, tower,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply SheafOfModules.hom_ext
    ext U m
    change tensorSection (q n) M U 1 m =
      (transition (q n) (q (n + 1)) (t n) (hq n) M).val.app U
        (tensorSection (q (n + 1)) M U 1 m)
    rw [transition_tensor, map_one])
  naturality {M N} f := by
    apply NatTrans.ext
    funext n
    apply SheafOfModules.hom_ext
    ext U m
    change tensorSection (q n.unop) N U 1 (f.val.app U m) =
      ((level (q n.unop)).map f).val.app U
        (tensorSection (q n.unop) M U 1 m)
    rw [level_tensor]

private theorem level_inverts {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    {P P' : CochainComplex (Mod R) ℤ} (f : P ⟶ P')
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P') (hf : QuasiIso f) :
    QuasiIso (((level q).mapHomologicalComplex (.up ℤ)).map f) := by
  have he : QuasiIso (((extension q).mapHomologicalComplex (.up ℤ)).map f) :=
    derivedChangeOfRingsIndependentCoefficients_kflat_invariance q (extension q)
      (fun _ ↦ rfl) (by intros; simp [extension, extensionPre, changeOfRingsHom])
      f hP hP' hf
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((level q).mapHomologicalComplex (.up ℤ)).map f) (toSheaf.{r} (ring R))).mp
  change QuasiIso (((toSheaf.{r} (ring S)).mapHomologicalComplex (.up ℤ)).map
    (((extension q).mapHomologicalComplex (.up ℤ)).map f))
  infer_instance

variable (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{wA} (Mod R)]
  [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ Mod R)]

private theorem derived_exists
    (T : Mod R ⥤ (ℕᵒᵖ ⥤ Mod R)) [T.Additive]
    (hinv : ∀ {P P' : CochainComplex (Mod R) ℤ} (f : P ⟶ P'),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P' → QuasiIso f →
        QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (LT : DerivedCategory (Mod R) ⥤ DerivedCategory (ℕᵒᵖ ⥤ Mod R))
      (ε : DerivedCategory.Qh ⋙ LT ⟶
        T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      (∀ (G : DerivedCategory (Mod R) ⥤ DerivedCategory (ℕᵒᵖ ⥤ Mod R))
          (a : DerivedCategory.Qh ⋙ G ⟶
            T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
        ∃! b : G ⟶ LT, Functor.whiskerLeft DerivedCategory.Qh b ≫ ε = a) ∧
      ∀ P : CochainComplex (Mod R) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient (Mod R) (.up ℤ)).obj P)) := by
  classical
  let Q := HomotopyCategory.quotient (Mod R) (.up ℤ)
  let F := T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let good : Set (HomotopyCategory (Mod R) (.up ℤ)) := fun X ↦
    ∃ P : CochainComplex (Mod R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧ Q.obj P = X
  have hres : ∀ X : HomotopyCategory (Mod R) (.up ℤ),
      ∃ (Y : HomotopyCategory (Mod R) (.up ℤ)) (s : Y ⟶ X),
        Y ∈ good ∧ HomotopyCategory.quasiIso (Mod R) (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    exact ⟨Q.obj P, Q.map p, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hinverts : ∀ (X Y : HomotopyCategory (Mod R) (.up ℤ)) (s : X ⟶ Y),
      X ∈ good → Y ∈ good → HomotopyCategory.quasiIso (Mod R) (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X Y s ⟨P, hP, rfl⟩ ⟨P', hP', rfl⟩ hs
    obtain ⟨f, rfl⟩ := Q.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hinv f hP hP' hf
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨_, LT, ε, huniv, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass (Mod R) (DerivedCategory (ℕᵒᵖ ⥤ Mod R))
      F good hres hinverts
  let := huniv
  refine ⟨LT, ε, ?_, fun P hP ↦ hcomp _ ⟨P, hP, rfl⟩⟩
  intro G a
  refine ⟨LT.leftDerivedLift ε (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) G a,
    LT.leftDerived_fac ε _ G a, ?_⟩
  intro b hb
  apply LT.leftDerived_ext ε (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) G
  rw [hb, LT.leftDerived_fac]

/-- The strict ordinary tensor tower, its specified scalar-unit augmentation and
its universal left derived presentation on the homotopy category.

Source: proetale.tex, Tag 099M (ordinary reduction tower); sites-cohomology.tex,
Tags 06YT and 06YS; derived.tex, Tags 06XN (dual) and 05S9.
(blueprint: lem-weil-pbc-derived-quotient-tower-presentation).

Proof:
1. Sheafify the balanced section maps `s ⊗ m ↦ t(s) ⊗ m`. Compatibility of the
ring maps makes these linear over R. The sheafified maps `id ⊗ f` form an additive
functor to strict towers. The maps `m ↦ 1 ⊗ m` commute with restrictions, module
maps and transitions because each ring transition preserves 1. They give the
ordinary augmentation. This uses def-pur-sheaf-tensor-product,
def-pc-sheaf-restrict-scalars and def-weil-inverse-system.
2. Kernels, cokernels and cohomology of strict towers are componentwise, so a
quasi-isomorphism is precisely a componentwise quasi-isomorphism. Restriction of
scalars retains the underlying abelian sheaf and hence cohomology.
3. At each level, use the independent-coefficient K-flat invariance helper of
lem-pur-derived-change-of-rings for the arbitrary ring map q_n. It shows that
scalar extension preserves quasi-isomorphisms between K-flat complexes. Restrict
scalars and apply step 2. No flat-term condition or flatness of q_n is needed.
4. Additivity preserves homotopy equations, shifts and the cone differential
matrix (Td, Ta; 0, -Td), including the cone inclusion and negative projection.
Consequently termwise T followed by derived localization is exact on the
homotopy category (def-weil-abstract-derived-category).
5. By lem-pc-kflat-resolution every complex has a K-flat quasi-isomorphic
resolution. Step 3 and this resolution property meet the hypotheses of
lem-pur-left-derived-from-kflat-class for the class of all K-flat complexes.
That theorem constructs LT and its universal counit, invertible on each K-flat
complex. Expanding the right Kan property gives the displayed unique lift of
every a. The augmentation remains the ordinary transformation of step 1. -/
theorem exists_presentation
    (S : ℕ → Sheaf J CommRingCat.{r}) (q : ∀ n : ℕ, R ⟶ S n)
    (t : ∀ n : ℕ, S (n + 1) ⟶ S n)
    (hq : ∀ n : ℕ, q (n + 1) ≫ t n = q n) :
    ∃ (T : Mod R ⥤ (ℕᵒᵖ ⥤ Mod R))
      (hobj : ∀ (M : Mod R) (n : ℕ), (T.obj M).obj (op n) = reductionObj (q n) M)
      (_ : T.Additive) (η : Functor.const ℕᵒᵖ ⟶ T),
      (∀ (M N : Mod R) (f : M ⟶ N) (n : ℕ),
        (T.map f).app (op n) = eqToHom (hobj M n) ≫
          (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map (q n))).map
            (changeOfRingsHom (q n) M f) ≫ eqToHom (hobj N n).symm) ∧
      (∀ (M : Mod R) (n : ℕ) (U : Cᵒᵖ) (s : (S (n + 1)).obj.obj U)
          (m : M.val.obj U),
        (eqToHom (hobj M (n + 1)).symm ≫
          (T.obj M).map (homOfLE (Nat.le_succ n)).op ≫ eqToHom (hobj M n)).val.app U
            (tensorSection (q (n + 1)) M U s m) =
          tensorSection (q n) M U ((t n).hom.app U s) m) ∧
      (∀ (M : Mod R) (n : ℕ) (U : Cᵒᵖ) (m : M.val.obj U),
        ((η.app M).app (op n) ≫ eqToHom (hobj M n)).val.app U m =
          tensorSection (q n) M U 1 m) ∧
      (∀ {P P' : CochainComplex (Mod R) ℤ} (f : P ⟶ P'),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P' → QuasiIso f →
          QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f)) ∧
      (∃ (LT : DerivedCategory (Mod R) ⥤ DerivedCategory (ℕᵒᵖ ⥤ Mod R))
          (ε : DerivedCategory.Qh ⋙ LT ⟶
            T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
        (∀ (G : DerivedCategory (Mod R) ⥤ DerivedCategory (ℕᵒᵖ ⥤ Mod R))
            (a : DerivedCategory.Qh ⋙ G ⟶
              T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
          ∃! b : G ⟶ LT, Functor.whiskerLeft DerivedCategory.Qh b ≫ ε = a) ∧
        ∀ P : CochainComplex (Mod R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
            IsIso (ε.app ((HomotopyCategory.quotient (Mod R) (.up ℤ)).obj P))) ∧
      (∀ X : CochainComplex (Mod R) ℤ,
        ∃ (P : CochainComplex (Mod R) ℤ) (f : P ⟶ X),
          CochainComplex.IsKFlatResolutionIndependentCoefficients (R := R) f) := by
  have hinv : ∀ {P P' : CochainComplex (Mod R) ℤ} (f : P ⟶ P'),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P' → QuasiIso f →
        QuasiIso (((tower S q t hq).mapHomologicalComplex (.up ℤ)).map f) := by
    intro P P' f hP hP' hf
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    exact level_inverts (q n.unop) f hP hP' hf
  refine ⟨tower S q t hq, fun _ _ ↦ rfl, inferInstance, augmentation S q t hq,
    ?_, ?_, ?_, hinv, derived_exists R (tower S q t hq) hinv, ?_⟩
  · intro M N f n
    simp [tower, level, extension, extensionPre, changeOfRingsHom]
  · intro M n U s m
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, tower,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact transition_tensor (q n) (q (n + 1)) (t n) (hq n) M U s m
  · intro M n U m
    exact ordinaryUnit_tensor (q n) M U m
  · intro X
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨P, f, hf, hP⟩

end SheafOfModules.DerivedQuotientTower
