/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Identity normalization

Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 0D6D, 0D6E and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

open CategoryTheory.MonoidalCategory in
private abbrev Site.ringSets (X : Site.{u, w}) :=
  (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).obj X.A

open CategoryTheory.MonoidalCategory in
private abbrev transpose {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T : Sheaf Y.J (Type u)} (x : T ⟶ Y.sets.obj (f.modules.obj M)) :=
  (f.adj.homEquiv T (X.sets.obj M)).symm (x ≫ f.underlying.hom.app M)

open CategoryTheory.MonoidalCategory in
private theorem transpose_injective {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) (T : Sheaf Y.J (Type u)) :
    Function.Injective (transpose f M (T := T)) := by
  intro x y h
  apply (cancel_mono (f.underlying.hom.app M)).mp
  exact (f.adj.homEquiv T (X.sets.obj M)).symm.injective h

open CategoryTheory.MonoidalCategory in
private theorem homEquiv_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : L.obj U ⟶ E) :
    a.homEquiv U E b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E =
      a'.homEquiv U E (c.inv.app U ≫ b) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let κ := conjugateIsoEquiv a a' c.symm
  change (a.unit.app U ≫ R.map b) ≫ κ.hom.app E = _
  rw [Category.assoc, κ.hom.naturality, ← Category.assoc]
  change (a.unit.app U ≫ (conjugateEquiv a a' c.inv).app (L.obj U)) ≫ _ = _
  rw [unit_conjugateEquiv, Category.assoc, ← R'.map_comp]

open CategoryTheory.MonoidalCategory in
private def liftLinear {X : Site.{u, w}} {M N : X.modules}
    (q : X.sets.obj M ⟶ X.sets.obj N)
    (ha : ∀ U (x y : M.val.obj U), q.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (q.hom.app U x) (q.hom.app U y))
    (hs : ∀ U (r : X.A.obj.obj U) (x : M.val.obj U),
      q.hom.app U (r • x) = r • (show N.val.obj U from q.hom.app U x)) : M ⟶ N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := q.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V i
        ext x
        exact CategoryTheory.congr_fun (q.hom.naturality i) x }

private def normalizedAdj {X : Site.{u, w}} {f : Morphism X X} (l : Lift f) :
    l.edge.pullback ⊣ f.modules :=
  l.edge.moduleAdjunction.ofNatIsoRight (eqToIso l.pushforward_eq)

private theorem normalized_transpose {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (M N : X.modules) (b : l.edge.pullback.obj M ⟶ N) :
    transpose f N (X.sets.map ((normalizedAdj l).homEquiv M N b)) =
      l.insertion M ≫ X.sets.map b := by
  apply (f.adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simpa only [normalizedAdj, Adjunction.homEquiv_ofNatIsoRight_apply,
    Functor.map_comp, eqToIso.hom, Functor.whiskerRight_app, Lift.insertion,
    Category.assoc] using l.ordinary_adjunction M N b

private theorem identity_mate {C : Type*} [Category C] {L R : C ⥤ C}
    (a : L ⊣ R) (e : L ≅ 𝟭 C) (M : C) :
    a.homEquiv M M (e.hom.app M) ≫
      (conjugateIsoEquiv a (Adjunction.id (C := C)) e.symm).hom.app M = 𝟙 M := by
  have h := homEquiv_conjugate a (Adjunction.id (C := C)) e M M (e.hom.app M)
  rw [Iso.inv_hom_id_app] at h
  refine h.trans ?_
  change (𝟙 M) ≫ (𝟙 M) = 𝟙 M
  exact Category.id_comp _

private def purePair {X : Site.{u, w}} (M N : X.modules)
    {T : Sheaf X.J (Type u)} (x : T ⟶ X.sets.obj M) (y : T ⟶ X.sets.obj N) :
    T ⟶ X.sets.obj ((monoidalCategory X.A).tensorObj M N) :=
  ⟨{ app := fun U ↦ ↾(fun t ↦ RingedTensor.pure X.A M N U
        (x.hom.app U t) (y.hom.app U t))
     naturality := by
       intro U V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change RingedTensor.pure X.A M N V (x.hom.app V (T.obj.map i t))
         (y.hom.app V (T.obj.map i t)) =
           ((monoidalCategory X.A).tensorObj M N).val.map i
             (RingedTensor.pure X.A M N U (x.hom.app U t) (y.hom.app U t))
       rw [hx, hy]
       exact (RingedTensor.pure_restrict X.A M N i _ _).symm }⟩

open CategoryTheory.MonoidalCategory in
private abbrev totalTensor (X : Site.{u, w}) :=
  Functor.uncurry.obj ((@curriedTensor X.modules _ (monoidalCategory X.A)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

private abbrev totalComparison {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (P Q : CochainComplex X.modules ℤ) :=
  l.edge.ordinaryTensor.totalIso X.A X.A l.edge.inverseRing l.edge.inverse
    l.edge.algebraic l.edge.ringMap l.edge.pullback l.edge.object_eq
    l.edge.pushforward l.edge.moduleAdjunction P Q

open CategoryTheory.MonoidalCategory in
-- The representative equation specializes several universe-polymorphic tensor models.
private theorem unit_of_tensor
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (c : F ≅ G)
    (h : ∀ U V, c.hom.app (U ⊗ V) ≫ Functor.OplaxMonoidal.δ G U V =
      Functor.OplaxMonoidal.δ F U V ≫ (c.hom.app U ⊗ₘ c.hom.app V)) :
    c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  have hh := c.hom.naturality (λ_ (𝟙_ C)).hom
  rw [← Functor.OplaxMonoidal.left_unitality_hom F,
    ← Functor.OplaxMonoidal.left_unitality_hom G] at hh
  simp only [Category.assoc] at hh
  rw [← Category.assoc (c.hom.app _), h, Category.assoc] at hh
  rw [← leftUnitor_naturality] at hh
  simp only [← tensorHom_id, ← id_tensorHom] at hh
  have hh' := (cancel_epi (Functor.OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C))).mp hh
  simp only [← Category.assoc] at hh'
  have hh'' := (cancel_mono (λ_ (G.obj (𝟙_ C))).hom).mp hh'
  have hright := congrArg (fun z ↦ z ≫ (𝟙 (𝟙_ D) ⊗ₘ c.inv.app (𝟙_ C))) hh''
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    Iso.hom_inv_id_app] at hright
  let : (tensorRight (𝟙_ D)).Faithful :=
    Functor.Faithful.of_iso (rightUnitorNatIso D).symm
  let : (tensorRight (F.obj (𝟙_ C))).Faithful :=
    Functor.Faithful.of_iso ((curriedTensor D).flip.mapIso
      (Functor.Monoidal.εIso F))
  apply (tensorRight (F.obj (𝟙_ C))).map_injective
  change (c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G) ▷ F.obj (𝟙_ C) =
    Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ C)
  simpa only [← tensorHom_id] using hright.symm

end CategoryTheory.RingedDerivedComparisons
