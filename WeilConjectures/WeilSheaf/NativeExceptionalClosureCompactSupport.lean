/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeExceptionalForgetfulData
public import WeilConjectures.WeilSheaf.NativeOpenProperForgetting
public import WeilConjectures.AlgebraicGeometry.LocallyFiniteAdicCompactSupportData
import WeilConjectures.WeilSheaf.NativeExceptionalCompactSupportRealization
import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapCongr

/-! # Closure transport for ordinary native compact support

Source: the closure-transport and refinement step of
cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

private theorem pullback_transport_naturality
    {A B S T T' : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    (f : A ⟶ B) (hf : f ≫ b = a) (s : T ⟶ S) (s' : T' ⟶ S)
    (t : T ⟶ T') (ht : t ≫ s' = s) :
    pullback.map a s b s f (𝟙 T) (𝟙 S) (by simpa using hf.symm) (by simp) ≫
        pullback.map b s b s' (𝟙 B) t (𝟙 S) (by simp) (by simpa using ht.symm) =
      pullback.map a s a s' (𝟙 A) t (𝟙 S) (by simp) (by simpa using ht.symm) ≫
        pullback.map a s' b s' f (𝟙 T') (𝟙 S) (by simpa using hf.symm) (by simp) := by
  apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]

private theorem closure_naturality (X Y : Space D) (f₀ : X.base ⟶ Y.base) :
    Scheme.Hom.geometricFiberMap f₀.left (comp_over f₀.left _) ≫ closureMap D Y =
      closureMap D X ≫ geometricMap D f₀ := by
  let s := (Scheme.specAlgebraicClosure D.k₀).hom
  let s' := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let t := Spec.map (CommRingCat.ofHom
    (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingHom)
  have ht : t ≫ s' = s := by
    dsimp only [s, s', t]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).commutes x
  have h := pullback_transport_naturality X.base.hom Y.base.hom f₀.left
    (Over.w f₀) s s' t ht
  exact h

private def open_transport {A B Z : Scheme.{u}} (e : A ≅ B)
    (i : A ⟶ Z) [IsOpenImmersion i] :
    ProEtale.adicOpenImmersionLowerShriek l i ≅
      ProEtale.adicLowerStar l e.hom ⋙
        ProEtale.adicOpenImmersionLowerShriek l (e.inv ≫ i) := by
  let j := e.inv ≫ i
  let adj := (ProEtale.adicLowerStarEquivalence l e).toAdjunction.comp
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l j)
  let q : ProEtale.adicUpperStar l i ≅
      ProEtale.adicUpperStar l j ⋙ ProEtale.adicLowerStar l e.inv :=
    ProEtale.adicUpperStarCongr l (by simp [j]) ≪≫
      ProEtale.adicUpperStarComp l e.hom j ≪≫
      Functor.isoWhiskerLeft _ (ProEtale.adicUpperStarIsoLowerStarInv l e)
  exact ((conjugateIsoEquiv
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l i) adj).symm q).symm

private def compact_transport {A B Z Y Y' : Scheme.{u}} (e : A ≅ B) (t : Y ≅ Y')
    (i : A ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y) :
    (ProEtale.adicOpenImmersionLowerShriek l i).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar l p).rightDerivedFunctor ⋙
          (ProEtale.adicLowerStar l t.hom).rightDerivedFunctor ≅
      (ProEtale.adicLowerStar l e.hom).rightDerivedFunctor ⋙
        (ProEtale.adicOpenImmersionLowerShriek l (e.inv ≫ i)).mapDerivedCategory ⋙
          (ProEtale.adicLowerStar l (p ≫ t.hom)).rightDerivedFunctor := by
  let q : (ProEtale.adicLowerStar l p).rightDerivedFunctor ⋙
        (ProEtale.adicLowerStar l t.hom).rightDerivedFunctor ≅
      (ProEtale.adicLowerStar l (p ≫ t.hom)).rightDerivedFunctor :=
    Functor.isoWhiskerLeft _
        (ProEtale.adicLowerStar l t.hom).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtale.adicLowerStarComp l p t.hom)
  let a := Functor.mapDerivedCategoryNatIso (open_transport l e i) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (ProEtale.adicLowerStar l e.hom).rightDerivedFunctorIsoMapDerivedCategory.symm _
  exact Functor.isoWhiskerLeft _ q ≪≫ Functor.isoWhiskerRight a _

private theorem compactification_comparison (R : Family l D)
    (X Y : Space D) (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀)
    (c d : Compactification (geometricMap D f₀)) :
    Nonempty
      ((ProEtale.DerivedCategory.boundedAdicConstructible l
          (geometric D X).base.left).ι ⋙ LocallyFiniteAdicCompactSupport.actual l c ≅
       (ProEtale.DerivedCategory.boundedAdicConstructible l
          (geometric D X).base.left).ι ⋙ LocallyFiniteAdicCompactSupport.actual l d) := by
  classical
  let J := (R.data (geometric D X)).realization.J
  let ff : J.FullyFaithful := Classical.choice
    ((Functor.FullyFaithful.nonempty_iff_map_bijective J).mpr
      (R.data (geometric D X)).realization.fully_faithful)
  let := ff.full
  let := ff.faithful
  let I := (ProEtale.DerivedCategory.boundedAdicConstructible l
    (geometric D X).base.left).ι
  have hI (K : (ProEtale.DerivedCategory.boundedAdicConstructible l
      (geometric D X).base.left).FullSubcategory) : J.essImage (I.obj K) :=
    ((R.data (geometric D X)).realization.image K.obj).mp K.property
  let H := Functor.essImage.liftFunctor I J hI
  let q : H ⋙ J ≅ I := Functor.essImage.liftFunctorCompIso I J hI
  obtain ⟨r, ⟨rc⟩, ⟨rd⟩⟩ := Compactification.exists_common_refinement c d
  let a := (S.refinements.refinement rc .closed).left.symm ≪≫
    (S.refinements.refinement rd .closed).left
  obtain ⟨ac⟩ := LocallyFiniteAdicCompactSupport.system_compact_support_realization
    l D (Fact.out : l ≠ D.p) (X := (geometric D X).base.left)
      (Y := (geometric D Y).base.left) (geometricMap D f₀)
      (R.data (geometric D X)).realization (R.data (geometric D Y)).realization S c
  obtain ⟨ad⟩ := LocallyFiniteAdicCompactSupport.system_compact_support_realization
    l D (Fact.out : l ≠ D.p) (X := (geometric D X).base.left)
      (Y := (geometric D Y).base.left) (geometricMap D f₀)
      (R.data (geometric D X)).realization (R.data (geometric D Y)).realization S d
  exact ⟨Functor.isoWhiskerRight q.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft H ac.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H a) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H ad ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight q _⟩

/-- Ordinary compact support commutes with the specified change of algebraic closure
on the full bounded constructible native category.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence; ordinary comparison, closure-transport step.
(blueprint: lem-sf-native-exceptional-closure-compact-support).

Proof: closureMap at X and Y are scheme isomorphisms; their naturality square
with f₀ commutes by the two pullback projections. Write i and p for the geometric
open and proper legs of c₀. Keep its middle scheme and form a compactification d
with open leg (closureMap X)⁻¹ followed by i and proper leg p followed by
closureMap Y. Transporting open extension along the source equivalence is the
isomorphism of left adjoints induced by the pullback compositor. The proper
comparison is the total-right-derived pushforward compositor, with the exact
closure equivalence on the right. These give the required comparison with d.
Exact inverse pullback shows that the source closure transport preserves bounded
constructibility. Choose a normalized realization family and one coefficient
system for the geometric map. The scalar-realization theorem compares the actual
functors for d and c with that system's left operations. A common refinement and
the system's two refinement isomorphisms compare those left operations. Lift the
bounded source inclusion through its fully faithful realization using the image
clause, whisker the scalar and refinement isomorphisms with this lift, and cancel
its realization isomorphism. This compares actual d and actual c on the full
bounded constructible category. Compose with the first transport. The argument
uses no exceptional native adjoint or Weil action, and its units cover zero
objects, empty schemes and identity maps. -/
theorem native_exceptional_closure_compact_support
    (X Y : Space D) (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) (c : Compactification (geometricMap D f₀)) :
    Nonempty
      ((ProEtale.DerivedCategory.boundedAdicConstructible l
          X.base.hom.geometricFiber).ι ⋙
        NativeWeilOpenProper.ordinaryCompactSupport (k₀ := D.k₀) (l := l) f₀.left c₀ ⋙
          (ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ≅
       (ProEtale.DerivedCategory.boundedAdicConstructible l
          X.base.hom.geometricFiber).ι ⋙
        (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
          LocallyFiniteAdicCompactSupport.actual l c) := by
  classical
  let e := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have hx : IsIso (closureMap D X) := by
    dsimp only [closureMap]
    infer_instance
  have hy : IsIso (closureMap D Y) := by
    dsimp only [closureMap]
    infer_instance
  let := c₀.over (k₀ := D.k₀)
  let i := Scheme.Hom.geometricFiberMap c₀.i (comp_over c₀.i (Spec (.of D.k₀)))
  let p := Scheme.Hom.geometricFiberMap c₀.g (comp_over c₀.g (Spec (.of D.k₀)))
  have hp : IsProper p := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
    (P := @IsProper) c₀.g (comp_over c₀.g _) inferInstance
  have hi : IsOpenImmersion i := inferInstance
  have hn := closure_naturality D X Y f₀
  let d : Compactification (X := (geometric D X).base.left)
      (Y := (geometric D Y).base.left) (geometricMap D f₀) :=
    { Z := (c₀.Z ↘ Spec (.of D.k₀)).geometricFiber
      i := inv (closureMap D X) ≫ i
      g := p ≫ closureMap D Y
      comm := by
        change geometricMap D f₀ = (inv (closureMap D X) ≫ i) ≫ (p ≫ closureMap D Y)
        symm
        rw [Category.assoc, ← Category.assoc i p]
        have hip : i ≫ p = Scheme.Hom.geometricFiberMap f₀.left
            (comp_over f₀.left _) := by
          dsimp only [i, p]
          rw [← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr c₀.comm.symm _ _
        rw [hip, hn]
        simp
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let P := ProEtale.DerivedCategory.boundedAdicConstructible l X.base.hom.geometricFiber
  let Q := ProEtale.DerivedCategory.boundedAdicConstructible l (geometric D X).base.left
  let CX := (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor
  have hCX (K : P.FullSubcategory) : Q (CX.obj K.obj) := by
    have hPull := ProEtale.bounded_homologyProperty_mapDerivedCategory_adicUpperStar
      (inv (closureMap D X)) K.property.1 K.property.2
    let push := ProEtale.adicLowerStar l (closureMap D X)
    let transport := push.rightDerivedFunctorIsoMapDerivedCategory.app K.obj ≪≫
      (Functor.mapDerivedCategoryNatIso
        (ProEtale.adicUpperStarIsoLowerStarInv l (asIso (closureMap D X)).symm).symm).app
          K.obj
    let : Q.IsClosedUnderIsomorphisms := by
      dsimp [Q, ProEtale.DerivedCategory.boundedAdicConstructible]
      infer_instance
    exact Q.prop_of_iso transport.symm hPull
  let V : P.FullSubcategory ⥤ Q.FullSubcategory :=
    P.liftFullSubcategory Q CX (fun K hK ↦ hCX ⟨K, hK⟩)
  obtain ⟨R⟩ := adic_qbar_constructible_realization D l (Fact.out : l ≠ D.p)
  obtain ⟨S⟩ := ConstructibleExceptionalCoefficients.exists_system.{u, 0}
    l (PadicAlgCl l) D (Fact.out : l ≠ D.p)
      (X := (geometric D X).base.left) (Y := (geometric D Y).base.left) (geometricMap D f₀)
  obtain ⟨a⟩ := compactification_comparison D l R X Y f₀ S d c
  let b := compact_transport l (asIso (closureMap D X)) (asIso (closureMap D Y)) i p
  exact ⟨Functor.isoWhiskerLeft P.ι b ≪≫ Functor.isoWhiskerLeft V a⟩

end WeilConjectures.NativeExceptionalForgetful
