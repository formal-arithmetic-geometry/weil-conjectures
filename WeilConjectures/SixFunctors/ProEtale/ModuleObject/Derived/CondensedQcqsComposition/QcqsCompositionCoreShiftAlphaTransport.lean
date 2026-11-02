/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.QcqsCompatibleTriangle
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
import Mathlib.AlgebraicGeometry.Noetherian

/-! Shift compatibility of the normalized compositor is invariant under comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private def restrictComparison
    {B E : Type*} [Category B] [Category E] [HasShift B ℤ] [HasShift E ℤ]
    (P : ObjectProperty E) [P.IsStableUnderShift ℤ]
    (F G : B ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (e : F ≅ G) :
    P.lift F hF ≅ P.lift G hG :=
  NatIso.ofComponents (fun K ↦ P.isoMk (e.app K))
    (fun f ↦ P.hom_ext (e.hom.naturality f))

private theorem restrictComparison_commShift
    {B E : Type*} [Category B] [Category E] [HasShift B ℤ] [HasShift E ℤ]
    (P : ObjectProperty E) [P.IsStableUnderShift ℤ]
    (F G : B ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (e : F ≅ G)
    [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (restrictComparison P F G hF hG e).hom ℤ := by
  have he : Functor.whiskerRight (restrictComparison P F G hF hG e).hom P.ι =
      (P.liftCompιIso F hF).hom ≫ e.hom ≫ (P.liftCompιIso G hG).inv := by
    ext K
    simp [restrictComparison, ObjectProperty.liftCompιIso]
  have : NatTrans.CommShift
      (Functor.whiskerRight (restrictComparison P F G hF hG e).hom P.ι) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ P.ι

-- Preserve the original names of the two universally quantified proof hypotheses.
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- Elaborating the native derived comparison functors needs this allowance.
/-- Abstract transport of shift compatibility from a normalized tower to arbitrary
compactifications through the comparison cocycle. Choose any compatible triangle
for the two geometric morphisms. `A.independent` rewrites the arbitrary alpha
component as the tower component conjugated by the three comparison components.
Apply `hComparison` to those components, `hTower` to the normalized tower, and
`NatTrans.CommShift.of_iso_inv` to inverse comparison maps; composition and
whiskering then give the desired square. The finite-field and separated finite-type
context ensures the required compatible triangle exists. Source: the
cocycle and common-refinement part of Stacks Tag 0F7J.
(blueprint: new-m5-qcqs-composition-core-shift-alpha-transport). -/
theorem qcqsCompositionCoreShiftAlphaTransport (ℓ : ℕ) [Fact ℓ.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    ∀ (hTower : ∀ (T : Compactification.Triangle (modelMap D h₀) (modelMap D g₀))
      [QuasiCompact (T.cf.g ≫ T.cg.i)] [QuasiCompact T.cf.i] [QuasiCompact T.cg.i],
      NatTrans.CommShift (A.alpha T.cf T.cg T.cfg).hom ℤ)
      (hComparison :
        (∀ c d : Compactification (modelMap D h₀),
          NatTrans.CommShift (A.sh.comparison c d).hom ℤ) ∧
        (∀ c d : Compactification (modelMap D g₀),
          NatTrans.CommShift (A.sg.comparison c d).hom ℤ) ∧
        (∀ c d : Compactification (modelMap D h₀ ≫ modelMap D g₀),
          NatTrans.CommShift (A.sgh.comparison c d).hom ℤ)),
      ∀ (c : Compactification (modelMap D h₀))
        (d : Compactification (modelMap D g₀))
        (e : Compactification (modelMap D h₀ ≫ modelMap D g₀)),
        NatTrans.CommShift (A.alpha c d e).hom ℤ := by
  intro hTower hComparison c d e
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hxft : LocallyOfFiniteType ((Over.pullback t).obj X₀).hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) t X₀ inferInstance
  have hzft : LocallyOfFiniteType ((Over.pullback t).obj Z₀).hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) t Z₀ inferInstance
  have hxqc : QuasiCompact ((Over.pullback t).obj X₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiCompact) t X₀ inferInstance
  have hzqc : QuasiCompact ((Over.pullback t).obj Z₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiCompact) t Z₀ inferInstance
  have : IsLocallyNoetherian ((Over.pullback t).obj X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback t).obj X₀).hom
  have : IsLocallyNoetherian ((Over.pullback t).obj Z₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback t).obj Z₀).hom
  have : CompactSpace ((Over.pullback t).obj X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback t).obj X₀).hom
  have : CompactSpace ((Over.pullback t).obj Z₀).left :=
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback t).obj Z₀).hom
  have : IsNoetherian ((Over.pullback t).obj X₀).left := ⟨⟩
  have : IsNoetherian ((Over.pullback t).obj Z₀).left := ⟨⟩
  obtain ⟨T⟩ := qcqsCompatibleTriangleExists ℓ D hℓ h₀ g₀
  have : IsLocallyNoetherian T.cf.Z := LocallyOfFiniteType.isLocallyNoetherian T.cf.g
  have : CompactSpace T.cf.Z := QuasiCompact.compactSpace_of_compactSpace T.cf.g
  have : IsNoetherian T.cf.Z := ⟨⟩
  have ht : NatTrans.CommShift (A.alpha T.cf T.cg T.cfg).hom ℤ := hTower T
  have hh : NatTrans.CommShift (A.sh.comparison c T.cf).hom ℤ := hComparison.1 c T.cf
  have hg : NatTrans.CommShift (A.sg.comparison d T.cg).hom ℤ := hComparison.2.1 d T.cg
  have he : NatTrans.CommShift (A.sgh.comparison e T.cfg).hom ℤ :=
    hComparison.2.2 e T.cfg
  let ch := restrictComparison _ _ _ (A.sh.preserves c) (A.sh.preserves T.cf)
    (A.sh.comparison c T.cf)
  let cg := restrictComparison _ _ _ (A.sg.preserves d) (A.sg.preserves T.cg)
    (A.sg.comparison d T.cg)
  let ce := restrictComparison _ _ _ (A.sgh.preserves e) (A.sgh.preserves T.cfg)
    (A.sgh.comparison e T.cfg)
  have : NatTrans.CommShift ch.hom ℤ := restrictComparison_commShift _ _ _ _ _ _
  have : NatTrans.CommShift cg.hom ℤ := restrictComparison_commShift _ _ _ _ _ _
  have : NatTrans.CommShift ce.hom ℤ := restrictComparison_commShift _ _ _ _ _ _
  have htransport : (A.alpha c d e).hom =
      Functor.whiskerRight ch.hom (A.sg.support ℓ d) ≫
        Functor.whiskerLeft (A.sh.support ℓ T.cf) cg.hom ≫
          (A.alpha T.cf T.cg T.cfg).hom ≫ ce.inv := by
    ext K
    have hi := A.independent c T.cf d T.cg e T.cfg K
    apply (cancel_mono ((A.sgh.comparison e T.cfg).hom.app K)).1
    simpa [ch, cg, ce, restrictComparison, Category.assoc] using hi
  rw [htransport]
  infer_instance
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
