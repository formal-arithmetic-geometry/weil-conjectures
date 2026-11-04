/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackCoefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackCrossTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackFrames

/-! # Local frame atlases for realization base change
Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A common frame atlas for the two realization pullback quotients: the pulled-back source
quotient and the target quotient after the canonical pullback coherence of
`projectiveBundleThetaQuotientLaw` have, on a common cover, matching free generators with equal
transitions and equal local coefficients. -/
structure ProjectiveBundleRealizationPullbackAtlas
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data) where
  ι : Type u
  U : ι → D'.A.data.relProj.Opens
  s : ∀ i, Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L, U i)
  t : ∀ i, Γ(D'.L, U i)
  cover : ⨆ i, U i = ⊤
  s_generator : ∀ i, Scheme.Modules.IsFreeGenerator (s i)
  t_generator : ∀ i, Scheme.Modules.IsFreeGenerator (t i)
  transition : ∀ i j (V : D'.A.data.relProj.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (a c : Γ(D'.A.data.relProj, V)),
      a • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
          (homOfLE hi).op (s i) =
        c • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
          (homOfLE hj).op (s j) →
      a • D'.L.presheaf.map (homOfLE hi).op (t i) =
        c • D'.L.presheaf.map (homOfLE hj).op (t j)
  coefficients : ∀ i (V : D'.A.data.relProj.Opens) (hi : V ≤ U i)
      (m : Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F), V)),
      ∃ c : Γ(D'.A.data.relProj, V),
        ((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app V m =
          c • ((Scheme.Modules.tensorPullback b.relProjComparison).obj D.L).presheaf.map
            (homOfLE hi).op (s i) ∧
        (((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
          (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
          ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
          (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app V m =
          c • D'.L.presheaf.map (homOfLE hi).op (t i)

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundlePullbackAdjunction projectiveBundlePullbackComp projectiveBundlePullbackCongr
  Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
private theorem transition_of_cross_tensor {T : Scheme.{u}} {M P Q : T.Modules}
    (q : M ⟶ P) (q' : M ⟶ Q)
    (hcross : ∀ (V : T.Opens) (m n : Γ(M, V)),
      Scheme.Modules.tmulSection (q.app V m) (q'.app V n) =
        Scheme.Modules.tmulSection (q.app V n) (q'.app V m))
    {ι : Type u} {U : ι → T.Opens} (m : ∀ i, Γ(M, U i))
    (hs : ∀ i, Scheme.Modules.IsFreeGenerator (q.app (U i) (m i))) :
    ∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
      a • P.presheaf.map (homOfLE hi).op (q.app (U i) (m i)) =
        c • P.presheaf.map (homOfLE hj).op (q.app (U j) (m j)) →
      a • Q.presheaf.map (homOfLE hi).op (q'.app (U i) (m i)) =
        c • Q.presheaf.map (homOfLE hj).op (q'.app (U j) (m j)) := by
  intro i j V hi hj a c hac
  obtain ⟨d, hd, hd'⟩ :=
    exists_projectiveBundleRealizationPullbackAtlas_coefficients q q' hcross (m i) (hs i)
      V hi (M.presheaf.map (homOfLE hj).op (m j))
  rw [Scheme.Modules.Hom.app_presheaf_map] at hd hd'
  have had : a = c * d := ((hs i).map hi).smul_left_injective (by
    dsimp only
    rw [mul_smul, ← hd]
    exact hac)
  rw [hd', smul_smul, had]

/-- Assemble the atlas from a cover by opens carrying source sections whose images under the two
quotient maps are free generators, using the cross-tensor identity for transitions and
coefficients. The quotient maps are spelled out so that the frame hypotheses match
`exists_projectiveBundleRealizationPullbackAtlas_frames` syntactically. -/
private theorem nonempty_projectiveBundleRealizationPullbackAtlas_of_frames
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    {ι : Type u} (U : ι → D'.A.data.relProj.Opens)
    (m : ∀ i, Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj
      ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F), U i))
    (hcover : ⨆ i, U i = ⊤)
    (hs : ∀ i, Scheme.Modules.IsFreeGenerator
      (((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app (U i) (m i)))
    (ht : ∀ i, Scheme.Modules.IsFreeGenerator
      ((((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
        ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
        (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app
          (U i) (m i)))
    (hcross : ∀ (V : D'.A.data.relProj.Opens)
      (m n : Γ((Scheme.Modules.tensorPullback b.relProjComparison).obj
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F), V)),
      Scheme.Modules.tmulSection
          (((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app V m)
          ((((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
            (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
            ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
            (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app
              V n) =
        Scheme.Modules.tmulSection
          (((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app V n)
          ((((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
            (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
            ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
            (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app
              V m)) :
    Nonempty (ProjectiveBundleRealizationPullbackAtlas D D' g e b) :=
  ⟨{ ι := ι
     U := U
     s := fun i ↦ ((Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient).app (U i)
      (m i)
     t := fun i ↦
      (((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
        ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
        (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient).app
          (U i) (m i)
     cover := hcover
     s_generator := hs
     t_generator := ht
     transition := transition_of_cross_tensor _ _ hcross m hs
     coefficients := fun i V hi n ↦
      exists_projectiveBundleRealizationPullbackAtlas_coefficients _ _ hcross (m i) (hs i) V hi n }⟩

/-- The affine-fraction calculation and normalized quotient equations produce a common frame
atlas for arbitrary normalized realizations.  This is the local geometric part of the proof.
Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
Proof: refine the affine base cover by degree-one standard opens.  Pull the source frame to the
corresponding target standard open and use the generator equation `hb`; homogeneous fractions
show that transition coefficients agree on every overlap.  Tensor pullback sections generate
locally, giving the coefficient equation for every source section.
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas). -/
theorem exists_projectiveBundleRealizationPullbackAtlas
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x))))) :
    Nonempty (ProjectiveBundleRealizationPullbackAtlas D D' g e b) := by
  obtain ⟨hU, hcover, hs, ht⟩ :=
    exists_projectiveBundleRealizationPullbackAtlas_frames D D' g e b hb
  exact nonempty_projectiveBundleRealizationPullbackAtlas_of_frames D D' g e b _ _ hcover hs ht
    (projectiveBundleRealizationPullback_cross_tensor D D' g e b hb)

end AlgebraicGeometry
