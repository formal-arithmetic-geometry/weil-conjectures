module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective
import Sheaf.AlgebraicGeometry.ChowFormalSystemExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Candidate algebraization on a fixed quasi-projective modification, before the support
argument. Source: Stacks Project, Theorem 088E, projective compactification argument
(blueprint: new-chow-algebraization-core-candidate).
The compactification, extension by zero, projective existence, and restriction steps
construct a coherent module whose formal completion is the pulled-back system. The
separate support theorem below supplies the remaining proper-support assertion. -/
theorem exists_chow_algebraization_core_candidate
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f) :
    ∃ F : CoherentModules Y,
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) := by
  classical
  let π := (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A))
  -- Use the concrete scheme-theoretic image as the projective compactification.
  let X := e.image
  let p : X ⟶ Spec (.of A) := e.imageι ≫ π
  let j : Y ⟶ X := e.toImage
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (q ≫ f)
  have : QuasiCompact e := QuasiCompact.of_comp e π
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  have hj : j ≫ p = q ≫ f := by
    dsimp [j, p]
    rw [← Category.assoc, e.toImage_imageι]
    exact he
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker
  have hkernel : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    dsimp [J]
    rw [Scheme.ker_of_isAffine]
    congr 1
    rw [← RingHom.ker_equiv_comp _
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).commRingCatIsoToRingEquiv]
    rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    change (RingHom.ker (Ideal.Quotient.mk I)).comap
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom = _
    rw [Ideal.mk_ker]
    exact (Ideal.map_symm
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv).symm
  have hQ' : Q = J.comap f := by
    rw [hkernel]
    exact hQ
  obtain ⟨H, ⟨hH⟩⟩ := exists_chow_formal_system_extension f J Q hQ' G hR q p j hj
  have hJ : (J.comap p).comap j = Q.comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, hj, Scheme.IdealSheafData.comap_comp, ← hQ']
  have : (completion X (J.comap p)).IsEquivalence :=
    completion_isEquivalence_of_projective_embedding A I X n e.imageι
  -- Projective existence algebraizes the extended system on the compactification.
  let F' := (completion X (J.comap p)).objPreimage H
  let β := (ObjectProperty.ι (IsCoherentFormalModule (J.comap p))).mapIso
    ((completion X (J.comap p)).objObjPreimageIso H).symm
  obtain ⟨⟨P, C, hP, _, ⟨α⟩⟩, _⟩ := exists_formalSystemsPullback j (J.comap p)
  let F := C.obj F'
  -- Compare restriction of completion with completion of the coherent restriction.
  let γ := (ObjectProperty.ι (IsCoherentFormalModule ((J.comap p).comap j))).mapIso
    (α.app F')
  have hPo : (P.obj ((completion X (J.comap p)).obj F')).obj =
      formalCompletionSystem (J.comap p) F'.obj ⋙ Scheme.Modules.tensorPullback j :=
    congrArg (fun T ↦ T.obj ((completion X (J.comap p)).obj F')) hP
  change (P.obj ((completion X (J.comap p)).obj F')).obj ≅
    formalCompletionSystem ((J.comap p).comap j) F.obj at γ
  rw [hPo, hJ] at γ
  refine ⟨F, ⟨hH ≪≫ ?_ ≪≫ γ⟩⟩
  exact ((Functor.whiskeringRight ℕᵒᵖ X.Modules Y.Modules).obj
    (Scheme.Modules.tensorPullback j)).mapIso β

end AlgebraicGeometry
