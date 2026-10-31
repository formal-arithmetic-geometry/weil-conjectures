/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.ScalarSixClosedScalarSupport
import WeilConjectures.SixFunctors.ScalarSixImmersionIdentifiers

/-! # Essential image of scalar extension for an immersion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Scalar extension of an immersion lies in the essential image of the new extension.

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md (2), open and closed
factorization; Stacks Tags 09AA, 09BM and 09AH.
(blueprint: lem-sfb-scalar-six-immersion-scalar-essential-image).

Proof: factor the quasi-compact immersion through its canonical scheme image. The
map to the image is open and the image map is closed. Use the proved closed-support
localization result for the closed factor and the specified open scalar comparison
for the open factor. Conjugate both comparisons by scalarSixExtensionComp and the
coefficient-immersion identifier. The composite is an isomorphism; its component
inverse witnesses essential-image membership. This statement records only membership,
without restriction normalization or naturality.
-/
theorem scalarSixImmersionScalar_mem_essImage
    (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    {k : Type u} [Field k] (O : ScalarSixOpenComparison E G k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (f : S ⟶ X) [IsImmersion f.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)) :
    (scalarSixExtension E G Λ' f).essImage
      ((scalarSixChange a X.left).obj ((scalarSixExtension E G Λ f).obj M)) := by
  have : QuasiCompact (f.left ≫ X.hom) := by
    simpa only [Over.w] using (inferInstance : QuasiCompact S.hom)
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left X.hom
  let Z : Over (Spec (.of k)) := Over.mk (f.left.imageι ≫ X.hom)
  let i : Z ⟶ X := Over.homMk f.left.imageι rfl
  let j : S ⟶ Z := Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ X.hom) = S.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact Over.w f)
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion f.left.imageι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion f.left.toImage)
  have : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (f.left.imageι ≫ X.hom))
  have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (f.left.imageι ≫ X.hom))
  have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (f.left.imageι ≫ X.hom))
  have hji : j ≫ i = f := by
    apply Over.OverMorphism.ext
    exact f.left.toImage_imageι
  let e (R : ScalarSixRing.{u}) :
      scalarSixExtension E G R j ⋙ scalarSixExtension E G R i ≅
        scalarSixExtension E G R f :=
    scalarSixExtensionComp E D G R i j (scalarSixImmersionIdentifiers G k R i j) ≪≫
      eqToIso (by simp only [hji])
  let o : scalarSixExtension E G Λ j ⋙ scalarSixChange a Z.left ≅
      scalarSixChange a S.left ⋙ scalarSixExtension E G Λ' j :=
    Functor.isoWhiskerRight (scalarSixOpenIso E G O Λ j) (scalarSixChange a Z.left) ≪≫
      scalarSixOpenScalarIso a j.left ≪≫
      Functor.isoWhiskerLeft (scalarSixChange a S.left) (scalarSixOpenIso E G O Λ' j).symm
  let N := (scalarSixExtension E G Λ j).obj M
  obtain ⟨L, ⟨b⟩⟩ := scalarSixClosedScalar_mem_essImage E G a i N
  let H := scalarSixExtension E G Λ' i
  let R := scalarSixPull Λ' i.left
  let rho := scalarSixRestriction E D G Λ' i
  let t : R.obj ((scalarSixChange a X.left).obj
      ((scalarSixExtension E G Λ i).obj N)) ≅ (scalarSixChange a Z.left).obj N :=
    ((C.theta a i.left).app ((scalarSixExtension E G Λ i).obj N)).symm ≪≫
      (scalarSixChange a Z.left).mapIso ((scalarSixRestriction E D G Λ i).app N)
  let g : L ≅ (scalarSixChange a Z.left).obj N :=
    (rho.app L).symm ≪≫ R.mapIso b ≪≫ t
  let c : (scalarSixChange a X.left).obj ((scalarSixExtension E G Λ f).obj M) ≅
      (scalarSixExtension E G Λ' f).obj ((scalarSixChange a S.left).obj M) :=
    (scalarSixChange a X.left).mapIso ((e Λ).app M).symm ≪≫
      b.symm ≪≫ H.mapIso g ≪≫ H.mapIso (o.app M) ≪≫
        (e Λ').app ((scalarSixChange a S.left).obj M)
  exact ⟨_, ⟨c.symm⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
