/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Finite-dimensional actual fibres of constructible native modules

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
paragraphs 5--6, forming the boundary determinant polynomial.
(blueprint: lem-wf-native-constructible-fibre-finite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeCondensedModule

/-- A constructible native module on a qcqs scheme has finite-dimensional actual fibres.
Source: latest blueprint, boundary local polynomial in sk-p-real-semi.proof.md,
paragraphs 5--6 (blueprint: lem-wf-native-constructible-fibre-finite).

Proof: finite constant models give local finite presentations on each stratum.
Undo the canonical coefficient comparison to obtain the ordinary constructibility
predicate. Its geometric-stalk theorem gives a finite presentation on Spec of the
algebraically closed field. The endomorphism field of the regular coefficient
module is Qbar_l, so Gaussian elimination on this presentation identifies its
cokernel with a finite biproduct of regular modules. Actual point sections are
additive and send the regular module to the standard lifted coefficient field
by the scalar-normalized unit isomorphism. The biproduct is thus a finite power
of that field. Transfer finite dimensionality through these linear isomorphisms.
Zero rank gives the empty product, so this includes the zero fibre. -/
theorem constructible_fibre_finiteDimensional
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Modules l T)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T M)
    (z : Spec (.of D.k) ⟶ T) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M z) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hs : IsFiniteConstantStratified (Profinite.padicAlgClRingObj l) T M := by
    rw [IsConstantModelConstructible,
      if_pos (show CompactSpace T ∧ QuasiSeparatedSpace T from
        ⟨inferInstance, inferInstance⟩)] at hM
    exact hM
  have hc := modelStratifiedConstructible (Profinite.padicAlgClRingObj l) T M hs
  obtain ⟨n, m, f, ⟨e⟩⟩ :=
    CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      (Profinite.padicAlgClRingObj l) (Field.toIsField D.k)
      IsField.isSepClosed_toField hc z
  obtain ⟨r, ⟨er⟩⟩ := exists_iso_biproduct_cokernel
    (CondensedRing.isIso_of_ne_zero_end_tensorUnit l (Field.toIsField D.k)
      IsField.isSepClosed_toField) (Iso.refl _) (Iso.refl _) f
  let F := pointSections l D.k
  have : F.Additive := by
    dsimp [F, pointSections]
    infer_instance
  let eq : F.obj ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M) ≅
      ModuleCat.of (ULift.{u + 1} (PadicAlgCl l))
        (Fin r → (ULift.{u + 1} (PadicAlgCl l))) :=
    F.mapIso (e ≪≫ er) ≪≫ F.mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ ↦ (pointSectionsUnitIso l D.k).symm) ≪≫
      ModuleCat.biproductIsoPi _
  exact LinearEquiv.finiteDimensional eq.toLinearEquiv.symm

end WeilConjectures.NativeCondensedModule
