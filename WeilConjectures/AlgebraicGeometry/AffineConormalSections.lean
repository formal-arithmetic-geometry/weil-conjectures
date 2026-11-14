/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.AffineConormalSectionsExistence
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-!
# Affine sections of the conormal sheaf

## References

* Stacks Project, Tags 01R2, 01R3
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The tensor pullback of the ideal of a closed immersion is quasi-coherent, and its
sections on the inverse image of an affine open are canonically `I/I²`.
The affine coordinates are supplied by `r : R ≃+* Γ(X, U)` and `I` is the ideal of `Z ∩ U`.
The equivalence is `R/I`-linear and sends `a mod I²` to `i* a`
(Stacks, Tags 01R2, 01R3). -/
theorem affine_conormal_sections {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((tensorPullback i).obj i.ker.toModules).IsQuasicoherent ∧
      ∀ (U : X.affineOpens) (R : Type v) [CommRing R]
        (r : R ≃+* Γ(X, U.1)) (I : Ideal R),
        I = RingHom.ker ((i.app U.1).hom.comp (r : R →+* Γ(X, U.1))) →
        ∃ e : LinearEquiv (r : R →+* Γ(X, U.1))
            (σ' := (r.symm : Γ(X, U.1) →+* R)) I.Cotangent
            Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1),
          ∀ (a : I) (s : Γ(i.ker.toModules, U.1)),
            i.ker.toModulesι.app U.1 s = r (a : R) →
            e (I.toCotangent a) =
              ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).app U.1 s := by
  constructor
  · have := SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_isClosedImmersion i.ker.subschemeι _
    have : i.ker.toModules.IsQuasicoherent :=
      isQuasicoherent_kernel i.ker.toPushforwardSubscheme
    let e : tensorPullback i ≅ pullback i :=
      (Classical.choose (exists_tensorPullbackAdjunction i)).leftAdjointUniq
        (pullbackPushforwardAdjunction i)
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (e.app i.ker.toModules).symm (by infer_instance)
  · exact affine_conormal_sections_existence i

end AlgebraicGeometry.Scheme.Modules
