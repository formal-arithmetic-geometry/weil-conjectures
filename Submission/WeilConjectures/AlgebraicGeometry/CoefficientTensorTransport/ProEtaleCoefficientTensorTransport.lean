/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientTensorCompatibility

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Tensor comparison for an isomorphism of coefficient sheaves

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6, and Modules on Sites,
Tag 03EL. The comparison here concerns inverse image and tensor only.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- A coefficient-ring isomorphism identifies derived tensor models compatibly with
canonical geometric tensor pullback. This has no direct-image or projection-mate clause.

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E, and Modules on Sites,
Tag 03EL; coefficient-isomorphism part of the proof of the projection formula, Tag 0B56.
(blueprint: lem-pbc-coefficient-restriction-tensor-comparison).

Proof: restriction along c is an exact equivalence, inverse to restriction along its
inverse. On module sheaves the canonical tensor comparison is the map which fixes
pure tensors, with the scalar actions identified by c. Its inverse fixes pure tensors
as well; the balancing relation uses that c is invertible. Thus restriction preserves
flat modules and, by applying the inverse equivalence to acyclic test complexes,
K-flat complexes. The ordinary tensor comparison commutes with restriction maps and
with the signed direct-sum total tensor. Localize it on flat K-flat pairs and use
the representative isomorphisms of z and aX. Flat K-flat resolutions in both variables
extend the resulting isomorphism uniquely to rho. For the displayed equation, apply
the representative normalization of each geometric tensor comparison. On each pure
tensor both routes are the same inverse-image section map with the action changed
by c. Their signed total maps agree, and localization and resolution descent give
the equation for all F and G. No boundedness, perfectness or nonzero-ring assumption
enters: the same constructions cover zero rings and empty sites. -/
theorem tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S) :
    ∃ rho : ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor ≅
        aX.tensor ⋙ pbcDerivedRestrict c.hom,
      ∀ F G : DerivedCategory (proEtaleRingModules Y R),
        (pullback f R S c).hom.app (aY.tensor.obj (F, G)) ≫
          (proEtaleCanonicalTensorComparison f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _) aY z).hom.app (F, G) =
        (pbcDerivedRestrict c.hom).map
            ((proEtaleCanonicalTensorComparison f R S c aY aX).hom.app (F, G)) ≫
          rho.inv.app ((proEtaleRingDerivedPullback f R S c).obj F,
            (proEtaleRingDerivedPullback f R S c).obj G) ≫
          z.tensor.map (Prod.mkHom ((pullback f R S c).hom.app F)
            ((pullback f R S c).hom.app G)) := by
  exact tensorComparison_compatibility f R S c aY z aX

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
