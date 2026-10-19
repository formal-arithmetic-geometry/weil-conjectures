/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # Flatness under étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The flat-sheaf part of étale sum preservation, in the canonical constant-ring
coordinates. Source: Stacks Project, More on Étale Cohomology, Tag 0GKF
(blueprint: lem-pur-etale-sum-flat-aux).

Proof: the constant-scalar equivalence and canonical ring-isomorphism transport
identify sheafified sectionwise tensor with tensor of module-valued sheaves. This
can be checked on pure tensors for the constant ring presheaf and then sheafified:
locally every scalar section comes from a constant scalar, so the same balancing
relations determine both products. The equivalence is exact and reflects exactness.
For a short exact sequence G on X, exact inverse image gives a short exact sequence
on U. Tensor with the given flat F, then apply exact sum extension. The natural
projection isomorphism identifies this composite sequence with the tensor of G by
sum extension of F. Tensor symmetry changes the factor order to the right tensor
used by IsFlatOnSite. Thus right tensor preserves short exact sequences and hence
finite limits and finite colimits in the abelian sheaf category. The argument uses
no nonzero coefficient, nonempty scheme, or boundedness hypothesis. -/
theorem etaleSum_preserves_flat_aux {U X : Scheme.{u}} (f : U ⟶ X)
    [hf : Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] :
    ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
      SheafOfModules.IsFlatOnSite (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleConstantModuleFunctor U A ⋙
          SheafOfModules.pushforward (F := 𝟭 U.Etale)
            (constantModuleHomRingIso U.smallEtaleTopology A).inv).obj F) →
      SheafOfModules.IsFlatOnSite (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleConstantModuleFunctor X A ⋙
          SheafOfModules.pushforward (F := 𝟭 X.Etale)
            (constantModuleHomRingIso X.smallEtaleTopology A).inv).obj
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf).obj F))  := by
  intro F hF
  apply (etaleConstantModule_flat_iff X A _).mp
  exact Functor.PreservesFlat.flat_obj
    (F := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf)
    ((etaleConstantModule_flat_iff U A F).mpr hF)

end AlgebraicGeometry.Scheme
