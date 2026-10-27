/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleToposPointFiberComparison
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# From the étale fiber comparison to the stalk comparison

This is the reconstruction and reindexing part of the point-classification
argument.  It turns a comparison on sheafified representables into the natural
isomorphism of inverse-image and geometric-stalk functors.
(blueprint: lem-trf-etale-topos-point-stalk-reconstruction)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def geometricRepresentableFiberIso
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    uliftYoneda.{u + 1} ⋙
      (pointSmallEtale s).presheafFiber (A := Type (u + 1)) ≅
      (pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1} := by
  let Φ := pointSmallEtale s
  let W := (Functor.whiskeringRight S.Etaleᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  change (yoneda ⋙ W) ⋙ Φ.presheafFiber ≅ Φ.fiber ⋙ uliftFunctor.{u + 1}
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerRight shrinkYonedaIsoYoneda W).symm Φ.presheafFiber ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Φ.presheafFiberCompIso uliftFunctor.{u + 1}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Φ.shrinkYonedaCompPresheafFiberIso uliftFunctor.{u + 1}

/-- A geometric comparison of the fiber functors determines the corresponding
natural isomorphism on all sheaves.
Source: Stacks Project, Sites, Tags 00YA--00YC; Etale Cohomology, Tag 04HU.
(blueprint: lem-trf-etale-topos-point-stalk-reconstruction)

Proof: let P be sheafification followed by p.inverse, and Q the presheaf fiber
at s. The geometric fiber of a representable is its lift set; compatibility
with ULift follows from commutation of the filtered fiber colimit with ULift.
Thus the supplied isomorphism identifies P and Q on lifted representables.
Both preserve colimits: sheafification and p.inverse are left adjoints, and
Q has the skyscraper presheaf right adjoint. The uniqueness of cocontinuous
extensions from lifted representables gives P ≅ Q. Finally sheafification is
a localization; Q localizes to the geometric sheaf fiber and P localizes to
p.inverse. Lifting the isomorphism through this localization gives the result.
This proves the reconstruction step without an unproved reconstruction lemma. -/
theorem etale_point_fiber_iso_to_stalk
    (S : Scheme.{u})
    (p : GeometricMorphism (Type (u + 1))
      (Sheaf S.smallEtaleTopology (Type (u + 1))))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (h : Nonempty (etalePointFiberFunctor S p ≅
      ((pointSmallEtale s).fiber ⋙ CategoryTheory.uliftFunctor.{u + 1}))) :
    Nonempty (p.inverse ≅ (pointSmallEtale s).sheafFiber (A := Type (u + 1))) := by
  classical
  let Φ := pointSmallEtale s
  let P := presheafToSheaf S.smallEtaleTopology (Type (u + 1)) ⋙ p.inverse
  let Q := Φ.presheafFiber (A := Type (u + 1))
  let : p.inverse.IsLeftAdjoint := p.adj.isLeftAdjoint
  let : Q.IsLeftAdjoint := Φ.skyscraperPresheafAdjunction.isLeftAdjoint
  let eQ : etalePointFiberFunctor S p ≅ uliftYoneda.{u + 1} ⋙ Q :=
    h.some ≪≫ (geometricRepresentableFiberIso S Ω s).symm
  let eP : etalePointFiberFunctor S p ≅ uliftYoneda.{u + 1} ⋙ P := Iso.refl _
  let e : P ≅ Q :=
    Presheaf.uniqueExtensionAlongULiftYoneda.{0} P eP ≪≫
      (Presheaf.uniqueExtensionAlongULiftYoneda.{0} Q eQ).symm
  exact ⟨Localization.liftNatIso
    (presheafToSheaf S.smallEtaleTopology (Type (u + 1)))
    S.smallEtaleTopology.W P Q p.inverse Φ.sheafFiber e⟩

end AlgebraicGeometry.Scheme
