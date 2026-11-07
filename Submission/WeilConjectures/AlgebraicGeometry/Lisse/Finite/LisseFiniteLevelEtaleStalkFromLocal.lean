/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # From an étale local isomorphism to a geometric stalk section

Source: Stacks Project, proetale.tex, Tag 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-stalk-from-local-section).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A representative of the local Isom presheaf over an étale neighbourhood of a
geometric point gives an element of the sheafified Isom stalk.  This isolates the
sheafification and point-fibre step from finite-level comparison.

Source: Stacks Project, proetale.tex, Tag 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-stalk-from-local-section).

Proof: Apply the canonical map from the local Isom presheaf to its sheafification
at the pointed étale object `(V,v)`.  The resulting germ lies in the geometric
stalk, and the point-fibre colimit map sends it to an element of the sheaf fibre.
No finite-level or boundedness hypothesis is needed for this evaluation step.
-/
theorem lisse_finite_level_etale_stalk_from_local_section
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (V : X.Etale) (v : (pointSmallEtale x).fiber.obj V)
    (h : Nonempty ((localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj D)) :
    Nonempty ((pointSmallEtale x).sheafFiber.obj
      (derivedLocalIsomorphismSheaf A D)) := by
  rcases h with ⟨e⟩
  let P := derivedLocalIsomorphismPresheaf A D
  let η := CategoryTheory.toSheafify X.smallEtaleTopology P
  refine ⟨((pointSmallEtale x).presheafFiber.map η)
    ((pointSmallEtale x).toPresheafFiber V v P e)⟩

end AlgebraicGeometry.Scheme
