/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.LisseFiniteLevelFixedRealizationLocalModel
import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison

/-! # Geometric descent of a local fixed-realization isomorphism

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A local fixed-realization isomorphism on a pro-etale covering sieve gives a local
section of the derived Isom presheaf through every geometric point.

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-descent).

Proof: Lift the geometric point to a member of the covering sieve. Reflect the local
isomorphism through the explicitly constructed fixed-realization equivalence and
restrict to an etale neighbourhood of the lifted point. The resulting inverse pair is
sent to the displayed pro-etale Isom presheaf section by the comparison functor.
-/
theorem exists_proetale_local_iso_section_of_fixed_realization_local_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hlocal : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj
              ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj D))) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left)
          (lisseTowerEtaleRing d n)
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E))
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj D)).obj
            (op ((toProEt U.left).obj V))) := by
  sorry

end AlgebraicGeometry.Scheme
