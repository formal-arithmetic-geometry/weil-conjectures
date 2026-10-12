/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # The counit calculation for tensor-Hom duality and a right adjoint

Source: Stacks Project, Duality for Schemes, Tag 0A9T.
(blueprint: lem-sc-perfect-right-adjoint-tensor-hom-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The tensor-Hom chain of Tag 0A9T is postcomposition with the canonical mate.
Source: Stacks Project, Duality for Schemes, Tag 0A9T.
(blueprint: lem-sc-perfect-right-adjoint-tensor-hom-comparison).
Proof: transpose both sides under `adj`. Naturality of its Hom equivalence turns
postcomposition with the mate into application of the restricted direct image to q,
followed by the counit defining that mate. Expand the two tensor-Hom equivalences:
the first inserts evaluation of the pulled-back dual and the second inserts
coevaluation of the original dual. Replace the inverses of pfK and pfD by their
specified pullback-adjoint formulas. Naturality of the pullback and right-adjoint
counits moves q and evaluation through those formulas. The tensorator's naturality
identifies evaluation of the mapped pairing with pullback of evaluation. Its
associativity and unit laws rearrange the resulting evaluation-coevaluation pair;
the triangle identity cancels it. The remaining composite is the restricted direct
image of q followed by pfK, the tensor of the right-adjoint counit at the unit, and
the right unitor. This is precisely the transpose of the right-hand side.
Full-subcategory morphisms have the same composition as the ambient morphisms,
so the same calculation applies to the displayed `homMk` morphisms. -/
theorem perfect_rightAdjoint_tensor_hom_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (K D : schemeDerivedQCohCategory Y) [ExactPairing K.obj D.obj]
    (E : schemeDerivedQCohCategory X)
    (pfK : (schemeDerivedDirectImage f).obj
        (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
      K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)
    (hpK : pfK.inv = (a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj
        ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
        (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj))
    (pfD : (schemeDerivedDirectImage f).obj
        (((derivedPullback f).obj D.obj) ⊗ E.obj) ≅
      D.obj ⊗ (schemeDerivedDirectImage f).obj E.obj)
    (hpD : pfD.inv = (a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) D.obj
        ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
        (derivedPullback f).obj D.obj ◁ a.counit.app E.obj))
    (q : E ⟶ ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
      hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩) :
    let p := ExactPairing.map (derivedPullback f) K.obj D.obj
    (adj.homEquiv E K)
      (ObjectProperty.homMk
        (tensorLeftHomEquiv ((schemeDerivedDirectImage f).obj E.obj) K.obj D.obj
          (𝟙_ (schemeDerivedCategory Y))
          (pfD.inv ≫ ((adj.homEquiv
            ⟨((derivedPullback f).obj D.obj) ⊗ E.obj, hTensor D E⟩ ⟨𝟙_ _, hO⟩).symm
            (ObjectProperty.homMk
              ((@tensorLeftHomEquiv _ _ _ E.obj ((derivedPullback f).obj K.obj)
                ((derivedPullback f).obj D.obj) (c.obj ⟨𝟙_ _, hO⟩).obj p).symm
                q.hom))).hom) ≫ (ρ_ K.obj).hom)) =
      q ≫ (adj.homEquiv
        ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
          hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
        (ObjectProperty.homMk (pfK.hom ≫
          K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)) := by sorry

end AlgebraicGeometry
