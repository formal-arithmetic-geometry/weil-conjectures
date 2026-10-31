/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctorsBasics.DetExistenceLocalizing
import WeilConjectures.SixFunctorsBasics.DetExistenceRestrictionRight
import WeilConjectures.SixFunctorsBasics.DetExistenceRestrictionAdjunction

/-!
# The exceptional inverse image preserves Dctf

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-existence/
`det-existence-restriction.md` and `det-existence-restriction.proof.md`
(blueprint: det-existence-restriction).

The compact-support functor is the recorded `localizingLowerShriek`, and its right adjoint
is specified by the supplied adjunction. The small categories use bounded
constant-model constructibility intersected with finite Tor amplitude, written inline
and pulled back by `ObjectProperty.inverseImage` along the localizing closure inclusion.
The conclusion specifies the Hom bijection of the given adjunction, so also its unit and counit.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 2000000 in
-- The dependent full-subcategory conclusion requires additional elaboration reductions.
/-- The Brown right adjoint on the localizing closures preserves Dctf, and the given
adjunction restricts to these full subcategories with its original Hom bijections.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-existence/
`det-existence-restriction.md`, both sentences (blueprint: det-existence-restriction).

Proof:
1. Reduce the six admissible coefficients to a finite ring A, O_E, E and Qlb:
   Z_ell and Q_ell are the cases E = Q_ell. By det-existence-localizing (3) the supplied
   G is right adjoint to this compactification lower shriek. The uniqueness clause of
   sk-prop-sf-existence identifies it, compatibly with the adjunction, with the right
   adjoints used by the coefficient theorems. Dctf is replete, so preservation transfers.
2. For A apply sk-prop-sf-rf-shriek-preservation. For O_E apply
   det-thm-int-restriction. For E and Qlb apply det-thm-restriction-glue (2), which
   gives preservation of Dbc. X and Y are qcqs, so
   det-def-localizing-closure-ctf-equals-bc (2) identifies Dctf with Dbc in these cases.
3. det-existence-localizing (2) gives preservation of Dctf by the left adjoint.
   Use the two membership assertions hF and hG to lift the actual functors to Dctf.
   Their full inclusions identify their Hom sets with the ambient Hom sets. Restrict
   the given adjunction's natural Hom bijections along these inclusions; the displayed
   equality states that these are exactly the original bijections, with the same
   unit and counit. This proves both sentences, for any supplied Brown adjunction. -/
theorem det_existence_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (c : Compactification.BoundaryCompactification f.left)
    (h : ∀ K, localizingClosureProEtale Λ X.left K → localizingClosureProEtale Λ Y.left
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∃ (hF : ∀ M :
        (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (localizingClosureProEtale Λ X.left).ι).FullSubcategory,
        (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (((localizingLowerShriek Λ c.obj.obj h).obj M.obj).obj))
      (hG : ∀ K :
        (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (localizingClosureProEtale Λ Y.left).ι).FullSubcategory,
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (G.obj K.obj).obj),
      ∃ adjSmall :
        (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (localizingClosureProEtale Λ Y.left).ι).lift
          ((ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ X.left).ι).ι ⋙
              localizingLowerShriek Λ c.obj.obj h) hF ⊣
        (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (localizingClosureProEtale Λ X.left).ι).lift
          ((ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ Y.left).ι).ι ⋙ G) hG,
        ∀ (M : (ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ X.left).ι).FullSubcategory)
          (K : (ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ Y.left).ι).FullSubcategory)
          (a : (localizingLowerShriek Λ c.obj.obj h).obj M.obj ⟶ K.obj),
          (adjSmall.homEquiv M K (ObjectProperty.homMk a)).hom =
            adj.homEquiv M.obj K.obj a := by
  classical
  obtain ⟨hX, hY, sX, sY, hAll, hrest⟩ :=
    det_existence_localizing Λ ell k _hcd f _hΛ
  let := hX
  let := hY
  let := sX
  let := sY
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  obtain ⟨htriX, htriY, hpres, hcoh, hexG⟩ := hrest c
  let hcur := hAll c
  have hF : ∀ M :
      (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ X.left).ι).FullSubcategory,
      (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (((localizingLowerShriek Λ c.obj.obj hcur).obj M.obj).obj) := by
    intro M
    exact hpres M.obj M.property
  have hG := det_existence_restriction_right Λ ell k _hcd f _hΛ c hcur G adj
  refine ⟨hF, hG, ?_⟩
  exact det_existence_restriction_adjunction Λ k f c hcur G adj hF hG

end AlgebraicGeometry.ProEtale.CondensedRing
