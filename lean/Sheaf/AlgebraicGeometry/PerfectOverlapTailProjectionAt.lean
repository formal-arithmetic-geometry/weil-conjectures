/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageTail
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapTailNormalForm
import Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionFactors

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local implicit_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom Monotone.functor
attribute [local implicit_reducible] SetLike.coe DFunLike.coe Set.inter
attribute [local semireducible] perfectOverlapStageTransport
attribute [local implicit_reducible] perfectOverlapStageTransport
  perfectOverlapStageEquivalence overlapSchemeIsoDerivedEquivalence
  CategoryTheory.Equivalence.mk
attribute [local irreducible] CategoryTheory.IsPullback.isoPullback
attribute [local irreducible] derivedPullback perfectHomComposition
  perfectOverlapStageObjectIso
  perfectOverlapDerivedPullbackTransport
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Combine the local normalization with the cartesian projection calculation.
Source: Stacks Project, Tags 08DW and 0D5S. Compose the normalization equality
with projection compatibility for its factors.
(blueprint: new-lem-pc-perfect-overlap-tail-projection-component-at). -/
theorem perfectOverlapTailProjectionAt
    {X Y K C T S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (l : Over.mk b ⟶ Over.mk q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫
          gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V))
            (by rw [← Scheme.Hom.comp_preimage, hgf]) =
        baseChangeMap ((U ⊓ V).ι ≫ pY) l ≫
          ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv) :
    perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V L hWL A ≫
        (perfectHomComparison ((U ⊓ V).ι ≫ pY) l).hom.app
          ((derivedPullback (Y.homOfLE hWL)).obj A) =
      (perfectOverlapStageTransport g f pX pK pY b q hg hf U V
        (gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V))
          (by rw [← Scheme.Hom.comp_preimage, hgf]))
        (baseChangeMap ((U ⊓ V).ι ≫ pY) l) hmap).hom.app
          ((schemeOpenOverlapRestriction K (homOfLE (fun _ hx ↦ hWL hx))).mapDerivedCategory.obj
            ((derivedPullback (f ∣_ L)).obj A)) ≫
        (derivedPullback (baseChangeMap ((U ⊓ V).ι ≫ pY) l)).map
          ((perfectOverlapStageObjectIso f pK pY q hf U V L hWL).hom.app A) := by
  have hn := perfectOverlapCompositeStageTailAt_eq_factors
    f gk g hgf pX pY b hg U V L hWL A
  exact (congrArg (fun z ↦ z ≫
    (perfectHomComparison ((U ⊓ V).ι ≫ pY) l).hom.app
      ((derivedPullback (Y.homOfLE hWL)).obj A)) hn).trans
    (perfectOverlapTailProjectionFactors
      f gk g hgf pX pK pY b q hg hf l U V L hWL A hmap)

end AlgebraicGeometry
