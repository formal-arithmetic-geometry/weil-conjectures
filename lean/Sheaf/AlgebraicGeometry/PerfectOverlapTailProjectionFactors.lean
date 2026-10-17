/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapTailNormalForm
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTwoFactors
import Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectFactors
import Sheaf.AlgebraicGeometry.PerfectOverlapStageTransportComponent

/-! # Cartesian projection after local tail normalization -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local implicit_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom Monotone.functor
attribute [local implicit_reducible] SetLike.coe DFunLike.coe Set.inter
attribute [local implicit_reducible] perfectOverlapStageEquivalence
  overlapSchemeIsoDerivedEquivalence CategoryTheory.Equivalence.mk
attribute [local irreducible] CategoryTheory.IsPullback.isoPullback Scheme.Opens.toScheme
attribute [local irreducible] derivedPullback perfectHomComposition
  perfectOverlapDerivedPullbackTransport
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Projection compatibility for the normalized factors, without the nested tail.
Source: Stacks Project, Tags 08DW and 0D5S, derived composition coherence.

Proof: Use the restricted composition and stage projection equations from
PerfectOverlapTailNormalForm for r,p,t and the two cartesian scheme isomorphisms.
Apply perfectOverlapProjectionTwoFactors with d1 the inverse inclusion comparison
on K, and d2 the comparison for jK followed by f restricted to L. Its proof is the
abstract projection prism followed by naturality twice, moving these two factors
across derived transport. Expand the f-stage comparison using
perfectOverlapStageObjectIso_hom_factors, map its factors by the base-change map,
and use functoriality of composition to identify the right-hand product.
Finally perfectOverlapStageTransport_hom_app identifies the transport component.
Associate the composites to obtain the displayed equation. Normalize the over-category
projections in the abstract prism before specializing its coefficient maps.
All equations are functorial and remain valid for empty or equal opens.
(blueprint: lem-pc-perfect-overlap-tail-projection-factors). -/
theorem perfectOverlapTailProjectionFactors
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
  let W := U ⊓ V
  let hP : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let hT : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let iX : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let _ξ := perfectOverlapNestedPullbackSquare gk iK iX hP hT
  let _κ := perfectOverlapCompositeLocalIso f gk g hgf L
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hT
  let jX := X.homOfLE (leOfHom iX)
  let jK := K.homOfLE (leOfHom iK)
  let p := jK ≫ (f ∣_ L)
  let t := jX ≫ (g ∣_ L)
  let e : (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≅ pullback (W.ι ≫ pY) b :=
    ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let a := Y.homOfLE hWL
  let hr : r ≫ p = t := perfectOverlapTailRestrictedComposite f gk g hgf U V L hWL
  let ht : e.inv ≫ t = pullback.fst (W.ι ≫ pY) b ≫ a :=
    perfectOverlapTailStageProjection g pX pY b hg U V L hWL
  let R := derivedPullback e.inv
  (R.map ((derivedPullback r).map
      ((overlapOpenInclusionPullbackIso K iK).inv.app ((derivedPullback (f ∣_ L)).obj A))) ≫
    R.map ((derivedPullback r).map ((perfectHomComposition jK (f ∣_ L)).hom.app A)) ≫
    R.map ((compositionTo r p t hr).hom.app A) ≫
    (perfectHomComposition e.inv t).hom.app A ≫
    (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app A ≫
    (perfectHomComposition (pullback.fst (W.ι ≫ pY) b) a).inv.app A) ≫
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
  intro W hP hT iX iK ξ κ r jX jK p t e a hr ht R
  let eK : (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme ≅ pullback (W.ι ≫ pY) q :=
    ((isPullback_morphismRestrict f W).paste_vert hf).isoPullback
  have hp : eK.inv ≫ p = pullback.fst (W.ι ≫ pY) q ≫ a :=
    perfectOverlapTailStageProjection f pK pY q hf U V L hWL
  have htransport :
      (perfectOverlapStageTransport g f pX pK pY b q hg hf U V
        (gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V))
          (by rw [← Scheme.Hom.comp_preimage, hgf]))
        (baseChangeMap ((U ⊓ V).ι ≫ pY) l) hmap).hom.app
          ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
            ((derivedPullback (f ∣_ L)).obj A)) =
      (perfectOverlapDerivedPullbackTransport r e eK
        (baseChangeMap (W.ι ≫ pY) l) hmap).hom.app
          ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
            ((derivedPullback (f ∣_ L)).obj A)) := by
    exact perfectOverlapStageTransport_hom_app g f pX pK pY b q hg hf U V r
      (baseChangeMap (W.ι ≫ pY) l) hmap
      ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ L)).obj A))
  have hobj : (perfectOverlapStageObjectIso f pK pY q hf U V L hWL).hom.app A =
      (derivedPullback eK.inv).map
        ((overlapOpenInclusionPullbackIso K iK).inv.app ((derivedPullback (f ∣_ L)).obj A)) ≫
      (derivedPullback eK.inv).map ((perfectHomComposition jK (f ∣_ L)).hom.app A) ≫
      (perfectHomComposition eK.inv p).hom.app A ≫
      (eqToIso (congrArg (fun k ↦ derivedPullback k) hp)).hom.app A ≫
      (perfectHomComposition (pullback.fst (W.ι ≫ pY) q) a).inv.app A := by
    exact perfectOverlapStageObjectIso_hom_factors f pK pY q hf U V L hWL A
  have H := perfectOverlapProjectionTwoFactors (W.ι ≫ pY) b q l r e eK hmap
    p t hr a ht hp A
    ((overlapOpenInclusionPullbackIso K iK).inv.app ((derivedPullback (f ∣_ L)).obj A))
    ((perfectHomComposition jK (f ∣_ L)).hom.app A)
  rw [htransport, hobj]
  simpa only [R, Functor.map_comp, Category.assoc] using H

end AlgebraicGeometry
