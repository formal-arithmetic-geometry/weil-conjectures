/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.Paper.ModuleCohomologyCupProduct
import Sheaf.Paper.CechCupPullbackCompat

/-! # Ordinary module comparison for external Cech pairing

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, equation-kunneth-on-cech.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- A prescribed external front/back cochain pairing compares to the module cup.
This assertion concerns ordinary module cohomology, with no scalar Ext cup.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-module-cech-external-pairing).

Proof: On the product scheme use the cover W indexed by pairs, and refine the
projection inverse images of U and V to W using the two index projections.
The refinement maps exist by the restriction and tensor-pullback unit formulas;
W covers because inverse image preserves unions and intersections distribute over
unions. Transport the factor cocycles through the explicit additive Cech complex
identifications. Their refinements are cocycles. The prescribed bidegree formula
for h says, tuple by tuple, that the inclusion of t is their front/back Cech cup.
The additive identifications preserve restrictions and sections, so this remains
true for the ordinary module Cech complexes. Monicity of the cycle inclusion
identifies the cycles. Apply Tag 01FD comparison naturality for each projection,
then Tag 0FKV compatibility of the ordinary Cech and module cups on W. The three
canonical comparisons are exactly cX, cY and cP. The two identities give the
claimed module cup of module pullback classes. Comparisons need not be invertible
and the covers need not be affine. In degree zero this is the section tensor
formula. For zero coefficients or an empty cover of the empty scheme all cycles
and classes vanish. -/
theorem picardModuleCech_externalPairing
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (cX : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcX : IsModuleCechComparison U F p cX)
    (cY : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcY : IsModuleCechComparison V G q cY)
    (cP : ((cechComplexFunctor
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcP : IsModuleCechComparison
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) (p + q) cP)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup : IsModuleCupProduct ((tensorPullback (pullback.fst f g)).obj F)
      ((tensorPullback (pullback.snd f g)).obj G) p q cup) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2
    let E := externalCupCoefficients f g F G
    let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
    ∀ (a : A.cycles p) (b : B.cycles q) (t : P.cycles (p + q)),
      P.iCycles (p + q) t = h ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) →
      cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso W E.presheafModuleCat
          (p + q)).inv
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso W
          (scalarPresheaf (pullback.fst f g ≫ f) E) (p + q)).hom
            (P.homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cX ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U
            (scalarPresheaf f F) p).hom (A.homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cY ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V
              (scalarPresheaf g G) q).hom (B.homologyπ q b))))) := by sorry

end AlgebraicGeometry.Scheme.Modules
