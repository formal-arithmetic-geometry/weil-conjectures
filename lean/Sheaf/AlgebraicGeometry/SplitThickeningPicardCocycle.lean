module

public import WeilConjectures.AlgebraicGeometry.Picard.DualNumbers
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import Sheaf.CategoryTheory.Sites.TorsorH1Functoriality
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImageUnit
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace

/-! # Infinitesimal line bundles and their transition cocycles

Source: Stacks Project, more-morphisms.tex, Tag 0C6R,
lemma-picard-group-first-order-thickening; cohomology.tex, Tag 09NU,
lemma-h1-invertible; Milne, Abelian Varieties, III Proposition 2.1, pp.90–91
(blueprint: lem-sfb-split-thickening-picard-cocycle).

The source's same-space model `X.dualNumbers` is the base change to k[epsilon]:
`Scheme.isPullback_dualNumbersProj` supplies the canonical identification. Its projection
and inclusion are `X.dualNumbersProj` and `X.dualNumbersι`. The canonical class below
uses the constructed, resolution-normalized comparison with module cohomology.
The local convention is m_j = (1 + epsilon c_ij) m_i, with Cech differential t_j-t_i.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The canonical class obtained by applying H1 to a ↦ 1+epsilon a, and then Hilbert 90.
Source: Stacks 0C6R and 09NU; the module/Ext comparison is the constructed common-resolution
comparison, rather than an arbitrarily selected equivalence
(blueprint: lem-sfb-split-thickening-picard-cocycle). -/
@[no_expose] def splitThickeningPicardClass (X : Scheme.{u}) :
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) →
      Additive X.dualNumbers.Pic :=
  fun v ↦ (Pic.toH1UnitsDualNumbersAddEquiv X).symm
    (Sheaf.H.map X.dualNumbersOneAddEps 1
      (Modules.moduleCohomologyExtResolutionEquiv X (Modules.unit X) 1 v))

/-- The exponential class is evaluated by the specified resolution-normalized composite.
Source: Stacks 0C6R, 09NU and 03FD
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof: evaluate the definition. The resolution-normalized module/Ext comparison is
followed by H1 of a ↦ 1+epsilon a and the inverse Hilbert-90 equivalence. This equation
exposes the canonical map without exposing its construction to downstream reduction. -/
theorem splitThickeningPicardClass_apply (X : Scheme.{u})
    (v : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) :
    splitThickeningPicardClass X v =
      (Pic.toH1UnitsDualNumbersAddEquiv X).symm
        (Sheaf.H.map X.dualNumbersOneAddEps 1
          (Modules.moduleCohomologyExtResolutionEquiv X (Modules.unit X) 1 v)) := by
  sorry

/-- The ij coefficient of an additive Cech 1-cocycle, using the existing module Cech complex.
Source: Stacks 01EQ and 0B8R (blueprint: lem-sfb-split-thickening-picard-cocycle). -/
def splitThickeningCocycleCoefficient {X : Scheme.{u}} {I : Type u}
    (U : I → X.Opens)
    (z : ((CategoryTheory.cechComplexFunctor U).obj
      (Modules.unit X).presheafModuleCat).cycles 1) (y : Fin 2 → I) :
    Γ(X, ∏ᶜ fun l : Fin 2 ↦ U (y l)) :=
  (Pi.π (fun w : Fin 2 → I ↦ (Modules.unit X).presheafModuleCat.obj
    (op (∏ᶜ fun l : Fin 2 ↦ U (w l)))) y)
      (((CategoryTheory.cechComplexFunctor U).obj
        (Modules.unit X).presheafModuleCat).iCycles 1 z)

/-- Frames on a thickening with precisely the transitions 1+epsilon c_ij.
Source: Stacks 09NU and Milne III 2.1, with the convention m_j=(1+epsilon c_ij)m_i
(blueprint: lem-sfb-split-thickening-picard-cocycle). -/
def HasSplitThickeningFrames {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (z : ((CategoryTheory.cechComplexFunctor U).obj
      (Modules.unit X).presheafModuleCat).cycles 1)
    (M : X.dualNumbers.Modules) : Prop :=
  ∃ s : ∀ i, Γ(M, U i), (∀ i, Modules.IsFreeGenerator (s i)) ∧
    ∀ y : Fin 2 → I,
      M.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 1).op (s (y 1)) =
        (M.smul (1 + TrivSqZeroExt.inr (splitThickeningCocycleCoefficient U z y))).hom
          (M.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 0).op (s (y 0)))

/-- The exponential class is the canonical additive equivalence onto the reduction kernel.
Source: Stacks 0C6R, specialized to the split thickening
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
1. On each affine open identify the thickening with R[epsilon]; localization commutes
   with dual numbers, so this gives O_X plus epsilon O_X on every open.
2. Split the units sequence by constants. Its inclusion is a ↦ 1+epsilon a and its
   retraction is u+epsilon v ↦ u⁻¹v. Direct multiplication verifies all split identities.
3. The universal right-derived delta-functor gives the long exact sequence. The section
   kills the degree-zero boundary; equivalently H1 of the explicit retraction is inverse
   to H1 of the inclusion on the kernel.
4. Hilbert 90 and picard-h1-restriction-compatibility identify reduction with the units
   reduction map. Module-abelian-zariski-cohomology, through the common-resolution
   comparison, identifies the additive source with module H1. Their composite is exactly
   splitThickeningPicardClass. Its values lie in the kernel and give the equivalence. -/
theorem splitThickeningPicardCocycle
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    ∃ β : ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) ≃+
        Additive (Pic.mapHom X.dualNumbersι).ker,
      ∀ v, (β v).toMul.val = (splitThickeningPicardClass X v).toMul := by
  sorry

/-- An arbitrary-cover Cech cocycle glues to the exponential line bundle, and every bundle
with those frames has the specified class. No acyclicity of the cover is assumed.
Source: Stacks 0B8R, 01EQ and 09NU; Milne III 2.1
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
5. Torsor-h1 identifies an additive cocycle with its torsor having a_j=c_ij+a_i.
   Torsor-h1-functoriality for a ↦ 1+epsilon a gives the frame torsor with the displayed
   multiplicative transitions. Hilbert 90 identifies its bundle. Normalized Cech
   comparison sends the cocycle to this torsor class: apply its connecting-map law to
   the torsor extension by the constant integers, using the local sections to lift 1.
   The same argument with the module comparison of 01EQ gives the module class here.
   Gluing free rank-one modules gives existence; an isomorphism sending the displayed
   frames to each other proves independence of the bundle representative. -/
theorem splitThickeningPicardCocycle_frames
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj
        (Modules.unit X).presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X))
    (hc : Modules.IsModuleCechComparison U (Modules.unit X) 1 c)
    (z : ((CategoryTheory.cechComplexFunctor U).obj
      (Modules.unit X).presheafModuleCat).cycles 1) :
    (∃ (M : X.dualNumbers.Modules) (_hM : Modules.IsInvertible M),
      HasSplitThickeningFrames U z M) ∧
    ∀ (M : X.dualNumbers.Modules) [Modules.IsInvertible M],
      HasSplitThickeningFrames U z M →
        (splitThickeningPicardClass X
          (c (((CategoryTheory.cechComplexFunctor U).obj
            (Modules.unit X).presheafModuleCat).homologyπ 1 z))).toMul =
          Pic.ofIsInvertible M := by
  sorry

/-- Cancelling the original transitions leaves exactly 1+epsilon c_ij.
Source: Stacks 09NU and 0B8R; Milne III 2.1
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
6. Tensor a frame of the deformation with the inverse of the pulled-back original
   frame. The coefficient on overlaps is t_ij(1+epsilon c_ij)t_ij⁻¹=1+epsilon c_ij.
   Apply the preceding frames statement. Tensor products multiply exponential units,
   giving 1+epsilon(c_ij+c'_ij), hence addition; a frame change adds h_j-h_i. -/
theorem splitThickeningPicardCocycle_deformation
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj
        (Modules.unit X).presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X))
    (hc : Modules.IsModuleCechComparison U (Modules.unit X) 1 c)
    (z : ((CategoryTheory.cechComplexFunctor U).obj
      (Modules.unit X).presheafModuleCat).cycles 1)
    (L : X.Modules) [Modules.IsInvertible L]
    (M : X.dualNumbers.Modules) [Modules.IsInvertible M]
    (hred : Pic.map X.dualNumbersι (Pic.ofIsInvertible M) = Pic.ofIsInvertible L)
    (t : ∀ y : Fin 2 → I, Γ(X, ∏ᶜ fun l : Fin 2 ↦ U (y l))ˣ)
    (s : ∀ i, Γ(L, U i)) (hs : ∀ i, Modules.IsFreeGenerator (s i))
    (r : ∀ i, Γ(M, U i)) (hr : ∀ i, Modules.IsFreeGenerator (r i))
    (ht : ∀ y : Fin 2 → I,
      L.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 1).op (s (y 1)) =
        (L.smul (t y).val).hom
          (L.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 0).op (s (y 0))))
    (htr : ∀ y : Fin 2 → I,
      M.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 1).op (r (y 1)) =
        (M.smul (TrivSqZeroExt.inl (t y).val *
          (1 + TrivSqZeroExt.inr (splitThickeningCocycleCoefficient U z y)))).hom
            (M.presheaf.map (Pi.π (fun l : Fin 2 ↦ U (y l)) 0).op (r (y 0)))) :
    Pic.ofIsInvertible M * (Pic.map X.dualNumbersProj (Pic.ofIsInvertible L))⁻¹ =
      (splitThickeningPicardClass X
        (c (((CategoryTheory.cechComplexFunctor U).obj
          (Modules.unit X).presheafModuleCat).homologyπ 1 z))).toMul := by
  sorry

/-- The canonical exponential identification commutes with arbitrary scheme pullback.
Source: Stacks 0B8R, 01EQ and 01F7
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
7. Represent each H1 class by a torsor and choose its local sections, obtaining a Cech
   cocycle. Every normalized comparison system computes its torsor class: apply the
   connecting law to the torsor extension by Z, onto on all tuple intersections by
   the chosen local sections. Cech-comparison-inverse-image-unit sends this cocycle to
   its inverse-image cocycle; coefficient naturality applies f sharp. The resulting
   coefficients are f sharp(c_ij). The pulled-back exponential units have precisely
   these coefficients. The canonical module/abelian comparison identifies the map of
   these classes with the ordinary module-cohomology map defined from f sharp. -/
theorem splitThickeningPicardCocycle_pullback
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : Y ⟶ X) (hf : f ≫ (X ↘ Spec (.of k)) = (Y ↘ Spec (.of k)))
    (v : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) :
    Pic.map f.dualNumbers (splitThickeningPicardClass X v).toMul =
      (splitThickeningPicardClass Y
        (Modules.moduleCohomologyFMap f
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) 1 v)).toMul := by
  sorry

/-- Rescaling epsilon, including scaling by zero, acts by the same scalar on cohomology.
Source: Milne III 2.1 and Stacks 0B8R
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
8. Scaling sends 1+epsilon c_ij to 1+epsilon a c_ij. Naturality of each normalized
   comparison system for the coefficient map multiplication by a sends the class to
   H1(a). Module-abelian-zariski-cohomology identifies this with the module endomorphism
   multiplication by a. No division occurs, so the formula also holds for a=0. -/
theorem splitThickeningPicardCocycle_scale
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (a : k)
    (v : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) :
    Pic.map (X.dualNumbersScale (globalSectionsRingHom k (X := X) a))
        (splitThickeningPicardClass X v).toMul =
      (splitThickeningPicardClass X (globalSectionsRingHom k (X := X) a • v)).toMul := by
  sorry

/-- Tensor product corresponds to addition under the specified canonical map.
Source: Stacks 0C6R and Milne III 2.1
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof: multiply the local transition units. Their product is
1+epsilon(c_ij+c'_ij), because epsilon squared is zero. The additive map on cohomology
and Hilbert 90 carry this to tensor product, as in proof step 6. -/
theorem splitThickeningPicardCocycle_tensor
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (v w : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj (Modules.unit X)) :
    (splitThickeningPicardClass X (v + w)).toMul =
      (splitThickeningPicardClass X v).toMul *
        (splitThickeningPicardClass X w).toMul := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The represented Picard tangent identification has the exponential normalization.
Source: Milne III Proposition 2.1, pp.90–91, map a ↦ 1+a epsilon
(blueprint: lem-sfb-split-thickening-picard-cocycle).

Proof:
9. The Picard splitting identifies the kernel of reduction on the Picard functor with
   that on Picard groups: Pic(Spec k) and Pic(Spec k[epsilon]) vanish, and the chosen
   k-point splits the sequence. Degree is unchanged on the closed fibre, so the kernel
   lies in Pic0. Transfer through the representation to tangent vectors. Milne's
   tangent comparison is inverse to H1(a ↦ 1+a epsilon), exactly the map constructed
   above. Tensor and scalar compatibility give the linear equivalence. The formula
   below fixes it on every tangent vector, so no arbitrary equivalence is substituted. -/
theorem splitThickeningPicardCocycle_tangent
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (J : Over (Spec (.of k))) [GrpObj J]
    (e : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy J)
    (he : IsPicardMul (X ↘ Spec (.of k)) e) :
    ∃ Φ : tangentSpaceAt J η[J] ≃ₗ[k] (Scheme.Modules.unit X).H 1,
      ∀ (v : tangentSpaceAt J η[J])
        (L : (pullback (X ↘ Spec (.of k))
          (Scheme.dualNumbersOver (Spec (.of k))).hom).Pic),
        e.homEquiv v.val =
          (toPicardFunctor (X ↘ Spec (.of k))).app
            (op (Scheme.dualNumbersOver (Spec (.of k)))) L →
        Scheme.Pic.map
          (Scheme.isPullback_dualNumbersProj (X ↘ Spec (.of k))).isoPullback.hom L =
            (Scheme.splitThickeningPicardClass X
              ((Scheme.Modules.moduleCohomologyExtResolutionEquiv X
                (Scheme.Modules.unit X) 1).symm (Φ v))).toMul := by
  sorry

end AlgebraicGeometry
