/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCartierGenericStalkDvr
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-! # Isomorphism near a noncontracted exceptional fibre

Source: Stacks Project, resolve.tex, Tag 0C5R,
Lemma `lemma-proper-birational-regular-surfaces`, final exceptional-fibre argument
(blueprint: lem-sfb-point-exceptional-isomorphism-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A proper birational map between point blowups of regular Noetherian surfaces,
nonconstant on the source exceptional fibre, is an isomorphism over a neighbourhood
of the target exceptional fibre. The induced fibre map is an isomorphism, and its
source is the entire inverse image of the target fibre as an underlying subset.

The centres are the vanishing ideals of the closed singletons, hence are reduced.
The exceptional schemes and their inclusions are the actual scheme-theoretic fibres.
Birationality means that the given map restricts to an isomorphism of dense opens.

Source: Stacks Project, resolve.tex, Tag 0C5R, final exceptional-fibre argument
(blueprint: lem-sfb-point-exceptional-isomorphism-neighbourhood).

Proof plan:
1. Apply lem-sfb-point-blowup-exceptional-conormal at t and s. The local dimension
   at t is one or two; the one-dimensional case has a one-point exceptional fibre
   and contradicts the nonconstant-image hypothesis. Thus both exceptional fibres
   are regular integral projective lines, effective Cartier divisors with positive
   conormal twist. The ambient blowups are integral regular Noetherian by
   lem-sfb-regular-point-blowup-geometry, and normal by rem-pc-regular-normal.
2. The composite E to S' is proper (lem-weil-pbc-closed-immersion-proper), so v is
   proper by lemma-nagata-proper-to-separated-target. Its closed irreducible image
   has more than one point, so it is all of the integral curve F. At the generic
   point of F the ambient local ring is a DVR by lem-sbc-regular-cartier-generic-stalk-dvr.
   The given dense-open isomorphism identifies generic points and local rings.
   Clause (2) of lem-sfb-normal-modification-codimension-one therefore gives an
   isomorphism neighbourhood of that generic point for h.
3. On this neighbourhood E is a closed subscheme of F containing its generic point.
   An ideal in an integral affine ring that vanishes in the fraction field is zero,
   so these subschemes agree there. Thus v is birational. Give E its kappa(s)-structure
   through v. Properness of v and F makes E proper over kappa(s), using
   lem-weil-pbc-proper-composition. Both are integral separated finite-type curves
   over that common field and F is normal, so
   lem-trf-proper-birational-normal-curve-iso gives that v is an isomorphism.
4. The canonical conormal map of lem-weil-pbc-closed-immersion-conormal-functorial
   is generically invertible, by the neighbourhood in step 2 and the affine
   ideal-mod-square formula. Identify both conormals with the positive twists from
   lem-sfb-point-blowup-exceptional-conormal. The absolute projective-line
   isomorphism v and lem-sfb-projective-line-twist-rigidity make it invertible
   everywhere; the residue fields need not initially be equal.
5. Identify E with F by v. The same conormal map is now the comparison for their
   two closed immersions into T' and S'. It is surjective, and h is locally of
   finite type by def-weil-proper-morphism. Apply lem-sfb-conormal-surjection-unramified
   to obtain unramified neighbourhoods of every point of E.
6. By lem-weil-pbc-unramified-quasi-finite-at-points and pqf-def-quasifinite, h is
   quasi-finite at every point of E. For each y in F choose its preimage under v.
   The target local ring is normal, so clause (4) of
   lem-sfb-normal-modification-codimension-one puts y in the maximal open N over
   which h is an isomorphism. This proves the neighbourhood conclusion.
7. Since F lies in N, each point of F has exactly one preimage under h, and the
   isomorphism v supplies that point in E. The commuting square gives the reverse
   containment, proving the equality of underlying closed subsets.
-/
theorem point_exceptional_isomorphism_neighbourhood
    (T S : Scheme.{u}) [IsIntegral T] [IsIntegral S] [IsNoetherian T] [IsNoetherian S]
    (hT : IsRegularScheme T) (hS : IsRegularScheme S)
    (hdimT : topologicalKrullDim T = 2) (hdimS : topologicalKrullDim S = 2)
    (t : T) (s : S) (ht : IsClosed ({t} : Set T)) (hs : IsClosed ({s} : Set S))
    (hdims : ringKrullDim (S.presheaf.stalk s) = 2)
    (h : (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowup ⟶
      (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowup) [IsProper h]
    (hbirational : ∃ (V : (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowup.Opens)
      (U : (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowup.Opens),
      Dense (V : Set (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowup) ∧
      Dense (U : Set (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowup) ∧
      ∃ e : V.toScheme ≅ U.toScheme, V.ι ≫ h = e.hom ≫ U.ι)
    (v : (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowupMap.fiber t ⟶
      (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowupMap.fiber s)
    (hcomm : (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowupMap.fiberι t ≫ h =
      v ≫ (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowupMap.fiberι s)
    (himage : ∃ e₁ e₂ : (IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowupMap.fiber t,
      v e₁ ≠ v e₂) :
    (∃ N : (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowup.Opens,
      Set.range ((IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowupMap.fiberι s) ⊆
        (N : Set (IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowup) ∧ IsIso (h ∣_ N)) ∧
    IsIso v ∧
    h ⁻¹' Set.range ((IdealSheafData.vanishingIdeal ⟨{s}, hs⟩).blowupMap.fiberι s) =
      Set.range ((IdealSheafData.vanishingIdeal ⟨{t}, ht⟩).blowupMap.fiberι t) := by
  sorry

end AlgebraicGeometry.Scheme
