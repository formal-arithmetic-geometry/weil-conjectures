/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.SurfaceRationalMapPointResolution
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup

/-! # Point-blowup domination of a modification over a regular trait surface

Source: Stacks Project, Resolution of Surfaces, Tag 0C5H, applied over C, with
Tags 0AGR, 02IZ, 02NS, 087S and 01WE for the dimension and projectivity bookkeeping
(blueprint: lem-sfb-regular-trait-modification-graph-tower).

The fraction field is arbitrary, with its specified fraction-ring structure. Special
fibres use the scheme-theoretic fibre over the closed point of the trait. The existing
ordinary blowup tower includes length zero and specifies the actual composite maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An H-projective modification of C is dominated, over C, by point blowups of Z.
The centres are reduced closed special-fibre points with two-dimensional regular local
rings; all tower levels retain integral, regular, Noetherian, H-projective geometry.

Source: Stacks Project, Tag 0C5H applied with S = C, X = Z and Y = Γ;
Tags 0AGR, 02IZ, 02NS, 087S and 01WE
(blueprint: lem-sfb-regular-trait-modification-graph-tower).

Proof plan:
1. A DVR has a uniformizer π and every nonzero element is a unit times a power of π
   (lem-weil-pbc-dvr-unit-times-uniformizer-power). Thus A[1/π] = F, and Spec A has
   exactly a generic point and a closed point. By
   lem-weil-pbc-principal-localization-open-immersion, Spec F is the open D(π).
   Its pullback U = Z_F is nonempty by the generic isomorphism and integrality of C_F,
   and dense by integrality of Z (def-pc-integral-scheme, def-pc-base-change).
2. H-projective composition and projective properness
   (lem-trf-h-projective-composition, lem-kun-projective-implies-proper) make Z proper
   over the trait. Its closed image contains the generic point, so the special fibre
   is nonempty. Minimize a nonempty closed subset there using
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Sobriety (lem-sc-scheme-sober)
   makes a minimal such subset a closed singleton, of local dimension two by hypothesis.
3. The chain formula lem-sc-scheme-stalk-dimension-generalization-chains identifies
   global dimension with the supremum of local dimensions
   (def-kun-topological-krull-dimension). The local upper bound and step 2 give dim Z = 2.
4. Over U form the map Z_F -> C_F -> Γ_F -> Γ using the inverse of p_F.
   Apply lem-sfb-surface-rational-map-point-resolution over C, with p proper by
   lem-kun-projective-implies-proper. This supplies the tower and a, with a p = b r,
   all levels integral, regular and Noetherian, and b an isomorphism over U.
5. Each centre avoids the inverse image of U. Since the trait has exactly two points,
   def-pc-base-change and def-pc-scheme-fibre identify that complement with the special
   fibre at every stage. The vanishing ideal gives the reduced point structure.
6. Induct on the levels to show all closed special-fibre points have local dimension
   two. Properness sends a closed point to a closed point; away from the centre the
   blowup is an isomorphism, and over the centre apply
   lem-sfb-regular-point-blowup-geometry. Regularity gives the regular local ring clause
   (def-weil-regular-scheme). There is no centre to check for length zero.
7. The reduced point ideal is quasi-coherent (def-sbc-closed-immersion-ideal-sheaf) and
   finite type on Noetherian affine charts (pqf-lem-affine-open-locnoeth,
   def-weil-pbc-noetherian-ring). Inductively apply
   lem-sfb-projective-affine-base-blowup over Spec A. Each blowup and each level over
   the trait is H-projective, starting from Z -> C -> Spec A.
8. Put h = b r and Y = Z_m. The C-morphism identity is a p = h
   (def-weil-scheme-over-base). H-projective composition makes h H-projective;
   its generic restriction is the composite of the two generic isomorphisms.
   For length zero b is the initial isomorphism and this construction gives h = r
   after identifying Z_0 with Z.
-/
theorem exists_regular_trait_modification_graph_tower
    (A F : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (C Z Γ : Scheme.{u}) [IsIntegral C] [IsIntegral Z] [IsIntegral Γ]
    (c : C ⟶ Spec (.of A)) [IsHProjective c]
    (r : Z ⟶ C) [IsHProjective r] [IsNoetherian Z]
    (hZ : IsRegularScheme Z)
    (hgeneric : IsIntegral (pullback c (Spec.map (CommRingCat.ofHom (algebraMap A F)))))
    (hr : IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map
      (Over.homMk r rfl : Over.mk (r ≫ c) ⟶ Over.mk c)).left))
    (hdim : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 2)
    (hspecial : ∀ z : (r ≫ c).fiber (IsLocalRing.closedPoint A),
      IsClosed ({z} : Set ((r ≫ c).fiber (IsLocalRing.closedPoint A))) →
        ringKrullDim (Z.presheaf.stalk
          ((r ≫ c).fiberι (IsLocalRing.closedPoint A) z)) = 2)
    (p : Γ ⟶ C) [IsHProjective p]
    (hp : IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map
      (Over.homMk p rfl : Over.mk (p ≫ c) ⟶ Over.mk c)).left)) :
    ∃ (B : OrdinaryBlowupTower Z) (a : B.level (Fin.last B.length) ⟶ Γ),
      (∀ i : Fin B.length, ∃ (z : B.level i.castSucc)
        (hz : IsClosed ({z} : Set (B.level i.castSucc))),
        B.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩ ∧
        (B.toBase i.castSucc ≫ r ≫ c) z = IsLocalRing.closedPoint A ∧
        IsRegularLocalRing ((B.level i.castSucc).presheaf.stalk z) ∧
        ringKrullDim ((B.level i.castSucc).presheaf.stalk z) = 2) ∧
      (∀ i : Fin (B.length + 1), IsIntegral (B.level i) ∧
        IsRegularScheme (B.level i) ∧ IsNoetherian (B.level i) ∧
        IsHProjective (B.toBase i ≫ r ≫ c)) ∧
      a ≫ p = B.toBase (Fin.last B.length) ≫ r ∧
      IsHProjective (B.toBase (Fin.last B.length) ≫ r) ∧
      IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map
        (Over.homMk (B.toBase (Fin.last B.length) ≫ r) rfl :
          Over.mk ((B.toBase (Fin.last B.length) ≫ r) ≫ c) ⟶ Over.mk c)).left) := by
  sorry

end AlgebraicGeometry
