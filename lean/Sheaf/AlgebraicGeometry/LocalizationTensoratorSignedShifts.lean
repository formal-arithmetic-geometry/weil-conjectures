/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Algebra.Homology.DerivedTensorShiftDescent
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Localization tensorators and signed shifts

Source: Stacks Project, cohomology.tex, Tag 0FPB; sites-cohomology.tex, Tags 06YS and
06YU; more-algebra.tex, Tag 0FNH, item-shift-tensor, with the second shift extracted first.
(blueprint: lem-sfb-localization-tensorator-signed-shifts)

The two auxiliary isomorphisms compose the existing one-variable comparisons in the
prescribed order. The theorem concerns arbitrary unbounded complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- Extract the second shift first, giving sign `(-1)^(b*i)` in shifted first degree `i`.
The unsigned first comparison is then shifted by `b`, and the two shifts are combined.
Source: Stacks Project, Tag 0FNH, item-shift-tensor, with the extraction order of the node.
(blueprint: lem-sfb-localization-tensorator-signed-shifts) -/
def schemeSignedTotalTensorShift
    (K L : CochainComplex (ringedSiteModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b : ℤ) : (K⟦a⟧ ⊗ L⟦b⟧) ≅ (K ⊗ L)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (K⟦a⟧) L (curriedTensor _) b ≪≫
    (shiftFunctor _ b).mapIso (CochainComplex.mapBifunctorShift₁Iso K L (curriedTensor _) a) ≪≫
    (shiftFunctorAdd' _ a b (a + b) rfl).symm.app (K ⊗ L)

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Extract the second shift and then the first in the specified K-flat derived tensor.
Uses the existing canonical scheme tensor-shift structure, descended from total tensor;
it makes no choice of a new tensor or of unnormalized shift comparisons.
Source: Stacks Project, Tags 0FNH and 06YU; the canonical K-flat localization construction.
(blueprint: lem-sfb-localization-tensorator-signed-shifts) -/
def schemeSignedDerivedTensorShift (M N : schemeDerivedCategory X) (a b : ℤ) :
    M⟦a⟧ ⊗ N⟦b⟧ ≅ (M ⊗ N)⟦a + b⟧ := by
  letI := schemeCanonicalTensorShift X
  exact (((curriedTensor _).obj (M⟦a⟧)).commShiftIso b).app N ≪≫
    (shiftFunctor _ b).mapIso ((((curriedTensor _).flip.obj N).commShiftIso a).app M) ≪≫
    (shiftFunctorAdd' _ a b (a + b) rfl).symm.app (M ⊗ N)

/-- The canonical lax localization tensorator commutes with the prescribed signed
simultaneous shift on arbitrary complexes. Neither tensorator is required to be invertible.
Source: Stacks Project, Tag 0FPB, canonical K-flat construction; Tags 06YS, 06YU and 0FNH.
(blueprint: lem-sfb-localization-tensorator-signed-shifts)

Proof. First extract the second complex shift using the total-tensor comparison of
lem-weil-pbc-total-tensor-integer-shifts; on first shifted degree i its sign is (-1)^(b*i).
Extracting the first shift afterwards is unsigned. The differential signs agree modulo two,
including for negative a and b (def-pc-tensor-complex-sheaves).
Choose flat-term K-flat resolutions P -> K and R -> L by lem-pc-kflat-resolution.
Their shifts remain resolving complexes by lem-weil-pbc-kflat-fixed-tensor-triangulated.
The tensor v of the two localized shifted resolution maps is therefore invertible.
On P,R, lem-sf-ringed-derived-native-tensor identifies the inverse tensorator with the
K-flat representative comparison. The transformation-extension property of
lem-weil-pbc-site-derived-tensor-descent identifies this tensor with the published tensor.
The normalization of lem-weil-pbc-derived-tensor-shift-descent, applied second then first,
gives the equality on P,R, after cancelling adjacent inverse representative comparisons.
Write A and B for the two displayed composites and w for the localized total resolution
map shifted by a+b. Naturality of the tensorator, total shift and localization shift gives
A(K,L) v = w A(P,R). Naturality of the descended shift gives B(K,L) v = w B(P,R).
The resolving-pair equality implies A(K,L) v = B(K,L) v. Cancel only v, proving the claim
without inverting w or the tensorator at K,L. -/
theorem localization_tensorator_signed_shifts
    (K L : CochainComplex (ringedSiteModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b : ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q (K⟦a⟧) (L⟦b⟧) ≫
        DerivedCategory.Q.map (schemeSignedTotalTensorShift X K L a b).hom ≫
        (DerivedCategory.Q.commShiftIso (a + b)).hom.app (K ⊗ L) =
      ((DerivedCategory.Q.commShiftIso a).hom.app K ⊗ₘ
        (DerivedCategory.Q.commShiftIso b).hom.app L) ≫
        (schemeSignedDerivedTensorShift X (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) a b).hom ≫
        (Functor.LaxMonoidal.μ DerivedCategory.Q K L)⟦a + b⟧' := by
  sorry

end AlgebraicGeometry
