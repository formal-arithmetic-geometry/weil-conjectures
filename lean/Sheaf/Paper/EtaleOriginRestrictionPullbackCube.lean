/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.EtaleOriginScalarPullbackData

/-! # Intrinsic realization and scalar pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Etale.scalarTensorIso Scheme.completedAdicDerivedChange

/-- The restriction/realization comparison commutes with geometric pullback.
Source: Stacks 03EL, 0D6D and 07A6; restriction part of the coefficient comparison
in Tag 0E48 (blueprint: lem-fix-etale-origin-restriction-pullback-cube).

Proof: first compare the ordinary right-adjoint squares on sections. Restriction
changes only the scalar action, and the normalized realization and direct-image
comparisons leave every scalar-unit section unchanged. The two pastings therefore
agree; the sheafification adjunction extends the equality from these sections.
Pass to complexes and use K-injective representatives for each right-derived
image and its restriction. Use the resolution comparisons to compare both routes
with direct image of the same resolution arrow; do not assume restriction preserves
K-injectivity. Cancel the localized quasi-isomorphisms. Conjugate this equality
under the two geometric adjunctions. The definition of originPullback is exactly
this conjugation of the ambient site/direct-image mate, whereas
originRestrictionPullback is the specified restriction/pullback inverse.
Naturality and the adjunction triangle identities give the displayed cube, with
the inverses of properOriginRestrictionIso at its two ends. This uses no tensor
comparison, no extension of scalars and no bound on the arbitrary B-complex N.
The argument applies unchanged to zero rings, zero complexes and empty schemes. -/
theorem etaleOriginRestrictionPullbackCube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) Y) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map
        ((properOriginRestrictionIso φ Y).inv.app N) ≫
      (originRestrictionPullback φ p).app
        ((finiteCoefficientIntrinsicDerivedComparison Y B).obj N) ≫
      (scalarMateRestriction φ Z).mapDerivedCategory.map ((originPullback B p).app N) =
    (originPullback A p).app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj N) ≫
      (finiteCoefficientIntrinsicDerivedComparison Z A).map
        ((Etale.scalarRestrictionPullbackIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).hom.app N) ≫
      (properOriginRestrictionIso φ Z).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).leftDerivedFunctor.obj
          N) := by sorry

end AlgebraicGeometry.ProEtale
