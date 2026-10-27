/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionCoprojection

/-! Tensor and adjunction consequences of the coordinate scalar normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite

/-- Tensoring the normalized coordinate scalar gives the canonical closed
coprojection formula and both twisted transpose equations.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, even-shift paragraph;
lem-pur-twisted-coordinate-section-normalization, Steps 6, 8--9.
(blueprint: lem-pur-coordinate-section-tensor-trace).

Proof: The finite Tate line and all its tensor powers are locally free of rank
one; their even shifts are invertible and have finite Tor amplitude. Proper
projection for the closed section therefore makes closedProjection and
closedTensorProjection invertible. Transpose inverse closed projection followed
by identity tensor the closed counit: this is precisely coprojectionMate.
The immersion-twist theorem proves its invertibility on these inputs. Substituting
the closed adjunct-counit identity into this mate shows that ordinaryOrientation
is the coefficient unitor inverse, identity tensor unitOrientation, then this
canonical mate. For the untwisted scalar, the two adjunct-counit identities and
the conjugate composition comparison turn the given scalar equation into the
exceptional composite identity. CoordinateLine.comparison and exceptionalComposition
are isomorphisms, so cancellation proves unitOrientation is invertible. Tensoring
it proves the asserted twisted isomorphy. Naturality of compact projection, with
the coefficient first, identifies the twisted compact composite with identity
tensor the scalar composite, conjugated by the coefficient unitor. The composition
projection mate for ps=id fixes the source as sectionComposition, with no extra
automorphism. Transposing this equality under the closed and compact adjunctions
gives the final exceptional identity. All interchanges have sign
(-1)^(2r*2)=1. These arguments apply also to the unit input separately and to the
empty base. -/
theorem coordinateSectionTensorTrace
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _)) :
    CoprojectionNormalization A T N hN hA hT hI ∧
    ∀ r : ℕ, ∃ hpf : IsIso (closedProjection A T
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)),
    IsIso (ordinaryOrientation A T N hN hA hT hI
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ∧
    ((sectionComposition A T).inv.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) =
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).inv ≫
      ((Etale.ordinaryFiniteTensor A T).obj
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).map
          ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
            (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
            CoordinateLine.integration A N hA T hN hT) ≫
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).hom) ∧
    (ordinaryOrientation A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app
          (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)) ≫
      (exceptionalComposition A T).hom.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) = 𝟙 _) := by sorry

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
