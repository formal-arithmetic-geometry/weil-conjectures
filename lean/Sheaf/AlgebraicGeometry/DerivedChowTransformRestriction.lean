/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Restriction of a derived Chow graph-kernel transform

Source: Stacks Project, More on Morphisms, Tag 0CSK,
lemma-compute-Fourier-Mukai-for-derived-chow, displayed derived isomorphism and proof
(blueprint: lem-sfb-derived-chow-transform-restriction).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- A graph structure-sheaf kernel on the inverse image of V gives the direct image
along the closed immersion j from U to V. The scheme P is identified with projective
n-space by eP, and T with X times_A P by the pullback condition. W is the common
inverse-image open, so the two resLE maps are precisely b|W and c|W. The right-hand
map is their specified composite, not an arbitrary closed immersion.

Source: Stacks Project, More on Morphisms, Tag 0CSK,
lemma-compute-Fourier-Mukai-for-derived-chow
(blueprint: lem-sfb-derived-chow-transform-restriction).

Proof:
1. Set T_V = q^{-1}(V). The inverse image of h is the closed immersion i:W -> T_V
   by lem-pc-closed-imm-base-change. Set e = b|W. The two projections composed
   with i equal U.ι composed with e and j composed with e, respectively.
2. By lem-pc-closed-module-pushforward-homology, closed module pushforwards are
   exact and preserve quasi-isomorphisms. Their K-injective computation
   (def-pc-ringed-spaces-derived-direct-image) identifies Rh_*O_Z[0] with
   (h_*O_Z)[0], and similarly for i. Restrict using
   lem-pc-restrict-derived-direct-image-open and the kernel hypothesis to obtain
   E|T_V isomorphic to Ri_*O_W[0].
3. Apply lem-pc-restrict-derived-direct-image-open to q and
   lem-pc-derived-tensor-open-restriction-natural to its integrand. Restriction is
   derived open pullback, since the structural ring map is an isomorphism and
   restriction is exact (def-pc-derived-pullback). Composition of pullbacks
   (lem-pc-ringed-spaces-derived-pullback-composition) identifies the first factor
   with M = Lp_V^*K. The left side is Rq_V*(M tensor Ri_*O_W[0]).
4. M has quasi-coherent cohomology by lem-pc-derived-pullback-qcoh-component
   and its local definition (pqf-def-coherent). O_W[0] also does. A closed
   immersion is affine and quasi-compact, and its diagonal is an isomorphism,
   hence it is quasi-separated. Thus i satisfies the projection-formula
   hypotheses, without assuming V quasi-compact or i finitely presented.
5. Apply lem-pc-projection-formula to i, O_W[0], M. Tensor symmetry from
   lem-sc-derived-internal-hom-adjunction and the unit from
   def-pc-scheme-derived-tensor-structure give Ri_*Li^*M. Apply Rq_V*, then
   lem-pc-derived-direct-image-composition and
   lem-pc-ringed-spaces-derived-pullback-composition to obtain R(je)_*Le^*(K|U).
6. Pullback along the isomorphism e is an equivalence by the unital composition
   comparisons of lem-pc-ringed-spaces-derived-pullback-composition. Its right
   adjoint Re_* (lem-pc-ringed-spaces-derived-adjoint) is its inverse. Composition
   of direct images (lem-pc-derived-direct-image-composition) therefore gives
   R(je)_*Le^*(K|U) isomorphic to Rj_*(K|U). Compose these derived isomorphisms. -/
theorem derivedChow_transform_restriction
    (A : Type u) [CommRing A] (n : ℕ)
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X P T Z : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (eP : P ≅ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A)
    (p : T ⟶ X) (q : T ⟶ P)
    (_hT : IsPullback p q f
      (eP.hom ≫ Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A))
    (h : Z ⟶ T) [IsClosedImmersion h]
    (U : X.Opens) (V : P.Opens) (W : Z.Opens)
    (hWU : W = (h ≫ p) ⁻¹ᵁ U) (hWV : W = (h ≫ q) ⁻¹ᵁ V)
    [IsIso ((h ≫ p).resLE U W hWU.le)]
    [IsClosedImmersion ((h ≫ q).resLE V W hWV.le)]
    (E : schemeDerivedCategory T)
    (_hE : Nonempty
      ((schemeOpenRestriction T (q ⁻¹ᵁ V)).mapDerivedCategory.obj E ≅
        (schemeOpenRestriction T (q ⁻¹ᵁ V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward h).obj
                (SheafOfModules.unit (moduleRings Z.toRingedSpace))))))
    (K : schemeDerivedQCohCategory X) :
    Nonempty
      ((schemeOpenRestriction P V).mapDerivedCategory.obj
          ((schemeDerivedDirectImage q).obj ((derivedPullback p).obj K.obj ⊗ E)) ≅
        (schemeDerivedDirectImage
          (inv ((h ≫ p).resLE U W hWU.le) ≫ (h ≫ q).resLE V W hWV.le)).obj
            ((schemeOpenRestriction X U).mapDerivedCategory.obj K.obj)) := by
  sorry

end AlgebraicGeometry
