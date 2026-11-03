/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.QcqsRefinementIndependence

/-! Transport of the normalized compositor through compactification refinements.
(blueprint: new-p3-qcqs-normalized-interchange-transport)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ell : ℕ) [Fact ell.Prime]

/-- The fixed-triangle normalized compositor transports through all compatible triangles.
Source: Stacks Tag 0F7J, lemma-shriek-composition; latest blueprint composition proof,
"The composition isomorphism" and "Verification of canonicity and associativity"
(blueprint: new-p3-qcqs-normalized-interchange-transport).

Proof: Dominate the supplied triangle and an arbitrary compatible triangle by a common
compatible refinement, using graph closures in fibre products. Apply the proper/open
tower-refinement identity to identify the two normalized component formulas through the
three proper refinement maps. The refinement fields of the coherent systems identify
these maps with their system comparisons. Cancel the common refinement using the comparison
cocycle equations and uniqueness of normalized interchange. The resulting formula on the
arbitrary triangle is exactly TowerNormalized for extendCompositor. -/
theorem qcqsNormalizedInterchangeTransport
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ell ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (T : Compactification.Triangle (modelMap D h₀) (modelMap D g₀))
    [QuasiCompact (T.cf.g ≫ T.cg.i)]
    (sh : System ell (modelMap D h₀)) (sg : System ell (modelMap D g₀))
    (sgh : System ell (modelMap D h₀ ≫ modelMap D g₀))
    (A : sh.support ell T.cf ⋙ sg.support ell T.cg ≅ sgh.support ell T.cfg)
    (hA : ∀ K : C ell (D.geometricFiber X₀).left,
      ∃ m, compositionInterchangeIsNormalized
          (Profinite.padicAlgClRingObj ell) T.cf.g T.cg.i
          (detSfBoundaryCompactification (middle T))
          (D((T.cf.i)_!open⟦Profinite.padicAlgClRingObj ell⟧).obj K.obj) m ∧
        ((A.hom.app K).hom =
          R((T.cg.g)_*⟦Profinite.padicAlgClRingObj ell⟧).map
            (m ≫ R((T.p)_*⟦Profinite.padicAlgClRingObj ell⟧).map
              ((openFactor (Profinite.padicAlgClRingObj ell) T.cf.i T.q T.cfg.i
                T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp (Profinite.padicAlgClRingObj ell)
            T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ell⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg
              (fun t ↦ lowerStar (Profinite.padicAlgClRingObj ell) t) T.p_g))).hom.app
            (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ell⟧).obj K.obj))) :
    TowerNormalized ell sh sg sgh (extendCompositor ell sh sg sgh T A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
