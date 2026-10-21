/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProjectionMateSquareCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback

/-!
# Tensor-comparison coherence for the pro-etale base-change square

Source: Stacks 07A4, 0D6D and 0E48
(blueprint: lemma-weil-pbc-proetale-projection-formula-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' u'' v'' u''' v'''

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


/-- Concrete tensor coherence for the four pro-etale pullbacks and their canonical
comparisons. It is obtained by instantiating `ringedSquareTensorCompatibility` with
the four pro-etale ringed edges and the canonical square comparison.

Proof: construct the ringed tensor square from the four pro-etale pullback edges and
apply the representative tensor compatibility theorem on flat K-flat complexes; tensor
descent gives the displayed derived identity.
(blueprint: lem-weil-pbc-proetale-projection-formula-tensor-coherence). -/
theorem proEtaleProjectionFormula_tensor_coherence
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RY')
    (cg' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj RX ≅ RX')
    (cf' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj RY' ≅ RX')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
      (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf'))
    (aY : ProEtaleTensorModel Y RY) (aX : ProEtaleTensorModel X RX)
    (aY' : ProEtaleTensorModel Y' RY') (aX' : ProEtaleTensorModel X' RX') :
    ∀ (P Q : DerivedCategory (proEtaleRingModules Y RY)),
      (proEtaleAmbientRingedPullbackComparison sq RX RY RX' RY'
        cf cg cg' cf' hcoeff).hom.app (aY.tensor.obj (P, Q)) ≫
          (proEtaleRingDerivedPullback g' RX RX' cg').map
            ((proEtaleCanonicalTensorComparison f RY RX cf aY aX).hom.app (P, Q)) ≫
          (proEtaleCanonicalTensorComparison g' RX RX' cg' aX aX').hom.app
            ((proEtaleRingDerivedPullback f RY RX cf).obj P,
              (proEtaleRingDerivedPullback f RY RX cf).obj Q) =
        (proEtaleRingDerivedPullback f' RY' RX' cf').map
            ((proEtaleCanonicalTensorComparison g RY RY' cg aY aY').hom.app (P, Q)) ≫
          (proEtaleCanonicalTensorComparison f' RY' RX' cf' aY' aX').hom.app
            ((proEtaleRingDerivedPullback g RY RY' cg).obj P,
              (proEtaleRingDerivedPullback g RY RY' cg).obj Q) ≫
          aX'.tensor.map (Prod.mkHom
            ((proEtaleAmbientRingedPullbackComparison sq RX RY RX' RY'
              cf cg cg' cf' hcoeff).hom.app P)
            ((proEtaleAmbientRingedPullbackComparison sq RX RY RX' RY'
              cf cg cg' cf' hcoeff).hom.app Q)) := by
  sorry

end AlgebraicGeometry.Scheme

