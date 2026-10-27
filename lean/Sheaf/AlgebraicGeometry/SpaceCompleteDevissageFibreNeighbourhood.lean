/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AffineCompleteDevissageDimensionFlattening
public import Sheaf.TraceFormula.CompleteAlgebraDevissage
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.TraceFormula.CompleteAlgebraDevissageBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Complete algebra devissages on charts covering a fibre

Source: Stacks Project, spaces-flat.tex, Tag 0CWJ; flat.tex, Tags 05HU and 05HX
(blueprint: lem-sfb-space-complete-devissage-fibre-neighbourhood).

The base is Spec Z in the chosen scheme universe. The affine schemes, their maps, and
section modules use the existing canonical constructions `affineDevissageScheme`,
`affineDevissageArrow` and `affineDevissageSections`. Fibre coverage is the inverse image
of the distinguished base point in the existing space of field-valued point classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finitely many affine etale charts cover the whole distinguished fibre after an
etale affine base neighbourhood, and the pulled-back section modules admit complete
algebra devissages over its distinguished prime. Finite presentation means local finite
presentation, quasi-compactness, and quasi-compactness of the diagonal.

Source: Stacks Project, spaces-flat.tex, Tag 0CWJ, specialized to finite presentation;
flat.tex, Tags 05HU, 05HX, 05I1 and 05HJ
(blueprint: lem-sfb-space-complete-devissage-fibre-neighbourhood).

Proof:
1. Choose an affine open neighbourhood Y_0 of y. Quasi-compactness of f makes X_0
   quasi-compact. The finite affine subatlas criterion gives an affine surjective etale
   atlas V of X_0. The chart test makes V to Y_0 locally finitely presented, hence its
   coordinate algebra is finitely presented. Use the quasi-compact affine tests,
   finite-affine-subatlas, chartwise-etale-permanence and affine lfp criteria.
2. The affine chart calculus identifies the restriction of M with the associated sheaf
   of its finitely presented section module N. Tensor realization identifies restriction
   with the stated pullback. Apply complete-algebra-devissage-etale-existence at every
   point of V_y, obtaining pointed affine etale base and source neighbourhoods with
   complete devissages and unchanged distinguished residue fields.
3. Etale cancellation makes the source maps to the corresponding base changes etale.
   Their fibre images are open and cover V_y. The affine fibre is quasi-compact, so take
   a finite subcover; take the empty family if V_y is empty.
4. Take the finite fibre product of the chosen base neighbourhoods, or Y_0 for an empty
   family. Its tensor-product ring maps to kappa(y) using the chosen residue-field maps.
   The kernel is a prime with residue field kappa(y), giving the common pointed affine
   etale neighbourhood. Use affine fibre products and etale base change and composition.
5. Base change the selected source charts to this common neighbourhood. They remain
   affine and representably etale. On the distinguished fibre their images still cover
   V_y, hence all of X_y by surjectivity of the atlas. This also verifies the empty case.
6. The affine etale maps and V to Y_0 have finitely presented coordinate algebras.
   Compose their finite presentations and tensor them with the common base ring.
   Each resulting affine chart map is locally finitely presented, quasi-compact and
   has quasi-compact diagonal, by affine-morphism permanence and separatedness.
7. Etale/Zariski comparison, affine base change for sections, and chart tensor
   realization identify the resulting sections with the tensor extensions of the
   previously chosen modules. Complete-algebra-devissage-base-change preserves their
   devissages at the distinguished prime. Rename the base and charts. No flatness of M
   or nonemptiness of the fibre is used. -/
theorem exists_completeDevissage_fibre_neighbourhood
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom))
    (M : X.QCoh) (hM : M.obj.IsFinitePresentation) (y : Y.left) :
    ∃ (R : CommRingCat.{u}) (g : affineDevissageScheme R ⟶ Y) (p : PrimeSpectrum R),
      Etale g.left ∧ g.left p = y ∧
      ∃ (n : ℕ) (A : Fin n → CommAlgCat.{u} R)
        (h : ∀ j : Fin n, schemeSpace (affineDevissageScheme (A j)) ⟶
          enlargedFibreProduct f (dimensionFlatBaseMap g)),
        (∀ j : Fin n,
          IsEtale (h j).hom.hom ∧
          (h j).hom ≫ Limits.pullback.snd f.hom (dimensionFlatBaseMap g).hom =
            (dimensionFlatBaseMap (affineDevissageArrow R (A j))).hom ∧
          ∃ hAfp : Algebra.FinitePresentation R (A j),
          ∃ hfinite : Module.Finite (A j)
            (affineDevissageSections (A j)
              ((moduleTensorPullback
                (h j ≫ enlargedFibreProductFst f (dimensionFlatBaseMap g))).obj M.obj)),
            Nonempty (@CompleteAlgebraDevissage R (A j) _ _ _
              (@Algebra.FiniteType.of_finitePresentation R (A j) _ _ _ hAfp) p.asIdeal inferInstance
              (affineDevissageSections (A j)
                ((moduleTensorPullback
                  (h j ≫ enlargedFibreProductFst f (dimensionFlatBaseMap g))).obj M.obj))
              _ _ hfinite)) ∧
        ∀ x : Point (enlargedFibreProduct f (dimensionFlatBaseMap g)).obj.obj,
          mapPoint (Limits.pullback.snd f.hom (dimensionFlatBaseMap g).hom).hom x =
            schemePointMap (𝟙 (yoneda.obj (affineDevissageScheme R))) p →
          ∃ j : Fin n, x ∈ pointImage (h j).hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
