/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechExtSectionIso
import Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions
import Mathlib.Algebra.Homology.HomologySequence

/-! # Boundary squares before taking the augmentation quotient

Source: Stacks Project, Tags 01EQ, 013T and 0117.
(blueprint: lem-pc-abelian-cech-augmentation-boundary-squares)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The coefficient and section augmentations have the same total boundary.
Source: Stacks 01EQ, augmented double complex; 013T, horseshoe; 0117, naturality.
(blueprint: lem-pc-abelian-cech-augmentation-boundary-squares)

Proof: Extend the prescribed end resolutions to a horseshoe resolution of T.X₂
using exists_horseshoe_prescribed_resolutions. The degreewise rows are split
short exact. Sections on each tuple intersection preserve the displayed
biproduct splittings. Products of those rows and finite direct sums along
first-quadrant total diagonals remain split exact. Form the corresponding
short exact sequences of section complexes and total complexes, and let δ
be the homology connecting morphism of the latter sequence in degree q.
The tuple-surjectivity hypothesis makes the coefficient Čech sequence short
exact. Its beta augmentations form a morphism to the total sequence by the
horseshoe augmentation equations; naturality of homology connecting maps
proves the first displayed square. The alpha restrictions form a morphism
from the section sequence to the total sequence by presheaf naturality;
the same homology naturality proves its boundary square. Identify the section
boundary with Sheaf.functorHδ: choose an Ext cocycle a, lift it through the
split middle resolution row, differentiate, and lift through the first row
inclusion. Applying the adjunction and evaluation at 1 gives precisely the
lift-differentiate-lift representative of the section boundary, with the
same differential and sign. The hypotheses on e₁ and e₃ identify all Ext
classes with these section classes. Substitution into the alpha square gives
the second displayed equation. These are squares for augmentations, with no
comparison maps c or d. The argument includes q = 0, arbitrary index sets,
and empty intersections; only total diagonals need to be finite. -/
theorem abelianCechAugmentation_boundary_squares
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ)
    (I₁ : InjectiveResolution T.X₁) (I₃ : InjectiveResolution T.X₃)
    (e₁ : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁ ≅
      (abelianCechSections I₁).homology (q + 1))
    (e₃ : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃ ≅
      (abelianCechSections I₃).homology q)
    (he₁ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₁.cocomplex.X (q + 1))
        (ha : a ≫ I₁.cocomplex.d (q + 1) ((q + 1) + 1) = 0)
        (z : (abelianCechSections I₁).cycles (q + 1)),
        I₁.extMk a ((q + 1) + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₁).iCycles (q + 1) z ∧
        e₁.hom t = (abelianCechSections I₁).homologyπ (q + 1) z)
    (he₃ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₃.cocomplex.X q)
        (ha : a ≫ I₃.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I₃).cycles q),
        I₃.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₃).iCycles q z ∧
        e₃.hom t = (abelianCechSections I₃).homologyπ q z) :
    ∃ (δ : ((abelianCechDouble U I₃).total (.up ℕ)).homology q ⟶
        ((abelianCechDouble U I₁).total (.up ℕ)).homology (q + 1)),
      TopCat.Sheaf.cechδ U hT hg q ≫
          HomologicalComplex.homologyMap (abelianCechBeta U I₁) (q + 1) =
        HomologicalComplex.homologyMap (abelianCechBeta U I₃) q ≫ δ ∧
      Sheaf.functorHδ hT q ≫ e₁.hom ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) =
        e₃.hom ≫ HomologicalComplex.homologyMap (abelianCechAlpha U I₃) q ≫ δ :=
  by sorry

end AlgebraicGeometry.Scheme.Modules
