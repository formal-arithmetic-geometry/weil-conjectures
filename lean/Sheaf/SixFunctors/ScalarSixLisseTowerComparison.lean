/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Normalized scalar-tower comparison for a lisse generator

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3),
common-field argument steps 3 and 5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For a lisse finite free module, changing coefficients in two stages before
extension by zero recovers the original rationalized generator. The equation fixes
this comparison by its restriction to the stratum.

Source: blueprint main-20261015, rational proper-base-change proof, paragraph (3),
common-field argument steps 3 and 5; scalar-six-pullback clauses (2)--(3).
(blueprint: lem-sfb-lisse-generator-normalized-tower).

Proof: Trivialize M on a pro-etale cover. Its finite free local presentations show
that M is flat and its degree-zero complex is K-flat. Thus the universal derived
counit for scalar extension along b is invertible on that complex, and composing
with the homotopy-localization and single-complex comparisons gives its canonical
ordinary degree-zero scalar comparison. The normalized scalar/extension comparison
identifies scalar extension of a_!M with a_! of the derived scalar extension of M.
These comparisons apply to the supplied normalized H, G and C: identify their open
extensions by uniqueness of left adjoints with the prescribed unit, their closed
extensions by the prescribed direct-image comparison, and use H's coherent gamma
for a locally closed factorization. The termwise equations of D identify the
resulting derived restrictions. Compose with the degree-zero comparison, invert,
and apply scalar extension along c. Follow this by the scalar-tower
comparison. This constructs e for the actual composite coefficient map b followed by c.
Restrict its inverse to Z. The normalized scalar/extension comparison restricts to
inverse theta, while scalar transitivity commutes with inverse image by C.tower.
Cancel the two extension restriction isomorphisms. Naturality of the derived
counit and of the single-complex comparison leaves precisely the displayed
equality. No flatness of b or c is required, only local finite freeness of M.
-/
theorem lisse_generator_normalized_tower
    {A B Q : ScalarSixRing.{u}}
    [IsCommMonObj A.X] [IsCommMonObj B.X] [IsCommMonObj Q.X]
    (b : A ⟶ B) (c : B ⟶ Q)
    (H : LocallyClosedExtensionData.{u}) (hH : H.Coherent) (D : H.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    {k : Type u} [Field k] (W Z : Over (Spec (.of k)))
    [IsCommMonObj (condensedRingObj A.X Z.left)]
    [IsCommMonObj (condensedRingObj B.X Z.left)]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Z ⟶ W) [IsImmersion a.left]
    (M : ModuleRingedComparison.internalModules A.X Z.left)
    (hM : IsLisseCoefficientModule A.X M) :
    ∃ e : (scalarSixChange c W.left).obj
        ((scalarSixExtension H G B a).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z.left)).obj M))) ≅
      (scalarSixChange (b ≫ c) W.left).obj
        ((scalarSixExtension H G A a).obj ((DerivedCategory.singleFunctor _ 0).obj M)),
      (scalarSixPull Q a.left).map e.inv ≫
          (C.theta c a.left).inv.app _ ≫
          (scalarSixChange c Z.left).map
            ((scalarSixRestriction H D G B a).hom.app _) =
        (C.theta (b ≫ c) a.left).inv.app _ ≫
          (scalarSixChange (b ≫ c) Z.left).map
            ((scalarSixRestriction H D G A a).hom.app _) ≫
          (scalarSixTower b c Z.left).inv.app _ ≫
          (scalarSixChange c Z.left).map
            ((Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X)
                b.hom.hom Z.left)).leftDerivedFunctorCounit.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj
                  ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
              DerivedCategory.Qh.map
                (((Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X)
                    b.hom.hom Z.left)).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
              (DerivedCategory.quotientCompQhIso
                (ModuleRingedComparison.internalModules B.X Z.left)).hom.app
                  (((Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X)
                      b.hom.hom Z.left)).mapHomologicalComplex
                    (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
              DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z.left))
                  (.up ℤ) 0).hom.app M)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
