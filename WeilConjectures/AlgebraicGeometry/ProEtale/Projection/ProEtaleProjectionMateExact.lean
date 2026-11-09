/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateData

/-!
# Exactness and the coefficient-unit normalization of the pro-etale mate

Source: Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

/-- The two coefficient functors of the actual pro-etale projection mate are exact,
and its natural transformation respects shifts and is invertible at the ring.
Source: Stacks Project, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-exact).

Proof: resolve both tensor variables by complexes of flat sheaves which are K-flat.
The signed total tensor carries mapping cones and integer shifts to their standard
counterparts. Descend these identifications along localization, using the given
representative isomorphisms to transport them to a and b. Exact inverse image and
K-injective direct image are triangulated with their canonical shift structures.
The pullback tensor comparison commutes with shifts: on resolving pairs this is
the signed total tensor equation, and full faithfulness of resolving localization
extends it to all pairs. The adjunction unit and counit commute with shifts, so
forming their tensor mate gives the asserted shift-compatible transformation.
At the degree-zero coefficient ring the ordinary pullback preserves the ring unit;
the tensor comparison and both unitors are multiplication on pure sections.
The adjunction triangle identity therefore identifies the mate with the composite
of the source unitor and inverse target unitor. Both are isomorphisms. -/
theorem proEtaleProjectionMateExact :
    ∃ (sF : ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ)
      (sG : (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).CommShift ℤ),
      ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).IsTriangulated ∧
      (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).IsTriangulated ∧
      ∃ τ : (Functor.curryObj a.tensor).obj
          ((proEtaleRingDerivedDirectImage f R S c).obj E) ⟶
        proEtaleRingDerivedPullback f R S c ⋙
          (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c,
        (∀ P, τ.app P = proEtaleProjectionFormulaMate f R S c a b E P) ∧
        NatTrans.CommShift τ ℤ ∧
        IsIso (τ.app ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))) :=
  proEtaleProjectionMateData.{u} f R S c a b E
end AlgebraicGeometry.Scheme
