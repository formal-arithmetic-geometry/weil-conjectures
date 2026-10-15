/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-!
# Derived pullback and tensor on arbitrary ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option synthInstance.maxSize 2048 in
/-- Derived pullback preserves K-flat complexes with flat terms and commutes with derived
 tensor, naturally in both arguments. Source: Stacks Project, Tags 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

The binders specify the objects named in the statement: `uStar`, via `hobj` and `hmap`, is
extension of scalars after algebraic inverse image; `LF` with `epsilon` is its left derived
functor. `PR` and `PS` are exactly the full subcategories of K-flat flat-term complexes.
`TR` and `TS` are the derived tensor bifunctors, identified by their natural total-tensor
comparisons on those subcategories. These are the comparisons supplied by
`site_derived_tensor_descent`, pulled back from homotopy categories to complexes. No flatness
of the ring map is assumed. The resulting natural isomorphism has components
`LF (F tensor G) ≅ LF F tensor LF G` for all unbounded derived objects.

Proof plan:
1. Resolve both inputs by K-flat complexes with flat terms (`lem-pc-kflat-resolution`).
   The tensor descent theorem (`lem-weil-pbc-site-derived-tensor-descent`) computes their
   derived tensor by total tensor. Pullback preserves K-flatness and flat terms by
   `lem-weil-pbc-ringed-pullback-preserves-kflat`, proving the first conclusion as well.
   `lem-weil-pbc-ringed-topoi-derived-pullback` computes `LF` on these representatives.
2. Total tensor of two K-flat complexes is K-flat: reassociate an acyclic test tensor as
   `(A tensor P) tensor Q`. The balanced tensor associator respects the differentials,
   whose three signs are `1`, `(-1)^a`, `(-1)^(a+p)`. K-flatness twice gives acyclicity.
3. Tensor products of flat terms are flat by associativity and exactness of each tensor
   functor. Each total term is a countable sum of these; `lem-pc-kflat-closure` makes it flat.
   The derived pullback comparison therefore applies to the total tensor itself.
4. The module pullback/pushforward adjunction
   (`lem-weil-pbc-ringed-topoi-module-adjunction`) implies that pullback preserves coproducts:
   maps out of the pulled-back sum correspond to families of maps out of its summands.
5. Invert the module tensor comparison
   (`lem-weil-pbc-ringed-topoi-module-pullback-tensor`) in each bidegree, sum it, and use step 4.
   This gives `beta : Tot(uStar P tensor uStar Q) ≅ uStar Tot(P tensor Q)`.
   Naturality handles each differential separately; additivity preserves the scalar signs.
6. Compose `epsilon` on the total tensor with the inverse of `Q(beta)` and the two tensor
   representative comparisons. Each factor is invertible and natural on representatives.
   The two-variable localization in `lem-weil-pbc-site-derived-tensor-descent` extends the
   comparison uniquely to all derived morphisms, also after inverting quasi-isomorphisms.
   Thus the natural isomorphism is independent of resolutions and is the canonical one.
-/
theorem ringedTopoiDerivedTensorPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS) :
    (∀ P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        CochainComplex.IsKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat) ∧
    Nonempty (TR ⋙ LF ≅ (LF.prod LF) ⋙ TS) := by
  sorry

end SheafOfModules
