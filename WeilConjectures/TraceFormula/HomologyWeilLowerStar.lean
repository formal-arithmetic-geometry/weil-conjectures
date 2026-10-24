/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.WeilObject.BoundedConstructible.Homology
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Homology sheaves of the pushforward of Weil objects along a finite morphism

Let `f : X ⟶ Y` be a finite morphism with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`. For a Weil object `K` for `e_X`, the homology sheaves of the derived
pushforward `Rf_*^Weil K` are the pushforwards of the homology sheaves of `K`, as Weil sheaves
for `e_Y` (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerStar_iso`):
```
Hʲ(Rf_*^Weil K) ≅ f_* Hʲ(K).
```
The pushforward of module objects along a finite morphism is exact
(`ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite`), so `Rf_*` commutes
with homology (`Functor.rightDerivedFunctorHomologyFunctorIso`). The Frobenius structures agree:
on homology, the derived base-change morphism of the Frobenius square is the base-change morphism
of module objects (`Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`), and the
base-change morphism on bounded constructible complexes is the restriction of the derived one on
the ambient derived categories (`Adjunction.map_exchangeRight_app_of_comm`). The two are
assembled by `Endofunctor.IsoAlgebra.mapOfNatIsoHomologyExchangeIso`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section SquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- On the ambient derived category, the inverse of the composition isomorphism of the derived
pullbacks on bounded constructible complexes is that of `leftDerivedUpperStarComp`. -/
@[simp]
lemma boundedConstructibleUpperStarComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Y')
    (K : Dᵇc(Y'.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarComp Λ ℓ f g).inv.app K).hom =
      (leftDerivedUpperStarComp Λ f.left g.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

set_option maxHeartbeats 1000000 in
-- the instances of the general lemmas are found for each of the categories of module objects
/-- On the ambient derived category, the pullback comparison of a commutative square on bounded
constructible complexes is the isomorphism of total left derived functors induced by the
comparison `upperStarSquareComparison` of the pullbacks of module objects. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_hom (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
      (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison Λ
        ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)).hom.app K.obj := by
  have h1 := boundedConstructiblePullbackSquareComparison_hom_app Λ ℓ sq K
  have h2 := Adjunction.leftDerivedFunctorSquareIso_hom_app_of_eq
    (upperStarSquareComparison Λ ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩) (upperStarComp Λ f'.left g.left)
      (upperStarComp Λ g'.left f.left) (by rw [Over.left_comp_left_eq_of_comp_eq sq.w]) rfl K.obj
  rw [h1, h2, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  simp only [boundedConstructibleUpperStarComp_inv_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom]
  have e : ∀ {A B : Dᵇc(X'.left)⟦Λ⟧} (h : A = B),
      (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    rintro _ _ rfl
    rfl
  simp only [e, leftDerivedUpperStarComp, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc]

end SquareComparison

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- The isomorphism `Lf^* ⋙ Le_X^* ≅ Le_Y^* ⋙ Lf^*` of derived pullbacks of module objects
induced by the Frobenius square, through the derived composition isomorphisms. -/
noncomputable abbrev weilDerivedSquareIso :=
  Adjunction.leftDerivedFunctorSquareIso
    (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (commSq_left_of_comp_eq eX eY hf))

/-- The derived base-change morphism `Rf_* ⋙ Le_Y^* ⟶ Le_X^* ⋙ Rf_*` of the Frobenius square on
the ambient derived categories of module objects. -/
noncomputable abbrev weilDerivedBaseChange :=
  Adjunction.exchangeRight
    (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).derivedAdjunction
    (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).derivedAdjunction
    (weilDerivedSquareIso ℓ eX eY hf)

end AlgebraicGeometry.ProEtale.CondensedRing
