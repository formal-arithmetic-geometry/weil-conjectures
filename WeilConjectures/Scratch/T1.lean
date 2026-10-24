module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

set_option profiler true in
example : (boundedConstructibleExchangeFormalism Λ ℓ k).obj (SepFinType.mk X) = Dᵇc(X.left)⟦Λ⟧ := rfl

set_option profiler true in
example : (boundedConstructibleExchangeFormalism Λ ℓ k).pb (SepFinType.homMk f) = boundedConstructibleUpperStar Λ ℓ f := rfl

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

lemma SepFinType.homMk_comp_homMk {A B C D : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
    [QuasiCompact A.hom] [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom] {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (w : a ≫ b = c ≫ d) :
    SepFinType.homMk a ≫ SepFinType.homMk b = SepFinType.homMk c ≫ SepFinType.homMk d :=
  ObjectProperty.hom_ext _ w

set_option profiler true in
lemma bla (sq : CommSq g' f' f g) :
    boundedConstructiblePullbackSquareComparison Λ ℓ sq =
      (boundedConstructibleExchangeFormalism Λ ℓ k).sqIso (SepFinType.homMk f')
        (SepFinType.homMk g') (SepFinType.homMk g) (SepFinType.homMk f)
        (SepFinType.homMk_comp_homMk sq.w.symm) := by
  rw [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp'_rfl]
  unfold ExchangeFormalism.pbComp' boundedConstructiblePullbackSquareComparison
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
