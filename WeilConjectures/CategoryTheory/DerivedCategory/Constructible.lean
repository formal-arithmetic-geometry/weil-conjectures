/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Etale
public import WeilConjectures.ConstructibleSheaf.ProEtale

/-!

# The constructible bounded derived category on the small sites of schemes

For a scheme `X`, morphism properties `P` and `Q` with `Q ≤ P`, and a concrete abelian
coefficient category `A`, this file defines the subcategory `Dᵇc` of the derived category
`DerivedCategory (Sheaf (X.smallGrothendieckTopology Q (Q := P)) A)` consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

The étale and pro-étale cases are the specializations to `P = Q = @Etale` and
`P = Q = @WeaklyEtale`; the notation `Dᵇc(X, A)` refers to the étale one.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
concrete Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullback entering
  `IsConstructibleSheaf`, come from the sorried instance
  `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`;
- the chosen localized category comes from the instance
  `HasDerivedCategory.ofIsGrothendieckAbelian` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, which installs
  `HasDerivedCategory.{u + 1}` on every sheaf category out of the Grothendieck abelian
  structure supplied by `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`. In
  particular the derived category is no longer taken at an auxiliary universe `w`.

## Main definitions

- `AlgebraicGeometry.Scheme.DerivedCategory.constructibleHomology`: the property of an
  object of the derived category of sheaves on a small site that all its homology sheaves
  are constructible.
- `AlgebraicGeometry.Scheme.DerivedCategory.boundedConstructible`: the property of being
  bounded with constructible homology.
- `AlgebraicGeometry.Scheme.DerivedCategoryBoundedConstructible`: the subcategory cut out
  by the property above, the constructible bounded derived category of the `ℓ`-adic
  formalism.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible` and
  `AlgebraicGeometry.ProEtale.DerivedCategoryBoundedConstructible`: the étale and
  pro-étale versions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

namespace Scheme

variable (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
  [Scheme.HasGeometricPoints P Q] (hQP : Q ≤ P)

variable (X : Scheme.{u})

section ConstructibleHomology

/-- An object of the derived category of sheaves on the small `Q`-site of `P`-schemes over
`X` has constructible homology if all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf (X.smallGrothendieckTopology Q (Q := P)) A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf P Q hQP
    ((DerivedCategory.homologyFunctor
      (Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of sheaves on a small site is bounded constructible
if it is bounded for the canonical t-structure and all its homology sheaves are
constructible. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf (X.smallGrothendieckTopology Q (Q := P)) A)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    Scheme.DerivedCategory.constructibleHomology A P Q hQP X

/-- The constructible bounded derived category, realized as the full subcategory of
bounded complexes with constructible homology in the derived category of sheaves on the
small `Q`-site of `P`-schemes over `X`. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (Scheme.DerivedCategory.boundedConstructible A P Q hQP X).FullSubcategory

noncomputable instance : Category (DerivedCategoryBoundedConstructible A P Q hQP X) :=
  inferInstanceAs <|
    Category (Scheme.DerivedCategory.boundedConstructible A P Q hQP X).FullSubcategory

/-- The inclusion of the constructible bounded derived category into the derived category
of sheaves on the small site. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    DerivedCategoryBoundedConstructible A P Q hQP X ⥤
      DerivedCategory (Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) :=
  (Scheme.DerivedCategory.boundedConstructible A P Q hQP X).ι

end BoundedConstructible

end Scheme

namespace Etale

variable (X : Scheme.{u})

/-- The constructible bounded derived category `Dᵇc(X, A)` of the small étale site. -/
noncomputable abbrev DerivedCategoryBoundedConstructible : Type _ :=
  Scheme.DerivedCategoryBoundedConstructible A @Etale @Etale le_rfl X

@[inherit_doc Etale.DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" =>
  Etale.DerivedCategoryBoundedConstructible A X

/-- The inclusion of `Dᵇc(X, A)` into the derived category of étale sheaves. -/
noncomputable abbrev DerivedCategoryBoundedConstructible.ι :
    Dᵇc(X, A) ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  Scheme.DerivedCategoryBoundedConstructible.ι A @Etale @Etale le_rfl X

end Etale

namespace ProEtale

variable (X : Scheme.{u})

/-- An object of the derived category of pro-étale sheaves has constructible homology if
all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  fun M ↦ ∀ n : ℤ, ProEtale.IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology X) A) n).obj M)

/-- An object of the derived category of pro-étale sheaves is bounded constructible if it
is bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ ProEtale.DerivedCategory.constructibleHomology A X

/-- The constructible bounded derived category of the small pro-étale site, realized as
the full subcategory of bounded complexes with constructible homology in the derived
category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (ProEtale.DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance : Category (ProEtale.DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <|
    Category (ProEtale.DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion into the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    ProEtale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (ProEtale.DerivedCategory.boundedConstructible A X).ι

end ProEtale

end AlgebraicGeometry
