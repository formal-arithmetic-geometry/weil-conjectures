/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution

/-!
# Right derived functors computed by acyclic resolutions

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives and K-injective resolutions. The unbounded right derived functor
`F.rightDerivedFunctor` is computed by bounded below complexes of `F`-acyclic objects:

- `CategoryTheory.Functor.rightDerivedFunctorObjQIsoOfRightAcyclic`: for a bounded below complex
  `K` of `F`-acyclic objects, `RF(K) ≅ F(K)` in `D(D)`;
- `CategoryTheory.Functor.rightDerivedFunctorSingleObjIsoOfResolution`: for a resolution
  `X[0] ⟶ K` of an object `X` by `F`-acyclic objects, `RF(X[0]) ≅ F(K)` in `D(D)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

end CategoryTheory.Functor
