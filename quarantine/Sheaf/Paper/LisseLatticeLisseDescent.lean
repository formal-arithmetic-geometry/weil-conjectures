/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData

/-! # Local rational identifications with free integral lattices imply rational lissity. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Local rational identifications with free integral lattices imply rational lissity.
Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.14(2), Remark 6.8.15.

Proof: trivialize every finite locally free M_i on a pro-etale covering of its chart.
Compose these covers with the etale covering c.Y; weakly etale localization makes
all composite maps objects of X.ProEt and transitivity makes them a covering family.
The prime remains invertible on them. Ordinary-completed comparison identifies the
completed integral pullback of N[0] to Y_i with its ordinary restriction in degree zero.
Use the assumed local rational isomorphism and apply further rational pullback to each
trivializing chart. Pullback composition identifies this with pullback from X. For M_i,
finite local freeness makes its single complex K-flat. Slice normalization identifies
all its finite reductions on the trivializing chart with the constant free quotient
modules of rank r. Completed perfect scalar pullback identifies the derived limit of
this tower with the free completed coefficient sheaf of rank r in degree zero, also
on a non-noetherian chart. Preservation of integral constructibility puts that free
object in the integral category. These objects and the transported isomorphisms are
exactly the witnesses required by IsRationalLisse. No image in the ordinary realization
is used at this stage, only the isomorphisms already lifted in raw rationalization.
The empty covering and rank zero work without modifications; ranks may vary.
(blueprint: lem-tw-lisse-lattice-lisse-descent). -/
theorem lattice_lisse_of_local_isomorphisms (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (a : Realizations l E) (X : LisseRealization.Base D l hl)
    (L : RationalModules l E X.scheme) (c : Choice l E a X.scheme L)
    (hN : sfIntegralConstructible l E X.scheme
      ((DerivedCategory.singleFunctor _ 0).obj c.N))
    (hloc : ∀ i : c.I,
      ∃ hNi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj ((integralPull l E (c.Y i).hom).obj c.N)),
      ∃ hMi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj (c.M i)),
        Nonempty ((sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj
              ((integralPull l E (c.Y i).hom).obj c.N), hNi⟩ ≅
          (sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj (c.M i), hMi⟩)) :
    IsRationalLisse l E X.scheme ((sfRationalConstructibleLocalization l E X.scheme).obj
      ⟨(DerivedCategory.singleFunctor _ 0).obj c.N, hN⟩) := by sorry

end WeilConjectures.LisseLattice
