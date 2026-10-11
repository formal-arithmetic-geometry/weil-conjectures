/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale

/-!
# Lifting ind-étale algebras along a closed immersion

Let `A` be a ring and `C̄` an `A`-algebra. The category `N_A(C̄)` has as objects the
factorizations `A ⟶ B ⟶ C̄` with `B` étale (of finite presentation) over `A`, and as morphisms
the compatible `A`-algebra maps; its colimit

`H_A(C̄) = colim_{N_A(C̄)} B`

comes with an `A`-algebra map to `C̄` (blueprint `def-exc-ind-etale-closed-lift`). When `C̄` is an
ind-étale algebra over `A ⧸ I`, `H_A(C̄)` is an ind-étale `A`-algebra lifting `C̄`: the reduction
`H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` is an isomorphism (blueprint `lem-exc-closed-lift-reduction`). This is
the ring-theoretic input to lifting pro-étale coverings of a closed subscheme
(`lem-exc-closed-cover-extension`).

## Implementation notes

The objects of `N_A(C̄)` are taken to be the quotients `A[x₁, …, xₙ] ⧸ J` that are étale over
`A`, so that `N_A(C̄)` is a small category (`Algebra.ClosedLift.Index`); every étale algebra of
finite presentation is isomorphic to such a quotient, so this is a skeleton-like small model of
the blueprint's indexing category, with the same colimit.

The two facts about this construction that belong to the subsection
`sk-prop-sf-open-closed-triangle` of the blueprint, that `N_A(C̄)` is filtered
(`lem-exc-closed-lift-filtered`) and the reduction isomorphism (`lem-exc-closed-lift-reduction`),
are stated here for use downstream.

## Main definitions

- `Algebra.ClosedLift.Index`: the indexing category `N_A(C̄)`.
- `Algebra.ClosedLift`: the `A`-algebra `H_A(C̄)`.
- `Algebra.ClosedLift.toAlgHom`: its map `H_A(C̄) ⟶ C̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

variable (A : Type u) [CommRing A] (C : Type u) [CommRing C] [Algebra A C]

namespace ClosedLift

/-- The objects of the indexing category `N_A(C̄)` of blueprint `def-exc-ind-etale-closed-lift`:
an étale `A`-algebra, presented as a quotient `A[x₁, …, xₙ] ⧸ J`, together with an `A`-algebra
map to `C̄`. -/
structure Index where
  /-- The number of variables of the presentation. -/
  n : ℕ
  /-- The ideal of relations of the presentation. -/
  rel : Ideal (MvPolynomial (Fin n) A)
  etale : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ rel)
  /-- The map to `C̄`. -/
  toC : (MvPolynomial (Fin n) A ⧸ rel) →ₐ[A] C

variable {A C}

/-- The étale `A`-algebra underlying an object of `N_A(C̄)`. -/
abbrev Index.alg (X : Index A C) : Type u := MvPolynomial (Fin X.n) A ⧸ X.rel

instance (X : Index A C) : Algebra.Etale A X.alg := X.etale

/-- The morphisms of `N_A(C̄)`: the `A`-algebra maps compatible with the maps to `C̄`. -/
@[ext]
structure Index.Hom (X Y : Index A C) where
  /-- The underlying `A`-algebra map. -/
  hom : X.alg →ₐ[A] Y.alg
  comp_toC : Y.toC.comp hom = X.toC

noncomputable instance : SmallCategory (Index A C) where
  Hom := Index.Hom
  id X := ⟨AlgHom.id A _, rfl⟩
  comp f g := ⟨g.hom.comp f.hom, by rw [← AlgHom.comp_assoc, g.comp_toC, f.comp_toC]⟩

@[simp]
lemma Index.id_hom (X : Index A C) : Index.Hom.hom (𝟙 X) = AlgHom.id A _ := rfl

@[simp]
lemma Index.comp_hom {X Y Z : Index A C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Index.Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl

variable (A C)

/-- The diagram `N_A(C̄) ⥤ CommAlgCat A` sending a factorization `A ⟶ B ⟶ C̄` to `B`. -/
noncomputable def diagram : Index A C ⥤ CommAlgCat.{u} A where
  obj X := CommAlgCat.of A X.alg
  map f := CommAlgCat.ofHom f.hom

/-- The cocone over `ClosedLift.diagram A C` with point `C̄`, given by the maps to `C̄`. -/
noncomputable def coconeC : Cocone (diagram A C) where
  pt := CommAlgCat.of A C
  ι :=
    { app X := CommAlgCat.ofHom X.toC
      naturality X Y f := by
        ext x
        simp only [diagram, Functor.const_obj_map]
        exact DFunLike.congr_fun f.comp_toC x }

end ClosedLift

/-- Blueprint `def-exc-ind-etale-closed-lift`: for an `A`-algebra `C̄`, the `A`-algebra
`H_A(C̄) = colim_{N_A(C̄)} B`, the colimit of the étale `A`-algebras `B` with an `A`-algebra map
to `C̄`. -/
def ClosedLift : Type u :=
  (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A)

noncomputable instance : CommRing (ClosedLift A C) :=
  inferInstanceAs (CommRing (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

noncomputable instance : Algebra A (ClosedLift A C) :=
  inferInstanceAs (Algebra A (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

namespace ClosedLift

/-- The map `H_A(C̄) ⟶ C̄` of blueprint `def-exc-ind-etale-closed-lift`, induced by the maps
`B ⟶ C̄` of the objects of `N_A(C̄)`. -/
noncomputable def toAlgHom : ClosedLift A C →ₐ[A] C :=
  (colimit.desc (diagram A C) (coconeC A C)).hom

/-- The colimit presentation of `H_A(C̄)` by the étale algebras of `N_A(C̄)`. -/
noncomputable def colimitPresentation :
    ColimitPresentation (Index A C) (CommAlgCat.of A (ClosedLift A C)) where
  diag := diagram A C
  ι := (colimit.cocone (diagram A C)).ι
  isColimit := colimit.isColimit (diagram A C)

/-- Blueprint `lem-exc-closed-lift-filtered` (subsection `sk-prop-sf-open-closed-triangle`): the
indexing category `N_A(C̄)` of `def-exc-ind-etale-closed-lift` is filtered. -/
instance isFiltered_index : IsFiltered (Index A C) :=
  sorry

/-- `H_A(C̄)` is ind-étale over `A`: it is the filtered colimit of the étale algebras of
`N_A(C̄)`. -/
instance indEtale : Algebra.IndEtale A (ClosedLift A C) :=
  ⟨⟨Index A C, inferInstance, inferInstance, colimitPresentation A C,
    fun X ↦ inferInstanceAs (Algebra.Etale A X.alg)⟩⟩

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- The map `H_A(C̄) ⟶ C̄` kills `I H_A(C̄)` when `C̄` is an `A ⧸ I`-algebra. -/
lemma map_le_ker_toAlgHom :
    I.map (algebraMap A (ClosedLift A C)) ≤ RingHom.ker (toAlgHom A C : ClosedLift A C →+* C) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- The reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of blueprint `def-exc-ind-etale-closed-lift`. -/
noncomputable def reduction :
    ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C)) →+* C :=
  Ideal.Quotient.lift _ (toAlgHom A C : ClosedLift A C →+* C) (map_le_ker_toAlgHom A C I)

/-- Blueprint `lem-exc-closed-lift-reduction` (subsection `sk-prop-sf-open-closed-triangle`): for
an ind-étale `A ⧸ I`-algebra `C̄`, the reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of the lift
`H_A(C̄)` of `def-exc-ind-etale-closed-lift` is an isomorphism. -/
theorem bijective_reduction [Algebra.IndEtale (A ⧸ I) C] :
    Function.Bijective (reduction A C I) :=
  sorry

end ClosedLift

end Algebra
