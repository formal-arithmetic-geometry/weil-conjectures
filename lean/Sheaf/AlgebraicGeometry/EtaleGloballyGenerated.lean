/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Globally generated étale sheaves of modules

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, definition `def-kun-global-generated`
(blueprint: def-kun-global-generated).

## Main definitions

- `AlgebraicGeometry.Scheme.etaleGlobalSectionsEvaluation`: the evaluation morphism from
  the coproduct of copies of the constant coefficient sheaf indexed by all global sections.
- `AlgebraicGeometry.Scheme.IsGloballyGeneratedEtaleSheaf`: the predicate that this map is epi.
- `AlgebraicGeometry.Scheme.etaleAbelianGlobalSectionsEvaluation` and
  `AlgebraicGeometry.Scheme.IsGloballyGeneratedAbelianEtaleSheaf`: the integer-coefficient case.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The evaluation morphism sends the basis vector indexed by a global section `s`
to `s`. The source is the constant sheaf of the free coefficient module on the global
sections. Since the constant-sheaf functor is a left adjoint, this is a model for the
coproduct of copies of the constant coefficient sheaf indexed by those sections.
Source: blueprint `def-kun-global-generated`, displayed evaluation morphism
(blueprint: def-kun-global-generated). -/
noncomputable def etaleGlobalSectionsEvaluation {T : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ ((F.obj.obj (op (Etale.mk (𝟙 T)))) →₀ Λ)) ⟶ F :=
  ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ F).symm
      (ModuleCat.ofHom (Finsupp.linearCombination Λ id))

/-- A sheaf of `Λ`-modules on the small étale site is globally generated if its
all-global-sections evaluation morphism is an epimorphism of sheaves.
The equivalent geometric-stalk criterion belongs to the other properties of this notion.
Source: blueprint `def-kun-global-generated`, global generation clause
(blueprint: def-kun-global-generated). -/
def IsGloballyGeneratedEtaleSheaf {T : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  Epi (etaleGlobalSectionsEvaluation F)

/-- The evaluation morphism for an abelian étale sheaf uses the free abelian group
on its global sections, or equivalently the coproduct of constant integer sheaves.
It is the case `Λ = ℤ` of the module construction, expressed directly in abelian groups;
the finitely supported integer combinations have the same universe as the sections.
Source: blueprint `def-kun-global-generated`, abelian sheaves clause
(blueprint: def-kun-global-generated). -/
noncomputable def etaleAbelianGlobalSectionsEvaluation {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of ((F.obj.obj (op (Etale.mk (𝟙 T)))) →₀ ℤ)) ⟶ F :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ F).symm
      (AddCommGrpCat.ofHom (Finsupp.linearCombination ℤ id).toAddMonoidHom)

/-- An abelian étale sheaf is globally generated if its integer-coefficient
evaluation morphism is epi.
Source: blueprint `def-kun-global-generated`, abelian sheaves clause
(blueprint: def-kun-global-generated). -/
def IsGloballyGeneratedAbelianEtaleSheaf {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  Epi (etaleAbelianGlobalSectionsEvaluation F)

end AlgebraicGeometry.Scheme
