/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses

/-! # Flat module objects under pro-étale inverse image

Source: Stacks Project, Tag 05VD, inverse image of flat module sheaves.
(blueprint: new-proetale-inverse-image-module-flat)
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Inverse image followed by transport along an isomorphism of coefficient
rings preserves flat module objects.

Source: Stacks Project, Tag 05VD, lemma-pullback-flat.
(blueprint: new-proetale-inverse-image-module-flat)

Proof. Identify internal abelian module sheaves with sheaves of modules over
section rings. The balanced tensor universal property identifies the two tensor
products, so flatness is the usual local equational criterion. A finite relation
in inverse image comes, locally, from one common stage of the filtered colimit
computing inverse image. The relation vanishes at a later common stage. Flatness
on the source then factors it through a finite matrix with zero relation matrix.
Pull back the covering on which this factorization exists. The same matrices
factor the pulled-back relation, proving flatness over the inverse-image ring.
Transport along the coefficient-ring isomorphism changes neither equations nor
factorizations. Applying the converse local equational criterion and transporting
back through the tensor-compatible equivalence proves categorical flatness.
The empty relation uses a final common stage; zero rings and empty schemes are
included. No Noetherian or finite-rank hypothesis is used. -/
theorem inverseImageModule_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    (Mod.mapModComap ρ).PreservesFlat := by sorry

end AlgebraicGeometry.ProEtale
