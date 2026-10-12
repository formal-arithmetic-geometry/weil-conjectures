/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums

/-! # Coproduct preservation by the shared derived tensor

Source: Stacks Project, Duality for Schemes, Tag 0A9U, first two sentences of proof;
Cohomology, Tags 06YH and 0FPB; Injectives, Tag 07D9.
(blueprint: lem-sc-derived-tensor-right-coproducts).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Tensoring on the right by any derived object preserves scheme-universe coproducts.
The localization universe w is independent of the scheme universe u.
Source: Stacks Project, Tag 0A9U, first two sentences of proof;
Cohomology, Tags 06YH and 0FPB; Injectives, Tag 07D9.
(blueprint: lem-sc-derived-tensor-right-coproducts).

Proof. Choose a K-flat representative P of E. The shared K-flat tensor comparison
identifies tensoring with E with total tensoring by P on representatives. Module
sheaf tensor preserves coproducts because it is a left adjoint in each variable.
Coproducts of cochain complexes are degreewise. In total degree n, tensoring a
coproduct complex by P therefore amounts to interchanging the coproduct of the
input complexes with the coproduct over pairs of degrees adding to n. The canonical
interchange isomorphisms commute with the tensor differential and assemble to a
natural isomorphism of complexes. Termwise coproducts give coproducts in the derived
category by derivedAmbientDirectSums, and the K-flat comparison is natural with
respect to their coprojections. Thus the image of each coproduct cofan under
tensorRight E is a colimit cofan. This proves preservation, including the empty
family. Represent the objects in the chosen localization universe w throughout;
no equality w = u and no Grothendieck instance in universe w is required. -/
theorem derivedTensorRight_preservesCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (tensorRight E) := by sorry

end AlgebraicGeometry
