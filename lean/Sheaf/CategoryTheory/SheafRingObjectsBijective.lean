/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Recovering ring sheaves from internal ring objects

Source: Stacks Project, Section 00YR and Proposition 00YV,
`proposition-functoriality-algebraic-structures-topoi`.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Reconstruction of ring sheaves from their internal operations.
(blueprint: lem-weil-pbc-sheaf-ring-objects-bijective)
Source: Stacks Project, Section 00YR, the sextuple description in the proof of
Proposition 00YV (proposition-functoriality-algebraic-structures-topoi).

Proof in words:
For surjectivity, evaluate the five maps of an internal commutative ring object
on every section set. Products are sectionwise and the tensor unit is the
singleton sheaf. The internal diagrams give associativity, unit, inverse,
commutativity and distributivity, hence a commutative ring on each section set.
Naturality of the operations makes every restriction a ring homomorphism.
The underlying set presheaf is the original sheaf; the underlying-set sheaf
criterion makes this presheaf of rings a sheaf of rings A. The assumed section
formulas identify the operations of F(A), after transport by hF, with the original
operations. Extensionality of natural transformations and proof irrelevance give
F(A) equal to the original bundled internal ring object, not merely isomorphic.
For injectivity, an equality F(A) = F(B), together with hF, identifies the
underlying set presheaves. The section formulas then identify addition, zero,
negation, multiplication and one. Thus the bundled commutative rings on each
section are equal: natural and integer scalar multiplication and powers are
uniquely fixed by their recursion laws, while all axiom witnesses are propositions.
The restrictions are equal because their underlying functions
are equal, and sheaf witnesses are propositions. Hence A = B.
No nonempty-section hypothesis is needed: constants are evaluated on the
singleton tensor unit; its section exists even for the empty site. -/
theorem sheafRingObjects_bijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J CommRingCat.{max u v w} ⥤
      CommRingObjCat (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}))
    (hops : ∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) :
    Function.Bijective F.obj := by sorry

end CategoryTheory
