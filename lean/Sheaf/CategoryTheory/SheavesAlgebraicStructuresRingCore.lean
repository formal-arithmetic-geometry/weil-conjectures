module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Sectionwise ring structures and their strict inverse construction.
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-ring-core)
Source: Stacks Project Section 00YR, rings as sextuples in Proposition 00YV.

Proof in words:
1. Keep the underlying sheaf of sets of a ring sheaf. Define addition and
   multiplication on the sectionwise product by the existing section operations;
   define zero and one on the singleton sheaf, and negation sectionwise.
   Restrictions preserve each operation. Ring identities on sections give all
   ring-object diagrams, including commutativity and distributivity. Send a
   ring-sheaf morphism to its underlying natural transformation.
2. Conversely, on each section set of an internal commutative ring object,
   evaluate its five operation maps (using the unique singleton section for
   constants). Evaluation of its diagrams gives the commutative ring axioms.
   Naturality makes restrictions ring homomorphisms. The underlying set presheaf
   is the original sheaf, so Presheaf.isSheaf_iff_isSheaf_forget makes this a ring
   sheaf. Evaluate ring-object morphisms to obtain natural ring homomorphisms.
3. Both constructions keep section sets and underlying maps. Each round trip
   recovers every operation pointwise; extensionality identifies the operation
   maps and the structures, while proof irrelevance identifies axiom and sheaf
   witnesses. Functor extensionality yields the four asserted strict equalities.
   The chosen equality hF transports the unchanged underlying sets, giving all
   five displayed operation formulas. -/
theorem sheavesAlgebraicStructuresRing_core
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∃ (F : Sheaf J CommRingCat.{max u v w} ⥤ CommRingObjCat (Sheaf J (Type (max u v w))))
        (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤ Sheaf J CommRingCat.{max u v w})
        (hF : F ⋙ CommRingObjCat.forget _ = sheafCompose J (forget CommRingCat.{max u v w})),
      G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) = CommRingObjCat.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
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
            (1 : A.obj.obj U)))) := by
  sorry

end CategoryTheory
