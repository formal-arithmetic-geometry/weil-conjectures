module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Etale Cohomology, Tag 0A50, proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-exact)

Proof: The two open immersions form a cover, and their fiber products are the intersections.
For every abelian sheaf I, the sheaf condition makes the map I(X) → I(U) × I(V) injective
with image the kernel of the difference of the restrictions to I(U ∩ V).
If I is injective, the Cech cocycle with components (0, gamma, -gamma, 0) for any section
gamma on U ∩ V is a boundary, by injective Cech acyclicity. A boundary gives two sections
whose difference restricts to gamma (change both signs if necessary). Hence the difference
map is surjective. Choose an injective resolution of F and apply this short exact sequence
in each degree. The restriction maps commute with the differentials, so this is a short
exact sequence of complexes of abelian groups. Its homology sequence gives the three
exactness assertions in every degree; homology of the two-term product is the product
of the homologies, and the induced maps are precisely the right derived restriction maps.
The complexes vanish in negative degrees, giving the initial degree-zero injection.
Lift a morphism of sheaves to a chain map between injective resolutions. Naturality of the
homology connecting maps and homotopy uniqueness make the connecting maps independent
of resolutions and natural in F, hence natural transformations as asserted. -/
theorem etale_mayerVietoris_exact (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
∃ δ : ∀ n : ℕ,
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived (n + 1),
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Function.Injective (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map (MorphismProperty.Over.homMk
            (A := Scheme.Etale.mk U.ι) (B := Scheme.Etale.mk (𝟙 X))
            U.ι (Category.comp_id U.ι)).op)).rightDerived 0).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived 0).app F
            x)) ∧
        (∀ n : ℕ,
          Function.Exact (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived n).app F
            x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived n).app F
            x))
            (fun x => ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u +
            1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ∧
          Function.Exact (fun (x :
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n).obj F ×
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n).obj F) =>
            ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ((δ n).app F) ∧
          Function.Exact ((δ n).app F)
            (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u
            + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived (n +
            1)).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived (n +
            1)).app F x))) := by
  sorry

end AlgebraicGeometry.Etale
