module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.SimplicialMatchingObject
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence
import Sheaf.CategoryTheory.SiteHypercoverDisjointUnion

/-!
# Geometric part of the affine acyclic hypercover construction

This theorem packages the finite-basis construction, its degreewise coproduct realization,
and the component evaluation comparisons.  The componentwise lifting theorem then supplies
weak contractibility. (blueprint: lem-weil-pbc-proetale-affine-acyclic-hypercover)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- Finite-basis geometry produces affine terms, component evaluation comparisons, and
epimorphic matching arrows. Source: Stacks Project, proetale.tex, Tag 09A1 (2), and
hypercovering.tex, Tags 0DAV, 0DB1, 0DB2
(blueprint: lem-weil-pbc-proetale-affine-acyclic-hypercover-geometry).
Proof: apply the finite-basis hypercover theorem in the qcqs subsite, then realize finite formal
coproducts in the full slice. Transport matching epimorphisms and component evaluation
bijections.
-/
theorem exists_affine_hypercover_geometry
    (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    ∃ U : SimplicialObject (Over W),
      (∀ n : ℕ, IsAffine (U _⦋n⦌).left.left) ∧
      (∀ n : ℕ, ∃ (I : Type (u + 1)) (V : I → X.ProEt)
        (maps : ∀ i : I, V i ⟶ (U _⦋n⦌).left),
        (∀ F : Sheaf (topology X) (Type (u + 1)),
          Function.Bijective (fun s : F.obj.obj (op (U _⦋n⦌).left) ↦
            fun i ↦ F.obj.map (maps i).op s)) ∧
        (∀ (i : I) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op (V i))))) ∧
      Epi ((topology X).yoneda.map (U _⦋0⦌).hom) ∧
      (∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌),
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋1⦌ ⟶ c.pt,
          (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) ∧
      (∀ n : ℕ, ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
