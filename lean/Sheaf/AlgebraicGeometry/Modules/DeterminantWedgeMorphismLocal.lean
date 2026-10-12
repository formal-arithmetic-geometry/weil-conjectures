module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Local existence of wedge maps on every open. The proof constructs the map on each open
by choosing local lifts; compatibility on overlaps is deferred to the gluing theorem.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-wedge-morphism-local-data).

Proof: Choose local lifts of the finitely many quotient sections using the epimorphism
property of `S.g`. The alternating wedge formula is independent of the choices because
the difference of two lifts lies in the image of `S.f`; after trivializing the finite
locally free first term, every resulting term has more than `r₁` basis factors and
vanishes by alternation. The universal properties of exterior powers and tensor products
then produce the displayed morphism on the open. -/
theorem determinant_wedgeMorphism_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  intro U
  exact determinant_wedgeMorphism_local_data_at S hS r₁ r₂ r₃ hr U

/-- A compatible family of local wedge maps glues to a sheaf morphism.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-wedge-morphism-glue).

Proof: The local maps have the same displayed formula on restrictions, hence agree on
overlaps by separatedness of the target sheaf. The sheaf gluing property assembles them
into one morphism, and the formula is preserved after restriction and therefore holds
on every open. -/
theorem determinant_wedgeMorphism_of_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (hlocal : ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  choose φU hφU using hlocal
  exact determinant_wedgeMorphism_glue_family S hS r₁ r₂ r₃ hr φU hφU

end AlgebraicGeometry.Scheme.Modules
