module

public import WeilConjectures.Topology.Sheaves.CechComparison
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The front face used by the Alexander--Whitney tuple formula. -/
def n2CupFront (p q : ℕ) : Fin (p + 1) → Fin (p + q + 1) :=
  fun i ↦ ⟨i.val, by omega⟩

/-- The back face, sharing the front face's last vertex. -/
def n2CupBack (p q : ℕ) : Fin (q + 1) → Fin (p + q + 1) :=
  fun j ↦ ⟨p + j.val, by omega⟩

/-- Restriction from a tuple intersection to a face intersection. -/
def n2CupFaceRestriction {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {n m : ℕ} (y : Fin n → ι) (face : Fin m → Fin n) :
    (⨅ i, U (y i)) ⟶ (⨅ j, U (y (face j))) :=
  homOfLE (le_iInf fun j ↦ iInf_le (fun i ↦ U (y i)) (face j))

/-- The coefficient Alexander--Whitney cochain, defined tuplewise. -/
def n2CechCupCochain {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X (p + q) :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)).symm
    (fun y ↦ tmulSection
      (F.presheaf.map (n2CupFaceRestriction U y (n2CupFront p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat p a
          (y ∘ n2CupFront p q)))
      (G.presheaf.map (n2CupFaceRestriction U y (n2CupBack p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat q b
          (y ∘ n2CupBack p q))))

end
end AlgebraicGeometry.Scheme.Modules
