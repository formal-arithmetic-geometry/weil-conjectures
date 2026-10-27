module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos

/-!
# Ordinary alteration topology and marked regular covers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Definitions 1.2.2,
2.3.1 and 2.3.3 (parameter 1), and Exposé VII, Theorem 1.1 (notation only)
(blueprint: def-per-ordinary-alteration-topology).

The underlying category is `PrimeToEllAlteration.Alt`, without a prime parameter.
The family refinement relation is the existing `PrimeToEllAlteration.Refines`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.OrdinaryAlteration

/-- Jointly surjective étale generators, written as presieves to allow families with arbitrary
index universes. Source: ILO II 2.1.1 at parameter 1, and 2.3.1
(blueprint: def-per-ordinary-alteration-topology). -/
def IsEtaleCoveringPresieve {S : Scheme.{u}} [IsNoetherian S]
    {T : PrimeToEllAlteration.Alt S} (R : Presieve T) : Prop :=
  (∀ (V : PrimeToEllAlteration.Alt S) (f : V ⟶ T), R f → Etale f.hom.left) ∧
    ∀ t : T.obj.left, ∃ (V : PrimeToEllAlteration.Alt S) (f : V ⟶ T) (v : V.obj.left),
      R f ∧ f.hom.left v = t

/-- The least topology containing jointly surjective étale families and proper surjective
singleton families. Source: ILO II 2.3.1, Remark 2.3.2 and Definition 2.3.3
(blueprint: def-per-ordinary-alteration-topology). -/
def topology (S : Scheme.{u}) [IsNoetherian S] :
    GrothendieckTopology (PrimeToEllAlteration.Alt S) :=
  sInf {J | (∀ (T : PrimeToEllAlteration.Alt S) (R : Presieve T),
      IsEtaleCoveringPresieve R → Sieve.generate R ∈ J T) ∧
    ∀ (T V : PrimeToEllAlteration.Alt S) (f : V ⟶ T),
      IsProper f.hom.left → Surjective f.hom.left →
        Sieve.generate (Presieve.singleton f) ∈ J T}

/-- A family covers if its sieve of arrows factoring through its members covers.
Source: ILO II 2.3.1--2.3.3
(blueprint: def-per-ordinary-alteration-topology). -/
def IsCoveringFamily {S : Scheme.{u}} [IsNoetherian S] {I : Type w}
    {T : PrimeToEllAlteration.Alt S} (V : I → PrimeToEllAlteration.Alt S)
    (f : ∀ i, V i ⟶ T) : Prop :=
  Sieve.ofArrows V f ∈ topology S T

/-- The identity of a reduced Noetherian base as an object of the existing category `alt/S`.
Source: ILO II 1.2.2--1.2.3
(blueprint: def-per-ordinary-alteration-topology). -/
def baseObject (S : Scheme.{u}) [IsNoetherian S] [IsReduced S] :
    PrimeToEllAlteration.Alt S :=
  ⟨Over.mk (𝟙 S), inferInstanceAs (LocallyOfFiniteType (𝟙 S)),
    inferInstanceAs (QuasiCompact (𝟙 S)), inferInstanceAs (IsReduced S),
    fun t ht ↦ ⟨ht, Eq.mpr
      (congrArg (fun f : S.residueField t ⟶ S.residueField t ↦ f.hom.Finite)
        (Scheme.residueFieldMap_id t)) (RingHom.Finite.id (S.residueField t))⟩⟩

/-- The predicate `U(S,Z)`: a finite ordinary alteration cover by nonempty integral regular
Noetherian schemes on each of which the inverse image of `Z` supports a strict normal crossings
boundary. Since `Z` is closed, empty interior says exactly that it is nowhere dense. The finite
family and the boundary may be empty. Source: ILO VII Theorem 1.1 (notation only), using II 2.3.3
(blueprint: def-per-ordinary-alteration-topology). -/
def U (S : Scheme.{u}) [IsNoetherian S] [IsReduced S]
    (Z : TopologicalSpace.Closeds S) (_hZ : interior (Z : Set S) = ∅) : Prop :=
  ∃ (n : ℕ) (T : Fin n → PrimeToEllAlteration.Alt S)
    (f : ∀ i, T i ⟶ baseObject S),
    IsCoveringFamily T f ∧
      ∀ i, IsIntegral (T i).obj.left ∧ IsRegularScheme (T i).obj.left ∧
        IsNoetherian (T i).obj.left ∧
        ∃ H : (T i).obj.left.IdealSheafData,
          IsStrictNormalCrossingsBoundary H ∧
            ((f i).hom.left ⁻¹' (Z : Set S)) = (H.support : Set (T i).obj.left)

end AlgebraicGeometry.OrdinaryAlteration
