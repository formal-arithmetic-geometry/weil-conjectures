module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Sheaf.Topology.AbelianOpenExtensionByZero

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u
namespace TopCat.Sheaf

/-- The finite normalized presentation data, without choosing its canonical sections.
Source: Stacks Project, Cohomology, Lemma 0A38, normalization construction.
(blueprint: lem-sc-constant-subsheaf-normalized-core)
The construction refines the finitely many generating sections by clopen fibres,
intersects the resulting compact opens, and adjoins positive gcd labels.  Bezout
identities give sections on the intersections.  The active gcd at each point is
retained, and the stalk bound discards labels larger than `b+1`; the resulting
coproduct map remains an epimorphism and has the divisibility property. -/
structure NormalizedPresentationData
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C)
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (b : ℕ) where
  n : ℕ
  A : Fin n → Opens X
  compact : ∀ i, IsCompact (A i : Set X)
  c : Fin n → ℕ
  positive : ∀ i, 0 < c i ∧ c i ≤ b + 1
  g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K
  epi : Epi g
  divisor : ∀ x : X, x ∈ iSup A →
    ∃ i, x ∈ A i ∧ ∀ j, x ∈ A j → c i ∣ c j

/-- Existence of the finite normalized presentation data.
Source: Stacks Project, Cohomology, Lemma 0A38, first two proof paragraphs.
(blueprint: lem-sc-constant-subsheaf-normalized-core) -/
theorem constantSubsheaf_normalized_core
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ d : NormalizedPresentationData X K C ι isoC b, True := by
  sorry


/-- Completion intermediate theorem. Source: Stacks Project, Cohomology, Lemma 0A38.
(blueprint: lem-sc-constant-subsheaf-normalized-completion) -/
theorem constantSubsheaf_normalized_completion
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) 
    (d : NormalizedPresentationData X K C ι isoC b):
    ∃ (n : ℕ) (A : Fin n → Opens X) (_ : ∀ i, IsCompact (A i : Set X))
      (c : Fin n → ℕ), (∀ i, 0 < c i ∧ c i ≤ b + 1) ∧
      ∃ (g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K), Epi g ∧
        ∃ s : ∀ i, K.obj.obj (op (A i)),
          ( ∀ i,
      (Sigma.ι (fun j => (abelianOpenExtensionByZero (A j)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) i ≫ g).hom.app
        (op (A i))
        (abelianOpenExtensionSection (A i)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1))) = s i) ∧
          ( ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ))) ∧
          (∀ x : X, x ∈ iSup A →
            ∃ i, x ∈ A i ∧ ∀ j, x ∈ A j → c i ∣ c j)  := by
  sorry

end TopCat.Sheaf

