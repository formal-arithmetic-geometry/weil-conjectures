module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory

/-! # Compatible deformation systems over a cofinal ideal filtration

Source: Stacks Project, Formal Deformation Theory, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system).

Indices start at zero: `ideal n` denotes I_{n+1}. All quotient algebras, residue
maps and transition maps are the literal canonical constructions. The formal-object
category uses exactly the existing `FormalObject` objects and `FormalHom` arrows,
with componentwise identities, composites and inverses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
  [Algebra.FiniteType R k]

/-- Proper decreasing ideals inducing the maximal-ideal-adic topology.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
structure CofinalIdealFiltration (C : CompleteLocalAlgebra R k) where
  ideal : ℕ → Ideal C.ring
  decreasing : Antitone ideal
  proper : ∀ n : ℕ, ideal n ≠ ⊤
  small : ∀ r : ℕ, ∃ n : ℕ, ideal n ≤ IsLocalRing.maximalIdeal C.ring ^ (r + 1)
  large : ∀ n : ℕ, ∃ r : ℕ, IsLocalRing.maximalIdeal C.ring ^ (r + 1) ≤ ideal n

section FormalObjectGroupoid

variable {F : CofibredGroupoids.{u, v, w} R k} {C : CompleteLocalAlgebra R k}

/-- Identity components commute with transitions. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-cofinal-filtration-system).
Transport preserves identity arrows, and both compositions are the transition itself. -/
theorem formalHom_id_comm (ξ : FormalObject F C) {m n : ℕ} (h : n ≤ m) :
    (push F (levelMap C h)).map (𝟙 (ξ.obj m)) ≫ (ξ.transition h).hom =
      (ξ.transition h).hom ≫ 𝟙 (ξ.obj n) := sorry

/-- Composites of compatible families are compatible. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-cofinal-filtration-system).
Expand transport of a composite, use the square for the second arrow and then the
first arrow, and reassociate. -/
theorem formalHom_comp_comm {ξ η ζ : FormalObject F C}
    (a : FormalHom ξ η) (b : FormalHom η ζ) {m n : ℕ} (h : n ≤ m) :
    (push F (levelMap C h)).map (a.app m ≫ b.app m) ≫ (ζ.transition h).hom =
      (ξ.transition h).hom ≫ (a.app n ≫ b.app n) := sorry

/-- Componentwise identity and composition of recorded formal arrows.
Source: Stacks, Tag 06H3 (blueprint: def-sfb-artin-cofinal-filtration-system). -/
instance formalObjectCategoryStruct : CategoryStruct (FormalObject F C) where
  Hom := FormalHom
  id ξ := ⟨fun n ↦ 𝟙 (ξ.obj n), fun h ↦ formalHom_id_comm ξ h⟩
  comp a b := ⟨fun n ↦ a.app n ≫ b.app n, fun h ↦ formalHom_comp_comm a b h⟩

/-- The category laws hold componentwise. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-cofinal-filtration-system).
FormalHom is determined by its components, since its square condition is a
proposition. The three equalities follow from the corresponding fibre category laws. -/
theorem formalObject_category_laws :
    (∀ (ξ η : FormalObject F C) (a : ξ ⟶ η), 𝟙 ξ ≫ a = a) ∧
    (∀ (ξ η : FormalObject F C) (a : ξ ⟶ η), a ≫ 𝟙 η = a) ∧
    (∀ (ξ η ζ θ : FormalObject F C) (a : ξ ⟶ η) (b : η ⟶ ζ) (c : ζ ⟶ θ),
      (a ≫ b) ≫ c = a ≫ (b ≫ c)) := sorry

/-- The category of formal objects with exactly the recorded compatible arrows.
Source: Stacks, Tag 06H3 (blueprint: def-sfb-artin-cofinal-filtration-system). -/
instance formalObjectCategory : Category (FormalObject F C) where
  id_comp := (formalObject_category_laws (F := F) (C := C)).1 _ _
  comp_id := (formalObject_category_laws (F := F) (C := C)).2.1 _ _
  assoc := (formalObject_category_laws (F := F) (C := C)).2.2 _ _ _ _

/-- All compatible families of arrows are invertible. Source: Stacks, Tag 06H3
(blueprint: def-sfb-artin-cofinal-filtration-system).
Invert every component in its fibre groupoid. Inverting the compatibility square
shows that these inverses form a FormalHom. The two inverse equations hold at every
level, hence hold for families. -/
theorem formalObject_isGroupoid : IsGroupoid (FormalObject F C) := sorry

attribute [instance] formalObject_isGroupoid

end FormalObjectGroupoid

variable {C : CompleteLocalAlgebra R k} (I : CofinalIdealFiltration C)

/-- Proper ideals in a local ring lie in the maximal ideal.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
Every element outside the maximal ideal is a unit. An ideal containing such an
element is the whole ring, contradicting properness. -/
theorem filtration_le_maximal (n : ℕ) : I.ideal n ≤ IsLocalRing.maximalIdeal C.ring :=
  sorry

/-- The literal quotient C/I_{n+1}. Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
abbrev FiltrationLevel (n : ℕ) := C.ring ⧸ I.ideal n

/-- Its residue marking, induced from the fixed marking of C.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system). -/
def filtrationResidue (n : ℕ) : FiltrationLevel I n →ₐ[R] k :=
  C.residueEquiv.toAlgHom.comp (Ideal.Quotient.factorₐ R (filtration_le_maximal I n))

/-- Each quotient is a marked Artinian local test algebra.
Source: Stacks, Tag 06H6 and Algebra Tag 00KH
(blueprint: def-sfb-artin-cofinal-filtration-system).
The ideal is proper and contains a positive power of the maximal ideal by `large`.
The quotient is Noetherian local with nilpotent maximal ideal, hence Artinian by
lem-weil-pbc-noetherian-local-quotient-artinian-local. Its residue augmentation is
surjective and has the quotient maximal ideal as kernel. -/
theorem filtration_isTestAlgebra (n : ℕ) :
    IsTestAlgebra R k (A := CommAlgCat.of R (FiltrationLevel I n))
      (filtrationResidue I n) := sorry

/-- The quotient with its canonical test-category structure.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
def filtrationTest (n : ℕ) : TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (filtrationResidue I n)), filtration_isTestAlgebra I n⟩

/-- Canonical quotient maps preserve the marked residue.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
Both composites send the class of c to its specified residue; quotient induction
and extensionality establish the equation. -/
theorem filtrationReduction_residue {m n : ℕ} (h : n ≤ m) :
    (filtrationResidue I n).comp (Ideal.Quotient.factorₐ R (I.decreasing h)) =
      filtrationResidue I m := sorry

/-- The quotient transition in the marked test category.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
def filtrationMap {m n : ℕ} (h : n ≤ m) : filtrationTest I m ⟶ filtrationTest I n :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (Ideal.Quotient.factorₐ R (I.decreasing h)))
    (congrArg CommAlgCat.ofHom (filtrationReduction_residue I h)))

/-- An equal-index quotient map is the identity.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
The maps agree on every representative, so quotient induction proves equality. -/
theorem filtrationMap_refl (n : ℕ) :
    filtrationMap I (le_refl n) = 𝟙 (filtrationTest I n) := sorry

/-- Quotient transitions compose canonically.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
Each composite sends a representative to its class at the smallest index.
Extensionality and quotient induction prove the equation. -/
theorem filtrationMap_comp {l m n : ℕ} (h : n ≤ m) (h' : m ≤ l) :
    filtrationMap I h' ≫ filtrationMap I h = filtrationMap I (h.trans h') := sorry

/-- Objects in the fibres with coherent invertible transitions at every pair of levels.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
structure FiltrationSystem (F : CofibredGroupoids.{u, v, w} R k) where
  obj : ∀ n : ℕ, fibre F (filtrationTest I n)
  transition : ∀ {m n : ℕ} (h : n ≤ m), (push F (filtrationMap I h)).obj (obj m) ≅ obj n
  transition_id : ∀ n : ℕ,
    (transition (le_refl n)).hom =
      eqToHom (congrArg (fun f ↦ (push F f).obj (obj n)) (filtrationMap_refl I n)) ≫
        (unitIso F (filtrationTest I n)).hom.app (obj n)
  transition_comp : ∀ {l m n : ℕ} (h : n ≤ m) (h' : m ≤ l),
    (push F (filtrationMap I h)).map (transition h').hom ≫ (transition h).hom =
      (compIso F (filtrationMap I h') (filtrationMap I h)).hom.app (obj l) ≫
        eqToHom (congrArg (fun f ↦ (push F f).obj (obj l)) (filtrationMap_comp I h h')) ≫
          (transition (h.trans h')).hom

variable {I} {F : CofibredGroupoids.{u, v, w} R k}

/-- Families of fibre arrows commuting with all transitions.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
structure FiltrationHom (s t : FiltrationSystem I F) where
  app : ∀ n : ℕ, s.obj n ⟶ t.obj n
  comm : ∀ {m n : ℕ} (h : n ≤ m),
    (push F (filtrationMap I h)).map (app m) ≫ (t.transition h).hom =
      (s.transition h).hom ≫ app n

/-- Identity families commute with transitions.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system).
Transport preserves identity arrows; both sides reduce to the transition. -/
theorem filtrationHom_id_comm (s : FiltrationSystem I F) {m n : ℕ} (h : n ≤ m) :
    (push F (filtrationMap I h)).map (𝟙 (s.obj m)) ≫ (s.transition h).hom =
      (s.transition h).hom ≫ 𝟙 (s.obj n) := sorry

/-- Compatible arrows compose componentwise.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system).
Expand transport of a composite, apply the two commuting squares in turn and
reassociate to obtain the required square. -/
theorem filtrationHom_comp_comm {s t z : FiltrationSystem I F}
    (a : FiltrationHom s t) (b : FiltrationHom t z) {m n : ℕ} (h : n ≤ m) :
    (push F (filtrationMap I h)).map (a.app m ≫ b.app m) ≫ (z.transition h).hom =
      (s.transition h).hom ≫ (a.app n ≫ b.app n) := sorry

/-- Componentwise identities and composites of compatible families.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
instance filtrationSystemCategoryStruct : CategoryStruct (FiltrationSystem I F) where
  Hom := FiltrationHom
  id s := ⟨fun n ↦ 𝟙 (s.obj n), fun h ↦ filtrationHom_id_comm s h⟩
  comp a b := ⟨fun n ↦ a.app n ≫ b.app n, fun h ↦ filtrationHom_comp_comm a b h⟩

/-- Category laws for compatible families.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system).
Families are equal when their components agree, since the square conditions are
propositions. The fibre identity and associativity laws give all three equalities. -/
theorem filtrationSystem_category_laws :
    (∀ (s t : FiltrationSystem I F) (a : s ⟶ t), 𝟙 s ≫ a = a) ∧
    (∀ (s t : FiltrationSystem I F) (a : s ⟶ t), a ≫ 𝟙 t = a) ∧
    (∀ (s t z y : FiltrationSystem I F) (a : s ⟶ t) (b : t ⟶ z) (c : z ⟶ y),
      (a ≫ b) ≫ c = a ≫ (b ≫ c)) := sorry

/-- The category of compatible systems over the cofinal filtration.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
instance filtrationSystemCategory : Category (FiltrationSystem I F) where
  id_comp := (filtrationSystem_category_laws (I := I) (F := F)).1 _ _
  comp_id := (filtrationSystem_category_laws (I := I) (F := F)).2.1 _ _
  assoc := (filtrationSystem_category_laws (I := I) (F := F)).2.2 _ _ _ _

/-- Compatible families form a groupoid.
Source: Stacks, paragraph before Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system).
Invert each component in its fibre. The original commuting square, composed with
the two inverses, proves compatibility. Inverse identities hold componentwise. -/
theorem filtrationSystem_isGroupoid : IsGroupoid (FiltrationSystem I F) := sorry

attribute [instance] filtrationSystem_isGroupoid

variable (I)

/-- Composing a quotient projection with a test arrow gives a marked local map.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
The quotient projection and the test arrow are local; their composite is local.
The test arrow preserves the augmentation, and the quotient augmentation is induced
from C, proving the displayed marking identity. -/
theorem filtrationLocalMap_properties (n : ℕ) {A : TestCategory R k}
    (f : filtrationTest I n ⟶ A) :
    IsLocalHom ((map f).comp (Ideal.Quotient.mkₐ R (I.ideal n))) ∧
    (∀ c : C.ring, residue A (((map f).comp (Ideal.Quotient.mkₐ R (I.ideal n))) c) =
      C.residueEquiv (IsLocalRing.residue C.ring c)) := sorry

/-- The specified map C → C/I_{n+1} → A, with its locality and marking retained.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system). -/
def filtrationLocalMap (n : ℕ) {A : TestCategory R k}
    (f : filtrationTest I n ⟶ A) : LocalMap C A where
  hom := (map f).comp (Ideal.Quotient.mkₐ R (I.ideal n))
  localHom := (filtrationLocalMap_properties I n f).1
  marked := (filtrationLocalMap_properties I n f).2

/-- A commuting square of factorizations gives the same map out of C.
Source: Stacks, Tag 06H6 (blueprint: def-sfb-artin-cofinal-filtration-system).
Precompose the given square with the quotient projection C → C/I_{n+1}.
Its composite with the quotient transition is the projection C → C/I_{m+1}.
Equality on representatives proves the required equality of algebra maps. -/
theorem filtrationLocalMap_comp {n m : ℕ} (h : m ≤ n)
    {A B : TestCategory R k} (f : filtrationTest I n ⟶ A)
    (f' : filtrationTest I m ⟶ B) (g : A ⟶ B)
    (hg : f ≫ g = filtrationMap I h ≫ f') :
    (map g).comp (filtrationLocalMap I n f).hom = (filtrationLocalMap I m f').hom :=
  sorry

/-- The comparison between two transported components along a commuting square of
factorizations: compose transports, use the square, separate transports, then use
the system transition. Source: Stacks, Tag 06H6
(blueprint: def-sfb-artin-cofinal-filtration-system). -/
def filtrationTransportComparison (s : FiltrationSystem I F) {n m : ℕ} (h : m ≤ n)
    {A B : TestCategory R k} (f : filtrationTest I n ⟶ A)
    (f' : filtrationTest I m ⟶ B) (g : A ⟶ B)
    (hg : f ≫ g = filtrationMap I h ≫ f') :
    (push F g).obj ((push F f).obj (s.obj n)) ≅ (push F f').obj (s.obj m) :=
  (compIso F f g).app (s.obj n) ≪≫
    eqToIso (congrArg (fun a ↦ (push F a).obj (s.obj n)) hg) ≪≫
    (compIso F (filtrationMap I h) f').symm.app (s.obj n) ≪≫
    (push F f').mapIso (s.transition h)

end AlgebraicGeometry.ArtinDeformation
