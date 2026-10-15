/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Data.Finset.Sort

/-! # Extended localization Čech complexes on ringed sites

Source: Stacks Project, Tags 0913 and 099H
(blueprint: def-weil-pbc-extended-localization-cech).

The construction uses the explicit cochain Koszul colimit of Tag 0913. Its degree-q
summands are indexed by subsets of cardinality q, including the empty subset in degree
zero. The transition on the subset I multiplies by the product of the f_i in I.
Thus its termwise colimit is the sheafification of the localization at that product;
the differential is the alternating localization differential. Finite coproducts are
finite products. The empty-subset transition is the identity, identifying degree zero
canonically with the original ring sheaf. For an empty family only degree zero remains.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules
namespace LocalizationCech

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Underlying ring sheaf. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
abbrev rings (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Index set in degree q. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
def Indices (r : ℕ) (q : ℤ) := {s : Finset (Fin r) // (s.card : ℤ) = q}

/-- Insertion raises the degree by one. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: insertion of a new element raises the finite cardinality by one; cast to integers. -/
theorem insert_degree {r : ℕ} {q : ℤ} (s : Indices r q) (j : Fin r) (h : j ∉ s.val) :
    ((insert j s.val).card : ℤ) = q + 1 := by
  sorry

/-- Free term on the subsets of cardinality q. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def term (R : Sheaf J CommRingCat.{u}) (r : ℕ) (q : ℤ) :
    CategoryTheory.ringedSiteModules.{u} (rings R) :=
  ∐ fun _ : Indices r q ↦ unit (rings R)

/-- The scalar endomorphism supplied by a global section. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def scalar (R : Sheaf J CommRingCat.{u})
    (f : (unit (rings R)).sections) : End (unit (rings R)) :=
  (unit (rings R)).unitHomEquiv.symm f

/-- Cochain Koszul differential at the positive exponent n+1. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def differential (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    term R r q ⟶ term R r (q + 1) := by
  classical
  exact Sigma.desc (fun s ↦ ∑ j : Fin r,
    if h : j ∉ s.val then
      (-1 : ℤ) ^ (s.val.filter (· < j)).card •
        ((scalar R (f j) ^ (n + 1)) ≫
          Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R))
            ⟨insert j s.val, insert_degree s j h⟩)
    else 0)

/-- The Koszul differential squares to zero. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on each free summand, pair the two orders of insertion of distinct indices.
The scalar endomorphisms commute because the coefficient ring is commutative, and
inserting the smaller index changes the sign of the other insertion. Repeated
indices contribute zero. Each pair therefore cancels. -/
theorem differential_sq (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    differential R r f n q ≫ differential R r f n (q + 1) = 0 := by
  sorry

/-- The positive-power cochain Koszul complex. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def koszul (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  CochainComplex.of (term R r) (differential R r f n) (differential_sq R r f n)

/-- Multiplication by the subset product; ordering fixes an actual composite.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def subsetScalar (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (s : Finset (Fin r)) :
    End (unit (rings R)) :=
  (s.sort (· ≤ ·)).foldr (fun j a ↦ scalar R (f j) ≫ a) (𝟙 _)

/-- Termwise transition from exponent n+1 to n+2. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def transitionTerm (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (q : ℤ) : term R r q ⟶ term R r q :=
  Sigma.desc (fun s ↦ subsetScalar R r f s.val ≫
    Sigma.ι (fun _ : Indices r q ↦ unit (rings R)) s)

/-- The transitions commute with the differentials. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the summand I and the component I union {j}, both composites have
coefficient (-1)^a(j,I) times (product over I of f_i) times f_j^(n+2). -/
theorem transition_comm (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    transitionTerm R r f q ≫ (koszul R r f (n + 1)).d q (q + 1) =
      (koszul R r f n).d q (q + 1) ≫ transitionTerm R r f (q + 1) := by
  sorry

/-- Koszul transition as a chain map. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def transition (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶ koszul R r f (n + 1) :=
  CochainComplex.ofHom (transitionTerm R r f) (transition_comm R r f n)

/-- Sequential diagram of positive-power Koszul complexes. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def diagram (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    ℕ ⥤ CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  Functor.ofSequence (transition R r f)

/-- The extended alternating localization Čech complex, constructed by the explicit
Koszul colimit. Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech).
On the subset I the cocone is a ↦ a/(product_I f_i)^(n+1). Every fraction occurs;
equality is eventual equality after multiplying by a power of that product.
The coefficient f_j^(n+1) becomes the localization map with sign (-1)^a(j,I).
Thus this is the extended alternating localization complex, including degree zero. -/
noncomputable def complex (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  colimit (diagram R r f)


/-- Restriction of scalars along a commutative coefficient map. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable abbrev restriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    CategoryTheory.ringedSiteModules.{u} (rings B) ⥤
      CategoryTheory.ringedSiteModules.{u} (rings R) :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

/-- Coefficient maps carry global sections to global sections. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: the naturality square of φ commutes with restriction; apply it to the section
and use the section's compatibility with restriction. -/
theorem mapSection_naturality {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (unit (rings B)).val.map a ((φ.hom.app X) (s.val X)) =
      (φ.hom.app Y) (s.val Y) := by
  sorry

/-- Image of a global section under the coefficient map. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def mapSection {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) : (unit (rings B)).sections :=
  ⟨fun X ↦ (φ.hom.app X) (s.val X), mapSection_naturality φ s⟩

/-- The coefficient map defines a unique linear morphism from the rank-one sheaf.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech).
Proof: the component is the ring homomorphism φ_U, linear for the restricted scalar
action. Its additivity is ring-map additivity, its linearity is multiplicativity,
and its naturality is the naturality of φ. Components determine a sheaf morphism. -/
theorem unitMap_existsUnique {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ∃! g : unit (rings R) ⟶ (restriction φ).obj (unit (rings B)),
      ∀ (X : Cᵒᵖ) (a : R.obj.obj X), g.val.app X a = (φ.hom.app X) a := by
  sorry

/-- The actual coefficient morphism, uniquely fixed by its sectionwise formula.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def unitMap {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    unit (rings R) ⟶ (restriction φ).obj (unit (rings B)) :=
  (unitMap_existsUnique φ).choose

/-- Comparison of the free Koszul terms, with the same subset labels.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonTerm {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (q : ℤ) : term R r q ⟶ (restriction φ).obj (term B r q) :=
  Sigma.desc (fun s ↦ unitMap φ ≫
    (restriction φ).map (Sigma.ι (fun _ : Indices r q ↦ unit (rings B)) s))

/-- The coefficient comparison commutes with the Koszul differential. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the summand I the j-th insertion has the same integer sign on both sides;
the equality φ(f_j^(n+1) a) = φ(f_j)^(n+1) φ(a) gives its scalar coefficient.
Coproduct extensionality then gives the equality. -/
theorem comparison_comm {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    comparisonTerm φ r q ≫
        (((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (koszul B r (mapSection φ ∘ f) n)).d q (q + 1) =
      (koszul R r f n).d q (q + 1) ≫ comparisonTerm φ r (q + 1) := by
  sorry

/-- The termwise coefficient map of Koszul complexes. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonStage {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶
      ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (koszul B r (mapSection φ ∘ f) n) :=
  CochainComplex.ofHom (comparisonTerm φ r) (comparison_comm φ r f n)

/-- Stage maps give a cocone into the restricted target Čech complex. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: coefficient maps carry each product of the f_i to the corresponding product
of their images, hence commute with each transition. Induction gives the same
identity for every natural-number arrow. The target colimit cocone then gives
exactly this naturality equation. -/
theorem comparisonCocone_naturality {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections)
    {n m : ℕ} (a : n ⟶ m) :
    (diagram R r f).map a ≫
        (comparisonStage φ r f m ≫
          ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (colimit.ι (diagram B r (mapSection φ ∘ f)) m)) =
      comparisonStage φ r f n ≫
        ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι (diagram B r (mapSection φ ∘ f)) n) := by
  sorry

/-- Cocone of the explicit coefficient comparisons. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonCocone {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) : Cocone (diagram R r f) where
  pt := ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (complex B r (mapSection φ ∘ f))
  ι :=
    { app := fun n ↦ comparisonStage φ r f n ≫
        ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι (diagram B r (mapSection φ ∘ f)) n)
      naturality := fun _ _ a ↦ comparisonCocone_naturality φ r f a }

/-- The canonical termwise localization comparison. On a fraction it sends
 a/(product_I f_i)^k to φ(a)/(product_I φ(f_i))^k.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    complex R r f ⟶
      ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (complex B r (mapSection φ ∘ f)) :=
  colimit.desc (diagram R r f) (comparisonCocone φ r f)

/-- The row presenting the ideal generated by the given global sections.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def idealRow (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    (∐ fun _ : Fin r ↦ unit (rings R)) ⟶ unit (rings R) :=
  Sigma.desc (fun j ↦ scalar R (f j))

/-- The coefficient map followed by the target quotient annihilates the source ideal.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the j-th summand, φ(f_j a) = φ(f_j) φ(a); this belongs to the target ideal.
The cokernel projection kills every generator, so the composite is zero. -/
theorem idealRow_comparison_zero {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    idealRow R r f ≫
      (unitMap φ ≫ (restriction φ).map (cokernel.π (idealRow B r (mapSection φ ∘ f)))) =
        0 := by
  sorry

/-- Underlying module morphism of the canonical quotient-ring-sheaf map.
The cokernel of the row is the sheafified quotient by the generated ideal; being
an isomorphism of this underlying module morphism is equivalent to the canonical
quotient-ring-sheaf map being an isomorphism.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def quotientComparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    cokernel (idealRow R r f) ⟶
      (restriction φ).obj (cokernel (idealRow B r (mapSection φ ∘ f))) :=
  cokernel.desc (idealRow R r f)
    (unitMap φ ≫ (restriction φ).map (cokernel.π (idealRow B r (mapSection φ ∘ f))))
    (idealRow_comparison_zero φ r f)


/-- Fold the unique empty-subset summand onto the coefficient sheaf.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def degreeZeroFold (R : Sheaf J CommRingCat.{u}) (r : ℕ) :
    term R r 0 ⟶ unit (rings R) :=
  Sigma.desc (fun _ ↦ 𝟙 _)

/-- There is no incoming differential in degree zero. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: a subset cannot have negative cardinality, so degree minus one is an empty
coproduct, hence zero. Every morphism out of it is zero. -/
theorem augmentation_incoming (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (i : ℤ)
    (h : (ComplexShape.up ℤ).Rel i 0) :
    (koszul R r f n).d i 0 ≫ degreeZeroFold R r = 0 := by
  sorry

/-- Koszul augmentation to the coefficient sheaf in degree zero.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentationStage (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶
      (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
        (ComplexShape.up ℤ) 0).obj (unit (rings R)) :=
  HomologicalComplex.mkHomToSingle (degreeZeroFold R r) (augmentation_incoming R r f n)

/-- The augmentations are compatible with the Koszul transitions. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: the empty-subset product is the identity. Thus every transition is the
identity in degree zero, where both augmentations are the fold. All other
augmentation components are zero. Iterate this equality along the given arrow. -/
theorem augmentation_naturality (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) {n m : ℕ} (a : n ⟶ m) :
    (diagram R r f).map a ≫ augmentationStage R r f m = augmentationStage R r f n := by
  sorry

/-- The augmentation cocone. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentationCocone (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) : Cocone (diagram R r f) where
  pt := (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
    (ComplexShape.up ℤ) 0).obj (unit (rings R))
  ι :=
    { app := augmentationStage R r f
      naturality := fun _ _ a ↦ augmentation_naturality R r f a }

/-- Augmentation of the extended Čech complex: identity on the empty-subset
coefficient sheaf in degree zero, and zero in every other degree.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentation (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    complex R r f ⟶
      (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
        (ComplexShape.up ℤ) 0).obj (unit (rings R)) :=
  colimit.desc (diagram R r f) (augmentationCocone R r f)

end LocalizationCech
end SheafOfModules
