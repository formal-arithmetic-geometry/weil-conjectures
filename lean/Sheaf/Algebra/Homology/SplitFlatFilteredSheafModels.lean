/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Split-flat filtered sheaf models

Source: Varshavsky, §5.2.1(b), and the explicit finite-flag adaptation of Stacks
Tags 077J, 06YQ and 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models).
The splitting is degreewise, never a splitting of complexes. The total tensor and
all its arrows are the existing direct-sum total bifunctor. Convolution is specified
by its actual image subobjects; no filtration is selected from an existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules.FilteredFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The existing module-sheaf category, with coefficients in a universe containing the site.
Source: Stacks, Modules on Sites, 03DA
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
abbrev Modules := ringedSiteModules.{r, r, v, u} ((sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Bounded-above complexes with the fixed uniform interval `[a,b]`.
Source: Stacks 05S2 and 077J (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
abbrev Complexes (a b : ℤ) :=
  UniformFilteredComplexes (Modules R) (some (a, b)) (CochainComplex.minus (Modules R))

/-- Degreewise split finite sums of flat sheaves, with integer grade labels.
The images of the summand injections specify every step of the filtration.
In a fixed interval, summands labelled outside it are necessarily zero, so this is
exactly a splitting with summands in its permitted grades, after deleting zero terms.
Source: finite-sum cover construction for Stacks 077J and 03EW
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def IsSplitFlat (K : FilteredObject (CochainComplex (Modules R) ℤ)) : Prop :=
  ∀ n : ℤ, ∃ (m : ℕ) (grade : Fin m → ℤ) (B : Fin m → Modules R)
    (e : (∐ B) ≅ K.obj.X n),
    (∀ i : Fin m, IsFlatOnSite.{u, v, r, r} (J := J) (R := R) (B i)) ∧
    ∀ p : ℤ, K.filtration.complexStep p n =
      Finset.univ.sup (fun i ↦
        if p ≤ grade i then imageSubobject (Sigma.ι B i ≫ e.hom) else ⊥)

/-- Split-flat objects and all filtered chain maps between them.
Source: Stacks 077J, finite-flag adaptation
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
abbrev FlatComplexes (a b : ℤ) :=
  ObjectProperty.FullSubcategory (fun K : Complexes R a b ↦ IsSplitFlat R K.obj)

/-- The full inclusion of split-flat chain complexes.
Source: Stacks 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def flatInclusion (a b : ℤ) : FlatComplexes R a b ⥤ Complexes R a b :=
  ObjectProperty.ι _

/-- Filtered chain homotopies, using Mathlib's homotopy identity and actual step lifts.
Source: Stacks, Derived Categories, §13.13 before 05S1
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def filteredHomotopyRel : HomRel (FilteredObject (CochainComplex (Modules R) ℤ)) :=
  fun {K L} f g ↦ ∃ h : Homotopy f.hom g.hom,
    ∀ p n m : ℤ, ∃ lift :
      (K.filtration.step p : CochainComplex (Modules R) ℤ).X n ⟶
        (L.filtration.step p : CochainComplex (Modules R) ℤ).X m,
      lift ≫ (L.filtration.step p).arrow.f m =
        (K.filtration.step p).arrow.f n ≫ h.hom n m

/-- Filtered complexes modulo the preceding filtered homotopies.
Source: Stacks 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
abbrev HomotopyCategory := CategoryTheory.Quotient (filteredHomotopyRel R)

/-- The fixed-interval split-flat full subcategory of the filtered homotopy category.
Source: Stacks 05S2, finite-flag adaptation
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
abbrev FlatHomotopy (a b : ℤ) :=
  ObjectProperty.FullSubcategory (fun K : HomotopyCategory R ↦
    uniformFilteredProperty (some (a, b)) (CochainComplex.minus (Modules R)) K.as ∧
      IsSplitFlat R K.as)

/-- The actual functor taking a filtered chain map to its homotopy class.
Source: Stacks 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def flatHomotopyQuotient (a b : ℤ) : FlatComplexes R a b ⥤ FlatHomotopy R a b where
  obj K := ⟨⟨K.obj.obj⟩, K.obj.property, K.property⟩
  map f := ObjectProperty.homMk ((CategoryTheory.Quotient.functor
    (filteredHomotopyRel R)).map f.hom.hom)

/-- Graded quasi-isomorphisms of filtered homotopy classes, expressed on a representative.
Source: Stacks 05S1 and 05S2
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def flatHomotopyQuasiIso (a b : ℤ) : MorphismProperty (FlatHomotopy R a b) :=
  fun {K L} f ↦ ∃ g : K.obj.as ⟶ L.obj.as,
    (CategoryTheory.Quotient.functor (filteredHomotopyRel R)).map g = f.hom ∧
      ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps g p)

/-- Widening an interval preserves the existing uniform bounded-above property.
Source: Stacks 05S2, inclusion of finite filtration intervals.
Proof: if `c ≤ a`, antitonicity gives `Fᶜ ≥ Fᵃ = ⊤`. If `b ≤ d`,
antitonicity gives `Fᵈ⁺¹ ≤ Fᵇ⁺¹ = ⊥`. Finiteness and the cochain bound
are unchanged. These are precisely the three clauses of `uniformFilteredProperty`.
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
theorem widenProperty (a b c d : ℤ) (ha : c ≤ a) (hb : b ≤ d)
    (K : FilteredObject (CochainComplex (Modules R) ℤ)) :
    uniformFilteredProperty (some (a, b)) (CochainComplex.minus (Modules R)) K →
      uniformFilteredProperty (some (c, d)) (CochainComplex.minus (Modules R)) K := by
  rintro ⟨hfinite, hbounds, hminus⟩
  obtain ⟨htop, hbot⟩ := hbounds a b rfl
  refine ⟨hfinite, ?_, hminus⟩
  intro c' d' h
  cases Option.some.inj h
  constructor
  · apply top_unique
    rw [← htop]
    exact K.filtration.antitone ha
  · apply bot_unique
    rw [← hbot]
    exact K.filtration.antitone (by omega)

/-- Interval inclusion on filtered chain complexes, keeping the object and every map.
Source: Stacks 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def widenComplexes (a b c d : ℤ) (ha : c ≤ a) (hb : b ≤ d) :
    Complexes R a b ⥤ Complexes R c d :=
  ObjectProperty.ιOfLE (fun K hK ↦ widenProperty R a b c d ha hb K hK)

/-- Interval inclusion on split-flat homotopy categories, keeping every homotopy class.
Source: Stacks 05S2 (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def widenFlatHomotopy (a b c d : ℤ) (ha : c ≤ a) (hb : b ≤ d) :
    FlatHomotopy R a b ⥤ FlatHomotopy R c d :=
  ObjectProperty.ιOfLE (fun K hK ↦
    ⟨widenProperty R a b c d ha hb K.as hK.1, hK.2⟩)

/-- The canonical interval inclusion after localization of split-flat homotopy classes.
The lift uses precisely the unchanged graded maps.
Source: Stacks 04VG (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def widenFlatLocalization (a b c d : ℤ) (ha : c ≤ a) (hb : b ≤ d) :
    (flatHomotopyQuasiIso R a b).Localization ⥤
      (flatHomotopyQuasiIso R c d).Localization :=
  Localization.Construction.lift
    (widenFlatHomotopy R a b c d ha hb ⋙ (flatHomotopyQuasiIso R c d).Q)
    (fun _ _ f hf ↦ (flatHomotopyQuasiIso R c d).Q_inverts
      ((widenFlatHomotopy R a b c d ha hb).map f) hf)

/-- The canonical interval inclusion in the existing chain-map localization.
Source: Stacks 04VG and 05S2
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def widenDerived (a b c d : ℤ) (ha : c ≤ a) (hb : b ≤ d) :
    UniformFilteredDerived (Modules R) (some (a, b)) (CochainComplex.minus (Modules R)) ⥤
      UniformFilteredDerived (Modules R) (some (c, d))
        (CochainComplex.minus (Modules R)) :=
  Localization.Construction.lift
    (widenComplexes R a b c d ha hb ⋙
      (uniformFilteredQuasiIso (some (c, d)) (CochainComplex.minus (Modules R))).Q)
    (fun _ _ f hf ↦
      (uniformFilteredQuasiIso (some (c, d)) (CochainComplex.minus (Modules R))).Q_inverts
        ((widenComplexes R a b c d ha hb).map f) hf)

/-- The direct-sum total tensor using the recorded canonical sheaf tensor bifunctor.
Source: Stacks 06YN (blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def tensorTotal (P W : CochainComplex (Modules R) ℤ) : CochainComplex (Modules R) ℤ :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := SheafOfModules.monoidalCategory R
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  CochainComplex.mapBifunctor P W (curriedTensor _)

/-- The actual total tensor of the two step inclusions.
Source: Stacks 06YN and Varshavsky §5.2.1(b)
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def tensorStepArrow (P W : FilteredObject (CochainComplex (Modules R) ℤ)) (p q : ℤ) :
    tensorTotal R (P.filtration.step p) (W.filtration.step q) ⟶
      tensorTotal R P.obj W.obj :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := SheafOfModules.monoidalCategory R
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  HomologicalComplex.mapBifunctorMap (P.filtration.step p).arrow (W.filtration.step q).arrow
    (curriedTensor _) (.up ℤ)

/-- A convolution filtration is specified by the sum of the actual tensor-step images.
Existence will be asserted, rather than assumed, by the resolution theorem.
Source: Varshavsky §5.2.1(b), filtered tensor referred to Illusie V §2
(blueprint: def-trf-split-flat-filtered-sheaf-models). -/
def IsConvolution (P W : FilteredObject (CochainComplex (Modules R) ℤ))
    (F : DecreasingFiltration (tensorTotal R P.obj W.obj)) : Prop :=
  ∀ s : ℤ, F.step s = imageSubobject
    (Sigma.desc (fun p : ℤ ↦ tensorStepArrow R P W p (s - p)))

end SheafOfModules.FilteredFlat
