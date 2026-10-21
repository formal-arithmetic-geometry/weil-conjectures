/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-!
# Filtered derived global Hom and filtration truncation calculus

Source: Varshavsky, §§5.1.2(a)–(c), 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus).

The theorem asserts the existence of the entire calculus; no functor is selected from
an unproved, non-unique existence theorem. The source and target categories are the
actual finite-filtered localizations, with their cone-normalized triangulations.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Strict lower boundedness, with an optional strict upper bound.
Source: Stacks, 05S4 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
def DegreeBound (bounded : Bool) (K : CochainComplex A ℤ) : Prop :=
  (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.X n)) ∧
    (bounded = false ∨ ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.X n))

/-- Uniformly finite filtrations on bounded or bounded-below complexes. The filtration
bounds are bounds on subcomplexes, not degree-dependent bounds.
Source: Varshavsky, 5.1.1(a) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
abbrev Complex (bounded : Bool) :=
  ObjectProperty.FullSubcategory (fun K : FilteredObject (CochainComplex A ℤ) =>
    K.filtration.IsFinite ∧ DegreeBound A bounded K.obj)

variable {A}

/-- The canonical associated-graded map is functorial.
Source: Stacks, 0121. Proof: restrict to the steps and apply the cokernel universal
property. Monicity makes restrictions unique and epimorphic quotient maps detect equality.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem graded_laws (bounded : Bool) (p : ℤ) :
    (∀ K : Complex A bounded,
      FilteredObject.gradedMapSteps (𝟙 K : K ⟶ K).hom p = 𝟙 (K.obj.filtration.gradedPiece p)) ∧
    (∀ (K L M : Complex A bounded) (f : K ⟶ L) (g : L ⟶ M),
      FilteredObject.gradedMapSteps (f ≫ g).hom p =
        FilteredObject.gradedMapSteps f.hom p ≫ FilteredObject.gradedMapSteps g.hom p) := by
  have hπ {K M : Complex A bounded} (f : K ⟶ M) :
      K.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫
          FilteredObject.gradedMapSteps f.hom p =
        FilteredObject.restrictionSteps f.hom p ≫
          M.obj.filtration.complexQuotientπ p (p + 1) (by omega) :=
    Classical.choose_spec (FilteredObject.exists_gradedMap_steps K.obj M.obj f.hom p)
  have hr {K M : Complex A bounded} (f : K ⟶ M) :
      FilteredObject.restrictionSteps f.hom p ≫ (M.obj.filtration.step p).arrow =
        (K.obj.filtration.step p).arrow ≫ f.hom.hom :=
    Classical.choose_spec (f.hom.preserves p)
  constructor
  · intro K
    have hi : FilteredObject.restrictionSteps (𝟙 K : K ⟶ K).hom p = 𝟙 _ := by
      apply (cancel_mono (K.obj.filtration.step p).arrow).1
      have h := hr (𝟙 K : K ⟶ K)
      change FilteredObject.restrictionSteps (𝟙 K : K ⟶ K).hom p ≫
        (K.obj.filtration.step p).arrow = (K.obj.filtration.step p).arrow ≫ 𝟙 _ at h
      simpa only [Category.id_comp, Category.comp_id] using h
    apply (cancel_epi (cokernel.π (Subobject.ofLE (K.obj.filtration.step (p + 1))
      (K.obj.filtration.step p) (K.obj.filtration.antitone_step (by omega))))).1
    change K.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ _ = _
    rw [hπ, hi, Category.id_comp]
    exact (Category.comp_id
      (K.obj.filtration.complexQuotientπ p (p + 1) (by omega))).symm
  · intro K M N f g
    have hc : FilteredObject.restrictionSteps (f ≫ g).hom p =
        FilteredObject.restrictionSteps f.hom p ≫
          FilteredObject.restrictionSteps g.hom p := by
      apply (cancel_mono (N.obj.filtration.step p).arrow).1
      rw [hr, Category.assoc, hr, ← Category.assoc, hr, Category.assoc]
      rfl
    apply (cancel_epi (cokernel.π (Subobject.ofLE (K.obj.filtration.step (p + 1))
      (K.obj.filtration.step p) (K.obj.filtration.antitone_step (by omega))))).1
    change K.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ _ = _
    rw [hπ, hc, Category.assoc, ← hπ, ← Category.assoc, ← hπ, Category.assoc]
    rfl

/-- The underlying complex functor.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
def forget (bounded : Bool) : Complex A bounded ⥤ CochainComplex A ℤ where
  obj K := K.obj.obj
  map f := f.hom.hom

/-- The associated-graded complex functor, using the recorded subquotient interface.
Source: Stacks, 012K (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def graded (bounded : Bool) (p : ℤ) :
    Complex A bounded ⥤ CochainComplex A ℤ where
  obj K := K.obj.filtration.gradedPiece p
  map f := FilteredObject.gradedMapSteps f.hom p
  map_id K := (graded_laws bounded p).1 K
  map_comp f g := (graded_laws bounded p).2 _ _ _ f g

/-- Graded quasi-isomorphisms of finite filtered complexes.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
def quasiIso (bounded : Bool) : MorphismProperty (Complex A bounded) :=
  fun {_ _} f => ∀ p : ℤ, QuasiIso ((graded bounded p).map f)

/-- The actual localization at graded quasi-isomorphisms. `true` means bounded;
`false` means bounded below. Source: Stacks, 05S2–05S6
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
abbrev Derived (bounded : Bool) := (quasiIso (A := A) bounded).Localization

/-- The canonical localization functor.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable abbrev Q (bounded : Bool) : Complex A bounded ⥤ Derived (A := A) bounded :=
  (quasiIso bounded).Q

/-- The filtration subcomplex before localization, with its induced filtration.
Source: Varshavsky, 5.1.1(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def highObject (K : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    FilteredObject (CochainComplex A ℤ) where
  obj := K.filtration.step r
  filtration := K.filtration.induced (K.filtration.step r)

/-- The quotient before localization, with its image filtration.
Source: Varshavsky, 5.1.1(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def lowObject (K : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    FilteredObject (CochainComplex A ℤ) where
  obj := cokernel (K.filtration.step r).arrow
  filtration := K.filtration.quotient (cokernel.π (K.filtration.step r).arrow)

/-- Subcomplex and quotient truncation preserve the strict cochain bounds and uniform
finite filtration. Source: Stacks, 05S4.
Proof: a subobject or quotient of a zero term is zero. Intersecting or taking images
preserves the lower whole-object and upper zero filtration steps.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem truncation_bounds (bounded : Bool) (K : Complex A bounded) (r : ℤ) :
    ((highObject K.obj r).filtration.IsFinite ∧
      DegreeBound A bounded (highObject K.obj r).obj) ∧
    ((lowObject K.obj r).filtration.IsFinite ∧
      DegreeBound A bounded (lowObject K.obj r).obj) := by
  sorry

/-- The bounded or bounded-below subcomplex truncation.
Source: Varshavsky, 5.1.1(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def high (bounded : Bool) (K : Complex A bounded) (r : ℤ) :
    Complex A bounded := ⟨highObject K.obj r, (truncation_bounds bounded K r).1⟩

/-- The bounded or bounded-below quotient truncation.
Source: Varshavsky, 5.1.1(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def low (bounded : Bool) (K : Complex A bounded) (r : ℤ) :
    Complex A bounded := ⟨lowObject K.obj r, (truncation_bounds bounded K r).2⟩

/-- Restrictions commute with the inclusions into the total complexes.
Source: Stacks, 0121. Proof: the restriction is the unique lift through the target
monomorphism, so its defining factorization is the asserted equality.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem restriction_square {K L : FilteredObject (CochainComplex A ℤ)}
    (f : K ⟶ L) (r : ℤ) :
    FilteredObject.restrictionSteps f r ≫ (L.filtration.step r).arrow =
      (K.filtration.step r).arrow ≫ f.hom := by
  sorry

/-- The inclusion and quotient preserve the induced and image filtrations.
Source: Stacks, 0121. Proof: use the pullback projection for the induced filtration
and the image factorization for the quotient filtration.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem truncation_maps (K : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    (∀ i : ℤ, ∃ l : ((highObject K r).filtration.step i : CochainComplex A ℤ) ⟶
      (K.filtration.step i : CochainComplex A ℤ),
      l ≫ (K.filtration.step i).arrow =
        ((highObject K r).filtration.step i).arrow ≫ (K.filtration.step r).arrow) ∧
    (∀ i : ℤ, ∃ l : (K.filtration.step i : CochainComplex A ℤ) ⟶
      ((lowObject K r).filtration.step i : CochainComplex A ℤ),
      l ≫ ((lowObject K r).filtration.step i).arrow =
        (K.filtration.step i).arrow ≫ cokernel.π (K.filtration.step r).arrow) := by
  sorry

/-- The actual subcomplex inclusion before localization.
Source: Varshavsky, 5.1.2(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def highι (bounded : Bool) (K : Complex A bounded) (r : ℤ) :
    high bounded K r ⟶ K :=
  ⟨⟨(K.obj.filtration.step r).arrow, (truncation_maps K.obj r).1⟩⟩

/-- The actual quotient map before localization.
Source: Varshavsky, 5.1.2(c) (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def lowπ (bounded : Bool) (K : Complex A bounded) (r : ℤ) :
    K ⟶ low bounded K r :=
  ⟨⟨cokernel.π (K.obj.filtration.step r).arrow, (truncation_maps K.obj r).2⟩⟩

/-- The stepwise cone maps into the total cone by the canonical cone map.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def coneStepMap {K L : FilteredObject (CochainComplex A ℤ)}
    (f : K ⟶ L) (r : ℤ) :
    mappingCone (FilteredObject.restrictionSteps f r) ⟶ mappingCone f.hom :=
  mappingCone.map _ _ (K.filtration.step r).arrow (L.filtration.step r).arrow
    (restriction_square f r)

/-- Images of the stepwise cone inclusions form a decreasing filtration.
Source: Stacks, 05S2. Proof: inclusions of successive steps induce a map of their
cones, commuting with the maps into the total cone; image subobjects are therefore ordered.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem cone_antitone {K L : FilteredObject (CochainComplex A ℤ)} (f : K ⟶ L) :
    Antitone (fun r : ℤ => imageSubobject (coneStepMap f r)) := by
  sorry

/-- The mapping cone with its actual direct-sum filtration.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def coneObject {K L : FilteredObject (CochainComplex A ℤ)} (f : K ⟶ L) :
    FilteredObject (CochainComplex A ℤ) where
  obj := mappingCone f.hom
  filtration :=
    { F := fun r => imageSubobject (coneStepMap f r)
      F_succ_le := fun r => cone_antitone f (by omega) }

/-- Shifting the step inclusions gives an antitone family of images.
Source: Stacks, 05S2. Proof: apply the shift functor to the inclusion of successive
subcomplexes and use functoriality of images.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem shift_antitone (K : FilteredObject (CochainComplex A ℤ)) (n : ℤ) :
    Antitone (fun r : ℤ =>
      imageSubobject
        ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map
          (K.filtration.step r).arrow)) := by
  sorry

/-- Cochain shift with the shifted filtration, independent of filtration indices.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def shiftObject (K : FilteredObject (CochainComplex A ℤ)) (n : ℤ) :
    FilteredObject (CochainComplex A ℤ) where
  obj := K.obj⟦n⟧
  filtration :=
    { F := fun r => imageSubobject
        ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map (K.filtration.step r).arrow)
      F_succ_le := fun r => shift_antitone K n (by omega) }

/-- Cones and shifts retain the relevant cochain boundedness and uniform finite filtration.
Source: Stacks, 05S2–05S4. Proof: each shifted term is a reindexed original term;
each cone term is a finite biproduct of two such terms. At filtration extremes the
stepwise cone map is respectively an isomorphism or has zero source.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem cone_shift_bounds (bounded : Bool) (K L : Complex A bounded) (f : K ⟶ L) (n : ℤ) :
    ((coneObject f.hom).filtration.IsFinite ∧
      DegreeBound A bounded (coneObject f.hom).obj) ∧
    ((shiftObject K.obj n).filtration.IsFinite ∧
      DegreeBound A bounded (shiftObject K.obj n).obj) := by
  sorry

/-- The finite filtered cone, in either boundedness variant.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def cone (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) :
    Complex A bounded := ⟨coneObject f.hom, (cone_shift_bounds bounded K L f 0).1⟩

/-- The finite filtered shifted complex.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def shift (bounded : Bool) (K : Complex A bounded) (n : ℤ) :
    Complex A bounded := ⟨shiftObject K.obj n, (cone_shift_bounds bounded K K (𝟙 K) n).2⟩

/-- The two cone-triangle maps preserve the cone and shifted filtrations.
Source: Stacks, 05S2. Proof: the inclusion of the target and the shifted-source projection
commute with the stepwise cone maps, and hence induce the asserted image factorizations.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem cone_maps (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) :
    (∃ i : L ⟶ cone bounded f, i.hom.hom = (mappingCone.triangle f.hom.hom).mor₂) ∧
    (∃ p : cone bounded f ⟶ shift bounded K 1,
      p.hom.hom = (mappingCone.triangle f.hom.hom).mor₃) := by
  sorry

/-- The filtered cone inclusion, uniquely fixed by its underlying chain map.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def coneι (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) :
    L ⟶ cone bounded f := (cone_maps bounded f).1.choose

/-- The filtered cone projection, with Mathlib's cone-triangle sign convention.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def coneπ (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) :
    cone bounded f ⟶ shift bounded K 1 := (cone_maps bounded f).2.choose

/-- A shifted filtered morphism preserves the shifted filtration.
Source: Stacks, 05S2. Proof: shift each factorization through a filtration step and
then use the universal property of its image subobject.
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
theorem shift_preserves (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) (n : ℤ) :
    ∀ i : ℤ, ∃ l : ((shift bounded K n).obj.filtration.step i : CochainComplex A ℤ) ⟶
      ((shift bounded L n).obj.filtration.step i : CochainComplex A ℤ),
      l ≫ ((shift bounded L n).obj.filtration.step i).arrow =
        ((shift bounded K n).obj.filtration.step i).arrow ≫
          (CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map f.hom.hom := by
  sorry

/-- The actual shifted filtered chain map.
Source: Stacks, 05S2 (blueprint: lem-trf-filtered-derived-hom-calculus). -/
noncomputable def shiftMap (bounded : Bool) {K L : Complex A bounded} (f : K ⟶ L) (n : ℤ) :
    shift bounded K n ⟶ shift bounded L n :=
  ⟨⟨(CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map f.hom.hom,
    shift_preserves bounded f n⟩⟩

end CochainComplex.FiniteFiltered


namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The standard triangulation of the actual filtered localization, characterized by
filtered mapping-cone triangles and the actual cochain shift, rather than by an
arbitrary distinguished-triangle predicate.
Source: Stacks, 05S2; Varshavsky, 5.1.2
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
class TriangulatedLocalization (bounded : Bool) where
  [preadditive : Preadditive (Derived (A := A) bounded)]
  [zero : HasZeroObject (Derived (A := A) bounded)]
  [shift : HasShift (Derived (A := A) bounded) ℤ]
  [shift_additive : ∀ n : ℤ,
    (CategoryTheory.shiftFunctor (Derived (A := A) bounded) n).Additive]
  [pretriangulated : Pretriangulated (Derived (A := A) bounded)]
  [triangulated : IsTriangulated (Derived (A := A) bounded)]
  shiftComparison : ∀ (K : Complex A bounded) (n : ℤ),
    (Q bounded).obj (FiniteFiltered.shift bounded K n) ≅ ((Q bounded).obj K)⟦n⟧
  shift_naturality : ∀ (K L : Complex A bounded) (f : K ⟶ L) (n : ℤ),
    (Q bounded).map (shiftMap bounded f n) ≫ (shiftComparison L n).hom =
      (shiftComparison K n).hom ≫ ((Q bounded).map f)⟦n⟧'
  cone_normalization : ∀ T : Triangle (Derived (A := A) bounded),
    T ∈ distTriang (Derived (A := A) bounded) ↔
      ∃ (K L : Complex A bounded) (f : K ⟶ L),
        Nonempty (T ≅ Triangle.mk ((Q bounded).map f)
          ((Q bounded).map (coneι bounded f))
          ((Q bounded).map (coneπ bounded f) ≫ (shiftComparison K 1).hom))

attribute [instance_reducible] TriangulatedLocalization.preadditive
  TriangulatedLocalization.shift TriangulatedLocalization.pretriangulated

attribute [instance] TriangulatedLocalization.preadditive TriangulatedLocalization.zero
  TriangulatedLocalization.shift TriangulatedLocalization.shift_additive
  TriangulatedLocalization.pretriangulated TriangulatedLocalization.triangulated

variable [HasDerivedCategory.{max u v} A]

/-- The bounded full subcategory of the ordinary derived category, described by actual
bounded representatives. Source: Stacks, 05S6, ordinary specialization
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
abbrev BoundedDerived := ObjectProperty.FullSubcategory
  (fun P : DerivedCategory A => ∃ K : CochainComplex A ℤ,
    DegreeBound A true K ∧ Nonempty (P ≅ DerivedCategory.Q.obj K))

/-- Forgetful, graded, and filtration truncation functors with their canonical maps.
Both boundedness variants use the same interface.
Source: Varshavsky, 5.1.2(a)–(c)
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
structure TruncationCalculus (bounded : Bool) [TriangulatedLocalization A bounded] where
  omega : Derived (A := A) bounded ⥤ DerivedCategory A
  [omega_shift : omega.CommShift ℤ]
  [omega_exact : omega.IsTriangulated]
  omegaComparison : Q bounded ⋙ omega ≅ forget bounded ⋙ DerivedCategory.Q
  gr : ℤ → Derived (A := A) bounded ⥤ DerivedCategory A
  grComparison : ∀ a : ℤ, Q bounded ⋙ gr a ≅ graded bounded a ⋙ DerivedCategory.Q
  high : ℤ → Derived (A := A) bounded ⥤ Derived (A := A) bounded
  low : ℤ → Derived (A := A) bounded ⥤ Derived (A := A) bounded
  [high_shift : ∀ r : ℤ, (high r).CommShift ℤ]
  [low_shift : ∀ r : ℤ, (low r).CommShift ℤ]
  [high_exact : ∀ r : ℤ, (high r).IsTriangulated]
  [low_exact : ∀ r : ℤ, (low r).IsTriangulated]
  inclusion : ∀ r : ℤ, high r ⟶ 𝟭 _
  quotient : ∀ r : ℤ, 𝟭 _ ⟶ low r
  highComparison : ∀ (r : ℤ) (K : Complex A bounded),
    (high r).obj ((Q bounded).obj K) ≅ (Q bounded).obj (FiniteFiltered.high bounded K r)
  lowComparison : ∀ (r : ℤ) (K : Complex A bounded),
    (low r).obj ((Q bounded).obj K) ≅ (Q bounded).obj (FiniteFiltered.low bounded K r)
  inclusion_normalization : ∀ (r : ℤ) (K : Complex A bounded),
    (highComparison r K).hom ≫ (Q bounded).map (highι bounded K r) =
      (inclusion r).app ((Q bounded).obj K)
  quotient_normalization : ∀ (r : ℤ) (K : Complex A bounded),
    (quotient r).app ((Q bounded).obj K) ≫ (lowComparison r K).hom =
      (Q bounded).map (lowπ bounded K r)
  connecting : ∀ r : ℤ, low r ⟶ high r ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ)
  distinguished : ∀ (r : ℤ) (P : Derived (A := A) bounded),
    Triangle.mk ((inclusion r).app P) ((quotient r).app P) ((connecting r).app P) ∈
      distTriang (Derived (A := A) bounded)
  high_support : ∀ (r a : ℤ) (P : Derived (A := A) bounded), a < r →
    IsZero ((gr a).obj ((high r).obj P))
  low_support : ∀ (r a : ℤ) (P : Derived (A := A) bounded), r ≤ a →
    IsZero ((gr a).obj ((low r).obj P))
  unique_triangle : ∀ (r : ℤ) (P : Derived (A := A) bounded)
    (L R : Derived (A := A) bounded) (i : L ⟶ P) (p : P ⟶ R) (d : R ⟶ L⟦(1 : ℤ)⟧),
    Triangle.mk i p d ∈ distTriang (Derived (A := A) bounded) →
    (∀ a : ℤ, a < r → IsZero ((gr a).obj L)) →
    (∀ a : ℤ, r ≤ a → IsZero ((gr a).obj R)) →
    ∃! e : Triangle.mk ((inclusion r).app P) ((quotient r).app P)
        ((connecting r).app P) ≅ Triangle.mk i p d,
      e.hom.hom₂ = 𝟙 P
  gradeProjection : high 0 ⋙ omega ⟶ gr 0
  gradeProjection_normalization : ∀ K : Complex A bounded,
    gradeProjection.app ((Q bounded).obj K) ≫ (grComparison 0).hom.app K =
      omega.map (highComparison 0 K).hom ≫
        omegaComparison.hom.app (FiniteFiltered.high bounded K 0) ≫
          DerivedCategory.Q.map (K.obj.filtration.complexQuotientπ 0 1 (by omega))

attribute [instance] TruncationCalculus.omega_shift TruncationCalculus.omega_exact
  TruncationCalculus.high_shift TruncationCalculus.low_shift
  TruncationCalculus.high_exact TruncationCalculus.low_exact



variable [HasDerivedCategory.{(max u v) + 1} AddCommGrpCat.{max u v}]

/-- The global Hom part of the filtered calculus. Its comparisons are natural in both
variables. A bilimit bicone states the finite direct sum without choosing arbitrary
filtration bounds or an order on its support.
Source: Varshavsky, 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
structure GlobalHomCalculus [TriangulatedLocalization A true]
    [TriangulatedLocalization AddCommGrpCat.{max u v} false]
    (B : TruncationCalculus A true)
    (C : TruncationCalculus AddCommGrpCat.{max u v} false) where
  omegaBounded : Derived (A := A) true ⥤ BoundedDerived A
  omegaBoundedComparison : omegaBounded ⋙ ObjectProperty.ι _ ≅ B.omega
  grBounded : ℤ → Derived (A := A) true ⥤ BoundedDerived A
  grBoundedComparison : ∀ a : ℤ, grBounded a ⋙ ObjectProperty.ι _ ≅ B.gr a
  ordinaryHom : (BoundedDerived A)ᵒᵖ ⥤ BoundedDerived A ⥤
    DerivedCategory AddCommGrpCat.{max u v}
  cohomology : ∀ (P Q : BoundedDerived A) (n : ℤ),
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).obj
      ((ordinaryHom.obj (op P)).obj Q)) ≃+ (P.obj ⟶ Q.obj⟦n⟧)
  cohomology_source : ∀ (P P' Q : BoundedDerived A) (f : P' ⟶ P) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).obj
      ((ordinaryHom.obj (op P)).obj Q)),
    cohomology P' Q n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).map
        ((ordinaryHom.map f.op).app Q) x) = f.hom ≫ cohomology P Q n x
  cohomology_target : ∀ (P Q Q' : BoundedDerived A) (f : Q ⟶ Q') (n : ℤ)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).obj
      ((ordinaryHom.obj (op P)).obj Q)),
    cohomology P Q' n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).map
        ((ordinaryHom.obj (op P)).map f) x) =
      cohomology P Q n x ≫ f.hom⟦n⟧'
  ordinary_model : ∀ (P Q : BoundedDerived A) (K I : CochainComplex A ℤ),
    DegreeBound A true K → DegreeBound A false I → (∀ n : ℤ, Injective (I.X n)) →
    Nonempty (DerivedCategory.Q.obj K ≅ P.obj) →
    Nonempty (DerivedCategory.Q.obj I ≅ Q.obj) →
    Nonempty ((ordinaryHom.obj (op P)).obj Q ≅ DerivedCategory.Q.obj
      ((AddCommGrpCat.uliftFunctor.{u, v}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomComplex K I)))
  filteredHom : (Derived (A := A) true)ᵒᵖ ⥤ Derived (A := A) true ⥤
    Derived (A := AddCommGrpCat.{max u v}) false
  underlyingComparison : ∀ P : Derived (A := A) true,
    filteredHom.obj (op P) ⋙ C.omega ≅
      omegaBounded ⋙ ordinaryHom.obj (op (omegaBounded.obj P))
  underlying_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    C.omega.map ((filteredHom.map f.op).app Q) ≫
        (underlyingComparison P').hom.app Q =
      (underlyingComparison P).hom.app Q ≫
        (ordinaryHom.map (omegaBounded.map f).op).app (omegaBounded.obj Q)
  gradedSum : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    Bicone (fun a : ℤ =>
      (ordinaryHom.obj (op ((grBounded a).obj P))).obj ((grBounded (a + r)).obj Q))
  gradedSum_isBilimit : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (gradedSum r P Q).IsBilimit
  finite_support : ∀ (r : ℤ) (P Q : Derived (A := A) true), ∃ S : Finset ℤ,
    ∀ a : ℤ, a ∉ S →
      IsZero ((ordinaryHom.obj (op ((grBounded a).obj P))).obj ((grBounded (a + r)).obj Q))
  gradedComparison : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (C.gr r).obj ((filteredHom.obj (op P)).obj Q) ≅ (gradedSum r P Q).pt
  graded_source : ∀ (r a : ℤ) (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    (C.gr r).map ((filteredHom.map f.op).app Q) ≫
        (gradedComparison r P' Q).hom ≫ (gradedSum r P' Q).π a =
      (gradedComparison r P Q).hom ≫ (gradedSum r P Q).π a ≫
        (ordinaryHom.map ((grBounded a).map f).op).app ((grBounded (a + r)).obj Q)
  graded_target : ∀ (r a : ℤ) (P Q Q' : Derived (A := A) true) (f : Q ⟶ Q'),
    (C.gr r).map ((filteredHom.obj (op P)).map f) ≫
        (gradedComparison r P Q').hom ≫ (gradedSum r P Q').π a =
      (gradedComparison r P Q).hom ≫ (gradedSum r P Q).π a ≫
        (ordinaryHom.obj (op ((grBounded a).obj P))).map ((grBounded (a + r)).map f)
  homEquiv : ∀ P Q : Derived (A := A) true,
    (P ⟶ Q) ≃+ (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).obj
      (C.omega.obj ((C.high 0).obj ((filteredHom.obj (op P)).obj Q)))
  homEquiv_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P) (g : P ⟶ Q),
    homEquiv P' Q (f ≫ g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).map
        (C.omega.map ((C.high 0).map ((filteredHom.map f.op).app Q))) (homEquiv P Q g)
  homEquiv_target : ∀ (P Q Q' : Derived (A := A) true) (f : Q ⟶ Q') (g : P ⟶ Q),
    homEquiv P Q' (g ≫ f) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).map
        (C.omega.map ((C.high 0).map ((filteredHom.obj (op P)).map f))) (homEquiv P Q g)
  forgetful_map : ∀ (P Q : Derived (A := A) true) (f : P ⟶ Q),
    cohomology (omegaBounded.obj P) (omegaBounded.obj Q) 0
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).map
        (C.omega.map ((C.inclusion 0).app ((filteredHom.obj (op P)).obj Q)) ≫
          (underlyingComparison P).hom.app Q) (homEquiv P Q f)) ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app (omegaBounded.obj Q).obj =
        omegaBoundedComparison.hom.app P ≫ B.omega.map f ≫
          omegaBoundedComparison.inv.app Q
  graded_projection : ∀ (a : ℤ) (P Q : Derived (A := A) true) (f : P ⟶ Q),
    cohomology ((grBounded a).obj P) ((grBounded a).obj Q) 0
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 0).map
        (C.gradeProjection.app ((filteredHom.obj (op P)).obj Q) ≫
          (gradedComparison 0 P Q).hom ≫ (gradedSum 0 P Q).π a ≫
            (ordinaryHom.obj (op ((grBounded a).obj P))).map
              (eqToHom (congrArg (fun b : ℤ => (grBounded b).obj Q) (Int.add_zero a))))
        (homEquiv P Q f)) ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).hom.app ((grBounded a).obj Q).obj =
        (grBoundedComparison a).hom.app P ≫ (B.gr a).map f ≫
          (grBoundedComparison a).inv.app Q

/-- All three cone-normalized triangulations and the bounded/plus truncation and global
Hom calculi, kept as existential data until the theorem is proved.
Source: Varshavsky, §§5.1.2 and 5.1.5
(blueprint: lem-trf-filtered-derived-hom-calculus). -/
structure DerivedHomCalculus where
  boundedModel : TriangulatedLocalization A true
  plusModel : TriangulatedLocalization A false
  abelianPlusModel : TriangulatedLocalization AddCommGrpCat.{max u v} false
  bounded : @TruncationCalculus A _ _ _ true boundedModel
  plus : @TruncationCalculus A _ _ _ false plusModel
  abelianPlus : @TruncationCalculus AddCommGrpCat.{max u v} _ _ _ false abelianPlusModel
  globalHom : @GlobalHomCalculus A _ _ _ _ boundedModel abelianPlusModel bounded abelianPlus

/-- Filtered derived Hom, truncation triangles, their unique functoriality, and the
canonical forgetful and graded projection maps.
Source: Varshavsky, §§5.1.2(a)–(c), 5.1.5 and Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-derived-hom-calculus).

Proof:
1. Filtered homotopies become equal in the localization: the filtered cylinder projection
is a graded quasi-isomorphism, so the two inclusions become equal. This identifies the
localizations of complexes and of their filtered homotopy category, using
lem-weil-pbc-localization-universal-property.
2. Use lem-trf-filtered-localization-injective-model and the fully faithful exact embedding
lem-trf-bounded-filtered-localization-embedding. Truncations, grades and forgetting commute
with shifts and cones on the injective model; they descend by the localization universal
property and preserve bounded inputs.
3. A finite filtered injective is a split flag of ordinary injectives, by downward splitting.
The cone-to-quotient map for the inclusion of a filtration step is a graded quasi-isomorphism.
This gives the actual inclusion/quotient distinguished triangle. For high L and low R every
filtered chain map L to R[q] vanishes. Thus all such derived Hom groups vanish. Apply
lem-weil-pbc-triangle-morphism-extension to obtain the unique comparison fixing the middle
object; reversing the comparison proves it is an isomorphism. Naturality follows from the
actual inclusion and quotient transformations.
4. For bounded P and a filtered injective resolution Q to I, take HomComplex P I with
F^r consisting of cochains carrying F^a P into F^{a+r} I for every a. The differential
preserves these subgroups. If P has grades [a,b] and I has grades [c,e], its filtration is
whole in degree c-b and zero in degree e-a+1. If P vanishes above v and I below w, its
cochain degrees vanish below w-v. The underlying Hom complex computes ordinary global
RHom: bounded-below injective complexes are K-injective, by
lem-weil-pbc-dplus-injective-representative and lem-weil-pbc-kinjective-hom-derived.
5. The canonical graded-cochain map has kernel F^{r+1}. For surjectivity split the target
flag, extend each map gr^a P to the appropriate injective target summand across
P/F^{a+1} P, and sum the finitely many extensions. It commutes with the Hom differential.
Consequently gr^r Hom is the direct sum of Hom(gr^a P,gr^{a+r} I), with the stated sign
of the filtration index. The splittings prove surjectivity only; the comparison is canonical.
6. Source homotopies induce S(f)=(-1)^n f h and target homotopies induce T(f)=k f.
They preserve filtration and satisfy dS+Sd=s*-t* and dT+Td=u*-v*. K-injectivity on every
grade inverts source quasi-isomorphisms; the injective-model equivalence supplies target
comparisons. Descend one variable at a time, obtaining a bifunctor and natural comparisons
independent of representatives. Its output is bounded below with uniformly finite filtration.
7. Degree-zero cycles of F^0 Hom are filtered chain maps; its boundaries are filtered
null-homotopies. The model theorem and bounded embedding give the natural Hom/H^0
isomorphism. Inclusion F^0 Hom into Hom forgets precisely the filtration condition, giving
the specified forgetful map. The quotient F^0 Hom to gr^0 Hom sends the same chain map to
its actual associated graded maps; inverting gr^a(Q to I) gives every stated projection
component gr^a P to gr^a Q. The truncation arguments apply
also to bounded-below complexes, without claiming bounded-below Hom for arbitrary plus
inputs. No finite injective dimension is assumed. -/
theorem filteredDerivedHomCalculus [EnoughInjectives A] :
    Nonempty (DerivedHomCalculus A) := by
  sorry

end CochainComplex.FiniteFiltered
