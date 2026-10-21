/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.RationalStratumIntegralModels
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.PbcUniformCompleteTriangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Finite integral cone models for rational realization

Source: Bhatt--Scholze, Proposition 6.8.14(2), pp. 61--62, expanded using
Lemma 6.8.13 and Stacks Tags 0145, 014A, 0152, 08J5
(blueprint: lem-per-rational-realization-finite-cone-models).

The finite lists below use only zero, the supplied integral quotient models, shifts,
and distinguished cones. No closure under retracts is included. Full faithfulness and
filtration models are assumptions throughout the essential-surjectivity construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme.RationalConeModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The existing compatible completed integral category, with unchanged morphisms.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models). -/
abbrev Integral := PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)

/-- The existing continuous rational module category, in the coefficient universe of the site.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models). -/
abbrev Modules := pbcModules X (rationalCoefficientSheaf l X E)

/-- The existing ambient derived category of rational module sheaves.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models). -/
abbrev Ambient := DerivedCategory (Modules l E X)

/-- The prescribed realization on integral objects and arrows, through the raw Q.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models). -/
abbrev realize (s : RationalModuleRealization l E X) :=
  pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ s.J

/-- The given integer-shift comparison of J, exposed without choosing a new comparison.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models). -/
instance realizationShift (s : RationalModuleRealization l E X) : s.J.CommShift ℤ := s.shift

/-- A finite integral construction. Every entry is zero, a supplied generator up to shift
and isomorphism, or a shifted distinguished cone between strictly earlier entries.
Source: the finite-filtration and truncation expansion of BS 6.8.14(2)
(blueprint: lem-per-rational-realization-finite-cone-models). -/
def FiniteConstruction (G : Integral l E X → Prop) (K : Integral l E X) : Prop :=
  ∃ (n : ℕ) (W : Fin (n + 1) → Integral l E X), W (Fin.last n) = K ∧
    ∀ r : Fin (n + 1), IsZero (W r).obj ∨
      (∃ (L : Integral l E X) (j : ℤ), G L ∧ Nonempty ((W r).obj ≅ L.obj⟦j⟧)) ∨
      (∃ (i j : Fin (n + 1)), i < r ∧ j < r ∧
        ∃ (k : ℤ) (f : (W i).obj ⟶ (W j).obj)
          (g : (W j).obj ⟶ (W r).obj⟦k⟧)
          (h : (W r).obj⟦k⟧ ⟶ (W i).obj⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang (PbcCompletedDerived X (pbcIntegralDatum l E)))

/-- A supplied finite sheaf filtration together with its integral degree-zero quotient models.
The stratum-model theorem supplies these data after its normalized scalar comparisons;
the filtration is retained rather than replaced by a mere assertion of essential image.
Source: BS 6.8.13 and 6.8.14(2)
(blueprint: lem-per-rational-realization-finite-cone-models). -/
structure Filtration (s : RationalModuleRealization l E X) (F : Modules l E X) where
  /-- Length, including zero. -/
  length : ℕ
  /-- Its module sheaves. -/
  H : Fin (length + 1) → Modules l E X
  /-- Inclusions into F. -/
  inclusion : ∀ k, H k ⟶ F
  /-- Consecutive inclusion maps. -/
  step : ∀ k : Fin length, H k.castSucc ⟶ H k.succ
  /-- Every term is a subobject. -/
  mono : ∀ k, Mono (inclusion k)
  /-- The initial term is zero. -/
  start : IsZero (H 0)
  /-- The final subobject is F. -/
  finish : IsIso (inclusion (Fin.last length))
  /-- The consecutive maps preserve the inclusions. -/
  commutes : ∀ k, step k ≫ inclusion k.succ = inclusion k.castSucc
  /-- Successive steps are monomorphisms. -/
  step_mono : ∀ k, Mono (step k)
  /-- The supplied integral quotient objects, including their compatible etale origins. -/
  model : Fin length → Integral l E X
  /-- Each is placed in degree zero integrally. -/
  degreeZero : ∀ k, ∃ M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)),
    Nonempty ((model k).obj ≅ (DerivedCategory.singleFunctor _ 0).obj M)
  /-- The supplied rational quotient identifications. -/
  quotient : ∀ k, (realize l E X s).obj (model k) ≅
    (DerivedCategory.singleFunctor (Modules l E X) 0).obj (cokernel (step k))

/-- Zero, shifts, and distinguished extensions belong to the isomorphism-closed image.
Source: BS 6.8.14(2) (blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 1 uses lem-weil-pbc-uniform-complete-triangulated and the exact realization
of lem-per-rational-module-realization-functor. For an extension lift its connecting
arrow by the assumed full faithfulness, clear its finite denominators in the raw
Hom tensor product, and take the integral cone. Rotate twice; TR3 compares its image
to the original triangle using 1 and the invertible uniformizer power. Stacks 014A
makes the third map invertible. Conjugate by endpoint isomorphisms (steps 2--4). -/
theorem image_closed (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful) :
    s.J.essImage.IsClosedUnderIsomorphisms ∧ s.J.essImage.ContainsZero ∧
      s.J.essImage.IsStableUnderShift ℤ ∧ s.J.essImage.IsTriangulatedClosed₂ := by
  sorry

/-- The unique lifted extension arrow has an integral fraction representative. The
integral cone and its negative shift realize the middle vertex. The triangle morphism
records the rescaling square explicitly; only the lifted arrow is unique.
Source: BS 6.8.14(2); Stacks 0145, 014A
(blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 2 identifies Hom in the raw rationalization with Hom tensor A[1/varpi].
A finite sum has a common nonnegative denominator. Full faithfulness supplies the
unique lift; the fraction formula supplies the scalar equation. Step 3 takes an
integral TR1 cone and shifts it by -1, retaining the completed-category membership.
Step 4 rotates the input triangle twice, with signs -i[1] and -p[1], and compares
it to the image cone using 1 and varpi^n. Both are invertible, so TR3 and Stacks
014A supply an invertible third map. Shifting back gives the claimed model. -/
theorem extension_cone (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (K₁ K₂ : Integral l E X) (C : Ambient l E X)
    (i : (realize l E X s).obj K₁ ⟶ C)
    (p : C ⟶ (realize l E X s).obj K₂)
    (δ : (realize l E X s).obj K₂ ⟶ ((realize l E X s).obj K₁)⟦(1 : ℤ)⟧)
    (_dist : Triangle.mk i p δ ∈ distTriang (Ambient l E X)) :
    ∃! α : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K₂ ⟶
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
          (K₁⟦(1 : ℤ)⟧),
      s.J.map α ≫ ((realize l E X s).commShiftIso (1 : ℤ)).hom.app K₁ = δ ∧
      ∃ (n : ℕ) (f : K₂ ⟶ K₁⟦(1 : ℤ)⟧),
        α = ((pbcRationalCoefficientEquiv l E).symm
          (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f ∧
        ∃ (D K : Integral l E X) (g : K₁⟦(1 : ℤ)⟧ ⟶ D)
          (h : D ⟶ K₂⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
          Nonempty (K.obj ≅ D.obj⟦(-1 : ℤ)⟧) ∧
          Nonempty ((realize l E X s).obj K ≅ C) ∧
          ∃ (φ : (Triangle.mk i p δ).rotate.rotate ⟶
              (realize l E X s).mapTriangle.obj (Triangle.mk f g h)),
            φ.hom₁ = 𝟙 _ ∧
            φ.hom₂ =
              ((realize l E X s).commShiftIso (1 : ℤ)).inv.app K₁ ≫
                (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
                  s.J).map (pbcUniformizer l E ^ n • 𝟙 (K₁⟦(1 : ℤ)⟧)) ∧
            IsIso φ.hom₁ ∧ IsIso φ.hom₂ ∧ IsIso φ.hom₃ := by
  sorry

/-- Every supplied finite filtration is modeled by a finite integral construction using
exactly its supplied quotient models.
Source: BS 6.8.13 and 6.8.14(2); Stacks 0152
(blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 5 starts with the integral zero object. At k, the short exact sequence
of the filtration gives a distinguished degree-zero triangle by
lem-sf-derived-ses-triangle. Its endpoints are identified with the previous model
and the supplied quotient model. Steps 2--4 lift its connecting map, clear its
denominator and append a shifted integral cone. Induct through the finite length;
length zero is already the zero case. No summand extraction occurs. -/
theorem filtration_model (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (F : Modules l E X) (t : Filtration l E X s F) :
    ∃ K : Integral l E X,
      FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) K ∧
      Nonempty ((realize l E X s).obj K ≅
        (DerivedCategory.singleFunctor (Modules l E X) 0).obj F) ∧
      ∃ W : Fin (t.length + 1) → Integral l E X,
        IsZero (W 0).obj ∧
        (∀ j, Nonempty ((realize l E X s).obj (W j) ≅
          (DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j))) ∧
        Nonempty ((W (Fin.last t.length)).obj ≅ K.obj) ∧
        (∀ j, FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) (W j)) ∧
        ∀ j : Fin t.length,
          ∃ (f : t.model j ⟶ (W j.castSucc)⟦(1 : ℤ)⟧) (D : Integral l E X)
            (g : (W j.castSucc)⟦(1 : ℤ)⟧ ⟶ D)
            (h : D ⟶ (t.model j)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
            Nonempty ((W j.succ).obj ≅ D.obj⟦(-1 : ℤ)⟧) := by
  sorry

/-- Every constructible sheaf in degree zero has a finite integral cone model.
Source: BS 6.8.13 and 6.8.14(2); Stacks 0152
(blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 5 takes the supplied filtration and applies filtration_model. Its base is
zero, and each short exact filtration sequence contributes one lifted connecting
arrow and one shifted integral cone. The supplied integral models are already in
the actual compatible completed category; neither retracts nor extra lattices enter. -/
theorem sheaf_model (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (_models : ∀ F : Modules l E X,
      (∃ t : FiniteLocallyClosedStratification X, ∀ k : Fin t.n,
        ((proEtaleModuleInverseImage (t.immersion k)
          (rationalCoefficientSheaf l X E)).obj F).IsFiniteLocallyFree) →
        Nonempty (Filtration l E X s F))
    (F : Modules l E X)
    (_constructible : ∃ t : FiniteLocallyClosedStratification X, ∀ k : Fin t.n,
      ((proEtaleModuleInverseImage (t.immersion k)
        (rationalCoefficientSheaf l X E)).obj F).IsFiniteLocallyFree) :
    ∃ (t : Filtration l E X s F) (K : Integral l E X),
      FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) K ∧
      Nonempty ((realize l E X s).obj K ≅
        (DerivedCategory.singleFunctor (Modules l E X) 0).obj F) := by
  sorry

/-- Bounded constructible cohomology is realized by the finite standard truncation tower,
using only integral models of its finitely many filtration quotients and integral cones.
The supplied interval may contain zero cohomology groups, or even be empty.
Source: BS 6.8.14(2); Stacks 08J5
(blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 5 constructs the degree-zero cohomology models from their supplied
filtrations, using filtration_model. Step 6 identifies tau_le(a-1) with zero and
tau_le b with C by quasi-isomorphisms. For every r from a through b,
lem-weil-pbc-truncation-triangle supplies tau_le(r-1) C -> tau_le r C -> H^r(C)[-r].
Shift the sheaf model by -r, and apply extension_cone to lift the connecting arrow
and append a shifted integral cone. Induction gives the models at every stage,
including the last model of C (step 7). Concatenate the finitely many constructions.
When all cohomology vanishes, 0 -> C is a quasi-isomorphism and no cone is needed. -/
theorem bounded_model (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (_models : ∀ F : Modules l E X,
      (∃ t : FiniteLocallyClosedStratification X, ∀ k : Fin t.n,
        ((proEtaleModuleInverseImage (t.immersion k)
          (rationalCoefficientSheaf l X E)).obj F).IsFiniteLocallyFree) →
        Nonempty (Filtration l E X s F))
    (C : Ambient l E X) (a b : ℤ)
    (_bounded : ∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C))
    (_constructible : ∀ r : ℤ, ∃ t : FiniteLocallyClosedStratification X,
      ∀ k : Fin t.n, ((proEtaleModuleInverseImage (t.immersion k)
        (rationalCoefficientSheaf l X E)).obj
          ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C)).IsFiniteLocallyFree) :
    ∃ (t : ∀ r : Set.Icc a b, Filtration l E X s
        ((DerivedCategory.homologyFunctor (Modules l E X) r.val).obj C))
      (K : Integral l E X),
      FiniteConstruction l E X (fun L ↦ ∃ (r : Set.Icc a b) (k : Fin (t r).length),
        L = (t r).model k) K ∧
      Nonempty ((realize l E X s).obj K ≅ C) ∧
      ∃ (W : Fin ((b - a + 1).toNat + 1) → Integral l E X),
        IsZero (W 0).obj ∧
        (∀ j, Nonempty ((realize l E X s).obj (W j) ≅
          (DerivedCategory.TStructure.t.truncLE (a - 1 + (j.val : ℤ))).obj C)) ∧
        Nonempty ((W (Fin.last (b - a + 1).toNat)).obj ≅ K.obj) ∧
        (∀ j, FiniteConstruction l E X (fun L ↦
          ∃ (r : Set.Icc a b) (k : Fin (t r).length), L = (t r).model k) (W j)) ∧
        ∀ j : Fin (b - a + 1).toNat,
          ∃ (L D : Integral l E X)
            (f : L ⟶ (W j.castSucc)⟦(1 : ℤ)⟧)
            (g : (W j.castSucc)⟦(1 : ℤ)⟧ ⟶ D) (h : D ⟶ L⟦(1 : ℤ)⟧),
            FiniteConstruction l E X (fun M ↦
              ∃ (r : Set.Icc a b) (k : Fin (t r).length), M = (t r).model k) L ∧
            Nonempty ((realize l E X s).obj L ≅
              ((DerivedCategory.singleFunctor (Modules l E X) 0).obj
                ((DerivedCategory.homologyFunctor (Modules l E X)
                  (a + (j.val : ℤ))).obj C))⟦-(a + (j.val : ℤ))⟧) ∧
            Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
            Nonempty ((W j.succ).obj ≅ D.obj⟦(-1 : ℤ)⟧) := by
  sorry

/-- In the acyclic case the integral zero object itself is a model.
Source: BS 6.8.14(2); Stacks 05RU
(blueprint: lem-per-rational-realization-finite-cone-models).
Proof: step 6 applies cohomology detection to 0 -> C; it is a quasi-isomorphism.
The exact realization carries the integral zero object to zero (step 1), so their
unique zero-object isomorphisms give the comparison, without a truncation tower. -/
theorem acyclic_model (s : RationalModuleRealization l E X)
    (C : Ambient l E X)
    (_acyclic : ∀ r : ℤ, IsZero ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C)) :
    ∃ K : Integral l E X, IsZero K.obj ∧
      Nonempty ((realize l E X s).obj K ≅ C) := by
  sorry

end AlgebraicGeometry.Scheme.RationalConeModels
