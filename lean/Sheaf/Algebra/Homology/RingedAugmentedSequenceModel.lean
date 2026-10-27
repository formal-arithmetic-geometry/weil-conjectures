/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveReplacementTriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatMapFactorization
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.AcyclicKFlatTensor

/-! # Strict ringed-site sequence models and tensor telescopes

Source: Stacks Project, derived.tex, Tags 090Z, 0CRH, 0CRI;
sites-cohomology.tex, Tags 06YS, 0G7D, 06YM, 06YT.
(blueprint: lem-sfb-ringed-augmented-sequence-model)

The auxiliary constructions are the actual countable sum, its successor endomorphism,
and its mapping cone. The comparison is normalized by the published signed cone/tensor
isomorphism. A commuting coefficient action is a ring homomorphism into the ring of
O-linear chain endomorphisms; this includes every commuting B-action in the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w d b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.RingedSequenceModel

section Telescope

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasCountableCoproducts A]

/-- The countable sum of a strict sequence. Source: Stacks 090Z
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
abbrev sum (P : ℕ ⥤ A) : A := ∐ (fun n : ℕ ↦ P.obj n)

/-- The actual telescope endomorphism 1-s. Source: Stacks 090Z
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def differential (P : ℕ ⥤ A) : sum P ⟶ sum P :=
  𝟙 _ - Sigma.desc (fun n : ℕ ↦ P.map (homOfLE (Nat.le_succ n)) ≫
    Sigma.ι (fun k : ℕ ↦ P.obj k) (n + 1))

/-- A map of sums induced by a compatible strict sequence map. Source: Stacks 0CRI
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def sumMap {P P' : ℕ ⥤ A} (r : P ⟶ P') : sum P ⟶ sum P' :=
  Sigma.desc (fun n : ℕ ↦ r.app n ≫ Sigma.ι (fun k : ℕ ↦ P'.obj k) n)

/-- The sum map commutes with 1-s. Source: Stacks 0CRI
(blueprint: lem-sfb-ringed-augmented-sequence-model).
Proof: restrict to the n-th coprojection, distribute subtraction, and use the
naturality of r on n → n+1. Coproduct extensionality finishes. -/
theorem sumMap_comm {P P' : ℕ ⥤ A} (r : P ⟶ P') :
    differential P ≫ sumMap r = sumMap r ≫ differential P' := by
  sorry

end Telescope

section ComplexTelescope

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasCountableCoproducts (CochainComplex A ℤ)]

/-- The concrete cone telescope. Source: Stacks 090Z
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def telescope (P : ℕ ⥤ CochainComplex A ℤ) : CochainComplex A ℤ :=
  mappingCone (differential P)

/-- The unshifted telescope leg. Source: Stacks 0CRH
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def leg (P : ℕ ⥤ CochainComplex A ℤ) (n : ℕ) : P.obj n ⟶ telescope P :=
  Sigma.ι (fun k : ℕ ↦ P.obj k) n ≫ mappingCone.inr (differential P)

/-- The map of actual cones induced by a strict sequence map. Source: Stacks 0CRI
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def telescopeMap {P P' : ℕ ⥤ CochainComplex A ℤ} (r : P ⟶ P') :
    telescope P ⟶ telescope P' :=
  mappingCone.map _ _ (sumMap r) (sumMap r) (sumMap_comm r)

end ComplexTelescope

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{w})

/-- The existing module-sheaf category. Source: Stacks 03DA
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
abbrev Modules := ringedSiteModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O)

/-- Flat-term K-flat strict sequence models. Source: Stacks 06YS, 0G7D
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def Resolving (P : ℕ ⥤ CochainComplex (Modules O) ℤ) : Prop :=
  ∀ n : ℕ, (P.obj n).IsKFlatIndependentCoefficients ∧
    ∀ i : ℤ, IsFlatOnSite (J := J) (R := O) ((P.obj n).X i)

/-- Tensor a strict sequence only in its coefficient complex. Source: Stacks 06YM
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def tensorSequence (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    (L : CochainComplex (Modules O) ℤ) : ℕ ⥤ CochainComplex (Modules O) ℤ :=
  P ⋙ (totalTensor O).flip.obj L

/-- Tensor-compatible maps in the strict sequence variable. Source: Stacks 06YM
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def tensorSequenceMap {P P' : ℕ ⥤ CochainComplex (Modules O) ℤ} (r : P ⟶ P')
    (L : CochainComplex (Modules O) ℤ) : tensorSequence O P L ⟶ tensorSequence O P' L :=
  Functor.whiskerRight r ((totalTensor O).flip.obj L)

/-- The tensor of a coefficient chain map at every stage. Source: Stacks 06YM
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def coefficientMap (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    {L L' : CochainComplex (Modules O) ℤ} (h : L ⟶ L') :
    tensorSequence O P L ⟶ tensorSequence O P L' :=
  Functor.whiskerLeft P ((totalTensor O).flip.map h)

/-- The canonical coproduct/tensor comparison, with no choices. Source: Stacks 03EP
(blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def sumTensor (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    (L : CochainComplex (Modules O) ℤ) :
    sum (tensorSequence O P L) ⟶ ((totalTensor O).obj (sum P)).obj L :=
  Sigma.desc (fun n : ℕ ↦ ((totalTensor O).map (Sigma.ι (fun k : ℕ ↦ P.obj k) n)).app L)

/-- The canonical comparison intertwines the telescope endomorphisms. Source: Stacks 03EP
and 06YM (blueprint: lem-sfb-ringed-augmented-sequence-model).
Proof: on each coprojection both successor terms are p_n tensor 1 followed by
its (n+1)-st tensor coprojection; additivity handles the identity-minus-successor. -/
theorem sumTensor_comm (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    (L : CochainComplex (Modules O) ℤ) :
    differential (tensorSequence O P L) ≫ sumTensor O P L =
      sumTensor O P L ≫ (((totalTensor O).map (differential P)).app L) := by
  sorry

/-- The canonical two-copy comparison to the tensor of the telescope endomorphism.
Source: Stacks 03EP and 06YM (blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def tensorConeMap (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    (L : CochainComplex (Modules O) ℤ) :
    telescope (tensorSequence O P L) ⟶ mappingCone (((totalTensor O).map (differential P)).app L) :=
  mappingCone.map _ _ (sumTensor O P L) (sumTensor O P L) (sumTensor_comm O P L)

/-- The existing signed cone/tensor isomorphism, with the published total tensor.
Source: Stacks 06YM (blueprint: lem-sfb-ringed-augmented-sequence-model). -/
def coneTensorIso (P : ℕ ⥤ CochainComplex (Modules O) ℤ)
    (L : CochainComplex (Modules O) ℤ) :
    ((totalTensor O).obj (telescope P)).obj L ≅
      mappingCone (((totalTensor O).map (differential P)).app L) :=
  letI : (ordinaryTensor O).Additive := by
    unfold ordinaryTensor
    infer_instance
  letI : ∀ M : Modules O, ((ordinaryTensor O).obj M).Additive := by
    intro M
    unfold ordinaryTensor
    infer_instance
  letI : ∀ A B : CochainComplex (Modules O) ℤ,
      HasMapBifunctor A B (ordinaryTensor O) := by
    intro A B
    unfold ordinaryTensor
    infer_instance
  mapBifunctorMappingCone₁Iso (differential P) L (ordinaryTensor O)

variable [HasDerivedCategory.{d} (Modules O)]

/-- Strict flat-term K-flat representatives, normalized telescope comparisons, and their
natural tensor isomorphisms, including coefficient actions and quasi-isomorphism roofs.
Source: Stacks 090Z, 0CRH, 0CRI, 06YS, 0G7D, 06YM, 06YT
(blueprint: lem-sfb-ringed-augmented-sequence-model).

Proof:
1. Choose K-injective representatives and chain representatives of the successor maps
using prop-pur-kinjective-resolutions-exist and lem-sf-kinjective-replacement-triangulated.
2. Induct with lem-pc-kflat-resolution and lem-pur-kflat-map-factorization to obtain
flat-term K-flat P_n and the compatible derived identifications.
3. Apply lem-pc-kflat-cone-direct-sum to the sum and its cone; localize the coproduct
using lem-kun-complex-colimit-hocolim. TR3 and lem-sf-triangle-morphism-iso compare
this triangle to any supplied telescope triangle, including the connecting morphism.
4. Distribute total tensor over the sum using lem-weil-pbc-independent-sheaf-tensor-colimits.
5. Use the two-copy cone comparison: the shifted generator has coefficients
1, -1, (-1)^(a-1), equal to 1, -1, -(-1)^a. This is the published cone/tensor map.
6. On both copies the naturality squares send x tensor l to r(x) tensor h(l).
lem-weil-pbc-kflat-fixed-tensor-triangulated inverts coefficient quasi-isomorphisms.
7. Exact sums and src-weil-homology-preserves-exact-colimits invert objectwise model
quasi-isomorphisms. The comparison cone is acyclic and K-flat; use
lem-pur-quasi-iso-cone-acyclic and lem-pur-acyclic-kflat-tensor-arbitrary with the signed
flip. Naturality therefore extends by inverses to both kinds of roofs.
8. A commuting B-action acts only on L. The same formulas commute with each action
endomorphism and its inverse comparison, without using flatness of B over R. -/
theorem ringed_augmented_sequence_model
    (E : ℕ ⥤ DerivedCategory (Modules O)) :
    (∃ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (_hP : Resolving O P)
      (vP : P ⋙ DerivedCategory.Q ≅ E),
      (telescope P).IsKFlatIndependentCoefficients ∧
      Nonempty (IsColimit (DerivedCategory.Q.mapCocone
        (Cofan.mk (sum P) (fun n : ℕ ↦ Sigma.ι (fun k : ℕ ↦ P.obj k) n)))) ∧
      ∀ (B : Cofan (fun n : ℕ ↦ E.obj n)) (_hB : IsColimit B)
        (uE : B.pt ⟶ B.pt)
        (_huE : ∀ n : ℕ, B.inj n ≫ uE =
          B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
        (K : DerivedCategory (Modules O))
        (g : B.pt ⟶ K) (c : K ⟶ B.pt⟦(1 : ℤ)⟧),
        Triangle.mk uE g c ∈ distTriang _ →
        ∃ (a : DerivedCategory.Q.obj (sum P) ≅ B.pt)
          (z : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (differential P)) ≅
            Triangle.mk uE g c),
          z.hom.hom₁ = a.hom ∧ z.hom.hom₂ = a.hom ∧
          (∀ n : ℕ, DerivedCategory.Q.map (Sigma.ι (fun k : ℕ ↦ P.obj k) n) ≫ a.hom =
            (vP.app n).hom ≫ B.inj n) ∧
          (∀ n : ℕ, DerivedCategory.Q.map (leg P n) ≫ z.hom.hom₃ =
            (vP.app n).hom ≫ B.inj n ≫ g)) ∧
    (∃ Φ : ∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ), Resolving O P →
        ∀ L : CochainComplex (Modules O) ℤ,
          telescope (tensorSequence O P L) ≅ ((totalTensor O).obj (telescope P)).obj L,
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L : CochainComplex (Modules O) ℤ),
        (Φ P hP L).hom ≫
            (coneTensorIso O P L).hom =
          tensorConeMap O P L) ∧
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L : CochainComplex (Modules O) ℤ) (n : ℕ),
        leg (tensorSequence O P L) n ≫ (Φ P hP L).hom = ((totalTensor O).map (leg P n)).app L) ∧
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L L' : CochainComplex (Modules O) ℤ) (h : L ⟶ L'),
        telescopeMap (coefficientMap O P h) ≫ (Φ P hP L').hom =
          (Φ P hP L).hom ≫ (((totalTensor O).obj (telescope P)).map h)) ∧
      (∀ (P P' : ℕ ⥤ CochainComplex (Modules O) ℤ)
        (hP : Resolving O P) (hP' : Resolving O P') (r : P ⟶ P')
        (L : CochainComplex (Modules O) ℤ),
        telescopeMap (tensorSequenceMap O r L) ≫ (Φ P' hP' L).hom =
          (Φ P hP L).hom ≫ (((totalTensor O).map (telescopeMap r)).app L)) ∧
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L L' : CochainComplex (Modules O) ℤ) (h : L ⟶ L'), QuasiIso h →
        IsIso (DerivedCategory.Q.map (telescopeMap (coefficientMap O P h))) ∧
        IsIso (DerivedCategory.Q.map (((totalTensor O).obj (telescope P)).map h))) ∧
      (∀ (P P' : ℕ ⥤ CochainComplex (Modules O) ℤ)
        (hP : Resolving O P) (hP' : Resolving O P') (r : P ⟶ P'),
        (∀ n : ℕ, QuasiIso (r.app n)) →
        ∀ L : CochainComplex (Modules O) ℤ,
        IsIso (DerivedCategory.Q.map (telescopeMap (tensorSequenceMap O r L))) ∧
        IsIso (DerivedCategory.Q.map (((totalTensor O).map (telescopeMap r)).app L))) ∧
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L H L' : CochainComplex (Modules O) ℤ) (s : H ⟶ L) (f : H ⟶ L'),
        QuasiIso s →
        ∀ (i : DerivedCategory.Q.obj (telescope (tensorSequence O P L)) ⟶
            DerivedCategory.Q.obj (telescope (tensorSequence O P H)))
          (j : DerivedCategory.Q.obj (((totalTensor O).obj (telescope P)).obj L) ⟶
            DerivedCategory.Q.obj (((totalTensor O).obj (telescope P)).obj H)),
        i ≫ DerivedCategory.Q.map (telescopeMap (coefficientMap O P s)) = 𝟙 _ →
        j ≫ DerivedCategory.Q.map (((totalTensor O).obj (telescope P)).map s) = 𝟙 _ →
        i ≫ DerivedCategory.Q.map (telescopeMap (coefficientMap O P f)) ≫
            (DerivedCategory.Q.mapIso (Φ P hP L')).hom =
          (DerivedCategory.Q.mapIso (Φ P hP L)).hom ≫ j ≫
            DerivedCategory.Q.map (((totalTensor O).obj (telescope P)).map f)) ∧
      (∀ (P H P' : ℕ ⥤ CochainComplex (Modules O) ℤ)
        (hP : Resolving O P) (_hH : Resolving O H) (hP' : Resolving O P')
        (s : H ⟶ P) (f : H ⟶ P'), (∀ n : ℕ, QuasiIso (s.app n)) →
        ∀ (L : CochainComplex (Modules O) ℤ)
          (i : DerivedCategory.Q.obj (telescope (tensorSequence O P L)) ⟶
            DerivedCategory.Q.obj (telescope (tensorSequence O H L)))
          (j : DerivedCategory.Q.obj (((totalTensor O).obj (telescope P)).obj L) ⟶
            DerivedCategory.Q.obj (((totalTensor O).obj (telescope H)).obj L)),
        i ≫ DerivedCategory.Q.map (telescopeMap (tensorSequenceMap O s L)) = 𝟙 _ →
        j ≫ DerivedCategory.Q.map (((totalTensor O).map (telescopeMap s)).app L) = 𝟙 _ →
        i ≫ DerivedCategory.Q.map (telescopeMap (tensorSequenceMap O f L)) ≫
            (DerivedCategory.Q.mapIso (Φ P' hP' L)).hom =
          (DerivedCategory.Q.mapIso (Φ P hP L)).hom ≫ j ≫
            DerivedCategory.Q.map (((totalTensor O).map (telescopeMap f)).app L)) ∧
      (∀ (P : ℕ ⥤ CochainComplex (Modules O) ℤ) (hP : Resolving O P)
        (L : CochainComplex (Modules O) ℤ) (B : Type b) [CommRing B]
        (ρ : B →+* End L) (b : B),
        telescopeMap (coefficientMap O P (ρ b)) ≫ (Φ P hP L).hom =
          (Φ P hP L).hom ≫ (((totalTensor O).obj (telescope P)).map (ρ b)))) := by
  sorry

end SheafOfModules.RingedSequenceModel
