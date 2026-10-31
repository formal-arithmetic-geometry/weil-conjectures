/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement

import WeilConjectures.CategoryTheory.MonoidalCyclicFlatCore
import WeilConjectures.CategoryTheory.MonoidalCyclicFlatResolutionData
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.RightFractionDenseSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Monoidal cyclic fixed pairs and flat resolutions

Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, step (2), auxiliary
fixed-pair generalization; Stacks Project, `sites-cohomology.tex`, lemma-K-flat-resolution
(blueprint: lem-pur-monoidal-cyclic-flat-resolutions).

The structure below packages the compatible structures and all the conclusions of the
existence theorem. It does not choose any of them from an unproved existence assertion.
The fixed pairs, integer powers, induction and counit are the existing upstream constructions.

## Main declarations

* `flatTermKFlatHomotopyObjects`: the full homotopy subcategory in the localization clause.
* `MonoidalCyclicFlatResolutions`: the compatible data and assertions of the conclusion.
* `monoidalCyclicFlatResolutions`: existence under the stated functorial flat-cover hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- The full homotopy subcategory represented by flat-term K-flat complexes.
Source: latest blueprint, auxiliary fixed-pair resolution input, localization clause
(blueprint: lem-pur-monoidal-cyclic-flat-resolutions).
Taking the essential image makes the full subcategory independent of the choice of a
representative of an object of the homotopy category. -/
def flatTermKFlatHomotopyObjects
    (C : Type u) [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCountableCoproducts C] :
    ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  fun K ↦ ∃ P : CochainComplex C ℤ,
    P.IsKFlatForTotalTensor ∧ (∀ n : ℤ, ObjectProperty.flat (P.X n)) ∧
      Nonempty ((HomotopyCategory.quotient C (.up ℤ)).obj P ≅ K)


private theorem flatTermKFlat_localization
    (C : Type u) [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCountableCoproducts C] [HasDerivedCategory.{w} C]
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (s : P ⟶ K),
        QuasiIso s ∧ P.IsKFlatForTotalTensor ∧ ∀ n : ℤ, ObjectProperty.flat (P.X n)) :
    ((flatTermKFlatHomotopyObjects C).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage
        (flatTermKFlatHomotopyObjects C).ι) := by
  let F := flatTermKFlatHomotopyObjects C
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have hF : ∀ X : HomotopyCategory C (.up ℤ),
      ∃ (Y : F.FullSubcategory) (s : F.ι.obj Y ⟶ X), W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hs, hP, hflat⟩ := hres K
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj P,
      P, hP, hflat, ⟨Iso.refl _⟩⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  obtain ⟨_, G, hG, ⟨e⟩⟩ := rightFractionDenseSubcategory W inferInstance F hF
    DerivedCategory.Qh (W.inverseImage F.ι).Q
  letI := hG
  exact Functor.IsLocalization.of_equivalence_target _ _ _ G.asEquivalence e

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  (T : A ⥤ A) [T.Additive] [T.IsEquivalence] [T.Braided]
  (B : A ⥤ A) (b : B ⟶ 𝟭 A)

/-- All compatible structures and conclusions of the cyclic flat-resolution theorem.
Source: latest blueprint, step (2), auxiliary resolving-category input, and Stacks Project,
`sites-cohomology.tex`, lemma-K-flat-resolution
(blueprint: lem-pur-monoidal-cyclic-flat-resolutions).
The tensor and unit are specified as actual fixed pairs. The internal-Hom comparison is
normalized by evaluation and its structure map by the strong-monoidal comparison and
conjugation. The induction functor and counit are `Free.functor` and `Free.adjunction`.
The localization clause is stated for every model `HasDerivedCategory.{w}` of the ordinary
derived category: the inclusion followed by `DerivedCategory.Qh` is itself a localization functor,
so the localized full subcategory is equivalent to `D(W)` through the induced functor.
All instance fields are conclusions, not assumptions on the fixed-pair category. -/
structure MonoidalCyclicFlatResolutions where
  /-- The diagonal monoidal structure. -/
  [monoidal : MonoidalCategory (IsoAlgebra T)]
  /-- Its tensor is additive in each variable. -/
  [monoidalPreadditive : MonoidalPreadditive (IsoAlgebra T)]
  /-- Its symmetry is inherited from the underlying category. -/
  [symmetric : SymmetricCategory (IsoAlgebra T)]
  /-- Its tensor has internal right adjoints. -/
  [closed : MonoidalClosed (IsoAlgebra T)]
  /-- The forgetful functor is strong symmetric monoidal. -/
  [forgetBraided : (forget T).Braided]
  /-- The fixed-pair category is Grothendieck in the chosen universe. -/
  [grothendieck : IsGrothendieckAbelian.{w} (IsoAlgebra T)]
  /-- Countable sums used by the underlying total tensor. -/
  [countableUnderlying : HasCountableCoproducts A]
  /-- Countable sums used by the fixed-pair total tensor. -/
  [countableFixed : HasCountableCoproducts (IsoAlgebra T)]
  /-- The tensor fixed pair with the diagonal structure isomorphism. -/
  tensor_object (M N : IsoAlgebra T) :
    M ⊗ N = mk (M.carrier ⊗ N.carrier)
      ((Functor.Monoidal.μIso T M.carrier N.carrier).symm ≪≫
        tensorIso M.str N.str)
  /-- The monoidal unit with the inverse unit comparison of T. -/
  unit_object : 𝟙_ (IsoAlgebra T) = mk (𝟙_ A) (Functor.Monoidal.εIso T).symm
  /-- The forgetful tensor comparison is the identity on the specified carriers. -/
  forget_tensor (M N : IsoAlgebra T) :
    (Functor.Monoidal.μIso (forget T) M N).hom =
      eqToHom (congrArg carrier (tensor_object M N)).symm
  /-- The forgetful unit comparison is the identity on the specified carrier. -/
  forget_unit : (Functor.Monoidal.εIso (forget T)).hom =
    eqToHom (congrArg carrier unit_object).symm
  /-- Forgetting preserves finite limits. -/
  forget_leftExact : PreservesFiniteLimits (forget T)
  /-- Forgetting preserves finite colimits. -/
  forget_rightExact : PreservesFiniteColimits (forget T)
  /-- Forgetting detects isomorphisms. -/
  forget_conservative : (forget T).ReflectsIsomorphisms
  /-- All small limits are created by forgetting. -/
  forget_createsLimits : CreatesLimitsOfSize.{w, w} (forget T)
  /-- All small colimits are created by forgetting. -/
  forget_createsColimits : CreatesColimitsOfSize.{w, w} (forget T)
  /-- Internal Hom on carriers, including its canonical evaluation and twisted structure. -/
  internalHom (M N : IsoAlgebra T) :
    ∃ (h : ((ihom M).obj N).carrier ≅ (ihom M.carrier).obj N.carrier)
      (γ : T.obj ((ihom M.carrier).obj N.carrier) ≅
        (ihom (T.obj M.carrier)).obj (T.obj N.carrier)),
      γ.hom = MonoidalClosed.curry
        ((Functor.Monoidal.μIso T M.carrier ((ihom M.carrier).obj N.carrier)).hom ≫
          T.map ((ihom.ev M.carrier).app N.carrier)) ∧
      T.map h.hom ≫ γ.hom ≫ MonoidalClosed.curry
        ((M.str.inv ▷ (ihom (T.obj M.carrier)).obj (T.obj N.carrier)) ≫
          (ihom.ev (T.obj M.carrier)).app (T.obj N.carrier) ≫ N.str.hom) =
        ((ihom M).obj N).str.hom ≫ h.hom ∧
      (Functor.Monoidal.μIso (forget T) M ((ihom M).obj N)).hom ≫
        (forget T).map ((ihom.ev M).app N) =
          (M.carrier ◁ h.hom) ≫ (ihom.ev M.carrier).app N.carrier
  /-- Cyclic induction is left exact. -/
  induction_leftExact : PreservesFiniteLimits (Free.functor T)
  /-- Cyclic induction is right exact. -/
  induction_rightExact : PreservesFiniteColimits (Free.functor T)
  /-- Its adjunction is the existing degree-zero induction adjunction. -/
  induction_adjunction : Nonempty (Free.functor T ⊣ forget T)
  /-- The carrier of induction is the coproduct of the coherent integer powers. -/
  induction_carrier (N : A) : ((Free.functor T).obj N).carrier = ∐ (Free.obj T N)
  /-- Its structure reindexes the integer powers by the successor map. -/
  induction_structure (N : A) (j : ℤ) :
    T.map (Sigma.ι (Free.obj T N) j) ≫ ((Free.functor T).obj N).str.hom =
      (Free.objSucc T N j).hom ≫ Sigma.ι (Free.obj T N) (j + 1)
  /-- Induction of the given flat cover has flat values. -/
  flat_cover (M : IsoAlgebra T) :
    ObjectProperty.flat ((Free.functor T).obj (B.obj M.carrier))
  /-- The specified natural composite is epic at each fixed pair. -/
  cover_epi (M : IsoAlgebra T) :
    Epi ((Free.functor T).map (b.app M.carrier) ≫ (Free.adjunction T).counit.app M)
  /-- Flatness is detected and preserved on carriers. -/
  flat_iff (M : IsoAlgebra T) : ObjectProperty.flat M ↔ ObjectProperty.flat M.carrier
  /-- K-flatness is detected and preserved by the termwise forgetful functor. -/
  kflat_iff (P : CochainComplex (IsoAlgebra T) ℤ) :
    P.IsKFlatForTotalTensor ↔
      CochainComplex.IsKFlatForTotalTensor
        (((forget T).mapHomologicalComplex (.up ℤ)).obj P)
  /-- The acyclic tensor test agrees with the two-sided quasi-isomorphism test. -/
  kflat_acyclic_iff (P : CochainComplex (IsoAlgebra T) ℤ) :
    P.IsKFlatForTotalTensor ↔
      ∀ Q : CochainComplex (IsoAlgebra T) ℤ, Q.Acyclic →
        (HomologicalComplex.tensorObj P Q).Acyclic ∧
          (HomologicalComplex.tensorObj Q P).Acyclic
  /-- Every unbounded complex receives a quasi-isomorphism from flat-term K-flat data. -/
  resolution (K : CochainComplex (IsoAlgebra T) ℤ) :
    ∃ (P : CochainComplex (IsoAlgebra T) ℤ) (s : P ⟶ K),
      QuasiIso s ∧ P.IsKFlatForTotalTensor ∧ ∀ n : ℤ, ObjectProperty.flat (P.X n)
  /-- The ordinary derived category exists with morphisms in the chosen universe. -/
  derived_exists : Nonempty (HasDerivedCategory.{w} (IsoAlgebra T))
  /-- For every model of the ordinary derived category with morphisms in the chosen universe,
  the inclusion of the full homotopy subcategory followed by `DerivedCategory.Qh` is a
  localization at the quasi-isomorphisms between its objects. -/
  localization [HasDerivedCategory.{w} (IsoAlgebra T)] :
    ((flatTermKFlatHomotopyObjects (IsoAlgebra T)).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso (IsoAlgebra T) (.up ℤ)).inverseImage
        (flatTermKFlatHomotopyObjects (IsoAlgebra T)).ι)

/-- Closed monoidal cyclic fixed pairs admit the stated canonical flat resolutions.
Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, step (2), auxiliary
resolving-category generalization; Stacks Project, `sites-cohomology.tex`,
lemma-K-flat-resolution (blueprint: lem-pur-monoidal-cyclic-flat-resolutions).

Proof:
1. `monoidalCyclicFlatCore` (blueprint: lem-pur-monoidal-cyclic-flat-core) supplies the
diagonal closed symmetric monoidal Grothendieck structure, exact cyclic induction, the flat
cover and the flat/K-flat detection clauses; install its tensor and countable sums.
2. `monoidalCyclicFlatResolutionData` (blueprint: lem-pur-monoidal-cyclic-flat-resolution-data)
gives, for the same core, a flat-term K-flat quasi-isomorphism onto every complex.
3. The Grothendieck fixed-pair category has K-injective resolutions, so a derived category
with morphisms in universe `w` exists.
4. For any such model, every homotopy object is the class of a complex `K`; its replacement
`P → K` is a quasi-isomorphism from an object of the full subcategory, so that subcategory is
right-fraction dense. Quasi-isomorphisms have a right calculus of fractions
(`lem-pc-quasi-isomorphisms-multiplicative-system`), so
`lem-trf-right-fraction-dense-subcategory` makes the restricted localization equivalent to
`D(W)` compatibly with `Qh`; hence the inclusion followed by `Qh` is a localization.
5. Assemble the bundle from the core, the replacements and steps 3-4. -/
theorem monoidalCyclicFlatResolutions
    (hb_epi : ∀ M : A, Epi (b.app M))
    (hb_flat : ∀ M : A, ObjectProperty.flat (B.obj M)) :
    Nonempty (MonoidalCyclicFlatResolutions.{u, v, w} T B b) := by
  obtain ⟨c⟩ := monoidalCyclicFlatCore T B b hb_epi hb_flat
  letI := c.monoidal
  letI := c.monoidalPreadditive
  letI := c.countableFixed
  letI : IsGrothendieckAbelian.{w} (IsoAlgebra T) := c.grothendieck
  obtain ⟨r⟩ := monoidalCyclicFlatResolutionData.{u, v, w} T B b c
  exact ⟨{
    monoidal := c.monoidal
    monoidalPreadditive := c.monoidalPreadditive
    symmetric := c.symmetric
    closed := c.closed
    forgetBraided := c.forgetBraided
    grothendieck := c.grothendieck
    countableUnderlying := c.countableUnderlying
    countableFixed := c.countableFixed
    tensor_object := c.tensor_object
    unit_object := c.unit_object
    forget_tensor := c.forget_tensor
    forget_unit := c.forget_unit
    forget_leftExact := c.forget_leftExact
    forget_rightExact := c.forget_rightExact
    forget_conservative := c.forget_conservative
    forget_createsLimits := c.forget_createsLimits
    forget_createsColimits := c.forget_createsColimits
    internalHom := c.internalHom
    induction_leftExact := c.induction_leftExact
    induction_rightExact := c.induction_rightExact
    induction_adjunction := c.induction_adjunction
    induction_carrier := c.induction_carrier
    induction_structure := c.induction_structure
    flat_cover := c.flat_cover
    cover_epi := c.cover_epi
    flat_iff := c.flat_iff
    kflat_iff := c.kflat_iff
    kflat_acyclic_iff := c.kflat_acyclic_iff
    resolution := r.resolution
    derived_exists := ⟨HasDerivedCategory.ofHasKInjectiveResolutions (IsoAlgebra T)⟩
    localization := by
      intro hD
      letI := hD
      exact flatTermKFlat_localization (IsoAlgebra T) r.resolution }⟩

end CategoryTheory.Endofunctor.IsoAlgebra
