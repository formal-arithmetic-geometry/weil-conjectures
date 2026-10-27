/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.CategoryTheory.DerivedCategory.KFlatTensorPresentation
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical Tor tests for exact adjoints

Source: blueprint main-20261015, `sec-six-functors/sk-lem-sf-open-ctf/`
`sk-prop-proper-image-localizing-open.proof.md`, finite Tor amplitude paragraph;
Stacks Tag 015F (blueprint: lem-sf-exact-adjoint-derived-tor-tests).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uA vA wA uB vB wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Adjunction

/-- Localize the degreewise adjunction with the standard exact-functor factorizations.
The units and counits are the localized degreewise units and counits.
Source: Stacks Tag 015F (blueprint: lem-sf-exact-adjoint-derived-tor-tests). -/
def exactDerivedOfUniverses
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {E : A ⥤ B} {R : B ⥤ A} [E.Additive] [R.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R) :
    E.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  letI : CatCommSq (E.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q E.mapDerivedCategory := ⟨E.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    E.mapDerivedCategory R.mapDerivedCategory

end CategoryTheory.Adjunction

namespace CategoryTheory.ExactAdjointTorTests

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [MonoidalCategory (DerivedCategory A)] [MonoidalCategory (DerivedCategory B)]
  {E : A ⥤ B} {R : B ⥤ A} [E.Additive] [R.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) {P : DerivedCategory B ⥤ DerivedCategory A}
  (α : P ≅ R.mapDerivedCategory) [P.Monoidal]

/-- The specified derived adjunction, transported along the exact comparison.
Source: blueprint finite Tor amplitude paragraph, Stacks 015F
(blueprint: lem-sf-exact-adjoint-derived-tor-tests). -/
def transportedAdjunction : E.mapDerivedCategory ⊣ P :=
  a.exactDerivedOfUniverses.ofNatIsoRight α.symm

/-- The canonical projection comparison, in the node's orientation.
Source: blueprint finite Tor amplitude paragraph
(blueprint: lem-sf-exact-adjoint-derived-tor-tests). -/
def projection (K : DerivedCategory A) (L : DerivedCategory B) :
    E.mapDerivedCategory.obj (K ⊗ P.obj L) ⟶ E.mapDerivedCategory.obj K ⊗ L :=
  E.mapDerivedCategory.map
      ((transportedAdjunction a α).unit.app K ▷ P.obj L) ≫
    E.mapDerivedCategory.map (Functor.LaxMonoidal.μ P (E.mapDerivedCategory.obj K) L) ≫
    (transportedAdjunction a α).counit.app (E.mapDerivedCategory.obj K ⊗ L)

/-- The specified Tor-test map: inverse projection, followed by the exact single comparison.
Source: blueprint finite Tor amplitude paragraph
(blueprint: lem-sf-exact-adjoint-derived-tor-tests). -/
def comparison [∀ (K : DerivedCategory A) (L : DerivedCategory B),
    IsIso (projection a α K L)] (K : DerivedCategory A) (N : B) :
    E.mapDerivedCategory.obj K ⊗ (DerivedCategory.singleFunctor B 0).obj N ⟶
      E.mapDerivedCategory.obj (K ⊗ (DerivedCategory.singleFunctor A 0).obj (R.obj N)) :=
  inv (projection a α K ((DerivedCategory.singleFunctor B 0).obj N)) ≫
    E.mapDerivedCategory.map (K ◁
      (α.hom.app ((DerivedCategory.singleFunctor B 0).obj N) ≫
        (R.mapDerivedCategorySingleFunctor 0).hom.app N))

/-- The specified comparison is invertible, natural in both inputs, and transfers every
all-heart-object Tor amplitude interval without a boundedness assumption.
Source: blueprint main-20261015, `sk-prop-proper-image-localizing-open.proof.md`,
finite Tor amplitude paragraph; Stacks Tag 015F
(blueprint: lem-sf-exact-adjoint-derived-tor-tests).

Proof plan:
1. Naturality of the transported unit, the monoidal tensorator and the transported
counit proves naturality of `projection` (def-weil-exact-derived-adjunction).
2. The degree-zero comparison `mapDerivedCategorySingleFunctor` is natural in N,
since it is termwise the identity on R(N) and the zero identification elsewhere
(lem-sf-exact-functor-derived-triangulated). Compose it with the supplied natural α.
3. Invert the natural projection comparisons and compose with E applied to tensoring
with this degree-zero comparison. The inverse is projection after E of tensoring with
the inverse degree-zero comparison. Cancellation proves invertibility; the two
naturality equations prove the displayed square for arbitrary derived f and heart g.
4. For each N and q outside [a,b], apply the assumed test to R(N). Exact-functor
cohomology comparison identifies H^q(E(T)) with E(H^q(T)) for the unbounded object
T = K tensor R(N)[0] (lem-weil-pbc-exact-functor-bounded-below). Additivity sends zero
to zero. Apply cohomology to the comparison isomorphism to obtain the desired
vanishing. The interval is unchanged, including the case a > b. -/
theorem exact_adjoint_derived_tor_tests
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [HasCountableCoproducts A]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [HasCountableCoproducts B]
    [SymmetricCategory (DerivedCategory A)] [SymmetricCategory (DerivedCategory B)]
    (_tensorA : DerivedCategory.KFlatTensorPresentation A)
    (_tensorB : DerivedCategory.KFlatTensorPresentation B)
    (c : DerivedCategory.Qh ⋙ P ⟶
      R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [P.IsLeftDerivedFunctor c (HomotopyCategory.quasiIso B (.up ℤ))]
    (_compatibility : Functor.whiskerLeft DerivedCategory.Qh α.hom ≫
      R.mapDerivedCategoryFactorsh.hom = c)
    [∀ (K : DerivedCategory A) (L : DerivedCategory B), IsIso (projection a α K L)] :
    (∀ (K : DerivedCategory A) (N : B), IsIso (comparison a α K N)) ∧
    (∀ (K K' : DerivedCategory A) (N N' : B) (f : K ⟶ K') (g : N ⟶ N'),
      (E.mapDerivedCategory.map f ⊗ₘ (DerivedCategory.singleFunctor B 0).map g) ≫
          comparison a α K' N' =
        comparison a α K N ≫ E.mapDerivedCategory.map
          (f ⊗ₘ (DerivedCategory.singleFunctor A 0).map (R.map g))) ∧
    (∀ (K : DerivedCategory A) (a b : ℤ),
      (∀ (M : A) (q : ℤ), q ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor A q).obj
          (K ⊗ (DerivedCategory.singleFunctor A 0).obj M))) →
      ∀ (N : B) (q : ℤ), q ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor B q).obj
          (E.mapDerivedCategory.obj K ⊗ (DerivedCategory.singleFunctor B 0).obj N))) := by
  have hproj (K K' : DerivedCategory A) (L L' : DerivedCategory B)
      (f : K ⟶ K') (g : L ⟶ L') :
      E.mapDerivedCategory.map (f ⊗ₘ P.map g) ≫ projection a α K' L' =
        projection a α K L ≫ (E.mapDerivedCategory.map f ⊗ₘ g) := by
    have hu : (f ⊗ₘ P.map g) ≫
        ((transportedAdjunction a α).unit.app K' ▷ P.obj L') =
        ((transportedAdjunction a α).unit.app K ▷ P.obj L) ≫
          (P.map (E.mapDerivedCategory.map f) ⊗ₘ P.map g) := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
        Category.id_comp]
      rw [← (transportedAdjunction a α).unit_naturality]
    have hm : (f ⊗ₘ P.map g) ≫
        ((transportedAdjunction a α).unit.app K' ▷ P.obj L') ≫
          Functor.LaxMonoidal.μ P (E.mapDerivedCategory.obj K') L' =
        ((transportedAdjunction a α).unit.app K ▷ P.obj L) ≫
          Functor.LaxMonoidal.μ P (E.mapDerivedCategory.obj K) L ≫
            P.map (E.mapDerivedCategory.map f ⊗ₘ g) := by
      rw [← Category.assoc, hu, Category.assoc, Functor.LaxMonoidal.μ_natural]
    dsimp only [projection]
    calc
      _ = E.mapDerivedCategory.map
          ((f ⊗ₘ P.map g) ≫
            ((transportedAdjunction a α).unit.app K' ▷ P.obj L') ≫
              Functor.LaxMonoidal.μ P (E.mapDerivedCategory.obj K') L') ≫
          (transportedAdjunction a α).counit.app
            (E.mapDerivedCategory.obj K' ⊗ L') := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by
        rw [hm]
        simp only [Functor.map_comp, Category.assoc]
        have hc := (transportedAdjunction a α).counit.naturality
          (E.mapDerivedCategory.map f ⊗ₘ g)
        dsimp only [Functor.comp_map, Functor.id_map] at hc
        rw [hc]
  have hiso (K : DerivedCategory A) (N : B) : IsIso (comparison a α K N) := by
    dsimp only [comparison]
    infer_instance
  refine ⟨hiso, ?_, ?_⟩
  · intro K K' N N' f g
    have hb : P.map ((DerivedCategory.singleFunctor B 0).map g) ≫
        (α.hom.app ((DerivedCategory.singleFunctor B 0).obj N') ≫
          (R.mapDerivedCategorySingleFunctor 0).hom.app N') =
        (α.hom.app ((DerivedCategory.singleFunctor B 0).obj N) ≫
          (R.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
            (DerivedCategory.singleFunctor A 0).map (R.map g) := by
      rw [← Category.assoc, α.hom.naturality, Category.assoc]
      have hs := (R.mapDerivedCategorySingleFunctor 0).hom.naturality g
      dsimp only [Functor.comp_map] at hs
      rw [hs, Category.assoc]
    have hinv :
        (E.mapDerivedCategory.map f ⊗ₘ (DerivedCategory.singleFunctor B 0).map g) ≫
          inv (projection a α K' ((DerivedCategory.singleFunctor B 0).obj N')) =
        inv (projection a α K ((DerivedCategory.singleFunctor B 0).obj N)) ≫
          E.mapDerivedCategory.map (f ⊗ₘ P.map
            ((DerivedCategory.singleFunctor B 0).map g)) := by
      apply (IsIso.eq_inv_comp
        (projection a α K ((DerivedCategory.singleFunctor B 0).obj N))).2
      rw [← Category.assoc, ← hproj, Category.assoc]
      simp
    dsimp only [comparison]
    rw [← Category.assoc, hinv]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp]
    rw [hb]
  · intro K lo hi h N q hq
    have hz := E.map_isZero (h (R.obj N) q hq)
    have ht : IsZero ((DerivedCategory.homologyFunctor B q).obj
        (E.mapDerivedCategory.obj
          (K ⊗ (DerivedCategory.singleFunctor A 0).obj (R.obj N)))) :=
      hz.of_iso ((E.mapDerivedCategoryHomologyFunctorIso q).symm.app _)
    exact ht.of_iso ((DerivedCategory.homologyFunctor B q).mapIso
      (asIso (comparison a α K N)))

end CategoryTheory.ExactAdjointTorTests
