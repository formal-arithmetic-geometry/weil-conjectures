/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.SecSmoothPurity.OpenScalarExchange
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.TateTwistLocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ULift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.InvertibleTensorScalarExtension

/-! # Derived scalar extension on the small pro-etale site

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.md
(blueprint: det-sp-scalar-extension-functor).

The underlying functor is the canonical K-flat derived extension of scalars along a
map of constant coefficient rings.  The accompanying statements record its exactness,
finite constructibility and Tor-amplitude preservation, Tate-line scalar extension,
and the canonical associativity comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived extension of scalars on the ordinary constant-ring pro-etale categories.
Source: Stacks Tags 06YY and 06YS; blueprint `det-sp-scalar-extension-functor`.

The functor is computed by a K-flat representative, and the target category carries
its action through the right tensor factor.  Its construction is the published
`scalarExtension`; no second tensor or localization is introduced here.
(blueprint: det-sp-scalar-extension-functor).
-/
noncomputable def scalarExtensionFunctor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  scalarExtension f T

/-- Exactness of the published derived tensor functor.
Source: Stacks 06YS, 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: resolve by K-flat complexes using lem-pc-kflat-resolution. The ordinary tensor
functor is additive and preserves shifts and mapping cones. Its left derived functor
therefore carries distinguished triangles to distinguished triangles, by
lem-pur-derived-change-of-rings. -/
theorem scalarExtensionFunctor_exact
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u}) :
    ∃ (_ : (scalarExtensionFunctor f T).CommShift ℤ),
      (scalarExtensionFunctor f T).IsTriangulated := by
  exact (reductionDerivedExistence T
    (proEtaleConstantRingMap (T := T) f)).choose_spec.choose_spec.2.1

/-- The actual universal counit on a complex, rather than a chosen model comparison.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorCounit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :=
  reductionScalarComplexCounit T (proEtaleConstantRingMap (T := T) f) P

/-- K-flat computation, including the functor and its target-ring tensor action.
Source: Stacks 06YS, 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: the universal counit in lem-pur-derived-change-of-rings is invertible on
K-flat complexes. Its cochain form conjugates by the two canonical quotient
factorizations, hence remains invertible. The ordinary complex is termwise sheafified
extension with B acting on the scalar factor. -/
theorem scalarExtensionFunctor_kflat_representation
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    IsIso (scalarExtensionFunctorCounit f T P) := by
  have hε := (reductionDerivedExistence T
    (proEtaleConstantRingMap (T := T) f)).choose_spec.choose_spec.2.2 P hP
  have : IsIso ((reductionDerivedCounit T (proEtaleConstantRingMap (T := T) f)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hε
  dsimp only [scalarExtensionFunctorCounit, reductionScalarComplexCounit,
    reductionComplexCounit]
  infer_instance

/-- The canonical formula S_f(Q(P)) ≅ Q(P tensor B), on every K-flat representative.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorKFlatIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    (scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) :=
  @asIso _ _ _ _ (scalarExtensionFunctorCounit f T P)
    (scalarExtensionFunctor_kflat_representation f T P hP)

/-- The map of representatives is u tensor id_B, with the same counit comparison.
Source: Stacks 06YY; clause (1) (blueprint: det-sp-scalar-extension-functor).
Proof: apply naturality of the universal derived counit and of the quotient
factorization maps. The selected ordinary tensor functor maps u to id_B tensor u
by the map clause of lem-pur-derived-change-of-rings. -/
theorem scalarExtensionFunctor_map
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    {P Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ}
    (v : P ⟶ Q) :
    (scalarExtensionFunctor f T).map (DerivedCategory.Q.map v) ≫
        scalarExtensionFunctorCounit f T Q =
      scalarExtensionFunctorCounit f T P ≫ DerivedCategory.Q.map
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).map v) := by
  let E := reductionChange T (proEtaleConstantRingMap (T := T) f)
  let S := scalarExtensionFunctor f T
  let q := HomotopyCategory.quotient
    (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)
  let ε := reductionDerivedCounit T (proEtaleConstantRingMap (T := T) f)
  let η : DerivedCategory.Q ⋙ S ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv S ≫
      Functor.whiskerLeft q ε ≫
      Functor.whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  exact η.naturality v

/-- Constructibility, boundedness and the identical Tor interval survive arbitrary
finite coefficient extension, including non-flat maps.
Source: blueprint proof (2), Stacks 094H, 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: (1) choose flat-term K-flat P by lem-pc-kflat-resolution. By
lem-pur-kflat-change-of-rings its extension is K-flat over B. A B-module Tor test is
the A-module Tor test after restriction, by balanced associativity, so the same
interval [a,b] works. Testing with the unit gives boundedness.
(2) Refine the finite constructible strata for the finitely many cohomology sheaves
by lem-weil-pbc-constructible-stratification-intersection. On every stratum the
restricted complex has finite locally constant cohomology. The constant-sheaf stalk
lemma identifies its finite local values. Apply lem-sp-stratum-scalar-extension
and lem-weil-pbc-locally-constant-tensor (Stacks 094H), since A is finite Noetherian
and B is a finite A-module. This gives constructible cohomology on the same strata.
No flatness or projective-dimension hypothesis on B is used. -/
theorem scalarExtensionFunctor_preserves_constructible_tor
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K))
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
        ((scalarExtensionFunctor f T).obj K))} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((scalarExtensionFunctor f T).obj K))) ∧
    HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b := by
  sorry

private theorem scalarExtensionFunctor_line_counit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}
  let R := proEtaleConstantRing T A
  let := hL
  have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := R) L :=
    (WeilConjectures.coefficientTwistLine_exact T L 1).2
  apply scalarExtensionFunctor_kflat_representation f T
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
  intro i
  by_cases hi : i = 0
  · subst i
    exact hflat
  · have hz := HomologicalComplex.isZero_single_obj_X
      (V := proEtaleRingModules T R) (.up ℤ) 0 L i hi
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.tensorPreadditive R
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm
      (ObjectProperty.flat_of_isZero hz).2

private noncomputable def scalarExtension_unit_iso
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u + 1}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J CommRingCat.{u + 1}) (α : R ⟶ S) :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} α
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) := by
  let M := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let d := (SheafOfModules.exists_unique_invertibleTensorScalarExtensionData R S α M).some
  exact d.unitComparison

private noncomputable def scalarExtension_over_iso
    (T : Scheme.{u}) (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : R ⟶ S) (L : proEtaleRingModules T R) (U : T.ProEt) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} α L).over U ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (((ProEt.topology T).overPullback CommRingCat.{u + 1} U).map α) (L.over U) := by
  let αU := ((ProEt.topology T).overPullback CommRingCat.{u + 1} U).map α
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} α L
  let e : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} αU (L.over U) ≅
      (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro V W f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change SheafOfModules.changeOfRingsMap αU (L.over U) f _ =
        SheafOfModules.changeOfRingsMap α L ((Over.forget U).op.map f) _
      erw [(SheafOfModules.exists_changeOfRingsMap αU (L.over U) f).choose_spec])
  let S' : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  have := SheafOfModules.overSheafificationMap_isIso.{u + 1, u, u + 1, u + 1} S' U P
  exact (asIso (SheafOfModules.overSheafificationMap.{u + 1, u, u + 1, u + 1} S' U P)).symm ≪≫
    (PresheafOfModules.sheafification (R := S'.over U) (𝟙 _)).mapIso e.symm

/-- A line extends by ordinary tensor and remains locally free of rank one.
Source: blueprint proof (3), Stacks 06YQ
(blueprint: det-sp-scalar-extension-functor).
Proof: trivialize L on a cover. It is flat there and therefore globally flat, so its
degree-zero complex is K-flat by lem-weil-pbc-independent-bounded-flat-kflat.
The derived counit computes its extension by ordinary tensor. On the same cover
ordinary tensor sends the free rank-one module A to B, proving rank one locally. -/
theorem scalarExtensionFunctor_line
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) 1 := by
  refine ⟨scalarExtensionFunctor_line_counit f T L hL, ?_⟩
  rw [proEtaleRingExtension_obj]
  obtain ⟨I, X, hX, he⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}.mp hL
  apply (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1} _).mp
  apply SheafOfModules.isInvertible_of_forall_over_unit.{u + 1, u, u + 1} X hX
  intro i
  let J := (ProEt.topology T).over (X i)
  let α := ((ProEt.topology T).overPullback CommRingCat.{u + 1} (X i)).map
    (proEtaleConstantRingMap (T := T) f)
  let R := ((ProEt.topology T).overPullback CommRingCat.{u + 1} (X i)).obj
    (proEtaleConstantRing T A)
  let S := ((ProEt.topology T).overPullback CommRingCat.{u + 1} (X i)).obj
    (proEtaleConstantRing T B)
  let : EssentiallySmall.{u + 1} (Over (X i)) := essentiallySmallSelf.{0} _
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  let d := (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel α).some
  let eL := (he i).some ≪≫ SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))
  exact ⟨scalarExtension_over_iso T _ _ (proEtaleConstantRingMap (T := T) f) L (X i) ≪≫
    (eqToIso (d.obj_eq (L.over (X i)))).symm ≪≫ d.E.mapIso eL ≪≫
    eqToIso (d.obj_eq _) ≪≫ scalarExtension_unit_iso J R S α⟩

/-- The rank-one derived computation as an explicit isomorphism to ordinary scalar tensor.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorLineIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    (scalarExtensionFunctor f T).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) :=
  @asIso _ _ _ _
      (scalarExtensionFunctorCounit f T ((HomologicalComplex.single _ (.up ℤ) 0).obj L))
      (scalarExtensionFunctor_line f T L hL).1 ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).app L)

/-- The finite signed Tate line, using the dependency's roots, powers, unit and duals.
The index n denotes the positive exponent m=n+1. The quotient map a is unique.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
abbrev scalarExtensionTateLine (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type u) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :=
  WeilConjectures.coefficientTwistLine T (R := proEtaleConstantRing T A)
    (tateFiniteLine T ℓ (ULift.{u + 1, u} A) n (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a)) r

/-- Semilinear maps between the signed finite Tate lines, before scalar extension.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
abbrev ScalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  ∀ r : ℤ, scalarExtensionTateLine T ℓ A n a r ⟶
    (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f)).obj
      (scalarExtensionTateLine T ℓ B n (f.comp a) r)

/-- Root tensors determine degree one; the coefficient map determines degree zero;
positive powers and negative duals are normalized by tensoring and evaluation.
The degree-one root equation uses HEq only to retain the two existing presentations
of that same degree-one line, without unfolding module sheafification during elaboration.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor). -/
def IsCanonicalScalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (c : ScalarExtensionTateMaps f T ℓ n a) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (proEtaleConstantRing T A).obj.obj U),
    (c 0).val.app U s = (proEtaleConstantRingMap (T := T) f).hom.app U s) ∧
  (∀ (V : T.ProEt) (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj (Opposite.op V)),
    HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s x) →
    HEq ((c 1).val.app (Opposite.op V) y)
      (tateFiniteTensor T ℓ (ULift.{u + 1, u} B) n
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp (f.comp a)) V
        ((proEtaleConstantRingMap (T := T) f).hom.app (Opposite.op V) s) x)) ∧
  (∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (x : (scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1))).val.obj U)
      (y : (scalarExtensionTateLine T ℓ A n a 1).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T B) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (d : (scalarExtensionTateLine T ℓ A n a (Int.negSucc k)).val.obj U)
      (x : (scalarExtensionTateLine T ℓ A n a (Int.ofNat (k + 1))).val.obj U),
    (((c (Int.negSucc k)).val.app U d).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (k + 1))).val.app U x) =
      (proEtaleConstantRingMap (T := T) f).hom.app U
        ((d.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

/-- There is exactly one semilinear family with the root, unit, power and dual formulas.
Source: blueprint proof (3), Stacks 03EK, 03EM
(blueprint: det-sp-scalar-extension-functor).
Proof: in degree one use the balanced root-tensor map induced by f. In degree zero
use the coefficient map. Tensor recursively for positive degrees. On a primitive-root
cover from det-def-sp-tate-twist-locally-free these are the coefficient map on a free
rank-one module. Thus the dual-evaluation formula determines the negative map uniquely.
The maps commute with restrictions and glue. Pure tensors and the nondegenerate local
evaluation pairing prove uniqueness. This is the finite-coefficient instance of
lem-sp-invertible-tensor-scalar-extension, and requires only ell invertible on T. -/
theorem scalarExtensionTateMaps_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    ∃! c : ScalarExtensionTateMaps f T ℓ n a,
      IsCanonicalScalarExtensionTateMaps f T ℓ n a c := by
  sorry

/-- The finite Tate scalar maps, fixed uniquely in every signed degree.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateMaps
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) : ScalarExtensionTateMaps f T ℓ n a :=
  (scalarExtensionTateMaps_existsUnique f T ℓ n a).exists.choose

/-- The signed Tate base-change isomorphism is uniquely fixed on scalar tensor sections.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: extend the normalized semilinear map by b tensor x ↦ b*c(x).
On the primitive-root cover all signed lines are the unit module, so the map is
multiplication B tensor A→B with inverse b↦b tensor 1. Glue the inverses.
The ordinary sheafification unit and local tensor generation give uniqueness. -/
theorem scalarExtensionTateIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    ∃! e : (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj
        (scalarExtensionTateLine T ℓ A n a r) ≅
          scalarExtensionTateLine T ℓ B n (f.comp a) r,
      ∀ (U : T.ProEtᵒᵖ) (b : (proEtaleConstantRing T B).obj.obj U)
        (x : (scalarExtensionTateLine T ℓ A n a r).val.obj U),
        e.hom.val.app U
            (reductionTensorSection T (proEtaleConstantRingMap (T := T) f) _ U b x) =
          b • (@id ((scalarExtensionTateLine T ℓ B n (f.comp a) r).val.obj U)
            ((scalarExtensionTateMaps f T ℓ n a r).val.app U x)) := by
  sorry

/-- The ordinary canonical comparison (A_T(r)) tensor B_T ≅ B_T(r).
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj
        (scalarExtensionTateLine T ℓ A n a r) ≅
      scalarExtensionTateLine T ℓ B n (f.comp a) r :=
  (scalarExtensionTateIso_existsUnique f T ℓ n a r).exists.choose

private theorem scalarExtensionTateLine_rank_one (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionTateLine T ℓ A n a r).IsFiniteLocallyFreeOfRank 1 := by
  let E := ULift.{u} (Padic ℓ)
  let Ω := AlgebraicClosure E
  have h := tateTwist_locallyFree.{u, u, 0} T ℓ E Ω (IsScalarTower.toAlgHom (Padic ℓ) E Ω)
  obtain ⟨I, U, f, ζ, e, hcover, hζ, he, hfinite, hrest⟩ := h
  have hann : ∀ x : ULift.{u + 1, u} A, (ℓ ^ (n + 1)) • x = 0 := by
    intro x
    have hz : ((ℓ ^ (n + 1) : ℕ) : ZMod (ℓ ^ (n + 1))) = 0 :=
      ZMod.natCast_self _
    have hzA : ((ℓ ^ (n + 1) : ℕ) : ULift.{u + 1, u} A) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (ULift.ringEquiv.symm.toRingHom.comp a) hz
    simp only [nsmul_eq_mul, hzA, zero_mul]
  obtain ⟨a', hlevel, hL, hsigned, _⟩ := hfinite (ULift.{u + 1, u} A) n hann
  have ha' : a' = ULift.ringEquiv.symm.toRingHom.comp a := Subsingleton.elim _ _
  subst a'
  exact (hsigned.1 r).1

/-- The Tate comparison computes derived extension in every signed degree and the
finite twists are rank-one locally free.
Source: blueprint proof (3), Stacks 06YQ
(blueprint: det-sp-scalar-extension-functor).
Proof: det-def-sp-tate-twist-locally-free trivializes the root line and every power
and dual on one cover. Hence every signed line is rank one and flat. Its degree-zero
complex is K-flat by lem-weil-pbc-independent-bounded-flat-kflat, so the universal
counit is invertible. Follow that counit with the localization of the ordinary
canonical scalarExtensionTateIso to obtain the derived comparison. -/
theorem scalarExtensionFunctor_tate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionTateLine T ℓ A n a r).IsFiniteLocallyFreeOfRank 1 ∧
    (scalarExtensionTateLine T ℓ B n (f.comp a) r).IsFiniteLocallyFreeOfRank 1 ∧
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarExtensionTateLine T ℓ A n a r))) := by
  have hA := scalarExtensionTateLine_rank_one T ℓ A n a r
  have hB := scalarExtensionTateLine_rank_one T ℓ B n (f.comp a) r
  exact ⟨hA, hB, scalarExtensionFunctor_line_counit f T _ hA⟩

/-- The canonical derived Tate comparison, formed from the universal counit and
ordinary normalized comparison through the standard single-complex factorization.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctorTateIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ) :
    (scalarExtensionFunctor f T).obj
        ((DerivedCategory.singleFunctor _ 0).obj (scalarExtensionTateLine T ℓ A n a r)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (scalarExtensionTateLine T ℓ B n (f.comp a) r) :=
  @asIso _ _ _ _
      (scalarExtensionFunctorCounit f T
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarExtensionTateLine T ℓ A n a r)))
      (scalarExtensionFunctor_tate f T ℓ n a r).2.2 ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).app
          (scalarExtensionTateLine T ℓ A n a r)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (scalarExtensionTateIso f T ℓ n a r)

/-- Signed Kummer comparisons are fixed by the power map on roots, the identity on
coefficients, tensor products in positive degrees, and dual evaluation in negative degrees.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor). -/
def IsCanonicalScalarExtensionTateLevelMaps
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A)
    (c : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r ⟶ scalarExtensionTateLine T ℓ A m a r) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (proEtaleConstantRing T A).obj.obj U),
    (c 0).val.app U s = s) ∧
  (∀ (V : T.ProEt) (s : (proEtaleConstantRing T A).obj.obj (Opposite.op V))
      (x : (proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj (Opposite.op V))
      (y : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) 1).val.obj (Opposite.op V)),
    HEq y (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) n
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1)))))) V s x) →
    HEq ((c 1).val.app (Opposite.op V) y)
      (tateFiniteTensor T ℓ (ULift.{u + 1, u} A) m
        (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp a) V s
        ((proEtaleRootsOfUnityTransition T (ℓ ^ (m + 1)) (ℓ ^ (n + 1))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))).hom.app (Opposite.op V) x))) ∧
  (∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (x : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.ofNat (k + 1))).val.obj U)
      (y : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) 1).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T A) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : T.ProEtᵒᵖ)
      (d : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.negSucc k)).val.obj U)
      (x : (scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) (Int.ofNat (k + 1))).val.obj U),
    (((c (Int.negSucc k)).val.app U d).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (k + 1))).val.app U x) =
      (d.app (Opposite.op (Over.mk (𝟙 U.unop)))) x

/-- Independence of every signed finite Tate line from the sufficiently large exponent,
with the Kummer-induced comparison fixed uniquely.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: clause (2) of det-def-sp-tate-twist-locally-free identifies the root lines by
the actual Kummer power map. On the primitive-root cover it sends the chosen generator
to the chosen generator, so is an isomorphism. Take the identity on the unit, tensor
powers of this map in positive degrees, and its inverse dual in negative degrees,
using lem-sp-invertible-tensor-scalar-extension. Evaluation specifies the dual uniquely.
The root formula and tensor sheafification give uniqueness at positive degrees;
nondegenerate evaluation gives it at negative degrees. -/
theorem scalarExtensionTateLevelIso_existsUnique
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :
    ∃! e : ∀ r : ℤ, scalarExtensionTateLine T ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r ≅ scalarExtensionTateLine T ℓ A m a r,
      IsCanonicalScalarExtensionTateLevelMaps T ℓ A m n hmn a (fun r ↦ (e r).hom) := by
  sorry

/-- The unique signed Kummer comparison used in exponent independence.
Source: blueprint clause (3) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionTateLevelIso
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type u) [CommRing A] [Finite A]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) :=
  (scalarExtensionTateLevelIso_existsUnique T ℓ A m n hmn a).exists.choose

/-- Scalar extension of Tate lines commutes with the canonical exponent comparisons.
Thus the canonical comparison (A(r))_B≅B(r) is independent of the common exponent.
Source: blueprint proof (3) (blueprint: det-sp-scalar-extension-functor).
Proof: on degree-one root tensors both paths apply the same Kummer power map and f
to the scalar. In degree zero both apply f. Tensoring proves the positive cases.
Evaluate both negative maps on a positive section; the evaluation formulas give the
same image under f. Nondegeneracy gives equality. Pure tensors then give the scalar
extension square in every signed degree, and the derived counits preserve it. -/
theorem scalarExtensionTateIso_exponent_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) (r : ℤ) :
    (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).map
        (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom ≫
      (scalarExtensionTateIso f T ℓ m a r).hom =
    (scalarExtensionTateIso f T ℓ n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r).hom ≫
      (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom := by
  sorry

/-- The constant ring maps compose as the specified ring homomorphisms do.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: RingHom.ulift respects composition. The constant-sheaf functor preserves
composition, so its images of f and g compose to its image of g.comp f. -/
theorem scalarExtensionFunctor_ringMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    proEtaleConstantRingMap (T := T) f ≫ proEtaleConstantRingMap (T := T) g =
      proEtaleConstantRingMap (T := T) (g.comp f) := by
  unfold proEtaleConstantRingMap
  rw [← Functor.map_comp]
  rfl

private theorem scalarExtension_conjugate
    {D : Type*} [Category D] {X X' Y Y' : D}
    (hX : X = X') (hY : Y = Y') (v : X ⟶ Y) (w : X' ⟶ Y')
    (h : v = eqToHom hX ≫ w ≫ eqToHom hY.symm) :
    eqToHom hX ≫ w = v ≫ eqToHom hY := by
  subst X'
  subst Y'
  simpa using h.symm

private def scalarExtension_complex_iso_aux
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (E : reductionModules T R ⥤ reductionModules T S) [E.Additive]
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hmap : ∀ {M N} (v : M ⟶ N), E.map v = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M v ≫ eqToHom (hobj N).symm)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      SheafOfModules.changeOfRingsComplex.{u + 1, u} φ P :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (hobj (P.X i))) (by
    intro i j hij
    change eqToHom (hobj (P.X i)) ≫ SheafOfModules.changeOfRingsHom φ (P.X i)
        (P.d i j) = E.map (P.d i j) ≫ eqToHom (hobj (P.X j))
    exact scalarExtension_conjugate _ _ _ _ (hmap (P.d i j)))

private def scalarExtension_change_complex_iso
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T φ).obj P ≅
      SheafOfModules.changeOfRingsComplex.{u + 1, u} φ P :=
  scalarExtension_complex_iso_aux T φ (reductionChange T φ)
    (reductionChangeExistence T φ).choose_spec.choose
    (reductionChangeExistence T φ).choose_spec.choose_spec.choose P

private theorem scalarExtension_change_kflat
    (T : Scheme.{u}) [EssentiallySmall.{u + 1} T.ProEt]
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := R) P)
    (hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (@SheafOfModules.monoidalCategory.{u, u + 1, u + 1}
        _ _ _ _ R _ _
        (SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R)) (P.X i))) :
    CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := S)
      ((reductionChangeComplex T φ).obj P) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have hk := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{u + 1, u} φ P hP hflat).1
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  intro X hX i
  let F := (MonoidalCategory.curriedTensor (reductionModules T S)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)
  exact (hk X hX i).of_iso ((F.obj X).mapIso (scalarExtension_change_complex_iso T φ P)).symm

private def scalarExtension_balance_homotopy
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    (reductionChange T (proEtaleConstantRingMap (T := T) f)).mapHomotopyCategory (.up ℤ) ⋙
        (reductionChange T (proEtaleConstantRingMap (T := T) g)).mapHomotopyCategory (.up ℤ) ⟶
      (reductionChange T (proEtaleConstantRingMap (T := T) (g.comp f))).mapHomotopyCategory
        (.up ℤ) where
  app X := (HomotopyCategory.quotient _ (.up ℤ)).map
    (reductionBalance T (proEtaleConstantRingMap (T := T) f)
      (proEtaleConstantRingMap (T := T) g)
      (proEtaleConstantRingMap (T := T) (g.comp f))
      (scalarExtensionFunctor_ringMap_comp f g T) X.as)
  naturality := by
    rintro ⟨P⟩ ⟨Q⟩ ⟨v⟩
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map _ =
      (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map _
    simp only [← Functor.map_comp]
    exact congrArg ((HomotopyCategory.quotient _ (.up ℤ)).map)
      (reductionBalance_naturality T _ _ _ (scalarExtensionFunctor_ringMap_comp f g T) v)

private def scalarExtension_composition_counit
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ (scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T) ⟶
      (reductionChange T (proEtaleConstantRingMap (T := T) (g.comp f))).mapHomotopyCategory
        (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) f))
      (scalarExtensionFunctor g T) ≫
    Functor.whiskerLeft
      ((reductionChange T (proEtaleConstantRingMap (T := T) f)).mapHomotopyCategory (.up ℤ))
      (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) g)) ≫
    Functor.whiskerRight (scalarExtension_balance_homotopy f g T) DerivedCategory.Qh

private def scalarExtension_composition_map
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ⟶
      scalarExtensionFunctor (g.comp f) T :=
  (reductionDerivedChange T (proEtaleConstantRingMap (T := T) (g.comp f))).leftDerivedLift
    (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) (g.comp f)))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ (scalarExtension_composition_counit f g T)

private theorem scalarExtension_complex_counit_eq
    {B D : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ) :
    reductionComplexCounit E L ε P =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) := by
  change L.map (𝟙 (DerivedCategory.Q.obj P)) ≫ ε.app _ ≫
    DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P))) ≫ 𝟙 _ = _
  have hL := L.map_id (DerivedCategory.Q.obj P)
  have hQ := (DerivedCategory.Qh (C := D)).map_id
    ((HomotopyCategory.quotient D (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj P))
  rw [hL, hQ]
  change (𝟙 _) ≫ ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) ≫ 𝟙 _ ≫ 𝟙 _ =
    ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalarExtension_composition_map_fac
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (scalarExtension_composition_map f g T).app (DerivedCategory.Q.obj P) ≫
        scalarExtensionFunctorCounit (g.comp f) T P =
      (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
        scalarExtensionFunctorCounit g T
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T
          (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
          (proEtaleConstantRingMap (T := T) (g.comp f))
          (scalarExtensionFunctor_ringMap_comp f g T) P) := by
  have h := (reductionDerivedChange T
    (proEtaleConstantRingMap (T := T) (g.comp f))).leftDerived_fac_app
    (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) (g.comp f)))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ (scalarExtension_composition_counit f g T)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  dsimp only [scalarExtensionFunctorCounit, reductionScalarComplexCounit]
  rw [scalarExtension_complex_counit_eq, scalarExtension_complex_counit_eq,
    scalarExtension_complex_counit_eq]
  dsimp only [scalarExtension_composition_map, scalarExtension_composition_counit,
    scalarExtension_balance_homotopy, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  exact h


private theorem scalarExtension_kflat_hom_ext
    (T : Scheme.{u}) {A : Type u} [CommRing A]
    {D : Type*} [Category D] {F G : proEtaleDerivedCategory T A ⥤ D}
    (τ σ : F ⟶ G)
    (h : ∀ P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
        (R := proEtaleConstantRing T A) P →
      τ.app (DerivedCategory.Q.obj P) = σ.app (DerivedCategory.Q.obj P)) : τ = σ := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  apply NatTrans.ext
  funext K
  obtain ⟨P, s, hP, hflat, hs, hepi⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := proEtaleConstantRing T A) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  apply (cancel_epi (F.map e.hom)).mp
  rw [τ.naturality, σ.naturality,
    h P ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)]

private theorem scalarExtension_composition_map_isIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    IsIso (scalarExtension_composition_map f g T) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have happ (K : proEtaleDerivedCategory T A) :
      IsIso ((scalarExtension_composition_map f g T).app K) := by
    obtain ⟨P, s, hP, hflat, hs, hepi⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := proEtaleConstantRing T A) (DerivedCategory.Q.objPreimage K)
    have hPlive := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
    have : QuasiIso s := hs
    let e : DerivedCategory.Q.obj P ≅ K :=
      asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    apply ((scalarExtension_composition_map f g T).isIso_app_iff_of_iso e).mp
    have := scalarExtensionFunctor_kflat_representation f T P hPlive
    have := scalarExtensionFunctor_kflat_representation (g.comp f) T P hPlive
    have := scalarExtensionFunctor_kflat_representation g T
      ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)
      (scalarExtension_change_kflat T _ P hPlive hflat)
    exact IsIso.of_isIso_fac_right (scalarExtension_composition_map_fac f g T P)
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (scalarExtension_composition_map f g T) happ


/-- The unique composition comparison fixed by balanced tensor on K-flat models.
Source: blueprint proof (4), Stacks 0G7E, 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: whisker the universal derived counits and compose with the homotopy image of
reductionBalance. The universal left-derived lift gives a natural comparison, whose
factorization equation is the displayed normalization on every complex. Resolve each
object by a flat-term K-flat complex. The ordinary object and map identifications
identify its extension with the explicit tensor complex, which remains K-flat by
lem-pur-kflat-change-of-rings. The three counits and balancing map are isomorphisms,
so the lifted comparison is invertible on every object. The normalization determines
it on K-flat representatives, and naturality along their resolution quasi-isomorphisms
proves uniqueness everywhere. -/
theorem scalarExtensionFunctor_composition_existsUnique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    ∃! α : scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
        scalarExtensionFunctor (g.comp f) T,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        α.hom.app (DerivedCategory.Q.obj P) ≫ scalarExtensionFunctorCounit (g.comp f) T P =
          (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
            scalarExtensionFunctorCounit g T
              ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
            DerivedCategory.Q.map (reductionBalance T
              (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
              (proEtaleConstantRingMap (T := T) (g.comp f))
              (scalarExtensionFunctor_ringMap_comp f g T) P) := by
  have := scalarExtension_composition_map_isIso f g T
  refine ⟨asIso (scalarExtension_composition_map f g T), ?_, ?_⟩
  · intro P hP
    exact scalarExtension_composition_map_fac f g T P
  · intro β hβ
    apply Iso.ext
    apply scalarExtension_kflat_hom_ext T
    intro P hP
    have := scalarExtensionFunctor_kflat_representation (g.comp f) T P hP
    apply (cancel_mono (scalarExtensionFunctorCounit (g.comp f) T P)).mp
    exact (hβ P hP).trans (scalarExtension_composition_map_fac f g T P).symm

/-- Canonical α, selected from its unique K-flat balancing characterization.
Source: blueprint clause (4) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctor_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
      scalarExtensionFunctor (g.comp f) T :=
  (scalarExtensionFunctor_composition_existsUnique f g T).exists.choose

/-- Naturality of this particular normalized α for every derived morphism.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: balance commutes with chain maps. Resolve the middle term of a roof by
lem-pc-kflat-resolution; the tensor functors invert its quasi-isomorphism by
lem-pur-derived-change-of-rings. Naturality for both roof arrows gives the equation. -/
theorem scalarExtensionFunctor_composition_naturality
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u})
    (K L : proEtaleDerivedCategory T A) (v : K ⟶ L) :
    (scalarExtensionFunctor g T).map ((scalarExtensionFunctor f T).map v) ≫
        (scalarExtensionFunctor_composition f g T).hom.app L =
      (scalarExtensionFunctor_composition f g T).hom.app K ≫
        (scalarExtensionFunctor (g.comp f) T).map v := by
  exact (scalarExtensionFunctor_composition f g T).hom.naturality v

private theorem scalarExtension_ringMap_id
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingMap (T := T) (RingHom.id A) = 𝟙 (proEtaleConstantRing T A) := by
  change (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (𝟙 (CommRingCat.of (ULift.{u + 1, u} A))) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

open scoped ChangeOfRings in
private theorem scalarExtension_identity_ordinary
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∃ e : reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A)) ≅ 𝟭 _,
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)) (U : T.ProEtᵒᵖ)
        (s : (proEtaleConstantRing T A).obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (reductionTensorSection T
          (proEtaleConstantRingMap (T := T) (RingHom.id A)) M U s x) = s • x := by
  rw [scalarExtension_ringMap_id]
  let φ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T A := 𝟙 _
  let adj : reductionChange T φ ⊣ 𝟭 _ := pbcScalarAdjunction φ
  let e := adj.leftAdjointUniq Adjunction.id
  refine ⟨e, ?_⟩
  intro M U s x
  have hunit := (pbcScalarAdjunction_exists φ).exists.choose_spec M U (s • x)
  have h := adj.unit_leftAdjointUniq_hom_app Adjunction.id M
  have hx := ConcreteCategory.congr_hom (congrArg (fun v ↦ v.val.app U) h) (s • x)
  change (e.hom.app M).val.app U ((adj.unit.app M).val.app U (s • x)) = s • x at hx
  change (adj.unit.app M).val.app U (s • x) =
    reductionTensorSection T φ M U 1 (s • x) at hunit
  have ht : reductionTensorSection T φ M U 1 (s • x) =
      reductionTensorSection T φ M U s x := by
    unfold reductionTensorSection completedAdicChangeTensor
    congr 2
    let : Module ((proEtaleConstantRing T A).obj.obj U)
        ((proEtaleConstantRing T A).obj.obj U) :=
      Module.compHom _ (φ.hom.app U).hom
    rw [TensorProduct.tmul_smul]
    change ((s : (proEtaleConstantRing T A).obj.obj U) * 1) ⊗ₜ[_, (φ.hom.app U).hom] x = _
    rw [mul_one]
  rw [hunit, ht] at hx
  exact hx


private theorem scalarExtension_tensor_hom_ext
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) {M : reductionModules T R} {N : reductionModules T S}
    (v w : (reductionChange T φ).obj M ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      v.val.app U (reductionTensorSection T φ M U 1 x) =
        w.val.app U (reductionTensorSection T φ M U 1 x)) : v = w := by
  apply ((pbcScalarAdjunction φ).homEquiv M N).injective
  ext U x
  change v.val.app U (((pbcScalarAdjunction φ).unit.app M).val.app U x) =
    w.val.app U (((pbcScalarAdjunction φ).unit.app M).val.app U x)
  have hunit := (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  change ((pbcScalarAdjunction φ).unit.app M).val.app U x =
    reductionTensorSection T φ M U 1 x at hunit
  rw [hunit]
  exact h U x

private def scalarExtension_complex_to_self
    {B : Type*} [Category B] [Abelian B] (E : B ⥤ B) [E.Additive]
    (e : E ≅ 𝟭 _) (P : CochainComplex B ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).obj P ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (P.X i)) (by
    intro i j hij
    exact (e.hom.naturality (P.d i j)).symm)

private def scalarExtension_identity_counit
    {A : Type u} [CommRing A] (T : Scheme.{u})
    (e : reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A)) ≅ 𝟭 _) :
    DerivedCategory.Qh ⋙ 𝟭 (proEtaleDerivedCategory T A) ⟶
      (reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A))).mapHomotopyCategory
        (.up ℤ) ⋙ DerivedCategory.Qh where
  app X := DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
    (scalarExtension_complex_to_self _ e X.as).inv)
  naturality := by
    rintro ⟨P⟩ ⟨Q⟩ ⟨v⟩
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map v) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map _) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map _) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map _)
    simp only [← CategoryTheory.Functor.map_comp]
    congr 2
    apply HomologicalComplex.hom_ext
    intro i
    exact e.inv.naturality (v.f i)

private def scalarExtension_identity_map
    {A : Type u} [CommRing A] (T : Scheme.{u})
    (e : reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A)) ≅ 𝟭 _) :
    𝟭 (proEtaleDerivedCategory T A) ⟶ scalarExtensionFunctor (RingHom.id A) T :=
  (reductionDerivedChange T (proEtaleConstantRingMap (T := T) (RingHom.id A))).leftDerivedLift
    (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) (RingHom.id A)))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ (scalarExtension_identity_counit T e)

private theorem scalarExtension_identity_map_fac
    {A : Type u} [CommRing A] (T : Scheme.{u})
    (e : reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A)) ≅ 𝟭 _)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (scalarExtension_identity_map T e).app (DerivedCategory.Q.obj P) ≫
      scalarExtensionFunctorCounit (RingHom.id A) T P =
        DerivedCategory.Q.map (scalarExtension_complex_to_self _ e P).inv := by
  have h := (reductionDerivedChange T
    (proEtaleConstantRingMap (T := T) (RingHom.id A))).leftDerived_fac_app
    (reductionDerivedCounit T (proEtaleConstantRingMap (T := T) (RingHom.id A)))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ (scalarExtension_identity_counit T e)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  dsimp only [scalarExtensionFunctorCounit, reductionScalarComplexCounit]
  rw [scalarExtension_complex_counit_eq]
  exact h

private theorem scalarExtension_identity_map_isIso
    {A : Type u} [CommRing A] (T : Scheme.{u})
    (e : reductionChange T (proEtaleConstantRingMap (T := T) (RingHom.id A)) ≅ 𝟭 _) :
    IsIso (scalarExtension_identity_map T e) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have happ (K : proEtaleDerivedCategory T A) :
      IsIso ((scalarExtension_identity_map T e).app K) := by
    obtain ⟨P, s, hP, hflat, hs, hepi⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := proEtaleConstantRing T A) (DerivedCategory.Q.objPreimage K)
    have hPlive := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
    have : QuasiIso s := hs
    let eP : DerivedCategory.Q.obj P ≅ K :=
      asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    apply ((scalarExtension_identity_map T e).isIso_app_iff_of_iso eP).mp
    have := scalarExtensionFunctor_kflat_representation (RingHom.id A) T P hPlive
    exact IsIso.of_isIso_fac_right (scalarExtension_identity_map_fac T e P)
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (scalarExtension_identity_map T e) happ

private theorem scalarExtension_identity_all_complexes
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∃ ε : scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        ∃ v : (reductionChangeComplex T
            (proEtaleConstantRingMap (T := T) (RingHom.id A))).obj P ⟶ P,
          (∀ (i : ℤ) (U : T.ProEtᵒᵖ)
            (s : (proEtaleConstantRing T A).obj.obj U) (x : (P.X i).val.obj U),
            (v.f i).val.app U (reductionTensorSection T
              (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i) U s x) = s • x) ∧
          ε.hom.app (DerivedCategory.Q.obj P) =
            scalarExtensionFunctorCounit (RingHom.id A) T P ≫ DerivedCategory.Q.map v := by
  obtain ⟨e, he⟩ := scalarExtension_identity_ordinary (A := A) T
  have := scalarExtension_identity_map_isIso T e
  let ε := (asIso (scalarExtension_identity_map T e)).symm
  have hnorm (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
      ε.hom.app (DerivedCategory.Q.obj P) =
        scalarExtensionFunctorCounit (RingHom.id A) T P ≫
          DerivedCategory.Q.map (scalarExtension_complex_to_self _ e P).hom := by
    change (asIso (scalarExtension_identity_map T e)).inv.app (DerivedCategory.Q.obj P) = _
    apply (cancel_epi ((asIso (scalarExtension_identity_map T e)).hom.app
      (DerivedCategory.Q.obj P))).mp
    rw [(asIso (scalarExtension_identity_map T e)).hom_inv_id_app]
    change 𝟙 _ = (scalarExtension_identity_map T e).app (DerivedCategory.Q.obj P) ≫ _
    rw [← Category.assoc, scalarExtension_identity_map_fac,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl
  refine ⟨ε, ?_⟩
  intro P
  refine ⟨(scalarExtension_complex_to_self _ e P).hom, ?_, hnorm P⟩
  intro i U s x
  exact he (P.X i) U s x

/-- The identity extension has a unique multiplication-normalized unitor.
Source: blueprint proof (4), Stacks 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: the inverse of the ordinary tensor unit is p ↦ 1 tensor p. Compose its
localization with the derived counit on a K-flat model. The two multiplication
maps are inverse and natural, so descend by lem-weil-pbc-site-derived-tensor-descent.
Pure tensors determine the chain map uniquely, and K-flat resolutions determine the
natural isomorphism uniquely. -/
theorem scalarExtensionFunctor_identity_existsUnique
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∃! ε : scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        ∃ v : (reductionChangeComplex T
            (proEtaleConstantRingMap (T := T) (RingHom.id A))).obj P ⟶ P,
          (∀ (i : ℤ) (U : T.ProEtᵒᵖ)
            (s : (proEtaleConstantRing T A).obj.obj U) (x : (P.X i).val.obj U),
            (v.f i).val.app U (reductionTensorSection T
              (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i) U s x) = s • x) ∧
          ε.hom.app (DerivedCategory.Q.obj P) =
            scalarExtensionFunctorCounit (RingHom.id A) T P ≫ DerivedCategory.Q.map v := by
  obtain ⟨ε, hε⟩ := scalarExtension_identity_all_complexes (A := A) T
  refine ⟨ε, fun P _ ↦ hε P, ?_⟩
  intro ε' hε'
  apply Iso.ext
  apply scalarExtension_kflat_hom_ext T
  intro P hP
  obtain ⟨v, hv, hfac⟩ := hε' P hP
  obtain ⟨w, hw, hwfac⟩ := hε P
  have hvw : v = w := by
    apply HomologicalComplex.hom_ext
    intro i
    apply scalarExtension_tensor_hom_ext T
      (proEtaleConstantRingMap (T := T) (RingHom.id A))
    intro U x
    exact (hv i U 1 x).trans (hw i U 1 x).symm
  exact hfac.trans ((congrArg (fun v ↦ scalarExtensionFunctorCounit (RingHom.id A) T P ≫
    DerivedCategory.Q.map v) hvw).trans hwfac.symm)

/-- The canonical identity-extension unitor, normalized by multiplication.
Source: blueprint clause (4) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctor_identity
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _ :=
  (scalarExtensionFunctor_identity_existsUnique (A := A) T).exists.choose

private theorem scalarExtension_composition_normalized
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (scalarExtensionFunctor_composition f g T).hom.app (DerivedCategory.Q.obj P) ≫
        scalarExtensionFunctorCounit (g.comp f) T P =
      (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
        scalarExtensionFunctorCounit g T
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T
          (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
          (proEtaleConstantRingMap (T := T) (g.comp f))
          (scalarExtensionFunctor_ringMap_comp f g T) P) := by
  have := scalarExtension_composition_map_isIso f g T
  have heq : scalarExtensionFunctor_composition f g T =
      asIso (scalarExtension_composition_map f g T) :=
    (scalarExtensionFunctor_composition_existsUnique f g T).unique
      (scalarExtensionFunctor_composition_existsUnique f g T).exists.choose_spec
      (fun P _ ↦ scalarExtension_composition_map_fac f g T P)
  rw [heq]
  exact scalarExtension_composition_map_fac f g T P

private theorem scalarExtension_balance_cocycle
    (T : Scheme.{u}) {R S U V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (χ : R ⟶ U) (ω : S ⟶ V) (ξ : R ⟶ V)
    (hχ : φ ≫ ψ = χ) (hω : ψ ≫ θ = ω)
    (hξ : χ ≫ θ = ξ) (hξ' : φ ≫ ω = ξ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T θ).map (reductionBalance T φ ψ χ hχ P) ≫
        reductionBalance T χ θ ξ hξ P =
      reductionBalance T ψ θ ω hω ((reductionChangeComplex T φ).obj P) ≫
        reductionBalance T φ ω ξ hξ' P := by
  subst χ
  subst ω
  subst ξ
  exact reductionBalance_cocycle T φ ψ θ P

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalarExtension_associativity
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A) :
    (scalarExtensionFunctor h T).map
        ((scalarExtensionFunctor_composition f g T).hom.app K) ≫
      (scalarExtensionFunctor_composition (g.comp f) h T).hom.app K =
    (scalarExtensionFunctor_composition g h T).hom.app
        ((scalarExtensionFunctor f T).obj K) ≫
      (scalarExtensionFunctor_composition f (h.comp g) T).hom.app K := by
  let τ := Functor.whiskerRight (scalarExtensionFunctor_composition f g T).hom
    (scalarExtensionFunctor h T) ≫ (scalarExtensionFunctor_composition (g.comp f) h T).hom
  let σ := Functor.whiskerLeft (scalarExtensionFunctor f T)
    (scalarExtensionFunctor_composition g h T).hom ≫
    (scalarExtensionFunctor_composition f (h.comp g) T).hom
  have heq : τ = σ := by
    apply scalarExtension_kflat_hom_ext T
    intro P hP
    have := scalarExtensionFunctor_kflat_representation (h.comp (g.comp f)) T P hP
    apply (cancel_mono (scalarExtensionFunctorCounit (h.comp (g.comp f)) T P)).mp
    dsimp only [τ, σ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.assoc]
    erw [scalarExtension_composition_normalized (g.comp f) h T P,
      scalarExtension_composition_normalized f (h.comp g) T P]
    erw [← reassoc_of% (scalarExtensionFunctor_composition g h T).hom.naturality
      (scalarExtensionFunctorCounit f T P)]
    erw [reassoc_of% scalarExtension_composition_normalized g h T
      ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)]
    erw [← CategoryTheory.Functor.map_comp_assoc, scalarExtension_composition_normalized]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [reassoc_of% scalarExtensionFunctor_map h T (reductionBalance T
      (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
      (proEtaleConstantRingMap (T := T) (g.comp f))
      (scalarExtensionFunctor_ringMap_comp f g T) P)]
    have hb := scalarExtension_balance_cocycle T
      (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
      (proEtaleConstantRingMap (T := T) h)
      (proEtaleConstantRingMap (T := T) (g.comp f))
      (proEtaleConstantRingMap (T := T) (h.comp g))
      (proEtaleConstantRingMap (T := T) (h.comp (g.comp f)))
      (scalarExtensionFunctor_ringMap_comp f g T)
      (scalarExtensionFunctor_ringMap_comp g h T)
      (scalarExtensionFunctor_ringMap_comp (g.comp f) h T)
      (scalarExtensionFunctor_ringMap_comp f (h.comp g) T) P
    have hb' := congrArg DerivedCategory.Q.map hb
    simp only [CategoryTheory.Functor.map_comp] at hb'
    exact
      congrArg (fun v ↦ (scalarExtensionFunctor h T).map
        ((scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P)) ≫
        (scalarExtensionFunctor h T).map
          (scalarExtensionFunctorCounit g T
            ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)) ≫
        scalarExtensionFunctorCounit h T
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) g)).obj
            ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)) ≫ v) hb'
  exact NatTrans.congr_app heq K

private theorem scalarExtension_balance_unit
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (v : (reductionChangeComplex T
        (proEtaleConstantRingMap (T := T) (RingHom.id B))).obj
          ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ⟶
      (reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)
    (hv : ∀ (i : ℤ) (U : T.ProEtᵒᵖ)
      (s : (proEtaleConstantRing T B).obj.obj U)
      (x : (((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P).X i).val.obj U),
      (v.f i).val.app U (reductionTensorSection T
        (proEtaleConstantRingMap (T := T) (RingHom.id B)) _ U s x) = s • x) :
    reductionBalance T (proEtaleConstantRingMap (T := T) f)
      (proEtaleConstantRingMap (T := T) (RingHom.id B))
      (proEtaleConstantRingMap (T := T) f)
      (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P = v := by
  apply HomologicalComplex.hom_ext
  intro i
  let φ := proEtaleConstantRingMap (T := T) f
  let ψ := proEtaleConstantRingMap (T := T) (RingHom.id B)
  apply ((pbcScalarAdjunction ψ).homEquiv _ _).injective
  apply scalarExtension_tensor_hom_ext T φ
  intro U x
  change ((reductionBalance T φ ψ φ
      (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P).f i).val.app U
      (((pbcScalarAdjunction ψ).unit.app ((reductionChange T φ).obj (P.X i))).val.app U
        (reductionTensorSection T φ (P.X i) U 1 x)) =
    (v.f i).val.app U
      (((pbcScalarAdjunction ψ).unit.app ((reductionChange T φ).obj (P.X i))).val.app U
        (reductionTensorSection T φ (P.X i) U 1 x))
  have hunit := (pbcScalarAdjunction_exists ψ).exists.choose_spec
    ((reductionChange T φ).obj (P.X i)) U (reductionTensorSection T φ (P.X i) U 1 x)
  change ((pbcScalarAdjunction ψ).unit.app ((reductionChange T φ).obj (P.X i))).val.app U
      (reductionTensorSection T φ (P.X i) U 1 x) =
    reductionTensorSection T ψ ((reductionChange T φ).obj (P.X i)) U 1
      (reductionTensorSection T φ (P.X i) U 1 x) at hunit
  rw [hunit]
  have hb := (reductionBalance_exists T φ ψ φ
    (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P).exists.choose_spec.2
      i U 1 1 x
  change ((reductionBalance T φ ψ φ
      (scalarExtensionFunctor_ringMap_comp f (RingHom.id B) T) P).f i).val.app U
      (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X i)) U 1
        (reductionTensorSection T φ (P.X i) U 1 x)) =
    reductionTensorSection T φ (P.X i) U (1 * ψ.hom.app U 1) x at hb
  have hv' := hv i U 1 (reductionTensorSection T φ (P.X i) U 1 x)
  change (v.f i).val.app U
      (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X i)) U 1
        (reductionTensorSection T φ (P.X i) U 1 x)) =
    1 • reductionTensorSection T φ (P.X i) U 1 x at hv'
  simp only [map_one, one_mul, one_smul] at hb hv'
  exact hb.trans hv'.symm

private theorem scalarExtension_identity_normalized
    {A : Type u} [CommRing A] (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    ∃ v : (reductionChangeComplex T
        (proEtaleConstantRingMap (T := T) (RingHom.id A))).obj P ⟶ P,
      (∀ (i : ℤ) (U : T.ProEtᵒᵖ)
        (s : (proEtaleConstantRing T A).obj.obj U) (x : (P.X i).val.obj U),
        (v.f i).val.app U (reductionTensorSection T
          (proEtaleConstantRingMap (T := T) (RingHom.id A)) (P.X i) U s x) = s • x) ∧
      (scalarExtensionFunctor_identity (A := A) T).hom.app (DerivedCategory.Q.obj P) =
        scalarExtensionFunctorCounit (RingHom.id A) T P ≫ DerivedCategory.Q.map v := by
  obtain ⟨ε, hε⟩ := scalarExtension_identity_all_complexes (A := A) T
  have heq : scalarExtensionFunctor_identity (A := A) T = ε :=
    (scalarExtensionFunctor_identity_existsUnique (A := A) T).unique
      (scalarExtensionFunctor_identity_existsUnique (A := A) T).exists.choose_spec
      (fun P _ ↦ hε P)
  rw [heq]
  exact hε P

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalarExtension_unit
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) :
    (scalarExtensionFunctor_composition f (RingHom.id B) T).hom.app K =
      (scalarExtensionFunctor_identity (A := B) T).hom.app
        ((scalarExtensionFunctor f T).obj K) := by
  have heq : (scalarExtensionFunctor_composition f (RingHom.id B) T).hom =
      Functor.whiskerLeft (scalarExtensionFunctor f T)
        (scalarExtensionFunctor_identity (A := B) T).hom := by
    apply scalarExtension_kflat_hom_ext T
    intro P hP
    dsimp only [Functor.whiskerLeft_app]
    have := scalarExtensionFunctor_kflat_representation f T P hP
    apply (cancel_mono (scalarExtensionFunctorCounit f T P)).mp
    obtain ⟨v, hv, hfac⟩ := scalarExtension_identity_normalized (A := B) T
      ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)
    have hbal := scalarExtension_balance_unit f T P v hv
    have hn := (scalarExtensionFunctor_identity (A := B) T).hom.naturality
      (scalarExtensionFunctorCounit f T P)
    change (scalarExtensionFunctor (RingHom.id B) T).map
        (scalarExtensionFunctorCounit f T P) ≫
        (scalarExtensionFunctor_identity (A := B) T).hom.app
          (DerivedCategory.Q.obj
            ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P)) =
      (scalarExtensionFunctor_identity (A := B) T).hom.app
        ((scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P)) ≫
        scalarExtensionFunctorCounit f T P at hn
    erw [scalarExtension_composition_normalized f (RingHom.id B) T P, ← hn, hfac, hbal]
  exact NatTrans.congr_app heq K

/-- The g=id unitor law and the associativity diagram for A→B→C→D.
Source: blueprint proof (4) (blueprint: det-sp-scalar-extension-functor).
Proof: for g=id the balanced map multiplies the two B scalars, which is exactly
the normalized identity unitor. For three maps both paths send d tensor
(c tensor (b tensor p)) to d*h(c)*h(g(b)) tensor p. Multiplicativity of h and
associativity in D identify these coefficients. Equality on local pure tensors
gives equality of chain maps; localization and the K-flat normalization descend
this equality to all derived objects. This is the rebracketing coherence, and
iterating it gives the pentagon with the usual unit identifications. -/
theorem scalarExtensionFunctor_coherence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    (∀ K : proEtaleDerivedCategory T A,
      (scalarExtensionFunctor_composition f (RingHom.id B) T).hom.app K =
        (scalarExtensionFunctor_identity (A := B) T).hom.app
          ((scalarExtensionFunctor f T).obj K)) ∧
    (∀ (D : Type u) [CommRing D] (h : C →+* D) (K : proEtaleDerivedCategory T A),
      (scalarExtensionFunctor h T).map
          ((scalarExtensionFunctor_composition f g T).hom.app K) ≫
        (scalarExtensionFunctor_composition (g.comp f) h T).hom.app K =
      (scalarExtensionFunctor_composition g h T).hom.app
          ((scalarExtensionFunctor f T).obj K) ≫
        (scalarExtensionFunctor_composition f (h.comp g) T).hom.app K) := by
  exact ⟨scalarExtension_unit f T, fun D _ h K ↦ scalarExtension_associativity f g h T K⟩

end AlgebraicGeometry.ProEtale
