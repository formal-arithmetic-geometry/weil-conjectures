/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.DualizingComplexId
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation

/-!
# Verdier biduality at a separably closed point

For a separably closed field `k`, the double-dual morphism of `Spec k` over itself is an
isomorphism on `Dctf(Spec k, Λ)` (blueprint `lem-weil-coefficient-frobenius`).

Every object of `Dctf(Spec k, Λ)` is dualizable: it is represented by a bounded complex of flat
constructible sheaves, and over a separably closed field such a sheaf is the constant sheaf on a
finite flat, hence finite projective, `Λ`-module, which is dualizable. Since the dualizing
complex of `Spec k` over itself is the unit, the double-dual morphism is then the biduality map
of a dualizable object, an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- A zero object is dualizable, being its own dual with zero evaluation and coevaluation. -/
theorem isDualizable_of_isZero {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] {X : C} (hX : IsZero X) : IsDualizable X :=
  ⟨{ rightDual := X
     exact :=
       { coevaluation' := 0
         evaluation' := 0
         coevaluation_evaluation' := (hX.of_iso (ρ_ X)).eq_of_src _ _
         evaluation_coevaluation' := (hX.of_iso (λ_ X)).eq_of_src _ _ } }⟩

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- The double-dual map `X ⟶ [[X, W], W]` is an isomorphism if and only if the double-dual map
relative to an isomorphic object `W'` is: the two differ by isomorphisms
(`CategoryTheory.MonoidalClosed.toIhomIhom_comp_ihom_map`). -/
lemma isIso_toIhomIhom_iff_of_iso {W W' : C} (e : W ≅ W') (X : C) :
    IsIso (toIhomIhom W X) ↔ IsIso (toIhomIhom W' X) := by
  have : IsIso (pre ((ihom X).map e.hom)) :=
    ⟨pre ((ihom X).map e.inv), by simp [← pre_map, ← Functor.map_comp],
      by simp [← pre_map, ← Functor.map_comp]⟩
  rw [← isIso_comp_right_iff (toIhomIhom W X) ((ihom _).map e.hom), toIhomIhom_comp_ihom_map,
    isIso_comp_right_iff]

end MonoidalClosed

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance] derivedBraidedCategory

section General

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- For the identity of a scheme `S`, the double-dual morphism `K ⟶ 𝔻 𝔻 K` is an isomorphism
for every dualizable `K`: the dualizing complex of `S` over itself is the unit
(`AlgebraicGeometry.Etale.dualizingComplexIdIso`), and the biduality map
`K ⟶ [[K, 𝟙], 𝟙]` of a dualizable object is an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_id_of_isDualizable (S : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)} (hK : IsDualizable K) :
    IsIso ((verdierDualDoubleDual A (𝟙 S)).app K) := by
  obtain ⟨_⟩ := hK
  exact (MonoidalClosed.isIso_toIhomIhom_iff_of_iso (dualizingComplexIdIso A S) K).2
    (MonoidalClosed.isIso_toIhomIhomUnit K)

end General

/-- A constructible sheaf of `Λ`-modules on a nonempty scheme `X` has a geometric point at which
its stalk is finitely generated: a point of `X` lies in a stratum, on which the sheaf is finite
locally constant, and the stalk of the pullback to the stratum is the stalk of the sheaf. -/
theorem exists_isFinitelyGenerated_sheafFiber_of_isConstructibleSheaf {X : Scheme.{u}}
    [Nonempty X] {R : Type (u + 1)} [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [IsConstructibleSheaf F] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
      ConcreteCategory.IsFinitelyGenerated ((pointSmallEtale s).sheafFiber.obj F) := by
  obtain ⟨S, hS⟩ := ‹IsConstructibleSheaf F›.exists_stratification
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (Classical.arbitrary X))
  rw [← S.range_immersion i] at hi
  obtain ⟨y, -⟩ := hi
  have := hS i
  let s : Spec (.of (SeparableClosure ((S.domain i).residueField y))) ⟶ S.domain i :=
    (SpecToEquivOfField (SeparableClosure ((S.domain i).residueField y)) _).2
      ⟨y, CommRingCat.ofHom (algebraMap ((S.domain i).residueField y) _)⟩
  exact ⟨_, _, inferInstance, s ≫ S.immersion i,
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} R ↦ M →ₗ[R] N) (CA := fun M : ModuleCat.{u + 1} R ↦ M)
      (F := (Etale.upperStar _ (S.immersion i)).obj F) _ s).of_iso
      ((Etale.upperStarCompSheafFiberIso _ (S.immersion i) s).app F)⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Over a separably closed field `k`, a flat constructible étale sheaf of `Λ`-modules on
`Spec k` is dualizable: it is the constant sheaf on its module of global sections `M`
(`AlgebraicGeometry.Scheme.isEquivalence_constantSheaf_of_isSepClosed`), which is flat, the
constant sheaf functor being a monoidal equivalence, and finite, being a stalk of the constructible
sheaf (`AlgebraicGeometry.Etale.exists_isFinitelyGenerated_sheafFiber_of_isConstructibleSheaf`).
So `M` is finite projective over the Noetherian ring `Λ`, hence dualizable, and the monoidal
constant sheaf functor preserves dualizability. -/
theorem isDualizable_of_flat_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] (hF : ObjectProperty.flat F) : IsDualizable F := by
  let c := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let M := c.asEquivalence.inverse.obj F
  let e : c.obj M ≅ F := c.asEquivalence.counitIso.app F
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} (Spec (.of k)).Etale := locallySmall_self _
  obtain ⟨Ω, _, _, s, hs⟩ := exists_isFinitelyGenerated_sheafFiber_of_isConstructibleSheaf F
  have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).1 (hs.of_iso
    ((pointSmallEtale s).sheafFiber.mapIso e.symm ≪≫
      (pointSmallEtale s).sheafFiberConstantSheafIso M))
  have : c.asEquivalence.functor.Monoidal := (inferInstance : c.Monoidal)
  have := c.asEquivalence.inverseMonoidal
  have : Module.Flat Λ M := (ModuleCat.flat_iff_flat M).1
    ((Functor.preservesFlat_of_isEquivalence c.asEquivalence.inverse).flat_obj hF)
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  have : Module.Projective Λ M := Module.Flat.projective_of_finitePresentation
  exact (IsDualizable.map c (ModuleCat.isDualizable_of_projective M)).of_iso e

/-- Over a separably closed field `k`, every object of `Dctf(Spec k, Λ)` is dualizable: it is
represented by a bounded complex of flat constructible sheaves
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`), whose terms are
dualizable (`AlgebraicGeometry.Etale.isDualizable_of_flat_of_isSepClosed`), and a bounded
complex of dualizable objects is dualizable in the derived category
(`DerivedCategory.isDualizable_Q_obj`). -/
theorem isDualizable_of_constructibleFiniteTor_of_isSepClosed {k : Type u} [Field k]
    [IsSepClosed k]
    {K : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) K) : IsDualizable K := by
  obtain ⟨a, b, ⟨⟨hbc, hab⟩, hta⟩⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  by_cases hab' : a ≤ b
  swap
  · have : K.IsGE a := hab.1
    have : K.IsLE b := hab.2
    exact isDualizable_of_isZero (_root_.DerivedCategory.TStructure.t.isZero K b a (by omega))
  obtain ⟨P, ⟨hPz, hPflat⟩, hPc, ⟨e⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel
    Λ a b hab' K hbc).1 (hasTorAmplitudeIn_of_torAmplitudeIn hta)
  have : P.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hPz i (.inl hi)
  have : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hPz i (.inr hi)
  refine IsDualizable.of_iso e.symm (_root_.DerivedCategory.isDualizable_Q_obj P a b fun n ↦ ?_)
  have := hPc n
  exact isDualizable_of_flat_of_isSepClosed Λ (P.X n) (hPflat n)

/-- Blueprint `lem-weil-coefficient-frobenius`, at the separably closed point: for a separably
closed field `k` and `K ∈ Dctf(Spec k, Λ)`, the double-dual morphism `K ⟶ 𝔻 𝔻 K` of the point
`Spec k` over itself is an isomorphism: under `RΓ(Spec k, -)` it is derived evaluation into the
coefficient double dual of a perfect complex of `Λ`-modules. -/
theorem isIso_verdierDualDoubleDual_app_id_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {K : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (𝟙 (Spec (.of k)))).app K) :=
  isIso_verdierDualDoubleDual_app_id_of_isDualizable _ _
    (isDualizable_of_constructibleFiniteTor_of_isSepClosed Λ hK)

end Etale

end AlgebraicGeometry
