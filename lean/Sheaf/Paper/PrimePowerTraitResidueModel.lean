/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Sheaf.FieldTheory.CanonicalTraitTameCharacter
public import Sheaf.Paper.TraitResidueModel
public import Sheaf.AlgebraicGeometry.TraitSheafGluing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Module.ZMod
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# The prime-power trait residue model

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, 1.2.1--1.2.3,
Propositions 1.2.1.2 and 1.2.2.1, and Lemma 1.2.3.2, printed pages 259--262.
(blueprint: lem-per-prime-power-trait-residue-model).

The auxiliary records use the published completed group algebra and its canonical action,
and specify the residue normalization equations on actual stalks and Tate coordinates.
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.all false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped MonoidAlgebra

namespace AlgebraicGeometry.Etale

/-- The canonical tame character, specified on every compatible uniformizer-root family.
Source: ILO XVII 1.2, p. 259 (blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueTameCharacter (R K Ks Ω : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks] [Field Ω] [Algebra Ks Ω] where
  character : Gal(Ks/K) →* TameRoots.limitSubgroup Ω (ringExpChar (IsLocalRing.ResidueField R))
  continuous_character : Continuous character
  surjective_character : Function.Surjective character
  roots_exist : ∀ π : R, Irreducible π →
    ∃ α : TameRoots.Order (ringExpChar (IsLocalRing.ResidueField R)) → Ks,
      (∀ d, α d ^ d.val = algebraMap K Ks (algebraMap R K π)) ∧
      (∀ d e, d.val ∣ e.val → α e ^ (e.val / d.val) = α d)
  root_formula : ∀ (π : R), Irreducible π → ∀ α :
    TameRoots.Order (ringExpChar (IsLocalRing.ResidueField R)) → Ks,
    (∀ d, α d ^ d.val = algebraMap K Ks (algebraMap R K π)) →
    (∀ d e, d.val ∣ e.val → α e ^ (e.val / d.val) = α d) →
    ∀ (h : Gal(Ks/K)) d,
      ((character h).val d : Ω) = algebraMap Ks Ω (h (α d) / α d)
  pro_p : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (f : character.ker →* Q), Continuous f → Function.Surjective f →
      ∃ a : ℕ, Nat.card Q = ringExpChar (IsLocalRing.ResidueField R) ^ a
  char_zero : ringExpChar (IsLocalRing.ResidueField R) = 1 → character.ker = ⊥
  generator : Nonempty {σ : TameRoots.limitSubgroup Ω
    (ringExpChar (IsLocalRing.ResidueField R)) // traitIsGenerator σ}

/-- The geometric generic point, using the chosen fraction-field tower. Source: ILO XVII 1.2
(blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable abbrev traitResidueGenericPoint (R K Ω : Type u)
    [CommRing R] [Field K] [Field Ω] [Algebra R K] [Algebra K Ω] :
    Spec (.of Ω) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap K Ω).comp (algebraMap R K)))

/-- The underlying generic module of a discrete-representation-valued functor.
Source: ILO XVII 1.2.2 (blueprint: lem-per-prime-power-trait-residue-model). -/
abbrev traitResidueUnderlying {C : Type v} [Category C]
    (Λ : Type (u + 1)) [CommRing Λ] (H : Type u) [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (V : C ⥤ Rep.DiscreteContinuousRep.{u + 1, u, u + 1} Λ H) :=
  V ⋙ traitDiscreteRepInclusion Λ H ⋙ forget₂ (Rep.{u + 1} Λ H) (ModuleCat.{u + 1} Λ)

/-- Stalks, their actual Galois action on germs, and the specialization of a closed germ.
The equation on global sections fixes specialization: on a strictly local scheme every
closed germ has a unique global representative. Source: ILO XVII 1.2.2
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitPrimePowerStalkData (R K Ks Ω Ωs : Type u) [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] (s : Spec (.of Ωs) ⟶ Spec (.of R))
    (Λ : Type (u + 1)) [CommRing Λ] where
  generic : TraitSheaves Λ R ⥤
    Rep.DiscreteContinuousRep.{u + 1, u, u + 1} Λ (Gal(Ks/K))
  genericIso : traitResidueUnderlying Λ (Gal(Ks/K)) generic ≅
    (Scheme.pointSmallEtale (traitResidueGenericPoint R K Ω)).sheafFiber
  underlying_additive : (traitResidueUnderlying Λ (Gal(Ks/K)) generic).Additive
  underlying_limits : PreservesFiniteLimits
    (traitResidueUnderlying Λ (Gal(Ks/K)) generic)
  underlying_colimits : PreservesFiniteColimits
    (traitResidueUnderlying Λ (Gal(Ks/K)) generic)
  specialization : (Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ) ⟶
    traitResidueUnderlying Λ (Gal(Ks/K)) generic
  invariant : ∀ (M : TraitSheaves Λ R) (w :
    ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj M) (h : Gal(Ks/K)),
    (generic.obj M).obj.ρ h (specialization.app M w) = specialization.app M w
  specialization_germ : ∀ (M : TraitSheaves Λ R)
    (m : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj M),
    genericIso.hom.app M (specialization.app M (traitGlobalGerm Λ s M m)) =
      traitGlobalGerm Λ (traitResidueGenericPoint R K Ω) M m
  action_germ : ∀ (M : TraitSheaves Λ R) (h : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
    (algebraMap Ks Ω).comp h.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω) →
    ∀ (X : (Spec (.of R)).Etale)
      (x x' : (Scheme.pointSmallEtale (traitResidueGenericPoint R K Ω)).fiber.obj X),
    x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
    ∀ z : M.obj.obj (op X),
    genericIso.hom.app M ((generic.obj M).obj.ρ h
      (genericIso.inv.app M ((Scheme.pointSmallEtale
        (traitResidueGenericPoint R K Ω)).toPresheafFiber X x M.obj z))) =
      (Scheme.pointSmallEtale (traitResidueGenericPoint R K Ω)).toPresheafFiber X x' M.obj z

attribute [instance] TraitPrimePowerStalkData.underlying_additive
  TraitPrimePowerStalkData.underlying_limits TraitPrimePowerStalkData.underlying_colimits

/-- Wild invariants use the published restriction and invariants functors.
Source: ILO XVII 1.2.2 (blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable abbrev traitResidueWild {C : Type v} [Category C]
    (Λ : Type (u + 1)) [CommRing Λ] (H G : Type u) [Group H] [Group G]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (V : C ⥤ Rep.DiscreteContinuousRep.{u + 1, u, u + 1} Λ H) (t : H →* G) :=
  V ⋙ traitDiscreteRepInclusion Λ H ⋙ Rep.resFunctor t.ker.subtype ⋙
    Rep.invariantsFunctor Λ t.ker

/-- The final term uses the published completed algebra and augmentation ideal.
Source: ILO XVII 1.2.2 (blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable def traitResidueHom {C : Type v} [Category C]
    (Λ : Type (u + 1)) [CommRing Λ] (G : Type u) [CommGroup G] [TopologicalSpace G]
    (N : C ⥤ ModuleCat.{u + 1} (Rep.CompletedAugmentation.Algebra Λ G)) :=
  N ⋙ (linearCoyoneda (Rep.CompletedAugmentation.Algebra Λ G)
    (ModuleCat.{u + 1} (Rep.CompletedAugmentation.Algebra Λ G))).obj
      (op (ModuleCat.of (Rep.CompletedAugmentation.Algebra Λ G)
        (Rep.CompletedAugmentation.Ideal Λ G))) ⋙
    ModuleCat.restrictScalars (algebraMap Λ (Rep.CompletedAugmentation.Algebra Λ G))

/-- Negative twist by the coefficient root line, with no equivariance condition on Hom.
Source: ILO XVII 1.2.3 (blueprint: lem-per-prime-power-trait-residue-model). -/
abbrev traitResidueNegative {C : Type v} [Category C]
    {Λ : Type (u + 1)} [CommRing Λ] (K : ModuleCat.{u + 1} Λ)
    (V : C ⥤ ModuleCat.{u + 1} Λ) :=
  V ⋙ (linearCoyoneda Λ (ModuleCat.{u + 1} Λ)).obj (op K)

/-- Totalization specified by its coproduct universal property and signed differential.
This is a coordinate interface for the usual direct-sum total complex, and fixes its
morphism on every summand. Source: ILO XVII Proposition 1.2.2.1
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueTotal (C : Type v) [Category C] [Preadditive C]
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : CochainComplex (C ⥤ ModuleCat.{u + 1} Λ) ℤ) where
  total : CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ
  inclusion : ∀ (L : CochainComplex C ℤ) (i j : ℤ),
    (F.X i).obj (L.X j) ⟶ (total.obj L).X (i + j)
  coproduct : ∀ (L : CochainComplex C ℤ) (n : ℤ),
    IsColimit (Cofan.mk ((total.obj L).X n)
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
        inclusion L ij.val.1 ij.val.2 ≫ eqToHom (by rw [ij.property])))
  differential : ∀ (L : CochainComplex C ℤ) (i j : ℤ),
    inclusion L i j ≫ (total.obj L).d (i + j) (i + j + 1) =
      (F.d i (i + 1)).app (L.X j) ≫
        inclusion L (i + 1) j ≫
          eqToHom (by simp [add_assoc, add_comm, add_left_comm]) +
      (-1 : ℤ) ^ i.natAbs •
        ((F.X i).map (L.d j (j + 1)) ≫
          inclusion L i (j + 1) ≫ eqToHom (by simp [add_assoc]))
  map_inclusion : ∀ {K K' : CochainComplex C ℤ} (f : K ⟶ K') (i j : ℤ),
    inclusion K i j ≫ (total.map f).f (i + j) =
      (F.X i).map (f.f j) ≫ inclusion K' i j


/-- The continuous additive characters, with discrete target and no equivariance condition.
Source: ILO XVII 1.2.3 (blueprint: lem-per-prime-power-trait-residue-model). -/
def TraitContinuousCharacters (G : Type u) [CommGroup G] [TopologicalSpace G]
    {Λ : Type (u + 1)} [CommRing Λ] (N : ModuleCat.{u + 1} Λ) :=
  {f : G →* Multiplicative N // @Continuous G (Multiplicative N) inferInstance ⊥ f}

/-- Descent of the actual wild invariants to the tame quotient, and a module-category
realization of their published canonical completed action. No completed algebra or action
is chosen: the last equation uses `Rep.CompletedAugmentation.action` itself.
Source: ILO XVII 1.2.1--1.2.2
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitPrimePowerWildData {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    {G : Type u} [CommGroup G] [TopologicalSpace G] (t : Gal(Ks/K) →* G) where
  [topologicalGroup : IsTopologicalGroup G]
  [compact : CompactSpace G]
  [hausdorff : T2Space G]
  [totallyDisconnected : TotallyDisconnectedSpace G]
  [finiteCoefficients : Finite Λ]
  tame : TraitSheaves Λ R ⥤ Rep.DiscreteContinuousRep.{u + 1, u, u + 1} Λ G
  tameUnderlying : traitResidueUnderlying Λ G tame ≅
    traitResidueWild Λ (Gal(Ks/K)) G D.generic t
  descent : ∀ (M : TraitSheaves Λ R) (h : Gal(Ks/K)) (x : (tame.obj M).obj.V),
    (tameUnderlying.hom.app M ((tame.obj M).obj.ρ (t h) x)).val =
      (D.generic.obj M).obj.ρ h (tameUnderlying.hom.app M x).val
  moduleFunctor : TraitSheaves Λ R ⥤
    ModuleCat.{u + 1} (Rep.CompletedAugmentation.Algebra Λ G)
  underlying : moduleFunctor ⋙
      ModuleCat.restrictScalars (algebraMap Λ (Rep.CompletedAugmentation.Algebra Λ G)) ≅
    traitResidueWild Λ (Gal(Ks/K)) G D.generic t
  completed_action : ∀ (M : TraitSheaves Λ R)
      (a : Rep.CompletedAugmentation.Algebra Λ G) (x : moduleFunctor.obj M),
    underlying.hom.app M (a • x) = tameUnderlying.hom.app M
      (Rep.CompletedAugmentation.action Λ G (tame.obj M) a
        (tameUnderlying.inv.app M (underlying.hom.app M x)))

/-- The exact three-term row, its specified arrows, and its finite-width totalization.
All degree identifications are natural in the sheaf. Source: ILO XVII 1.2.2,
Proposition 1.2.2.1 (blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueRow {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    {G : Type u} [CommGroup G] [TopologicalSpace G]
    {t : Gal(Ks/K) →* G}
    (N : TraitPrimePowerWildData D t) where
  row : CochainComplex (TraitSheaves Λ R ⥤ ModuleCat.{u + 1} Λ) ℤ
  closed : row.X 0 ≅ (Scheme.pointSmallEtale s).sheafFiber
  wild : row.X 1 ≅ traitResidueWild Λ (Gal(Ks/K)) G D.generic t
  hom : row.X 2 ≅ traitResidueHom Λ G N.moduleFunctor
  outside : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → IsZero (row.X i)
  first_differential : ∀ (M : TraitSheaves Λ R) (x : (row.X 0).obj M),
    (wild.hom.app M ((row.d 0 1).app M x)).val =
      D.specialization.app M (closed.hom.app M x)
  last_differential : ∀ (M : TraitSheaves Λ R) (x : (row.X 1).obj M)
      (a : Rep.CompletedAugmentation.Ideal Λ G),
    (hom.hom.app M ((row.d 1 2).app M x)).hom a =
      a.val • (@id (N.moduleFunctor.obj M)
        (N.underlying.inv.app M (wild.hom.app M x)))
  additive : ∀ i : ℤ, (row.X i).Additive
  exact_limits : ∀ i : ℤ, PreservesFiniteLimits (row.X i)
  exact_colimits : ∀ i : ℤ, PreservesFiniteColimits (row.X i)
  totalization : TraitResidueTotal (TraitSheaves Λ R) Λ row
  quasi_isomorphisms : ∀ {K K' : CochainComplex (TraitSheaves Λ R) ℤ}
    (f : K ⟶ K'), QuasiIso f → QuasiIso (totalization.total.map f)
  bounded_below : ∀ L : CochainComplex (TraitSheaves Λ R) ℤ,
    CochainComplex.plus _ L → CochainComplex.plus _ (totalization.total.obj L)

/-- Averaging is natural and normalized on every finite wild quotient fixing a vector.
Multiplication by its order avoids choosing an inverse or quotient representatives.
Source: ILO XVII 1.2.2--1.2.3
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueAverage {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    {G : Type u} [CommGroup G] [TopologicalSpace G] (t : Gal(Ks/K) →* G) where
  projector : traitResidueUnderlying Λ (Gal(Ks/K)) D.generic ⟶
    traitResidueWild Λ (Gal(Ks/K)) G D.generic t
  fixes : ∀ (M : TraitSheaves Λ R)
    (x : (traitResidueWild Λ (Gal(Ks/K)) G D.generic t).obj M),
    projector.app M x.val = x
  finite_formula : ∀ (M : TraitSheaves Λ R)
      (x : (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).obj M)
      (U : OpenNormalSubgroup t.ker) [Fintype (t.ker ⧸ U.toSubgroup)]
      (r : (t.ker ⧸ U.toSubgroup) → t.ker),
    (∀ a, QuotientGroup.mk (r a) = a) →
    (∀ h : U.toSubgroup, (D.generic.obj M).obj.ρ h.val.val x = x) →
    Fintype.card (t.ker ⧸ U.toSubgroup) • (projector.app M x).val =
      ∑ a, (D.generic.obj M).obj.ρ (r a).val x

/-- The actual Tate stalk and its canonical root coordinates. The displayed germ formula
fixes the additive identification with roots, including the coefficient and sign.
Source: ILO XVII 1.2.3; Stacks Tag 03PK
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueTate (R K Ω : Type u) [CommRing R] [Field K] [Field Ω]
    [Algebra R K] [Algebra K Ω] [IsAlgClosed Ω]
    (Λ : Type (u + 1)) [CommRing Λ] (q p : ℕ) (hq : (q : Λ) = 0)
    (hqp : 0 < q ∧ q.Coprime p) where
  line : ModuleCat.{u + 1} Λ
  stalk : line ≅ (Scheme.pointSmallEtale (traitResidueGenericPoint R K Ω)).sheafFiber.obj
    (Scheme.finiteEtaleTateSheaf Λ q (Spec (.of R)) hq 1)
  roots : line ≃+ Additive (rootsOfUnity q Ω)
  germ : ∀ (W : (Spec (.of R)).Etale)
    (x : (Scheme.pointSmallEtale (traitResidueGenericPoint R K Ω)).fiber.obj W)
    (z : ((Spec (.of R)).rootsOfUnitySheaf q).obj.obj (op W)),
    (((roots (stalk.inv ((Scheme.pointSmallEtale
        (traitResidueGenericPoint R K Ω)).toPresheafFiber W x
          (Scheme.finiteEtaleTateSheaf Λ q (Spec (.of R)) hq 1).obj
          (Scheme.finiteEtaleTateOneGenerator Λ q (Spec (.of R)) hq (op W) 1 z)))).toMul).val
        : Ωˣ) =
      Units.map (((x.left.appTop) ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)
        (((kernel.ι (q • 𝟙 (Spec (.of R)).gmSheaf)).hom.app (op W) z).down.toMul)
  coordinate : TameRoots.limitSubgroup Ω p →* Multiplicative line
  coordinate_formula : ∀ g : TameRoots.limitSubgroup Ω p,
    (((roots (Multiplicative.toAdd (coordinate g))).toMul).val : Ωˣ) =
      g.val ⟨q, hqp⟩
  free_rank_one : Nonempty (line ≃ₗ[Λ] Λ)
  twist_limits : PreservesFiniteLimits (tensorRight line)
  characters : ∀ N : ModuleCat.{u + 1} Λ,
    (line →ₗ[Λ] N) ≃ TraitContinuousCharacters (TameRoots.limitSubgroup Ω p) N
  character_formula : ∀ (N : ModuleCat.{u + 1} Λ) (f : line →ₗ[Λ] N)
      (g : TameRoots.limitSubgroup Ω p),
    Multiplicative.toAdd ((characters N f).val g) =
      f (Multiplicative.toAdd (coordinate g))


attribute [instance] TraitResidueTate.twist_limits

/-- Generator-normalized residue maps, with homotopies in the category of functors.
Thus uniqueness means uniqueness of a homotopy natural in every sheaf, rather than
uniqueness at a single module. Source: ILO XVII Lemma 1.2.3.2
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueCochain {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    {p q : ℕ} {hq : (q : Λ) = 0} {hqp : 0 < q ∧ q.Coprime p}
    (T : TraitResidueTate R K Ω Λ q p hq hqp)
    {t : Gal(Ks/K) →* TameRoots.limitSubgroup Ω p}
    (N : TraitPrimePowerWildData D t) (F : TraitResidueRow D N)
    (av : TraitResidueAverage D t) where
  generatorIdeal : ∀ _σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ},
    Rep.CompletedAugmentation.Algebra Λ (TameRoots.limitSubgroup Ω p) ≃ₗ[
      Rep.CompletedAugmentation.Algebra Λ (TameRoots.limitSubgroup Ω p)]
        Rep.CompletedAugmentation.Ideal Λ (TameRoots.limitSubgroup Ω p)
  generatorIdeal_formula : ∀ (σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ})
      (a : Rep.CompletedAugmentation.Algebra Λ (TameRoots.limitSubgroup Ω p)),
    (generatorIdeal σ a).val = (1 - Rep.CompletedAugmentation.groupElement Λ _ σ.val) * a
  residue : ∀ _σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ},
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (traitResidueNegative T.line (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic)) ⟶
      F.row⟦(2 : ℤ)⟧
  residue_formula : ∀ (σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ})
      (M : TraitSheaves Λ R)
      (f : (traitResidueNegative T.line
        (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic)).obj M),
    (F.hom.hom.app M (((residue σ).f 0).app M
      ((HomologicalComplex.singleObjXSelf
        (V := TraitSheaves Λ R ⥤ ModuleCat.{u + 1} Λ) (ComplexShape.up ℤ) 0
        (traitResidueNegative T.line
          (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic))).inv.app M f))).hom
        (generatorIdeal σ 1) =
      @id (N.moduleFunctor.obj M)
        (N.underlying.inv.app M (av.projector.app M
          (f.hom (Multiplicative.toAdd (T.coordinate σ.val)))))
  unique_natural_homotopy : ∀ σ τ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ},
    Nonempty (Homotopy (residue σ) (residue τ)) ∧
      Subsingleton (Homotopy (residue σ) (residue τ))
  totalResidue : ∀ _σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ},
    (traitResidueNegative T.line
      (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶ F.totalization.total ⋙ shiftFunctor _ (2 : ℤ)
  totalResidue_formula : ∀ (σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ})
      (L : CochainComplex (TraitSheaves Λ R) ℤ) (j : ℤ),
    ((totalResidue σ).app L).f j =
      (HomologicalComplex.singleObjXSelf
        (V := TraitSheaves Λ R ⥤ ModuleCat.{u + 1} Λ) (ComplexShape.up ℤ) 0
        (traitResidueNegative T.line
          (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic))).inv.app (L.X j) ≫
        ((residue σ).f 0).app (L.X j) ≫
          F.totalization.inclusion L 2 j ≫
            eqToHom (congrArg (F.totalization.total.obj L).X (add_comm 2 j))
  evaluation : traitResidueNegative T.line (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic) ⋙
      tensorRight T.line ≅ traitResidueUnderlying Λ (Gal(Ks/K)) D.generic
  evaluation_formula : ∀ (M : TraitSheaves Λ R)
      (f : (traitResidueNegative T.line
        (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic)).obj M) (z : T.line),
    evaluation.hom.app M (f ⊗ₜ[Λ] z) = f.hom z
  positiveResidue : ∀ _σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ},
    (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      F.totalization.total ⋙ (tensorRight T.line).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ shiftFunctor _ (2 : ℤ)
  positiveResidue_formula : ∀ (σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ})
      (L : CochainComplex (TraitSheaves Λ R) ℤ) (j : ℤ),
    ((positiveResidue σ).app L).f j =
      evaluation.inv.app (L.X j) ≫ (tensorRight T.line).map (((totalResidue σ).app L).f j)

/-- The canonical derived-support comparison map on a bounded below representing complex.
It is the ordinary right-derived unit, transported through the published localization
comparison isomorphisms. Source: ILO XVII Proposition 1.2.2.1
(blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable def traitResidueSupportUnit (R : Type u) [CommRing R]
    (Λ : Type (u + 1)) [CommRing Λ] (π : R)
    (K : CochainComplex.Plus (TraitSheaves Λ R)) :
    DerivedCategory.Q.obj (((supportedEtaleSections Λ (Spec (.of R))
      (PrimeSpectrum.basicOpen π)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) ⟶
      (derivedSupportedEtaleSections Λ (Spec (.of R)) (PrimeSpectrum.basicOpen π)).obj
        (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app _ ≫
    DerivedCategory.Qh.map
      (((supportedEtaleSections Λ (Spec (.of R))
        (PrimeSpectrum.basicOpen π)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          K.obj) ≫
    DerivedCategory.Plus.ι.map
      ((supportedEtaleSections Λ (Spec (.of R))
        (PrimeSpectrum.basicOpen π)).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient (TraitSheaves Λ R)).obj K))


/-- The total row represents the published right-derived supported-section functor.
The augmentation equation pins the comparison to the ordinary kernel inclusion and
right-derived unit. The residue descends for every representing complex and generator.
Source: ILO XVII Proposition 1.2.2.1 and Definition 1.2.3.1
(blueprint: lem-per-prime-power-trait-residue-model). -/
structure TraitResidueDerived {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    {p q : ℕ} {hq : (q : Λ) = 0} {hqp : 0 < q ∧ q.Coprime p}
    (T : TraitResidueTate R K Ω Λ q p hq hqp)
    {t : Gal(Ks/K) →* TameRoots.limitSubgroup Ω p}
    {N : TraitPrimePowerWildData D t} (F : TraitResidueRow D N)
    {av : TraitResidueAverage D t} (c : TraitResidueCochain D T N F av) (π : R) where
  model : DerivedCategory.Plus (TraitSheaves Λ R) ⥤
    DerivedCategory (ModuleCat.{u + 1} Λ)
  factors : CochainComplex.Plus.ι _ ⋙ F.totalization.total ⋙ DerivedCategory.Q ≅
    DerivedCategory.Plus.Q ⋙ model
  comparison : model ≅ derivedSupportedEtaleSections Λ (Spec (.of R))
    (PrimeSpectrum.basicOpen π)
  augmentation :
    (supportedEtaleSections Λ (Spec (.of R)) (PrimeSpectrum.basicOpen π)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶ F.totalization.total
  augmentation_formula : ∀ (L : CochainComplex (TraitSheaves Λ R) ℤ)
      (j : ℤ),
    ((augmentation.app L).f j) =
      (supportedEtaleSectionsι Λ (Spec (.of R)) (PrimeSpectrum.basicOpen π)).app (L.X j) ≫
        traitGlobalGerm Λ s (L.X j) ≫ F.closed.inv.app (L.X j) ≫
          F.totalization.inclusion L 0 j ≫ eqToHom (congrArg _ (zero_add j))
  comparison_normalization : ∀ L : CochainComplex.Plus (TraitSheaves Λ R),
    DerivedCategory.Q.map (augmentation.app L.obj) ≫ factors.hom.app L ≫
        comparison.hom.app (DerivedCategory.Plus.Q.obj L) =
      traitResidueSupportUnit R Λ π L
  negative : DerivedCategory.Plus (TraitSheaves Λ R) ⥤
    DerivedCategory (ModuleCat.{u + 1} Λ)
  negative_factors : CochainComplex.Plus.ι _ ⋙
      (traitResidueNegative T.line
        (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Plus.Q ⋙ negative
  negativeResidue : negative ⟶ model ⋙ shiftFunctor _ (2 : ℤ)
  negativeResidue_normalization : ∀ (σ : {σ : TameRoots.limitSubgroup Ω p // traitIsGenerator σ})
      (L : CochainComplex.Plus (TraitSheaves Λ R)),
    negative_factors.hom.app L ≫ negativeResidue.app (DerivedCategory.Plus.Q.obj L) =
      DerivedCategory.Q.map ((c.totalResidue σ).app L.obj) ≫
        ((DerivedCategory.Q (C := ModuleCat.{u + 1} Λ)).commShiftIso (2 : ℤ)).hom.app _ ≫
          (shiftFunctor _ (2 : ℤ)).map (factors.hom.app L)



/-- The derived geometric generic stalk on an actual bounded below representative.
Source: ILO XVII 1.2.3 (blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable def traitResidueGenericFactors {R K Ks Ω Ωs : Type u} [CommRing R]
    [Field K] [Algebra R K] [Field Ks] [Algebra K Ks]
    [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsAlgClosed Ω]
    [Field Ωs] [IsAlgClosed Ωs] {s : Spec (.of Ωs) ⟶ Spec (.of R)}
    {Λ : Type (u + 1)} [CommRing Λ]
    (D : TraitPrimePowerStalkData R K Ks Ω Ωs s Λ)
    (L : CochainComplex.Plus (TraitSheaves Λ R)) :
    DerivedCategory.Q.obj
      (((traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj) ≅
      (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).mapDerivedCategory.obj
        ((DerivedCategory.Plus.Q.obj L).obj) :=
  (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).mapDerivedCategoryFactors.symm.app L.obj ≪≫
    (traitResidueUnderlying Λ (Gal(Ks/K)) D.generic).mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso (TraitSheaves Λ R)).symm.app L.obj)

/-- Prime-power coefficient modules use the common small-etale coefficient universe.
Source: ILO XVII 1.2, coefficient integer q = ell^n
(blueprint: lem-per-prime-power-trait-residue-model). -/
abbrev TraitPrimePowerCoefficients (ell n : ℕ) := ULift.{u + 1} (ZMod (ell ^ n))

/-- The specified coefficient ring is annihilated by the specified integer.
Source: ILO XVII 1.2 (blueprint: lem-per-prime-power-trait-residue-model).
Proof: `ell^n` is zero in `ZMod (ell^n)` by the quotient definition; the ring equivalence
with `ULift` preserves natural-number casts and zero. -/
theorem traitPrimePowerCoefficients_annihilated (ell n : ℕ) :
    ((ell ^ n : ℕ) : TraitPrimePowerCoefficients.{u} ell n) = 0 := by
  sorry

/-- A fixed uniformizer used to present the generic complement of the closed point.
The choice is made from Mathlib's nonempty uniformizer theorem, so no proposition is
used as data. Source: Mathlib `IsDiscreteValuationRing.exists_irreducible`
(blueprint: lem-per-prime-power-trait-residue-model). -/
noncomputable def traitResidueUniformizer (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] : R :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible R)

/-- The canonical prime-power residue model and its generator-independent derived map.
The target twist is the total left derived functor of tensoring with the actual Tate
stalk. Since that stalk is free of rank one, the displayed canonical comparison with
the exact tensor functor identifies it with tensor on every representing complex.

Source: ILO, Travaux de Gabber, Expose XVII 1.2.1--1.2.3, Proposition 1.2.1.2,
Proposition 1.2.2.1, Definition 1.2.3.1 and Lemma 1.2.3.2, printed pp. 259--262
(blueprint: lem-per-prime-power-trait-residue-model).

Proof:
1. Apply `lem-per-trait-tame-algebra` to obtain the canonical root character, its pro-p
kernel (trivial for p=1) and a topological generator.
2. In the cyclic quotient B_d, the kernel of 1-z is generated by the norm N_d, and its
image is the augmentation ideal. Project solutions from B_(ell^n*d); differences project
to ell^n*N_d=0. These compatible solutions prove that multiplication by 1-sigma is an
isomorphism from A to its augmentation ideal, including injectivity.
3. Use `lem-per-trait-sheaf-gluing` for the actual stalks and specialization. Averaging
on finite wild quotients is independent of refinement; it is linear, natural, fixes
invariants and commutes with H. Averaging a lift proves exactness of wild invariants.
Evaluation at 1-sigma makes the final Hom functor exact, so all three row functors are exact.
4. The generic representation and then wild invariants preserve injectives, by exact
left adjoints and `lem-exc-rg-right-adjoint-preserves-injectives`.
5. The first row cohomology is the supported-section kernel. For injective M, extending
(0,Lambda,0) along (Lambda,Lambda,id) proves middle exactness.
6. For invariant x fixed by sigma^d, the norm at ell^n*d kills x. Extend the map
(1-z)B_(ell^n*d) to B_(ell^n*d) in discrete G-modules to solve (1-sigma)y=x.
7. Use `lem-weil-pbc-module-sheaves-grothendieck-abelian`,
`lem-sp-grothendieck-enough-injectives` and
`lem-sc-bounded-below-injective-resolution-existence` for bounded below injective models.
8. The three-step column filtration proves preservation of quasi-isomorphisms. Exact
augmented injective rows identify the total with the published supported derived functor;
the right-derived unit fixes this comparison canonically.
9. Projection G to mu_(ell^n) has kernel (ell^n)G. Every continuous additive character to
an ell^n-torsion module factors through it. Evaluation, averaging and inverse evaluation
at 1-sigma give the specified cochain maps; the primitive root gives a rank-one Tate line.
10. Naturality with (0,V,0) and the averaging projector reduces natural homotopies to
discrete G-modules. 11. Natural underlying-module operations are exactly compatible
finite group-algebra elements, by evaluating on 1 in Lambda[G/U].
12. If 1-sigma'=u(1-sigma), the two residue maps differ by g=alpha*u^(-1).
Their natural homotopy equation is (1-sigma)h=1-g.
13. The geometric sums extend from integers modulo ell^n*d and show epsilon(u)=alpha.
Thus 1-g belongs to I, and Step 2 gives a unique h. Totalize these natural maps and
homotopies. Localize, use the support comparison and tensor evaluation to untwist; this
gives a natural map in D^+(Lambda), independent of generator and representative. -/
theorem exists_primePowerTraitResidueModel
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] (hell : IsUnit (ell : R))
    (K Ks Ω : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    [Field Ω] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (Ωs : Type u) [Field Ωs] [IsAlgClosed Ωs]
    (s : Spec (.of Ωs) ⟶ Spec (.of R)) (hs : s default = IsLocalRing.closedPoint R)
    :
    ∃ (hqp : 0 < ell ^ n ∧ (ell ^ n).Coprime (ringExpChar (IsLocalRing.ResidueField R)))
      (t : TraitResidueTameCharacter R K Ks Ω)
      (D : TraitPrimePowerStalkData R K Ks Ω Ωs s (TraitPrimePowerCoefficients.{u} ell n))
      (N : TraitPrimePowerWildData D t.character)
      (F : TraitResidueRow D N)
      (av : TraitResidueAverage D t.character)
      (T : TraitResidueTate R K Ω (TraitPrimePowerCoefficients.{u} ell n)
        (ell ^ n) (ringExpChar (IsLocalRing.ResidueField R))
        (traitPrimePowerCoefficients_annihilated ell n) hqp)
      (c : TraitResidueCochain D T N F av)
      (E : TraitResidueDerived D T F c (traitResidueUniformizer R)),
      ∃ sp : DerivedCategory.Plus.ι ⋙
          (traitResidueUnderlying (TraitPrimePowerCoefficients.{u} ell n)
            (Gal(Ks/K)) D.generic).mapDerivedCategory ⟶
        derivedSupportedEtaleSections (TraitPrimePowerCoefficients.{u} ell n)
            (Spec (.of R)) (PrimeSpectrum.basicOpen (traitResidueUniformizer R)) ⋙
          (tensorRight T.line).leftDerivedFunctor ⋙ shiftFunctor _ (2 : ℤ),
        ∀ (σ : {σ : TameRoots.limitSubgroup Ω (ringExpChar (IsLocalRing.ResidueField R)) //
            traitIsGenerator σ})
          (L : CochainComplex.Plus
            (TraitSheaves (TraitPrimePowerCoefficients.{u} ell n) R)),
          (traitResidueGenericFactors D L).hom ≫ sp.app (DerivedCategory.Plus.Q.obj L) =
            DerivedCategory.Q.map ((c.positiveResidue σ).app L.obj) ≫
              ((DerivedCategory.Q (C := ModuleCat.{u + 1}
                (TraitPrimePowerCoefficients.{u} ell n))).commShiftIso (2 : ℤ)).hom.app _ ≫
              (shiftFunctor _ (2 : ℤ)).map
                ((tensorRight T.line).mapDerivedCategoryFactors.inv.app _ ≫
                  (tensorRight T.line).mapDerivedCategory.map
                    (E.factors.hom.app L ≫ E.comparison.hom.app (DerivedCategory.Plus.Q.obj L)) ≫
                  (tensorRight T.line).leftDerivedFunctorIsoMapDerivedCategory.inv.app _) := by
  sorry

end AlgebraicGeometry.Etale
