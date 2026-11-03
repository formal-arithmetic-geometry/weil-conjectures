/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleSupportedHom
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.CartierComplementQuasiCompact
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-! # The global divisor class for every admissible condensed coefficient

Source: latest blueprint, lem-pur-divisor-class, global Kummer construction and
local equation formula (blueprint: lem-pur-divisor-class).
The class is the unique supported class glued from singleton frame boundaries.
The relative pole/Kummer class is a separate construction compared only in (b).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- Ext in the standard localization universe of the actual internal module category.
Source: the derived-category convention (blueprint: lem-pur-divisor-class). -/
instance moduleExt (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    HasExt.{u + 2} (Modules Λ X) := HasExt.standard _

/-- An admissible condensed ring has a unique unital continuous integral coefficient map.
Source: coefficient conventions and sk-def-sp-tate-twist
(blueprint: lem-pur-divisor-class).
Proof: for a finite ring use Z_l → Z/l^r → A; for O_E, E, and Qbar use their
recorded inclusions. Condensed morphisms from Z_l are continuous, so density of
Z and preservation of one imply uniqueness. Transport across a coefficient-ring
isomorphism. The zero ring is included. -/
theorem integralMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :
    ∃! f : Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[P.coefficients.l]) ⟶ Λ, True := by
  sorry

/-- The unique integral coefficient map; only its uniqueness proof is postponed.
Source: sk-def-sp-tate-twist (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def integralMap (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :=
  (integralMap_existsUnique P Λ hΛ).choose

/-- The actual root-tower Tate line after extension to Λ, not the regular unit.
Source: sk-def-sp-tate-twist (blueprint: lem-pur-divisor-class). -/
def line (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) (X : Scheme.{u}) : Modules Λ X :=
  (Mod.extendScalars (coefficientMap (integralMap P Λ hΛ).hom X)).obj
    (tateModule X P.coefficients.l)

/-- The full inverse system of units, with power-l transition maps.
Source: the Kummer construction (blueprint: lem-pur-divisor-class). -/
def powerUnits (ell : ℕ) (X : Scheme.{u}) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun _ : ℕ ↦ Scheme.proEtaleUnitsSheaf X)
    (fun _ ↦ Scheme.proEtaleUnitsPower X ell)

/-- Projection-normalized root inclusions and level comparisons. Every data field
is fixed by its tensor-generator or inverse-limit-coordinate equation.
Source: the compatible-root Kummer sequence (blueprint: lem-pur-divisor-class). -/
structure KummerData (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) where
  level : ∀ n : ℕ, (tateModuleLevel X ell (n + 1)).X ≅
    Scheme.proEtaleRootsOfUnitySheaf X (ell ^ (n + 1))
  level_spec : ∀ n : ℕ,
    (λ_ (rootsOfUnitySheaf X (ell ^ (n + 1)))).inv ≫
      η[condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X] ▷ _ ≫
        (level n).hom = (PurityTransport.rootComparison X (ell ^ (n + 1))).hom
  inclusion : (tateModule X ell).X ⟶ limit (powerUnits ell X)
  zeroth : inclusion ≫ limit.π (powerUnits ell X) (op 0) = 0
  positive : ∀ n : ℕ,
    inclusion ≫ limit.π (powerUnits ell X) (op (n + 1)) =
      (limit.π (tateModuleSystem X ell) (op (n + 1))).hom ≫
        (level n).hom ≫ Scheme.proEtaleRootsOfUnityInclusion X (ell ^ (n + 1))

/-- The projection and tensor-generator equations determine the Kummer data uniquely.
Source: compatible-root Kummer construction (blueprint: lem-pur-divisor-class).
Proof: tensoring the l-primary roots with Z_l identifies the free module with
the roots; the insertion of a root fixes this identification. The coordinates
(1,z_1,z_2,...) define a limit cone; uniqueness of a map to a limit fixes its
inclusion. The zero coordinate is one, written zero additively. -/
theorem kummerData_existsUnique (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :
    ∃! K : KummerData ell X, True := by
  sorry

/-- The canonical root-coordinate Kummer data.
Source: the Kummer construction (blueprint: lem-pur-divisor-class). -/
def kummerData (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) : KummerData ell X :=
  (kummerData_existsUnique ell X).choose

/-- The complete Kummer complex, before changing coefficients.
Source: the Kummer construction (blueprint: lem-pur-divisor-class). -/
def kummerComplex (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  ShortComplex.mk (kummerData ell X).inclusion
    (limit.π (powerUnits ell X) (op 0)) (kummerData ell X).zeroth

/-- The complete pro-etale Kummer sequence is short exact when l is invertible.
Source: lem-pur-divisor-class, Kummer construction (blueprint: lem-pur-divisor-class).
Proof: the kernel is exactly the compatible root system. Pro-etale locally any
unit admits compatible l-power roots, so projection to its zeroth coordinate
is locally surjective. This proves exactness of this sequence itself. -/
theorem kummer_exact (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    (kummerComplex P.coefficients.l X).ShortExact := by
  sorry

/-- Insertion of the full Tate module into its scalar extension.
Source: sk-def-sp-tate-twist (blueprint: lem-pur-divisor-class). -/
def rootInsertion (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) (X : Scheme.{u}) :
    (tateModule X P.coefficients.l).X ⟶ (line P Λ hΛ X).X :=
  (Mod.extendUnit (coefficientMap (integralMap P Λ hΛ).hom X)
    (tateModule X P.coefficients.l)).hom

/-- The positive full Kummer boundary followed by the native coefficient insertion.
Source: lem-pur-divisor-class, +∂κ normalization (blueprint: lem-pur-divisor-class). -/
def kummerClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    Abelian.Ext.{u + 1} (Scheme.proEtaleUnitsSheaf X) (line P Λ hΛ X).X 1 :=
  cartierKummerClass (kummer_exact P X a) (rootInsertion P Λ hΛ X)

/-- The positive relative Cartier Kummer class c_D, constructed from O(D) and
its canonical complementary frame. It does not define the frame class cl(D).
Source: lem-amb-cartier-kummer-map, relative class; lem-pur-divisor-class(b)
(blueprint: lem-pur-divisor-class). -/
def CartierSpec (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (c : Abelian.Ext.{u + 2} (source Λ i) (line P Λ hΛ X) 2) : Prop :=
  (Ext.mk₀ (supportedGenerator Λ i)).comp
      (c.mapExactFunctor (Mod.forget (condensedRingObj Λ.X X))) (zero_add 2) =
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI)).comp
      (kummerClass P Λ hΛ X a) (rfl : 1 + 1 = 2)

/-- The scalar adjunct of the full relative boundary exists uniquely.
Source: relative Cartier construction in lem-pur-divisor-class(b)
(blueprint: lem-pur-divisor-class).
Proof: the supported integral sheaf is flat and its derived free Λ-module is
canonically i_*Λ_D, by the open/closed sequence. The derived scalar adjunction
therefore gives a bijection from module Ext to abelian Ext with this supported
integral source. Apply its inverse to the displayed positive pole/Kummer
splice. Injectivity gives uniqueness of the complete native arrow. -/
theorem cartier_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! c : Abelian.Ext.{u + 2} (source Λ i) (line P Λ hΛ X) 2,
      CartierSpec P Λ hΛ a i hI c := by
  sorry

/-- The independent coefficient-linear c_D, specified by the full positive boundary.
Source: lem-pur-divisor-class (blueprint: lem-pur-divisor-class). -/
def cartierExt (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :=
  (cartier_existsUnique P Λ hΛ a i hI).choose

/-- c_D in actual derived kernel cohomology, via the cocycle-normalized supported-Hom
identification. Source: lem-pur-divisor-class (blueprint: lem-pur-divisor-class). -/
def cartierClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    (H Λ i 2).obj ((DerivedCategory.Plus.singleFunctor (Modules Λ X) 0).obj
      (line P Λ hΛ X)) :=
  let : QuasiCompact i.openComplement.ι := cartierComplement_quasiCompact i hI
  (supportedHom Λ i _ 2).symm (cartierExt P Λ hΛ a i hI).hom

/-- The Cartier arrow is the image of the independently constructed c_D.
Source: lem-pur-supported-hom applied to lem-pur-divisor-class
(blueprint: lem-pur-divisor-class). -/
def cartierArrow (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :=
  let : QuasiCompact i.openComplement.ι := cartierComplement_quasiCompact i hI
  supportedHom Λ i _ 2 (cartierClass P Λ hΛ a i hI)

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible

namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- The coefficient prime is invertible at every point over the fixed field.
Source: purity conventions (blueprint: lem-pur-divisor-class).
Proof: its image is nonzero in characteristic p because l and p are distinct primes;
the residue ring is a field, hence that image is a unit. -/
theorem prime_isUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (x : X) :
    IsUnit (P.coefficients.l : X.residueField x) := by
  simpa only [map_natCast] using
    (P.coefficientPrime_isUnit_stalk X a x).map (X.residue x).hom

/-- The integral comparison together with its finite-root normalization. The
finite comparisons are fixed on root generators, and all limit projections fix
its integral arrow. Source: Cartesian coefficients (blueprint: lem-pur-divisor-class). -/
structure RootPullData (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) where
  iso : (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
    (tateModule Y ell) ≅ tateModule X ell
  level : ∀ n : ℕ,
    (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
      (tateModuleLevel Y ell n) ≅ tateModuleLevel X ell n
  normalized : ∀ n : ℕ,
    PurityTransport.PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f (level n)
      (PurityTransport.rootTensorPull ell f n)
  projection : ∀ n : ℕ,
    iso.hom ≫ limit.π (tateModuleSystem X ell) (op n) =
      (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).map
        (limit.π (tateModuleSystem Y ell) (op n)) ≫ (level n).hom

private theorem rootPullNormalized_unique
    (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e e' : (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
      (tateModuleLevel Y ell n) ≅ tateModuleLevel X ell n)
    (h : PurityTransport.PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f e
      (PurityTransport.rootTensorPull ell f n))
    (h' : PurityTransport.PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f e'
      (PurityTransport.rootTensorPull ell f n)) : e = e' := by
  apply Iso.ext
  let a := (Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) Y))
    (Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.continuousMapRingObj ℤ_[ell]) f))).inv.app
        (tateModuleLevel Y ell n)
  have heq : (Mod.forget
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X)).map (a ≫ e.hom) =
    (Mod.forget
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X)).map (a ≫ e'.hom) :=
    eq_of_heq (h.trans h'.symm)
  have heq' := (Mod.forget
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X)).map_injective heq
  exact (cancel_epi a).mp heq'

/-- The root-generator and projection equations uniquely determine all comparison data.
Source: the published integralComparison and finite root normalization
(blueprint: lem-pur-divisor-class).
Proof: apply integralComparison to obtain the integral comparison and its normalized
finite comparisons. Choose those finite comparisons. Their normalization on roots
fixes their underlying maps, and faithfulness of forgetful modules fixes the module
maps. The limit projection equations then fix the integral comparison. Iso inverses
and the proof fields are unique, giving uniqueness of the entire structure. -/
theorem rootPullData_existsUnique (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃! _D : RootPullData ell f, True := by
  classical
  obtain ⟨e, he, hunique⟩ := PurityTransport.integralComparison ell f
  let en := fun n : ℕ ↦ (he n).choose
  have hn (n : ℕ) := (he n).choose_spec.1
  have hp (n : ℕ) := (he n).choose_spec.2
  refine ⟨⟨e, en, hn, hp⟩, trivial, ?_⟩
  rintro ⟨e', en', hn', hp'⟩ _
  have he' : e' = e := hunique e' (fun n ↦ ⟨en' n, hn' n, hp' n⟩)
  have hen : en' = en := by
    funext n
    exact rootPullNormalized_unique ell f n (en' n) (en n) (hn' n) (hn n)
  cases he'
  cases hen
  rfl

/-- The comparison fixed by its root generators and every inverse-limit projection.
Source: Cartesian coefficients (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def rootPullIso (ell : ℕ) [hPrime : Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (ell : X.residueField x)]
    [hY : ∀ y : Y, Invertible (ell : Y.residueField y)] :
    (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
      (tateModule Y ell) ≅ tateModule X ell :=
  (@rootPullData_existsUnique.{u} ell hPrime X Y f hX hY).choose.iso

/-- The scalar-extension comparison is fixed on the pulled-back integral generators.
Its iso is not free data: the displayed equality specifies its underlying map
on a set of scalar generators. Source: Cartesian coefficients
(blueprint: lem-pur-divisor-class). -/
structure ScalarRootPullData (ell : ℕ) [Fact ell.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (a : Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ell]) ⟶ Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] where
  iso : (CondensedRing.upperStar Λ.X f).obj
    ((Mod.extendScalars (coefficientMap a.hom Y)).obj (tateModule Y ell)) ≅
      (Mod.extendScalars (coefficientMap a.hom X)).obj (tateModule X ell)
  generator :
    (ProEtale.upperStar Ab.{u + 1} f).map
        (Mod.extendUnitHom (coefficientMap a.hom Y) (tateModule Y ell)) ≫
      CondensedRing.upperStarUnitHom Λ.X f
        ((Mod.extendScalars (coefficientMap a.hom Y)).obj (tateModule Y ell)) ≫
      iso.hom.hom =
    CondensedRing.upperStarUnitHom (Profinite.continuousMapRingObj ℤ_[ell]) f
        (tateModule Y ell) ≫ (rootPullIso ell f).hom.hom ≫
      Mod.extendUnitHom (coefficientMap a.hom X) (tateModule X ell)

private theorem scalarPull_generator
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    (ProEtale.upperStar Ab.{u + 1} f).map
        (Mod.extendUnitHom (coefficientMap a Y) M) ≫
      CondensedRing.upperStarUnitHom S f
        ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
          (PurityTransport.scalarPull a f e).hom.hom =
    CondensedRing.upperStarUnitHom R f M ≫ e.hom.hom ≫
      Mod.extendUnitHom (coefficientMap a X) N := by
  have hp := CondensedRing.upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom a f M
  have hi :
      (ProEtale.upperStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (coefficientMap a Y) M) ≫
        CondensedRing.upperStarUnitHom S f
          ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
            ((CondensedRing.pullIso a f).inv.app M).hom =
      CondensedRing.upperStarUnitHom R f M ≫
        Mod.extendUnitHom (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) := by
    erw [← Category.assoc, ← hp]
    simp only [Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom']
    erw [Category.comp_id]
  have ht := congrArg (fun k ↦ k ≫
    ((Mod.extendScalars (coefficientMap a X)).map e.hom).hom) hi
  simpa only [PurityTransport.scalarPull, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Mod.comp_hom', Category.assoc,
    Mod.extendUnitHom_comp_extendScalars_map_hom] using ht

private theorem scalarPull_hom_ext
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)}
    {g g' : (CondensedRing.upperStar S f).obj
      ((Mod.extendScalars (coefficientMap a Y)).obj M) ⟶ N}
    (h : (ProEtale.upperStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (coefficientMap a Y) M) ≫
        CondensedRing.upperStarUnitHom S f
          ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫ g.hom =
      (ProEtale.upperStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (coefficientMap a Y) M) ≫
        CondensedRing.upperStarUnitHom S f
          ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫ g'.hom) : g = g' := by
  apply (cancel_epi ((CondensedRing.pullIso a f).hom.app M)).mp
  apply Mod.hom_ext_of_extendUnitHom
  have : IsIso (CondensedRing.upperStarUnitHom R f M) := by
    dsimp only [CondensedRing.upperStarUnitHom]
    rw [← CondensedRing.extendScalarsIsoComapInv_inv_app_hom]
    infer_instance
  apply (cancel_epi (CondensedRing.upperStarUnitHom R f M)).mp
  simpa only [Mod.comp_hom', Category.assoc,
    CondensedRing.upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom_assoc] using h

/-- The actual scalar-extension generators determine the Cartesian comparison uniquely.
Source: sk-prop-sfb-cartesian-coefficients, canonical scalar comparison
(blueprint: lem-pur-divisor-class).
Proof: apply the published scalarPull to the root-normalized integral comparison.
The generator equation is the defining unit equation of the scalar-change mate,
followed by naturality of the scalar-extension unit. Conversely the adjunctions
for inverse image and extension of scalars say that a linear map out of this
source is determined on those generators. Thus its hom, inverse and proof fields
are unique, and so is the displayed data. -/
theorem scalarRootPullData_existsUnique (ell : ℕ) [Fact ell.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (a : Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ell]) ⟶ Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃! _D : ScalarRootPullData ell Λ a f, True := by
  let e : (CondensedRing.upperStar Λ.X f).obj
      ((Mod.extendScalars (coefficientMap a.hom Y)).obj (tateModule Y ell)) ≅
        (Mod.extendScalars (coefficientMap a.hom X)).obj (tateModule X ell) :=
    PurityTransport.scalarPull (R := Profinite.continuousMapRingObj.{u} ℤ_[ell])
      (S := Λ.X) a.hom f (rootPullIso ell f)
  have hg := scalarPull_generator
    (R := Profinite.continuousMapRingObj.{u} ℤ_[ell]) (S := Λ.X)
    a.hom f (rootPullIso ell f)
  refine ⟨⟨e, hg⟩, trivial, ?_⟩
  rintro ⟨e', hg'⟩ _
  have hi : e' = e := Iso.ext (scalarPull_hom_ext
    (R := Profinite.continuousMapRingObj.{u} ℤ_[ell]) (S := Λ.X)
    a.hom f _ (hg'.trans hg.symm))
  cases hi
  rfl

/-- The generator-normalized scalar comparison, rather than an arbitrary isomorphism.
Source: Cartesian coefficients (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def extendedLinePull (ell : ℕ) [hPrime : Fact ell.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (a : Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ell]) ⟶ Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (ell : X.residueField x)]
    [hY : ∀ y : Y, Invertible (ell : Y.residueField y)] :
    (CondensedRing.upperStar Λ.X f).obj
      ((Mod.extendScalars (coefficientMap a.hom Y)).obj (tateModule Y ell)) ≅
        (Mod.extendScalars (coefficientMap a.hom X)).obj (tateModule X ell) :=
  (scalarRootPullData_existsUnique ell Λ a f).choose.iso

/-- The uniquely determined residue inverse of the coefficient prime.
Source: prime invertibility over the fixed field (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def residueInverse (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (x : X) :
    Invertible (P.coefficients.l : X.residueField x) :=
  (prime_isUnit P X a x).invertible

/-- The canonical root-normalized coefficient pullback, specialized to the setting.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def linePull (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (CommRingCat.of P.field.k))
    (aY : Y ⟶ Spec (CommRingCat.of P.field.k)) (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ.X f).obj (line P Λ hΛ Y) ≅ line P Λ hΛ X :=
  letI (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    residueInverse P X aX x
  letI (y : Y) : Invertible (P.coefficients.l : Y.residueField y) :=
    residueInverse P Y aY y
  extendedLinePull P.coefficients.l Λ (integralMap P Λ hΛ) f

/-- Pullback of the shifted native Tate line with the canonical shift and single comparisons.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def twistPull (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (CommRingCat.of P.field.k))
    (aY : Y ⟶ Spec (CommRingCat.of P.field.k)) (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ.X f).obj
      (((DerivedCategory.singleFunctor (Modules Λ Y) 0).obj (line P Λ hΛ Y)) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (line P Λ hΛ X)) ⟦(2 : ℤ)⟧ :=
  (Functor.commShiftIso (CondensedRing.upperStar Λ.X f).leftDerivedFunctor
    (self := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X f).leftAdjointCommShift ℤ)
      (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((CondensedRing.upperStar Λ.X f).singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (linePull P Λ hΛ aX aY f))

/-- Pullback of the coefficient unit, fixed by the inverse-image tensor unit map.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: lem-pur-divisor-class). -/
def unitPull (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).app
      ((DerivedCategory.singleFunctor _ 0).obj (unit Λ Y)) ≪≫
    ((CondensedRing.upperStar Λ.X f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ.X f)).symm

/-- Closed-source pullback is the ordinary closed exchange mate followed by pullback
of the coefficient unit. Source: det-sf-open-closed-sequence-ring-sheaf(4)
(blueprint: lem-pur-divisor-class). -/
def closedSourcePull (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X D' X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
    {d : D' ⟶ D} {g : X' ⟶ X} (sq : CommSq d i' i g) :
    (moduleObjectDerivedPullback Λ.X g).obj
      ((DerivedCategory.singleFunctor _ 0).obj (source Λ i)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj (source Λ i') :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).hom.app _ ≫
    ((CondensedRing.upperStar Λ.X g).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((CondensedRing.lowerStarBaseChange Λ.X sq).app (unit Λ D) ≫
        (CondensedRing.lowerStar Λ.X i').map
          (Functor.Monoidal.εIso (CondensedRing.upperStar Λ.X d)).inv)

/-- The integral morphism sending one to the specified unit.
Source: Kummer connecting map (blueprint: lem-pur-divisor-class). -/
def unitSection (X : Scheme.{u}) (t : Γ(X, ⊤)ˣ) :=
  ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId X)).homEquiv
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (Scheme.proEtaleUnitsSheaf X)).symm
      (AddCommGrpCat.unitHom
        (M := (Scheme.proEtaleUnitsSheaf X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
        (ULift.up (Additive.ofMul t)))

/-- The native Kummer class of a unit is fixed by the full scalar-adjunction equation.
Source: Kummer sequence in lem-pur-divisor-class (blueprint: lem-pur-divisor-class).
Proof: the free coefficient module on the integral unit is the regular module.
Derived free/forgetful adjunction is therefore a bijection in every Ext degree.
Apply it to the pullback of the full Kummer extension along the specified unit. -/
theorem unitKummer_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    ∃! q : Abelian.Ext.{u + 2} (unit Λ X) (line P Λ hΛ X) 1,
      (Ext.mk₀ (generator Λ X)).comp
        (q.mapExactFunctor (Mod.forget (condensedRingObj Λ.X X))) (zero_add 1) =
      (Ext.mk₀ (unitSection X t)).comp (kummerClass P Λ hΛ X a) (zero_add 1) := by
  sorry

/-- The full Kummer class of a unit, before applying the support boundary.
Source: lem-pur-divisor-class(a),(c) (blueprint: lem-pur-divisor-class). -/
def unitKummer (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (t : Γ(X, ⊤)ˣ) :=
  (unitKummer_existsUnique P Λ hΛ X a t).choose

/-- The canonical coefficient restriction to the closed direct image, defined
by the inverse-image adjunction unit and tensor-unit comparison.
Source: support restriction (blueprint: lem-pur-divisor-class). -/
def unitRestriction (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) : unit Λ X ⟶ source Λ i :=
  (CondensedRing.upperStarLowerStarAdjunction Λ.X i).unit.app (unit Λ X) ≫
    (CondensedRing.lowerStar Λ.X i).map
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ.X i)).inv

/-- Orthogonality of the two specific coefficient localization maps.
Source: open/closed sequence (blueprint: lem-pur-divisor-class).
Proof: restriction to the closed complement kills extension by zero. The
composite is the adjunct of the resulting zero map, hence vanishes. -/
theorem coefficientSequence_zero (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X (X.basicOpen f).ι
      ).counit.app (unit Λ X) ≫
      unitRestriction Λ (X.zeroLocusSubschemeι {f}) = 0 := by
  apply ((CondensedRing.upperStarLowerStarAdjunction Λ.X
    (X.zeroLocusSubschemeι {f})).homEquiv _ _).symm.injective
  have hz := CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ.X (X.basicOpen f).ι (X.zeroLocusSubschemeι {f})
    (by
      rw [Scheme.Opens.range_ι, Scheme.range_zeroLocusSubschemeι_singleton,
        Scheme.Opens.range_ι]
      exact disjoint_compl_right)
    ((CondensedRing.upperStar Λ.X (X.basicOpen f).ι).obj (unit Λ X))
  exact hz.eq_of_src _ _

/-- The actual native coefficient localization sequence for V(f), with no regularity assumption.
Source: open/closed sequence (blueprint: lem-pur-divisor-class). -/
def coefficientSequence (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) (f : Γ(X, ⊤)) :=
  ShortComplex.mk
    ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X (X.basicOpen f).ι
      ).counit.app (unit Λ X))
    (unitRestriction Λ (X.zeroLocusSubschemeι {f})) (coefficientSequence_zero Λ X f)

private theorem localization_shortExact
    {C : Type*} [Category* C] [Abelian C]
    {O Z : Type u} [Category.{v} O] [Abelian O] [Category.{v} Z] [Abelian Z]
    {F : C ⥤ O} {G : C ⥤ Z} {L : O ⥤ C} {R : Z ⥤ C}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : L ⊣ F) (b : G ⊣ R) [IsIso a.unit] [IsIso b.counit]
    (hd : JointlyReflectIsomorphisms (pairFunctor F G))
    (hz : ∀ N, IsZero (F.obj (R.obj N)))
    (hzi : ∀ N, IsZero (G.obj (L.obj N)))
    (M : C) (hzero : a.counit.app M ≫ b.unit.app M = 0) :
    (ShortComplex.mk (a.counit.app M) (b.unit.app M) hzero).ShortExact := by
  let Q := ShortComplex.mk (a.counit.app M) (b.unit.app M) hzero
  change Q.ShortExact
  rw [hd.shortExact_iff]
  rintro (_ | _)
  · have hgi : IsIso (G.map (b.unit.app M)) := by
      have h := b.left_triangle_components M
      rw [← IsIso.inv_eq_of_inv_hom_id h]
      infer_instance
    have hfi : (Q.map G).f = 0 := (hzi _).eq_of_src _ _
    exact
      { exact := (ShortComplex.exact_iff_mono _ hfi).2
          (by exact @IsIso.mono_of_iso _ _ _ _ _ hgi)
        mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
        epi_g := by exact @IsIso.epi_of_iso _ _ _ _ _ hgi }
  · have hfj : IsIso (F.map (a.counit.app M)) := by
      have h := a.right_triangle_components (Y := M)
      rw [← IsIso.inv_eq_of_hom_inv_id h]
      infer_instance
    have hgj : (Q.map F).g = 0 := (hz _).eq_of_tgt _ _
    exact
      { exact := (ShortComplex.exact_iff_epi _ hgj).2
          (by exact @IsIso.epi_of_iso _ _ _ _ _ hfj)
        mono_f := by exact @IsIso.mono_of_iso _ _ _ _ _ hfj
        epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }

private theorem localization_shortExact_normalized
    {C : Type*} [Category* C] [Abelian C]
    {O Z : Type u} [Category.{v} O] [Abelian O] [Category.{v} Z] [Abelian Z]
    {F : C ⥤ O} {G : C ⥤ Z} {L : O ⥤ C} {R : Z ⥤ C}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : L ⊣ F) (b : G ⊣ R) [IsIso a.unit] [IsIso b.counit]
    (hd : JointlyReflectIsomorphisms (pairFunctor F G))
    (hz : ∀ N, IsZero (F.obj (R.obj N)))
    (hzi : ∀ N, IsZero (G.obj (L.obj N)))
    (M : C) {N : Z} (c : G.obj M ≅ N)
    (hzero : a.counit.app M ≫ (b.unit.app M ≫ R.map c.hom) = 0) :
    (ShortComplex.mk (a.counit.app M) (b.unit.app M ≫ R.map c.hom) hzero).ShortExact := by
  have hzero' : a.counit.app M ≫ b.unit.app M = 0 := by
    apply (cancel_mono (R.map c.hom)).1
    simpa only [Category.assoc, zero_comp] using hzero
  let Q := ShortComplex.mk (a.counit.app M) (b.unit.app M) hzero'
  have hQ : Q.ShortExact := localization_shortExact a b hd hz hzi M hzero'
  let S := ShortComplex.mk (a.counit.app M) (b.unit.app M ≫ R.map c.hom) hzero
  let e : Q ≅ S := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (R.mapIso c)
    (by simp [Q, S]) (by simp [Q, S])
  exact ShortComplex.shortExact_of_iso e hQ

private theorem module_open_unit_isIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j).unit := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom R j)
    ).fullyFaithfulFunctor.comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
        ).fullyFaithfulMapModLeft
  have : (CondensedRing.openImmersionLowerShriek R j).Full := ff.full
  have : (CondensedRing.openImmersionLowerShriek R j).Faithful := ff.faithful
  exact (CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j
    ).unit_isIso_of_L_fully_faithful

private theorem module_localization_exact
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    {N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)}
    (c : (CondensedRing.upperStar R i).obj M ≅ N)
    (hSeq :
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j).counit.app M ≫
        ((CondensedRing.upperStarLowerStarAdjunction R i).unit.app M ≫
          (CondensedRing.lowerStar R i).map c.hom) = 0) :
    (ShortComplex.mk
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j).counit.app M)
      ((CondensedRing.upperStarLowerStarAdjunction R i).unit.app M ≫
        (CondensedRing.lowerStar R i).map c.hom) hSeq).ShortExact := by
  have hz (N' : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R Z)) :
      IsZero ((CondensedRing.upperStar R j).obj
        ((CondensedRing.lowerStar R i).obj N')) := by
    have h := ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
      hij.disjoint N'.X
    rw [← CondensedRing.lowerStar_obj_X R i N'] at h
    exact CondensedRing.isZero_of_isZero_X R
      (h.of_iso (CondensedRing.upperStarObjXIso R j _))
  have hzi (N' : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj R U)) :
      IsZero ((CondensedRing.upperStar R i).obj
        ((CondensedRing.openImmersionLowerShriek R j).obj N')) :=
    CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
      R j i hij.symm.disjoint N'
  have : IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j).unit :=
    module_open_unit_isIso R j
  exact localization_shortExact_normalized
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction R j)
    (CondensedRing.upperStarLowerStarAdjunction R i)
    (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl R i j hij)
    hz hzi M c hSeq

/-- Exactness of the specified coefficient localization sequence.
Source: det-sf-open-closed-sequence-ring-sheaf (blueprint: lem-pur-divisor-class).
Proof: after forgetting modules, the open and closed restrictions detect exactness.
On the open the first map is identity and the third object is zero; on the
closed the first object is zero and the second map is identity. -/
theorem coefficientSequence_exact (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) (f : Γ(X, ⊤)) : (coefficientSequence Λ X f).ShortExact := by
  have hij : IsCompl (Set.range (X.zeroLocusSubschemeι {f}).base)
      (Set.range (X.basicOpen f).ι.base) := by
    rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  exact module_localization_exact Λ.X (X.zeroLocusSubschemeι {f})
    (X.basicOpen f).ι hij (unit Λ X)
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ.X (X.zeroLocusSubschemeι {f}))).symm
    (coefficientSequence_zero Λ X f)

/-- Extend the native Kummer class of f on X_f by zero and apply the twist counit.
Source: lem-pur-divisor-class(a),(c) (blueprint: lem-pur-divisor-class). -/
@[irreducible]
def openKummer (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (f : Γ(X, ⊤)) :
    Abelian.Ext.{u + 2}
      ((CondensedRing.openImmersionLowerShriek Λ.X (X.basicOpen f).ι).obj
        ((CondensedRing.upperStar Λ.X (X.basicOpen f).ι).obj (unit Λ X)))
      (line P Λ hΛ X) 1 :=
  let j := (X.basicOpen f).ι
  let J := CondensedRing.openImmersionLowerShriek Λ.X j
  (Ext.mk₀ (J.map (Functor.Monoidal.εIso (CondensedRing.upperStar Λ.X j)).inv)).comp
    (((unitKummer P Λ hΛ _ (j ≫ a) (X.basicOpenUnit f)).mapExactFunctor J).comp
      (Ext.mk₀ (J.map (linePull P Λ hΛ (j ≫ a) a j).inv ≫
        (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X j).counit.app
          (line P Λ hΛ X))) (add_zero 1)) (zero_add 1)

/-- The actual support-boundary Ext class for every function, including nilpotents.
Source: lem-pur-divisor-class(a),(c) (blueprint: lem-pur-divisor-class). -/
def principalExt (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (f : Γ(X, ⊤)) :
    Abelian.Ext.{u + 2} (source Λ (X.zeroLocusSubschemeι {f})) (line P Λ hΛ X) 2 :=
  (ShortComplex.ShortExact.extClass.{u + 2} (coefficientSequence_exact Λ X f)).comp
    (openKummer P Λ hΛ X a f) (rfl : 1 + 1 = 2)

/-- The actual +∂κ(f) as a derived arrow: the preceding localization splice.
Source: lem-pur-divisor-class(a),(c) (blueprint: lem-pur-divisor-class). -/
def principalBoundary (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (f : Γ(X, ⊤)) :=
  (principalExt P Λ hΛ X a f).hom

/-- The local equation boundary uses the independently constructed support connecting map.
Source: lem-pur-divisor-class(a) (blueprint: lem-pur-divisor-class). -/
def equationBoundary (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (f : Γ(X, ⊤))
    (_hf : (X.zeroLocusSubschemeι {f}).ker.IsInvertible) :=
  principalBoundary P Λ hΛ X a f

/-- A smooth codimension-one family over a separated finite-type base. This
existential geometric condition supplies the scope of bottom-degree gluing;
no cohomology class or comparison map is part of it.
Source: lem-pur-divisor-class, opening hypotheses (blueprint: lem-pur-divisor-class). -/
def SmoothDivisorPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k)) (i : D ⟶ X) : Prop :=
  ∃ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of P.field.k)) (v : X ⟶ B) (n : ℕ),
    v ≫ b = a ∧ IsSeparated b ∧ LocallyOfFiniteType b ∧ QuasiCompact b ∧
    IsSeparated a ∧ LocallyOfFiniteType a ∧ QuasiCompact a ∧
    SmoothOfRelativeDimension n v ∧ Smooth (i ≫ v) ∧
    ∀ z : D, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)

/-- The stated family supplies exactly the geometric scope of frame gluing.
Source: lem-pur-divisor-class, opening hypotheses (blueprint: lem-pur-divisor-class).
Proof: use B, b, v, n as the four existential witnesses; the structural equation
is reflexivity, the eight morphism properties are the given instances, and the
last field is the given codimension equation. No cohomological input is needed. -/
theorem smoothDivisorPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {B X D : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (v : X ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ X) [Smooth (i ≫ v)]
    (hcodim : ∀ z : D, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)) :
    SmoothDivisorPair P (v ≫ b) i := by
  exact ⟨B, b, v, n, rfl, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hcodim⟩

/-- The singleton frame class is by definition the actual +∂κ(f) boundary.
Source: def-pur-frame-class, c=1; lem-pur-divisor-class(a)
(blueprint: lem-pur-divisor-class). -/
def singletonFrameClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (U : Scheme.{u}) (a : U ⟶ Spec (CommRingCat.of P.field.k)) (f : Γ(U, ⊤)) :=
  principalBoundary P Λ hΛ U a f

/-- Rank-one frame independence for all admissible coefficients, in the actual
closed-source presentations. Source: lem-pur-frame-independence, c=1, and the
global frame construction of lem-pur-divisor-class (blueprint: lem-pur-divisor-class).
Proof: refine two equation frames to a common equation neighbourhood; their
ratio is a unit. Kummer additivity writes the difference of their Kummer classes
as the class of that unit. It extends across the neighbourhood, so exactness
kills its support boundary. Closed-source and coefficient pullback comparisons
are precisely those induced by restriction of the same supported sections.
This is the singleton specialization of frame independence, at the given Λ. -/
theorem singleton_frame_independent (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hpair : SmoothDivisorPair P a i)
    (U : Scheme.{u}) (e : U ⟶ X) [Etale e] (f₁ f₂ : Γ(U, ⊤))
    (d₁ : U.zeroLocusSubscheme {f₁} ⟶ D) (d₂ : U.zeroLocusSubscheme {f₂} ⟶ D)
    (sq₁ : IsPullback d₁ (U.zeroLocusSubschemeι {f₁}) i e)
    (sq₂ : IsPullback d₂ (U.zeroLocusSubschemeι {f₂}) i e) :
    closedSourcePull Λ sq₁.toCommSq ≫ singletonFrameClass P Λ hΛ U (e ≫ a) f₁ =
      closedSourcePull Λ sq₂.toCommSq ≫ singletonFrameClass P Λ hΛ U (e ≫ a) f₂ := by
  sorry

/-- Every equation chart restricts to its singleton frame boundary. This
specification contains no pole extension, Cartier class, or Chern class.
The comparison has quasi-compact complementary open; the smooth finite-type
gluing hypotheses imply this scope.
Source: lem-pur-divisor-class, definition and (a) (blueprint: lem-pur-divisor-class). -/
def FrameGluingSpec (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i]
    (c : (H Λ i 2).obj ((DerivedCategory.Plus.singleFunctor (Modules Λ X) 0).obj
      (line P Λ hΛ X))) : Prop :=
  ∀ [QuasiCompact i.openComplement.ι] (U : Scheme.{u}) (e : U ⟶ X) [Etale e] (f : Γ(U, ⊤))
    (d : U.zeroLocusSubscheme {f} ⟶ D)
    (sq : IsPullback d (U.zeroLocusSubschemeι {f}) i e),
    closedSourcePull Λ sq.toCommSq ≫ singletonFrameClass P Λ hΛ U (e ≫ a) f =
      (moduleObjectDerivedPullback Λ.X e).map (supportedHom Λ i _ 2 c) ≫
        (twistPull P Λ hΛ (e ≫ a) a e).hom

/-- Singleton frame classes glue to a unique global supported class in bottom degree.
Source: lem-pur-divisor-class, opening construction; lem-pur-frame-independence;
lem-pur-smooth-divisor-low-support; lem-pur-supported-bottom-gluing
(blueprint: lem-pur-divisor-class).
Proof: smooth-pair coordinates and the codimension-one dimension calculation
supply local single nonzerodivisor equations. Finite type gives finite-dimensional
stalks. Apply singleton_frame_independent on common refinements to obtain a
compatible family of the defined principalBoundary classes. Low-support
vanishing below degree two identifies bottom supported cohomology with sections
of its degree-two local cohomology sheaf, also for the specified native Λ line.
For integral coefficients this low-degree bound follows on the full root tower
from the finite bound: the lower finite cohomology groups vanish, so no lower
inverse-limit correction remains. Integral extension rings are finite free;
field coefficients follow by exact localization and the algebraic closure by
filtered scalar extension. This establishes only the low-degree bound, without
reconstructing a class morphism from finite reductions.
Bottom-degree supported gluing gives existence and separation gives uniqueness.
The normalized supported-Hom comparison expresses those actual restrictions
as the equations in FrameGluingSpec. No Cartier-pair Kummer class enters. -/
theorem frame_class_glues (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hpair : SmoothDivisorPair P a i) :
    ∃! c : (H Λ i 2).obj ((DerivedCategory.Plus.singleFunctor (Modules Λ X) 0).obj
      (line P Λ hΛ X)), FrameGluingSpec P Λ hΛ a i c := by
  sorry

/-- cl(D) is the unique supported class glued from the singleton frame classes.
Source: lem-pur-divisor-class, first sentence (blueprint: lem-pur-divisor-class). -/
def divisorClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (_hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) :=
  (frame_class_glues P Λ hΛ a i hpair).choose

/-- The actual arrow of the glued frame class under the supported-Hom identification.
Source: lem-pur-divisor-class and lem-pur-supported-hom
(blueprint: lem-pur-divisor-class). -/
def divisorArrow (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) :=
  let : QuasiCompact i.openComplement.ι := cartierComplement_quasiCompact i hI
  supportedHom Λ i _ 2 (divisorClass P Λ hΛ a i hI hpair)

/-- The explicit open-chart form of the defining frame-gluing property.
Source: lem-pur-divisor-class(a) (blueprint: lem-pur-divisor-class). -/
def LocalEquationLaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) : Prop :=
  ∀ (U : Scheme.{u}) (e : U ⟶ X) [IsOpenImmersion e] (f : Γ(U, ⊤))
    (hf : (U.zeroLocusSubschemeι {f}).ker.IsInvertible)
    (d : U.zeroLocusSubscheme {f} ⟶ D)
    (sq : IsPullback d (U.zeroLocusSubschemeι {f}) i e),
    closedSourcePull Λ sq.toCommSq ≫ equationBoundary P Λ hΛ U (e ≫ a) f hf =
      (moduleObjectDerivedPullback Λ.X e).map (divisorArrow P Λ hΛ a i hI hpair) ≫
        (twistPull P Λ hΛ (e ≫ a) a e).hom

/-- The glued class has its defining singleton-frame formula on every equation chart.
Source: lem-pur-divisor-class(a) (blueprint: lem-pur-divisor-class).
Proof: use the specified property of the unique glued class; an open chart is
an etale chart, and singletonFrameClass is principalBoundary by definition. -/
theorem divisor_class (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) :
    FrameGluingSpec P Λ hΛ a i (divisorClass P Λ hΛ a i hI hpair) ∧
      LocalEquationLaw P Λ hΛ a i hI hpair := by
  have : QuasiCompact i.openComplement.ι := cartierComplement_quasiCompact i hI
  have hc : FrameGluingSpec P Λ hΛ a i (divisorClass P Λ hΛ a i hI hpair) :=
    (frame_class_glues P Λ hΛ a i hpair).choose_spec.1
  refine ⟨hc, ?_⟩
  intro U e _ f hf d sq
  exact hc U e f d sq

/-- The local-equation law of the specified global divisor arrow, for every smooth
Cartier pair. Source: lem-pur-divisor-class(a)
(blueprint: lem-pur-divisor-class-local-equation).
Proof: take the local-equation component of divisor_class. This retains the
actual glued class and the specified closed-source and Tate comparisons. -/
theorem divisor_localEquation (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) :
    LocalEquationLaw P Λ hΛ a i hI hpair :=
  (divisor_class P Λ hΛ a i hI hpair).2

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible

namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- The class of the canonical frame torsor of a line bundle, transported to
pro-etale units by the published comparison maps. This construction does not
use any divisor extension. Source: GmPicard and lem-pur-kummer-additivity
(blueprint: lem-pur-divisor-class). -/
def picardUnits (X : Scheme.{u}) (L : X.Pic) :
    Abelian.Ext.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (Scheme.proEtaleUnitsSheaf X) 1 :=
  cartierBoundaryImage (ProEtale.comparisonUpperStar Ab.{u + 1} X)
    (cartierIntegralConstantComparisonIso X).inv (cartierUnitsComparison X)
    (Scheme.Pic.toCohomologicalPicardGroup X L)

/-- The ordinary Chern class is the Kummer boundary of the independently defined
Picard frame-torsor class. Source: lem-pur-kummer-additivity
(blueprint: lem-pur-divisor-class). -/
def ChernSpec (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (L : X.Pic)
    (c : Abelian.Ext.{u + 2} (unit Λ X) (line P Λ hΛ X) 2) : Prop :=
  (Ext.mk₀ (generator Λ X)).comp
      (c.mapExactFunctor (Mod.forget (condensedRingObj Λ.X X))) (zero_add 2) =
    (picardUnits X L).comp (kummerClass P Λ hΛ X a) (rfl : 1 + 1 = 2)

/-- The Picard-torsor Kummer boundary determines the native ordinary Chern class.
Source: lem-pur-kummer-additivity (blueprint: lem-pur-divisor-class).
Proof: apply the full Kummer connecting map to the canonical class of the
frame torsor Isom(O,L), then the root coefficient insertion. The derived
free/forgetful adjunction at the integral unit is a bijection, giving the
unique native module class. No supported class or relative pole extension is used. -/
theorem chern_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (L : X.Pic) :
    ∃! c : Abelian.Ext.{u + 2} (unit Λ X) (line P Λ hΛ X) 2,
      ChernSpec P Λ hΛ X a L c := by
  sorry

/-- The all-admissible first Chern class of an actual Picard-group line bundle.
Source: lem-pur-kummer-additivity (blueprint: lem-pur-divisor-class). -/
def firstChern (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) (L : X.Pic) :=
  (chern_existsUnique P Λ hΛ X a L).choose

/-- The independent c1(O(D)) uses the actual dual ideal as its Picard object.
Source: lem-pur-divisor-class(b) (blueprint: lem-pur-divisor-class). -/
def divisorChern (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :=
  letI := hI.isInvertible_dual_toModules
  firstChern P Λ hΛ X a (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules))

/-- Forgetting support is precomposition with the actual closed coefficient unit.
Source: lem-pur-divisor-class(b) (blueprint: lem-pur-divisor-class). -/
def forgetDivisor (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hpair : SmoothDivisorPair P a i) :=
  (DerivedCategory.singleFunctor _ 0).map
    (unitRestriction Λ i) ≫ divisorArrow P Λ hΛ a i hI hpair

/-- Canonical restriction of the supported coefficient along a support inclusion.
Precomposition with its single gives extension of supports on cohomology.
Source: lem-pur-divisor-class(c) (blueprint: lem-pur-divisor-class). -/
def supportRestriction (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D Z X : Scheme.{u}} (i : D ⟶ X) (s : Z ⟶ X) (d : D ⟶ Z)
    (hd : d ≫ s = i) : source Λ s ⟶ source Λ i :=
  (CondensedRing.lowerStar Λ.X s).map
      (unitRestriction Λ d) ≫
    (CondensedRing.lowerStarComp Λ.X d s).hom.app (unit Λ D) ≫
    (CondensedRing.lowerStarCongr Λ.X hd).hom.app (unit Λ D)

/-- Product-ideal addition of smooth codimension-one families, in the union support.
Source: lem-pur-divisor-class(c) (blueprint: lem-pur-divisor-class). -/
def DivisorAddition (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {B X : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (v : X ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)] : Prop :=
  ∀ {D₁ D₂ Z : Scheme.{u}} (i₁ : D₁ ⟶ X) (i₂ : D₂ ⟶ X) (s : Z ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion s]
    [Smooth (i₁ ≫ v)] [Smooth (i₂ ≫ v)] [Smooth (s ≫ v)]
    (hc₁ : ∀ z : D₁, ringKrullDim (X.presheaf.stalk (i₁ z)) =
      ringKrullDim (D₁.presheaf.stalk z) + (1 : WithBot ℕ∞))
    (hc₂ : ∀ z : D₂, ringKrullDim (X.presheaf.stalk (i₂ z)) =
      ringKrullDim (D₂.presheaf.stalk z) + (1 : WithBot ℕ∞))
    (hcs : ∀ z : Z, ringKrullDim (X.presheaf.stalk (s z)) =
      ringKrullDim (Z.presheaf.stalk z) + (1 : WithBot ℕ∞))
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hs : s.ker.IsInvertible), s.ker = i₁.ker * i₂.ker →
    ∀ (d₁ : D₁ ⟶ Z) (d₂ : D₂ ⟶ Z) (hd₁ : d₁ ≫ s = i₁) (hd₂ : d₂ ≫ s = i₂),
    divisorArrow P Λ hΛ (v ≫ b) s hs (smoothDivisorPair P b v n s hcs) =
      (DerivedCategory.singleFunctor _ 0).map (supportRestriction Λ i₁ s d₁ hd₁) ≫
          divisorArrow P Λ hΛ (v ≫ b) i₁ h₁ (smoothDivisorPair P b v n i₁ hc₁) +
        (DerivedCategory.singleFunctor _ 0).map (supportRestriction Λ i₂ s d₂ hd₂) ≫
          divisorArrow P Λ hΛ (v ≫ b) i₂ h₂ (smoothDivisorPair P b v n i₂ hc₂)

/-- Multiplication of arbitrary functions adds boundaries in their union support.
The inclusions d1,d2 are maps of closed subschemes, uniquely fixed by hd1,hd2.
Source: lem-pur-divisor-class(c) (blueprint: lem-pur-divisor-class). -/
def FunctionAddition (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  ∀ (U : Scheme.{u}) (e : U ⟶ X) [IsOpenImmersion e] (f₁ f₂ : Γ(U, ⊤))
    (d₁ : U.zeroLocusSubscheme {f₁} ⟶ U.zeroLocusSubscheme {f₁ * f₂})
    (d₂ : U.zeroLocusSubscheme {f₂} ⟶ U.zeroLocusSubscheme {f₁ * f₂})
    (hd₁ : d₁ ≫ U.zeroLocusSubschemeι {f₁ * f₂} = U.zeroLocusSubschemeι {f₁})
    (hd₂ : d₂ ≫ U.zeroLocusSubschemeι {f₁ * f₂} = U.zeroLocusSubschemeι {f₂}),
    principalBoundary P Λ hΛ U (e ≫ a) (f₁ * f₂) =
      (DerivedCategory.singleFunctor _ 0).map
        (supportRestriction Λ _ _ d₁ hd₁) ≫ principalBoundary P Λ hΛ U (e ≫ a) f₁ +
      (DerivedCategory.singleFunctor _ 0).map
        (supportRestriction Λ _ _ d₂ hd₂) ≫ principalBoundary P Λ hΛ U (e ≫ a) f₂

/-- The frame-glued divisor class, its comparison with the separate relative
Cartier class c_D, its independent Picard-torsor first Chern normalization, and addition.
Source: latest blueprint lem-pur-divisor-class(a)--(c)
(blueprint: lem-pur-divisor-class).
Proof: (1) smooth-pair coordinates and finite-dimensional stalks give singleton
Cartier frames. (2) Frame independence and bottom-degree supported gluing define
cl(D), with (a) by the singleton frame definition. (3) In the relative pole
extension the inverse equation maps to one; a horseshoe lift sends that one
to -d psi(f inverse), so its supported units class is the relative class of
O(D) with its canonical complementary trivialization. (4) Resolve the Kummer
sequence by a degreewise split injective short exact sequence. Apply supported,
full and complementary sections to obtain the 3 by 3 diagram. If dx=b+g,
then db+dg=d²x=0, so its two composite boundaries anticommute. Thus c_D=-cl(D)
on every equation chart, and bottom-degree separation makes the equality global.
Forgetting the relative torsor splitting gives the independently defined Picard
frame torsor, hence c_D forgets to c1(O(D)). Chern additivity identifies its
negative with c1(O(-D)). (5) Kummer and support boundaries are additive and natural
for support inclusions, giving the arbitrary-function formula. Apply that formula
on product-equation charts and bottom-degree gluing for the smooth sum to obtain
the divisor-addition formula. No sign comparison is used to define cl(D). -/
theorem divisor_class_full (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {B X D : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (v : X ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ X) [IsClosedImmersion i] [Smooth (i ≫ v)]
    (hcodim : ∀ z : D, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)) :
    ∃ hI : i.ker.IsInvertible,
      LocalEquationLaw P Λ hΛ (v ≫ b) i hI (smoothDivisorPair P b v n i hcodim) ∧
      cartierClass P Λ hΛ (v ≫ b) i hI =
        -divisorClass P Λ hΛ (v ≫ b) i hI (smoothDivisorPair P b v n i hcodim) ∧
      (DerivedCategory.singleFunctor _ 0).map (unitRestriction Λ i) ≫
        cartierArrow P Λ hΛ (v ≫ b) i hI = (divisorChern P Λ hΛ (v ≫ b) i hI).hom ∧
      forgetDivisor P Λ hΛ (v ≫ b) i hI (smoothDivisorPair P b v n i hcodim) =
        -(divisorChern P Λ hΛ (v ≫ b) i hI).hom ∧
      FunctionAddition P Λ hΛ X (v ≫ b) ∧ DivisorAddition P Λ hΛ b v n := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
