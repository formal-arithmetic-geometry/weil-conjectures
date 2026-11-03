/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.StrictWeilDerivedScalar.StrictWeilDerivedScalarFrobenius
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Cohomology scalar extension and Frobenius for strict Weil pairs

Source: latest blueprint,
part-weights-riemann-hypothesis/sec-zeta-weil/sec-integrality-and-independence-of/
sk-thm-weil-final/prop-every-iterate-trace.proof.md,
the scalar-descent sentence and its E-model clause
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius).

The maps are homology of the specified derived comparisons, preceded by the canonical flat
scalar/homology identification. The section scalar rings are canonically the coefficient fields;
`Module.Finite` over these rings is finite dimensionality over E or Omega. The proposition
`ComparisonProperties` packages the clauses of this one statement, including the uniform local
vanishing interval. It supplies no comparison map as arbitrary data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct
namespace WeilConjectures.StrictWeilCohomologyScalar
open StrictWeilDerivedScalar

/-- The canonical flat tensor/cohomology identification. Its direction sends a tensor of a
cycle class to the class of that tensor. Source: the flat scalar identifications in the
scalar-descent sentence of prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
def flatCohomologyComparison (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    [PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E)] (i : ℤ) :
    DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (MonObj.Γ (Profinite.continuousMapRingObj E))) i ⋙
      pointSubfieldSectionExtension.{u} ell E ≅
    (pointSubfieldSectionExtension.{u} ell E).leftDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (MonObj.Γ (Profinite.padicAlgClRingObj ell))) i :=
  by
    letI : (pointSubfieldSectionExtension.{u} ell E).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ell E))).isLeftAdjoint
    exact (pointSubfieldSectionExtension.{u} ell E).leftDerivedFunctorHomologyFunctorIso i

/-- The map b_{c,i} is the flat cohomology comparison followed by H^i of the canonical b_c.
Source: latest blueprint, scalar-descent sentence of prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
def compactMap (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hFlat : PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E))
    {Y : Scheme.{u}} {a : Y ⟶ Spec (.of D.k)} (c : Compactification a)
    (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y) (i : ℤ) :
    (pointSubfieldSectionExtension ell E).obj
        ((condensedRingCompactCohomology (Profinite.continuousMapRingObj E) c i).obj K) ⟶
      (condensedRingCompactCohomology (Profinite.padicAlgClRingObj ell) c i).obj
        ((change ell E Y).obj K) := by
  letI := hFlat
  exact (flatCohomologyComparison ell E i).hom.app
      ((condensedRingCompactCoefficientComplex (Profinite.continuousMapRingObj E) c).obj K) ≫
    (NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) i).map
      (StrictWeilDerivedScalar.compactComparison D ell E c K)

/-- The map b_{x,j} is the flat cohomology comparison followed by H^j of the canonical b_x.
Exact inverse image and exact point sections identify H^j of this stalk complex with
Gamma_s xbar^* H^j(K). Source: latest blueprint, the scalar-descent sentence
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
def stalkMap (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hFlat : PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E))
    {Y : Scheme.{u}}
    (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y)
    (z : Spec (.of D.k) ⟶ Y) (j : ℤ) :
    (pointSubfieldSectionExtension ell E).obj
        ((NativeCondensedDerived.cohomology (Profinite.continuousMapRingObj E) j).obj
          (NativeCondensedDerived.stalk (Profinite.continuousMapRingObj E) D K z)) ⟶
      (NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) j).obj
        (NativeCondensedDerived.stalk (Profinite.padicAlgClRingObj ell) D
          ((change ell E Y).obj K) z) := by
  letI := hFlat
  exact (flatCohomologyComparison ell E j).hom.app
      (NativeCondensedDerived.stalk (Profinite.continuousMapRingObj E) D K z) ≫
    (NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) j).map
      (StrictWeilDerivedScalar.stalkComparison D ell E K z)

/-- The strict Omega pair with its boundedness proof attached; its structure is exactly
T(theta) after chi inverse from extendedPair. Source: latest blueprint, induced Weil structure
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
def extendedComplex (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : strictWeilComplexCategory D ell hEll Y₀ (.finite E))
    (hΩ : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left)
      (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier) :
    strictWeilComplexCategory D ell hEll Y₀ .qbar :=
  ⟨extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj, hΩ⟩

/-- A display abbreviation for the existing compact cohomology functor, with no new model.
Source: latest blueprint, H_c^i in the scalar-descent sentence
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
abbrev compactGroup
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}} {s : Scheme.{u}} {a : Y ⟶ s} (c : Compactification a)
    (K : NativeCondensedDerived.Ambient Λ Y) (i : ℤ) :=
  (condensedRingCompactCohomology Λ c i).obj K

/-- A display abbreviation for cohomology of the recorded exact scalar stalk complex.
Exactness identifies it canonically with Gamma_s z^* H^j(K).
Source: latest blueprint, stalk-vector-space convention in the scalar-descent sentence
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
abbrev stalkGroup
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : FiniteFieldDatum.{u}) {Y : Scheme.{u}} (K : NativeCondensedDerived.Ambient Λ Y)
    (z : Spec (.of D.k) ⟶ Y) (j : ℤ) :=
  (NativeCondensedDerived.cohomology Λ j).obj (NativeCondensedDerived.stalk Λ D K z)

/-- H^j of the existing local n-fold return. Positive-power index n-1 represents exponent n.
Source: latest blueprint, local Frobenius in the scalar-descent sentence
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
abbrev localOperator
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : FiniteFieldDatum.{u}) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (K : Endofunctor.IsoAlgebra (NativeCondensedDerived.pull Λ g))
    (z : Spec (.of D.k) ⟶ Y) (n : ℕ)
    (hz : z ≫ NativeCondensedModule.localPositivePower g (n - 1) =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫ z) (j : ℤ) :=
  (NativeCondensedDerived.cohomology Λ j).map
    (NativeCondensedDerived.operator Λ D g K.carrier K.str z (n - 1) hz)

/-- All degreewise clauses for the specified maps, including bounds uniform in the local lift.
This proposition packages the conclusion; its arrows are the actual b_c and b_x comparisons.
Source: latest blueprint, scalar-descent sentence of prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius). -/
structure ComparisonProperties
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : Compactification (D.geometricFiber Y₀).hom)
    (K : strictWeilComplexCategory D ell hEll Y₀ (.finite E))
    (hFlat : PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E))
    (hΩ : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left)
      (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier) : Prop where
  compact_iso : ∀ i : ℤ, IsIso (compactMap D ell E hFlat c K.obj.carrier i)
  compact_finite : ∀ i : ℤ,
    Module.Finite (MonObj.Γ (Profinite.continuousMapRingObj E))
        (compactGroup (Profinite.continuousMapRingObj E) c K.obj.carrier i) ∧
      Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj ell))
        (compactGroup (Profinite.padicAlgClRingObj ell) c
          (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier i) ∧
      Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj ell))
        ((pointSubfieldSectionExtension ell E).obj
          (compactGroup (Profinite.continuousMapRingObj E) c K.obj.carrier i))
  compact_frobenius : ∀ (i : ℤ) (m : ℕ),
    (pointSubfieldSectionExtension ell E).map
        ((End.of (GlobalGeometricFrobenius.globalGeometricFrobeniusOnCohomology
          D ell hEll Y₀ (.finite E) c K i).2) ^ m) ≫
        compactMap D ell E hFlat c K.obj.carrier i =
      compactMap D ell E hFlat c K.obj.carrier i ≫
        ((End.of (GlobalGeometricFrobenius.globalGeometricFrobeniusOnCohomology
          D ell hEll Y₀ .qbar c (extendedComplex D ell hEll E Y₀ K hΩ) i).2) ^ m)
  compact_vanishing : ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
    IsZero (compactGroup (Profinite.continuousMapRingObj E) c K.obj.carrier i) ∧
      IsZero (compactGroup (Profinite.padicAlgClRingObj ell) c
        (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier i) ∧
      IsZero ((pointSubfieldSectionExtension ell E).obj
        (compactGroup (Profinite.continuousMapRingObj E) c K.obj.carrier i))
  local_vanishing : ∃ a b : ℤ,
    ∀ (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
      (t : Spec (.of D.k) ≅ Spec (.of D.k))
      (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
      z ≫ pullback.fst Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        t.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left →
      z ≫ pullback.snd Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = t.hom →
      ∀ j : ℤ, (j < a ∨ b < j) →
      IsZero (stalkGroup (Profinite.continuousMapRingObj E) D K.obj.carrier z j) ∧
        IsZero (stalkGroup (Profinite.padicAlgClRingObj ell) D
          (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier z j) ∧
        IsZero ((pointSubfieldSectionExtension ell E).obj
          (stalkGroup (Profinite.continuousMapRingObj E) D K.obj.carrier z j))
  local_comparison : ∀ (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (b : Spec (.of D.k) ≅ Spec (.of D.k))
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (_hz₁ : z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      b.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (_hz₂ : z ≫ pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = b.hom),
    ∃ hz : z ≫ NativeCondensedModule.localPositivePower
          (D.geometricFrobenius Y₀).hom (n - 1) =
        NativeCondensedModule.localPositivePower
          (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫ z,
      ∀ j : ℤ,
        IsIso (stalkMap D ell E hFlat K.obj.carrier z j) ∧
        Module.Finite (MonObj.Γ (Profinite.continuousMapRingObj E))
          (stalkGroup (Profinite.continuousMapRingObj E) D K.obj.carrier z j) ∧
        Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj ell))
          (stalkGroup (Profinite.padicAlgClRingObj ell) D
            (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier z j) ∧
        Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj ell))
          ((pointSubfieldSectionExtension ell E).obj
            (stalkGroup (Profinite.continuousMapRingObj E) D K.obj.carrier z j)) ∧
        (pointSubfieldSectionExtension ell E).map
            (localOperator (Profinite.continuousMapRingObj E) D
              (D.geometricFrobenius Y₀).hom K.obj z n hz j) ≫
            stalkMap D ell E hFlat K.obj.carrier z j =
          stalkMap D ell E hFlat K.obj.carrier z j ≫
            localOperator (Profinite.padicAlgClRingObj ell) D
              (D.geometricFrobenius Y₀).hom
              (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj) z n hz j

private theorem perfect_finite {R : Type v} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {C : DerivedCategory (ModuleCat.{v} R)}
    (h : DerivedCategory.IsPerfectRingComplex C) (i : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C) := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := h
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C ≅ P.homology i :=
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P
  have := (hP i).2
  have : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite R (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv eH.toLinearEquiv.symm

private theorem perfect_bounds {R : Type v} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {C : DerivedCategory (ModuleCat.{v} R)}
    (h : DerivedCategory.IsPerfectRingComplex C) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C) := by
  obtain ⟨P, a, b, ha, hb, _, ⟨e⟩⟩ := h
  have := ha
  have := hb
  refine ⟨a, b, fun i hi ↦ ?_⟩
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C ≅ P.homology i :=
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P
  rcases hi with hi | hi
  · exact (P.exactAt_of_isGE a i hi).isZero_homology.of_iso eH
  · exact (P.exactAt_of_isLE b i hi).isZero_homology.of_iso eH

private theorem field_of_surjective {F R : Type*} [Field F] [CommRing R] [Nontrivial R]
    (f : F →+* R) (hf : Function.Surjective f) : IsField R := by
  refine ⟨exists_pair_ne R, mul_comm, ?_⟩
  intro a ha
  obtain ⟨x, rfl⟩ := hf a
  have hx : x ≠ 0 := fun h ↦ ha (by rw [h, map_zero])
  exact ⟨f x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

private theorem homology_intertwines
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (H : A ⥤ C) (J : B ⥤ D) (T : A ⥤ B) (S : C ⥤ D)
    (e : H ⋙ S ≅ T ⋙ J) {X : A} {Y : B}
    (f : T.obj X ⟶ Y) (v : X ⟶ X) (w : Y ⟶ Y)
    (hv : T.map v ≫ f = f ≫ w) :
    S.map (H.map v) ≫ (e.hom.app X ≫ J.map f) =
      (e.hom.app X ≫ J.map f) ≫ J.map w := by
  have hn := e.hom.naturality v
  change S.map (H.map v) ≫ e.hom.app X = e.hom.app X ≫ J.map (T.map v) at hn
  rw [← Category.assoc, hn, Category.assoc, ← J.map_comp, hv, J.map_comp,
    Category.assoc]

private theorem map_end_pow {A B : Type*} [Category A] [Category B]
    (H : A ⥤ B) {X : A} (v : End X) (m : ℕ) :
    H.map (v ^ m) = (End.of (H.map v)) ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    simp only [pow_succ, End.mul_def, H.map_comp, hm]

private theorem intertwines_powers {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) {X : A} {Y : B} (f : T.obj X ⟶ Y)
    (v : End X) (w : End Y) (h : T.map v ≫ f = f ≫ w) (m : ℕ) :
    T.map (v ^ m) ≫ f = f ≫ w ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    simp only [pow_succ, End.mul_def, T.map_comp, Category.assoc]
    rw [hm, ← Category.assoc, h, Category.assoc]

set_option maxHeartbeats 2000000 in
-- Converting the condensed derived comparisons to scalar homology unfolds large functor composites.
/-- The canonical cohomology scalar maps are Frobenius-equivariant linear isomorphisms,
with finite-dimensional groups and bounded degree support, uniformly in the local point.
Source: latest blueprint, scalar-descent sentence of prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-cohomology-scalar-frobenius).

Proof plan, following the three DAG steps:
1. Apply strictWeil_derived_scalar_frobenius to the finite-field datum, coefficient inclusion,
Y_0 and compactification. It supplies bounded constructibility of the induced Omega pair,
the canonical derived comparisons b_c and b_x, their invertibility and Frobenius equalities,
and perfectness of both source and target scalar complexes. No replacement comparison is
chosen. The point relation is the semilinear return g_Y^n xbar = xbar g_s^n.
2. Perfect complexes over the section fields have finite-dimensional cohomology in bounded
intervals. Point pullback and terminal sections are exact, so H^j of the local scalar complex
is Gamma_s xbar^* H^j(K), with the same induced return operator. The section fields are E and
Omega by the constant-section identifications. In particular tensoring their cohomology groups
preserves finite dimensionality. Flatness of this field inclusion supplies hFlat; this is a
conclusion of the theorem, not an additional hypothesis on K or on the geometry.
3. Use lem-weil-cohomology-commutes-scalar-extension: its canonical flat comparison is
flatCohomologyComparison, defined by the exact-functor homology comparison and the unique
left-derived comparison. Compose it with homology of the specified b_c or b_x to obtain
compactMap and stalkMap. They are isomorphisms. Naturality passes the derived Frobenius
identities to these maps. The degree-i global action is H^i(F_c); its powers commute with
homology by functoriality. Induct on m, starting at m=0, to obtain every global identity.
The local identity uses the stated n-fold return once. Finally boundedness of K gives
one interval outside which its cohomology sheaves vanish. Exact pullback and point sections
kill these zero sheaves at every geometric point, uniformly; the Omega comparison and
scalar extension give the same interval for both other local groups. This handles the
zero complex, empty scheme, arbitrary shifts, n=1 and m=0. -/
theorem strictWeil_cohomology_scalar_frobenius
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : Compactification (D.geometricFiber Y₀).hom) :
    ∃ hFlat : PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E),
      ∀ K : strictWeilComplexCategory D ell hEll Y₀ (.finite E),
        ∃ hΩ : boundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left)
          (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier,
          ComparisonProperties D ell hEll E Y₀ c K hFlat hΩ := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let RE := MonObj.Γ (Profinite.continuousMapRingObj.{u} E)
  let RO := MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell)
  let f : RE →+* RO := MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl ell E)
  let : Nontrivial RO := ⟨⟨1, 0, fun h ↦
    Profinite.PadicAlgCl.one_ne_zero_end_regular ell
      (by simpa only [map_one, map_zero] using congrArg Mod.regularEndRingHom h)⟩⟩
  let : Nontrivial RE := f.domain_nontrivial
  let : Field RE := (field_of_surjective (Profinite.continuousMapConstRingHom E)
    (Profinite.continuousMapConstRingHom_surjective E)).toField
  let : IsNoetherianRing RO := isNoetherianRing_of_surjective (PadicAlgCl ell) RO
    (Profinite.PadicAlgCl.constRingHom ell) (Profinite.PadicAlgCl.constRingHom_surjective ell)
  let : Algebra RE RO := f.toAlgebra
  have hf : f.Flat := by
    rw [← f.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
    infer_instance
  let hFlat : PreservesFiniteLimits (pointSubfieldSectionExtension.{u} ell E) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  refine ⟨hFlat, ?_⟩
  obtain ⟨hΩ, hc, _, hl⟩ := strictWeil_derived_scalar_frobenius D ell hEll E Y₀ c
  intro K
  refine ⟨hΩ K, ?_⟩
  obtain ⟨hci, hcE, hcO, hcF⟩ := hc K
  have := hci
  have ci (i : ℤ) : IsIso (compactMap D ell E hFlat c K.obj.carrier i) := by
    unfold compactMap
    infer_instance
  have si (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
      [IsIso (stalkComparison D ell E K.obj.carrier z)] (j : ℤ) :
      IsIso (stalkMap D ell E hFlat K.obj.carrier z j) := by
    unfold stalkMap
    infer_instance
  refine ⟨ci, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hE := perfect_finite hcE i
    have hO := perfect_finite hcO i
    have := ci i
    have ht := (Module.Finite.equiv_iff
      (asIso (compactMap D ell E hFlat c K.obj.carrier i)).toLinearEquiv.symm).1 hO
    exact ⟨hE, hO, ht⟩
  · intro i m
    apply intertwines_powers
    exact homology_intertwines
      (DerivedCategory.homologyFunctor _ i) (DerivedCategory.homologyFunctor _ i)
      (scalarChange ell E) (pointSubfieldSectionExtension ell E)
      (flatCohomologyComparison ell E i) _ _ _ hcF
  · obtain ⟨a, b, h⟩ := perfect_bounds hcE
    refine ⟨a, b, fun i hi ↦ ?_⟩
    have hE := h i hi
    have ht := (pointSubfieldSectionExtension ell E).map_isZero hE
    have := ci i
    have hO := ht.of_iso (asIso (compactMap D ell E hFlat c K.obj.carrier i)).symm
    exact ⟨hE, hO, ht⟩
  · obtain ⟨⟨a, b, hab⟩, _⟩ :=
      (mem_boundedConstructible_iff _ K.obj.carrier).1 K.property
    refine ⟨a, b, ?_⟩
    intro n hn x t z hz₁ hz₂ j hj
    obtain ⟨hz, hlocal, _⟩ := hl n hn x t z hz₁ hz₂
    have hloc := hlocal K
    have := hloc.1
    have hE := Functor.isZero_homologyFunctor_mapDerivedCategory_obj
      (NativeCondensedPoint.sections (Profinite.continuousMapRingObj E) D.k)
      (Functor.isZero_homologyFunctor_mapDerivedCategory_obj
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) z) (hab j hj))
    have ht := (pointSubfieldSectionExtension ell E).map_isZero hE
    have := si z j
    exact ⟨hE, ht.of_iso (asIso (stalkMap D ell E hFlat K.obj.carrier z j)).symm, ht⟩
  · intro n hn x b z hz₁ hz₂
    obtain ⟨hz, hlocal, _⟩ := hl n hn x b z hz₁ hz₂
    obtain ⟨hsi, hsE, hsO, hsF⟩ := hlocal K
    have := hsi
    refine ⟨hz, fun j ↦ ?_⟩
    have := si z j
    have hE := perfect_finite hsE j
    have hO := perfect_finite hsO j
    have ht := (Module.Finite.equiv_iff
      (asIso (stalkMap D ell E hFlat K.obj.carrier z j)).toLinearEquiv.symm).1 hO
    refine ⟨si z j, hE, hO, ht, ?_⟩
    exact homology_intertwines
      (DerivedCategory.homologyFunctor _ j) (DerivedCategory.homologyFunctor _ j)
      (scalarChange ell E) (pointSubfieldSectionExtension ell E)
      (flatCohomologyComparison ell E j) _ _ _ hsF

end WeilConjectures.StrictWeilCohomologyScalar
