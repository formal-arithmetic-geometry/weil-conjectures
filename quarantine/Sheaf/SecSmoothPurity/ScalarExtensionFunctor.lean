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

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
import Sheaf.Paper.CompletedIntegralCoefficients
import Sheaf.SixFunctors.IntrinsicDerivedTensor
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.Paper.StratumScalarExtension
import Sheaf.Paper.LocallyConstantTensor
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.InvertibleTensorScalarExtension
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.ProEtaleConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

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
set_option warn.sorry false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The unique composition comparison fixed by balanced tensor on K-flat models.
Source: blueprint proof (4), Stacks 0G7E, 06YY
(blueprint: det-sp-scalar-extension-functor).
Proof: lem-pur-kflat-change-of-rings makes P tensor B K-flat, so both counits compute
successive extension. The published reductionBalance sends c tensor (b tensor p)
to c*g(b) tensor p, with inverse inserting 1. It is natural on chain maps and
preserves quasi-isomorphisms between K-flat models. The localization equivalence
lem-weil-pbc-site-derived-tensor-descent descends it through roofs to the displayed
natural isomorphism. Every derived object has a K-flat representative, and counits
are invertible on those representatives, so the normalization determines it uniquely. -/
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
  sorry

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
  sorry

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
  sorry

/-- The canonical identity-extension unitor, normalized by multiplication.
Source: blueprint clause (4) (blueprint: det-sp-scalar-extension-functor). -/
def scalarExtensionFunctor_identity
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    scalarExtensionFunctor (RingHom.id A) T ≅ 𝟭 _ :=
  (scalarExtensionFunctor_identity_existsUnique (A := A) T).exists.choose

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
  sorry

end AlgebraicGeometry.ProEtale
