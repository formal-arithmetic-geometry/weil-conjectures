/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.IteratedWeilCocycle
public import Sheaf.Paper.TraceFormulaLocalFrobeniusOperator
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import Sheaf.SixFunctors.FrobeniusFixedPoints
public import Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws
public import WeilConjectures.ZetaSeries

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.FieldTheory.UniqueSubfieldOfClosure
import Sheaf.SixFunctors.SchemeFrobenius
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.IteratedWeilMap
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization
import Sheaf.Paper.CompactSupportPerfectness

/-!
# Local Frobenius conjugacy along the normalized orbit

Source: Weil conjectures blueprint, main-20261015, sec-trace-formula/sk-c-proper-global,
lem-trf-local-frobenius-conjugacy.md (blueprint: lem-trf-local-frobenius-conjugacy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.Scheme

/-- The stalk at the identity point is evaluation at the final site object, with its
canonical germ normalization. Source: Stacks Tag 0993 and the pointed-neighbourhood
colimit (blueprint: lem-trf-local-frobenius-conjugacy).
Proof: the neighbourhood `(s,id)` is initial: its unique arrow to `(U,u)` is `u`.
It is terminal after taking opposites. The colimit is therefore evaluation at this
terminal object. The displayed restriction sends `[U,u,a]` to `u^*a` and respects
all colimit relations and the constant scalar action. Its inverse inserts a section
as a germ at `(s,id)`. These formulas are natural in module maps and determine both
maps uniquely. -/
theorem proEtalePointStalkSections_existsUnique
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] :
    ∃! e : finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A ≅
        WeilConjectures.pointFiniteSections k A,
      ∀ (M : proEtaleRingModules (Spec (.of k))
          (proEtaleConstantRing (Spec (.of k)) A))
        (N : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k))))
        (a : M.val.obj (op N.right)),
        e.hom.app M (proEtaleCoefficientModuleGerm (𝟙 _) A M N a) =
          M.val.map ((ProEt.forget (Spec (.of k))).preimage
            (X := ProEt.mk (𝟙 (Spec (.of k)))) (Y := N.right) N.hom).op a := by
  sorry

/-- The uniquely germ-normalized evaluation comparison. Source: Stacks Tag 0993
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def proEtalePointStalkSections
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] :
    finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A ≅
      WeilConjectures.pointFiniteSections k A :=
  (proEtalePointStalkSections_existsUnique k A).exists.choose

/-- Exact point evaluation and the exact stalk have the same derived localization.
Source: Stacks Tags 0993 and 0D6D
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def proEtalePointDerivedStalkSections
    (D : WeilConjectures.FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    proEtaleFiniteCoefficientDerivedStalk A (𝟙 (Spec (.of D.k))) ≅
      (WeilConjectures.pointFiniteSections D.k A).mapDerivedCategory :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  Functor.mapDerivedCategoryNatIso (proEtalePointStalkSections D.k A)

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The arithmetic field Frobenius sigma(c)=c^q, using the existing finite-field
Frobenius equivalence. Source: blueprint local Frobenius conjugacy, opening conventions
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localArithmeticFrobenius (T : TraceFormulaCoefficientConventions.{u}) :
    T.datum.k ≃+* T.datum.k :=
  letI := Fintype.ofFinite T.datum.k₀
  (FiniteField.frobeniusAlgEquivOfAlgebraic T.datum.k₀ T.datum.k).toRingEquiv

/-- The normalized Galois orbit: source reparametrization makes each translate a k-point.
This is the explicit formula G^i(z)=Spec(sigma^i) followed by z and then g^i.
Source: blueprint local Frobenius conjugacy, clause 1
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusOrbit (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) (i : ℕ) :
    Spec (.of T.datum.k) ⟶ T.geometricBaseChange :=
  Spec.map (CommRingCat.ofHom ((T.localArithmeticFrobenius ^ i).toRingHom)) ≫
    (z ≫ (End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ i)

/-- The lifts of x are k-morphisms whose projection has image x.
Source: blueprint local Frobenius conjugacy, opening paragraph
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def IsLocalFrobeniusLift (T : TraceFormulaCoefficientConventions.{u}) (x : T.X₀.left)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) : Prop :=
  z ≫ T.structureMap = 𝟙 _ ∧
    (z ≫ pullback.fst T.X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))).base
        (IsLocalRing.closedPoint T.datum.k) = x

/-- Scalar extension of an extension-field rational point, expressed by its model
projection. For a k-point the other projection is the identity, so this characterizes
precisely its scalar extension by the fibre-product universal property.
Source: blueprint local Frobenius conjugacy, clause 1
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def RepresentsLocalFrobeniusLift (T : TraceFormulaCoefficientConventions.{u})
    (m : ℕ) (hm : 1 ≤ m) (y : T.datum.extensionPoints T.X₀ m hm)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) : Prop :=
  z ≫ pullback.fst T.X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) =
    Spec.map (CommRingCat.ofHom (T.datum.extensionSubfield m hm).subtype) ≫ y.left

/-- The canonical comparison from Fib_s(Lz^*K) to the derived geometric stalk.
At the identity point the comparison sends [U,u,a] to u^*a, so its normalization
agrees with evaluation at s, not with an arbitrary isomorphism of point complexes.
Source: Stacks Tags 0993 and 05V1; blueprint local Frobenius conjugacy, proof steps 3--4
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFibreStalkComparison (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :
    T.finiteLocalFibre z ≅ proEtaleFiniteCoefficientDerivedStalk T.coefficientRing z :=
  Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback T.coefficientRing z)
      (proEtalePointDerivedStalkSections T.datum T.coefficientRing).symm ≪≫
    proEtaleDerivedPullbackStalkComparison T.coefficientRing z (𝟙 _) ≪≫
    eqToIso (congrArg (proEtaleFiniteCoefficientDerivedStalk T.coefficientRing)
      (Category.id_comp z))

/-- The recorded Weil iterate, extended to exponent zero by canonical identity pullback.
Source: blueprint local Frobenius conjugacy, clause 2
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localWeilIterate (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) : (i : ℕ) →
    (proEtaleConstantRingDerivedPullback T.coefficientRing
      ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ i)).obj K.obj.carrier ≅
        K.obj.carrier
  | 0 => eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      (pow_zero (End.of (T.datum.geometricGaloisFrobenius T.X₀)))) ≪≫
    (proEtaleStalkDerivedIdentityPullback T.coefficientRing T.geometricBaseChange).app
      K.obj.carrier
  | i + 1 => T.iteratedWeilIsomorphismSucc K i

/-- The specified transport T_i = phi^[i] c_i^{-1} r_{p_i,sigma^i}^{-1}, in actual
point-fibre coordinates. It is indexed by an integer iterate, without reducing modulo d.
Source: blueprint local Frobenius conjugacy, clause 2
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusTransport (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) (i : ℕ) :
    (T.finiteLocalFibre (T.localFrobeniusOrbit z i)).obj K.obj.carrier ≅
      (T.finiteLocalFibre z).obj K.obj.carrier :=
  (T.localFibreStalkComparison (T.localFrobeniusOrbit z i)).app K.obj.carrier ≪≫
    (proEtaleDerivedStalkReparam T.coefficientRing
      (z ≫ (End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ i)
      (T.localArithmeticFrobenius ^ i)).symm.app K.obj.carrier ≪≫
    (proEtaleDerivedPullbackStalkComparison T.coefficientRing
      ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ i) z).symm.app K.obj.carrier ≪≫
    (proEtaleFiniteCoefficientDerivedStalk T.coefficientRing z).mapIso
      (T.localWeilIterate K i) ≪≫
    (T.localFibreStalkComparison z).symm.app K.obj.carrier

/-- The lifts form one degree-d normalized Frobenius orbit; the specified transports
satisfy the zero and cocycle laws, conjugate every multiple-degree local operator,
and preserve its categorical trace. The one-circuit conjugacy class is lift-independent.

Source: main-20261015 blueprint, sec-trace-formula/sk-c-proper-global,
lem-trf-local-frobenius-conjugacy.md, clauses 1--3, with the DAG's explicit semilinear
reparametrization and zero-iterate conventions
(blueprint: lem-trf-local-frobenius-conjugacy).

Proof (the eight steps of the DAG):
1. The geometric-point dictionary and fibre-product universal property identify the
   lifts with k₀-embeddings of the finite residue field into k. Its cardinality is q^d
   by a residue-field basis. Finite-field Galois Frobenius gives exactly d embeddings,
   since all images are the unique q^d-element subfield of the algebraic closure.
2. On affine coordinates, Spec(sigma) followed by z and g sends a tensor a tensor b
   to e(a)^q b. Thus G cycles these embeddings. If d divides m, each embedding factors
   uniquely through F_(q^m). The q^m-power coordinate formula fixes z, and
   thm-trf-frobenius-fixed-points identifies the corresponding rational component.
3. Reparametrize pointed neighbourhoods by precomposing their lift with Spec(alpha),
   preserving every section. The inverse uses alpha inverse. Colimits give the existing
   canonical A-linear reparametrization. Exactness descends it to derived complexes.
   At the identity point the colimit is evaluation at s, precisely Fib_s.
4. lem-trf-proetale-pullback-stalk-coherence supplies the germ-normalized comparison,
   its identity and composition laws and its reparametrization compatibility.
5. Combine those laws with lem-trf-iterated-weil-cocycle. Both composites first remove
   sigma^(i+j), insert the same section in the iterated base-change neighbourhood,
   and apply the successive Weil factors. The displayed T cocycle follows. For a zero
   index the canonical identity comparisons give T_0=id. No periodicity of T is used.
6. Use the scheme/Galois comparison specified by absolute-Frobenius trivialization.
   lem-trf-frobenius-stalk-trivialization-normalization identifies its stalk, after
   the pullback comparisons, with inverse reparametrization by sigma^m. Hence the
   local operator defined by rho, kappa and phi^[m] is exactly the circuit transport.
7. The two cocycle factorizations of T_(i+m)=T_(m+i), with G^m z=z, give
   T_i F_(z_i,m)=F_(z,m) T_i. Compose with T_i inverse to obtain the stated conjugacy.
8. prop-trf-compact-support-perfectness gives perfect ordinary-module geometric
   stalks for the bounded constructible finite-Tor carrier. The canonical Fib/stalk
   comparison transfers this to the displayed fibre complexes. Conjugacy invariance
   in prop-trf-trace-formal-laws gives equal categorical traces. Set m=d and use the
   enumeration of all lifts to obtain independence of the one-circuit conjugacy class.

HEq in the zero and cocycle laws expresses equality after the equality of their source
points, also stated explicitly below. All operators and transports have the literal
Fib_s(Lz^*K) as source and target. -/
theorem local_frobenius_conjugacy
    (T : TraceFormulaCoefficientConventions.{u}) (K : T.strictWeilComplex)
    (x : T.X₀.left) (_hx : IsClosed ({x} : Set T.X₀.left)) :
    letI : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    Nat.card {z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange //
      T.IsLocalFrobeniusLift x z} = T.X₀.hom.degreeOver x ∧
    ∀ (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
      (_hz : T.IsLocalFrobeniusLift x z),
    ∃ (hd : 1 ≤ T.X₀.hom.degreeOver x)
      (hP : ∀ i : ℕ, DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((T.finiteLocalFibre (T.localFrobeniusOrbit z i)).obj K.obj.carrier))
      (hP₀ : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((T.finiteLocalFibre z).obj K.obj.carrier)),
      (∀ i : ℕ, T.IsLocalFrobeniusLift x (T.localFrobeniusOrbit z i)) ∧
      Function.Injective
        (fun i : Fin (T.X₀.hom.degreeOver x) ↦ T.localFrobeniusOrbit z i.val) ∧
      (∀ (w : Spec (.of T.datum.k) ⟶ T.geometricBaseChange),
        T.IsLocalFrobeniusLift x w →
        ∃ i : Fin (T.X₀.hom.degreeOver x), T.localFrobeniusOrbit z i.val = w) ∧
      (∀ i : ℕ, T.localFrobeniusOrbit z (i + T.X₀.hom.degreeOver x) =
        T.localFrobeniusOrbit z i) ∧
      (∀ i : ℕ, T.localFrobeniusOrbit z i =
        ((fun w ↦ T.localFrobeniusOrbit w 1)^[i]) z) ∧
      (∀ i j : ℕ, T.localFrobeniusOrbit (T.localFrobeniusOrbit z i) j =
        T.localFrobeniusOrbit z (i + j)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), T.X₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∃! y : T.datum.extensionPoints T.X₀ m hm,
          T.RepresentsLocalFrobeniusLift m hm y (T.localFrobeniusOrbit z i)) ∧
      HEq (T.localFrobeniusTransport K z 0).hom
        (𝟙 ((T.finiteLocalFibre z).obj K.obj.carrier)) ∧
      (∀ i j : ℕ,
        HEq (T.localFrobeniusTransport K z (i + j)).hom
          ((T.localFrobeniusTransport K (T.localFrobeniusOrbit z i) j).hom ≫
            (T.localFrobeniusTransport K z i).hom)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), T.X₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∃ (hf₀ : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z)
          (hfᵢ : T.localFrobeniusOrbit z i ≫ T.datum.schemeFrobeniusIterate T.X₀ m =
            T.localFrobeniusOrbit z i),
          T.finiteLocalFrobenius K m hm (T.localFrobeniusOrbit z i) hfᵢ =
            (T.localFrobeniusTransport K z i).hom ≫ T.finiteLocalFrobenius K m hm z hf₀ ≫
              (T.localFrobeniusTransport K z i).inv ∧
          DerivedCategory.perfectCategoricalTrace.{u + 1}
              ((T.finiteLocalFibre (T.localFrobeniusOrbit z i)).obj K.obj.carrier) (hP i)
              (T.finiteLocalFrobenius K m hm (T.localFrobeniusOrbit z i) hfᵢ) =
            DerivedCategory.perfectCategoricalTrace.{u + 1}
              ((T.finiteLocalFibre z).obj K.obj.carrier) hP₀
              (T.finiteLocalFrobenius K m hm z hf₀)) ∧
      (∀ (w : Spec (.of T.datum.k) ⟶ T.geometricBaseChange),
        T.IsLocalFrobeniusLift x w →
        ∃ (hf₀ : z ≫ T.datum.schemeFrobeniusIterate T.X₀ (T.X₀.hom.degreeOver x) = z)
          (hf₁ : w ≫ T.datum.schemeFrobeniusIterate T.X₀ (T.X₀.hom.degreeOver x) = w)
          (e : (T.finiteLocalFibre w).obj K.obj.carrier ≅
            (T.finiteLocalFibre z).obj K.obj.carrier),
          T.finiteLocalFrobenius K (T.X₀.hom.degreeOver x) hd w hf₁ =
            e.hom ≫ T.finiteLocalFrobenius K (T.X₀.hom.degreeOver x) hd z hf₀ ≫ e.inv) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
