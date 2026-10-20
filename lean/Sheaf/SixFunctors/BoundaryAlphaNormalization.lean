/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DualityPairing
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-!
# Evaluation-normalized boundary alpha on the ordinary etale derived categories

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md, second paragraph,
and the node's expanded proof steps 1--6
(blueprint: lem-weil-boundary-alpha-normalization).

Every map below is built from the recorded etale functors. The Hom-chain equivalence
is constructed from adjunctions and the canonical projection map independently of alpha.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The actual finite quotient coefficient ring, lifted to the small-etale coefficient
universe. Index n denotes level n+1, so every positive level occurs.
Source: coefficient convention (blueprint: lem-weil-boundary-alpha-normalization). -/
abbrev boundaryCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- Finiteness of the lifted positive-level quotient, from the recorded coefficient theorem.
Source: coefficient convention (blueprint: lem-weil-boundary-alpha-normalization). -/
instance boundaryCoefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (boundaryCoefficient l E n) :=
  Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))

variable (A : Type (u + 1)) [CommRing A]

/-- The descended Koszul symmetry, exactly the symmetry in AmbientDualityPairing.
Source: evaluation identities (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundarySigma (T : Scheme.{u}) (M N : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj N ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj N).obj M :=
  (etaleKoszulSymmetry A T).choose M N

/-- Evaluation DK tensor K to W, obtained from the actual tensor-Hom counit and the
Koszul symmetry. This is the evaluation normalized by AmbientDualityPairing.
Source: evaluation identities (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryEvaluation {T : Scheme.{u}} (W K : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W)).obj K ⟶ W :=
  (boundarySigma A T _ K).hom ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app W

variable [Finite A] {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- Ri_* is Ri_! for the closed immersion, and this is its ambient right adjoint.
Source: ambient exceptional adjunction (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryG := (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint

/-- The actual canonical projection map in the order FB tensor M to F(B tensor i^*M).
Source: expanded proof step 2 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryProjection (B : DerivedCategoryModule A Z) (M : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (R(lowerStar (ModuleCat.{u + 1} A) i).obj B)).obj M ⟶
      R(lowerStar (ModuleCat.{u + 1} A) i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj B).obj
          (L(upperStar (ModuleCat.{u + 1} A) i).obj M)) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app B).app M


/-- q is the exceptional transpose of PF inverse followed by 1 tensor the counit.
The three arrows before tensoring the counit are PF inverse in the node's tensor order.
Source: expanded proof step 4 (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaQ (M N : DerivedCategoryModule A T)
    (hPi : IsIso (boundaryProjection A i ((boundaryG A i).obj N) M)) :
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj (L(upperStar (ModuleCat.{u + 1} A) i).obj M)).obj
      ((boundaryG A i).obj N) ⟶
        (boundaryG A i).obj (((derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj N) :=
  letI := hPi
  (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).homEquiv _ _
    (R(lowerStar (ModuleCat.{u + 1} A) i).map (boundarySigma A Z _ _).hom ≫
      inv (boundaryProjection A i ((boundaryG A i).obj N) M) ≫
      (boundarySigma A T _ M).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj M).map
        ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app N))

/-- The specified r_K, with DK equal to RHom(K,W), not a separately supplied object.
Source: evaluation-normalized r (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaR (W K : DerivedCategoryModule A T)
    (hPi : IsIso (boundaryProjection A i
      ((boundaryG A i).obj (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W)) K)) :
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      ((boundaryG A i).obj (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W))).obj
        (L(upperStar (ModuleCat.{u + 1} A) i).obj K) ⟶ (boundaryG A i).obj W :=
  (boundarySigma A Z _ _).hom ≫
    boundaryAlphaQ A i K (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W) hPi ≫
    (boundaryG A i).map
      ((boundarySigma A T K _).hom ≫ boundaryEvaluation A W K)

/-- Alpha is the tensor-Hom transpose of the specified r_K with its signed symmetry.
Source: normalized comparison (blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlpha (W K : DerivedCategoryModule A T)
    (hPi : IsIso (boundaryProjection A i
      ((boundaryG A i).obj (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W)) K)) :
    (boundaryG A i).obj (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) Z).obj
        (op (L(upperStar (ModuleCat.{u + 1} A) i).obj K))).obj ((boundaryG A i).obj W) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      (L(upperStar (ModuleCat.{u + 1} A) i).obj K)).homEquiv _ _
    ((boundarySigma A Z _ _).hom ≫ boundaryAlphaR A i W K hPi)

/-- The independent composite of six bijections: exceptional adjunction, tensor-Hom,
first symmetry, projection, exceptional adjunction, and symmetry followed by tensor-Hom.
It never mentions alpha. Source: expanded proof steps 1--3
(blueprint: lem-weil-boundary-alpha-normalization). -/
def boundaryAlphaHomChain (W K : DerivedCategoryModule A T) (B : DerivedCategoryModule A Z)
    (hPi : IsIso (boundaryProjection A i B K)) :
    (B ⟶ (boundaryG A i).obj (((derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj W)) ≃
      (B ⟶ ((derivedHom (ModuleCat.{u + 1} A) Z).obj
        (op (L(upperStar (ModuleCat.{u + 1} A) i).obj K))).obj ((boundaryG A i).obj W)) :=
  letI := hPi
  ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).homEquiv B _).symm |>.trans
    (((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).homEquiv _ W).symm) |>.trans
    (Iso.homCongr (boundarySigma A T K _) (Iso.refl W)) |>.trans
    (Iso.homCongr (asIso (boundaryProjection A i B K)) (Iso.refl W)) |>.trans
    ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).homEquiv _ W) |>.trans
    (Iso.homCongr (boundarySigma A Z B _) (Iso.refl ((boundaryG A i).obj W))) |>.trans
    ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      (L(upperStar (ModuleCat.{u + 1} A) i).obj K)).homEquiv B _)

/-- The structure-map exceptional inverse image of the constant coefficient object.
Source: omega_T convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryOmegaT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :=
  dualizingComplex (ModuleCat.{u + 1} A) aT

/-- The actual contravariant RHom into omega_T.
Source: D_T convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryDT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :=
  verdierDual (ModuleCat.{u + 1} A) aT

/-- The actual contravariant RHom into omega_Z = i^times omega_T.
Source: D_Z convention (blueprint: lem-weil-boundary-alpha-normalization). -/
noncomputable def boundaryDZ {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :=
  (derivedHom (ModuleCat.{u + 1} A) Z).flip.obj ((boundaryG A i).obj (boundaryOmegaT A aT))

/-- The evaluation-normalized closed-costalk comparison is an isomorphism, realizes
exactly the displayed Hom chain on finite-Tor constructible tests, and is contravariantly
natural in every admissible K. All functors and all arrows are the canonical etale ones.

Source: cor-weil-boundary-duality-discharge.proof.md, second paragraph;
expanded node proof steps 1--6 (blueprint: lem-weil-boundary-alpha-normalization).

Proof:
1. Tensor-Hom adjunction on the ordinary small etale ringed sites gives the two
   currying bijections. The exceptional adjunction is on the whole ordinary derived
   category, so it applies before restricting to finite-Tor constructible test objects.
2. Write pi(B,M) for the canonical FB tensor M to F(B tensor i^*M) projection. In the
   opposite tensor order PF is symmetry, pi, and F of symmetry. Thus its inverse is
   precisely the three arrows used in boundaryAlphaQ. Projection naturality gives a
   bijection on Hom by precomposition with pi inverse.
3. Compose the two adjunctions, the currying bijections and these two symmetry changes.
   This is boundaryAlphaHomChain, independently of alpha. On b its first part is
   evaluation after the exceptional counit composed with F(b) tensor the identity.
4. Transpose r_K back through the exceptional adjunction. Naturality of symmetry
   and the projection map cancel the two signed interchanges. The result is exactly
   the previous Hom-chain value at b = identity. Naturality in b then identifies the
   chain at every b with b followed by this particular evaluation-normalized alpha.
5. Set X = G(D_T K), Y = D_Z(i^*K). Both are finite-Tor constructible by hGDK and
   hdual applied to hiK. Surjectivity of the chain at Y gives gamma with gamma alpha
   equal to identity. Injectivity of the chain at X gives alpha gamma equal to
   identity. This proves that the specified alpha is an isomorphism without testing
   on arbitrary pro-etale objects.
6. Evaluation dinaturality, projection naturality in K, and the two adjunction
   naturality identities identify the chain on G(D_T u) b with D_Z(i^*u) after the
   chain for K'. Take b = identity and use step 4. This proves the displayed
   contravariant naturality equation, with the same signed symmetry throughout.
-/
theorem boundaryAlphaNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M))
    (K : DerivedCategoryModule (boundaryCoefficient l E n) T)
    (hK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K)
    (_hDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
      ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K)))
    (_hiK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K))
    (hGDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      ((boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))))
    (_hdual : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryDZ (boundaryCoefficient l E n) i aT).obj (op B))) :
    IsIso (boundaryAlpha (boundaryCoefficient l E n) i
      (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK)) ∧
    (∀ (B : DerivedCategoryModule (boundaryCoefficient l E n) Z)
      (hB : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B)
      (b : B ⟶ (boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))),
      boundaryAlphaHomChain (boundaryCoefficient l E n) i
        (boundaryOmegaT (boundaryCoefficient l E n) aT) K B (hPF B hB.1 K hK) b =
      b ≫ boundaryAlpha (boundaryCoefficient l E n) i
        (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK)) ∧
    (∀ (K' : DerivedCategoryModule (boundaryCoefficient l E n) T)
      (hK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K')
      (_hDK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K')))
      (_hiK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K'))
      (hGDK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryG (boundaryCoefficient l E n) i).obj
          ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K'))))
      (u : K ⟶ K'),
      (boundaryG (boundaryCoefficient l E n) i).map
          ((boundaryDT (boundaryCoefficient l E n) aT).map u.op) ≫
        boundaryAlpha (boundaryCoefficient l E n) i
          (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK) =
      boundaryAlpha (boundaryCoefficient l E n) i
          (boundaryOmegaT (boundaryCoefficient l E n) aT) K' (hPF _ hGDK'.1 K' hK') ≫
        (boundaryDZ (boundaryCoefficient l E n) i aT).map
          (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).map u).op) := by
  sorry

end AlgebraicGeometry.Etale
