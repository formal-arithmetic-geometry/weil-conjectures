/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.SixFunctors.EtaleHomThickLocus
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.Paper.SfHomTriangulated
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Paper.PrimeFieldTensorDevissage
import Sheaf.Paper.CtfHomCoefficientComparison

/-!
# Dualizing complexes under extension of coefficients

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Definition 7.1.1, Theorems 7.1.3 and 7.6.1, printed pp. 300--301 and 310--311
(blueprint: lem-per-coefficient-change-dualizing).

All functors use ordinary small-etale module sheaves. General-ring constructibility
uses finitely generated stalks, whereas the original finite-ring predicate uses finite
constant values. The biduality arrow below is the transpose of signed evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.CoefficientChangeDualizing

/-- Internal Hom into K, with its existing contravariant functoriality.
Source: ILO XVII, Definition 7.1.1 (blueprint: lem-per-coefficient-change-dualizing). -/
abbrev dual (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (K : DerivedCategoryModule R X) :
    (DerivedCategoryModule R X)ᵒᵖ ⥤ DerivedCategoryModule R X :=
  (derivedHom (ModuleCat.{u + 1} R) X).flip.obj K

/-- The canonical evaluation-transpose biduality arrow. Evaluation first swaps
DK and M by the descended signed symmetry and then applies the tensor-Hom counit.
Source: ILO XVII, Definition 7.1.1 (blueprint: lem-per-coefficient-change-dualizing). -/
def biduality (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (K M : DerivedCategoryModule R X) :
    M ⟶ (dual R X K).obj (op ((dual R X K).obj (op M))) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} R)
    ((dual R X K).obj (op M))).homEquiv M K
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app
        ((dual R X K).obj (op M))).app M ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) M).counit.app K)

/-- The existing evaluation-normalized natural coefficient comparison. Its defining
transpose equation determines every component uniquely; this selects determined data.
Source: ILO XVII, Theorem 7.6.1 (blueprint: lem-per-coefficient-change-dualizing). -/
def homComparison {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (X : Scheme.{u}) (φ : R →+* S) (K : DerivedCategoryModule R X) :
    EtaleHomLeft X φ K ⟶ EtaleHomRight X φ K :=
  (etaleHomComparison_thickLocus X φ).choose K

/-- Extension of a prime-field dualizing complex gives duality on bounded constructible
complexes of finite Tor amplitude over every commutative Noetherian coefficient algebra.
The finite-field clause uses the original finite-coefficient category. The last clause
pins both internal-Hom identifications to their canonical evaluation transposes and
identifies the actual biduality arrows, rather than merely their endpoints.

Source: ILO XVII, Definition 7.1.1, Theorems 7.1.3 and 7.6.1, pp. 300--301, 310--311
(blueprint: lem-per-coefficient-change-dualizing).

Proof:
1. Split the prime-field stalk complexes into their cohomology. Extension gives bounded
   finite free stalks on a common finite stratification. Tensoring with any module sheaf
   keeps the same interval, by lem-sfb-etale-derived-tensor-stalk and exact conservative
   geometric stalks (prop-weil-pbc-geometric-stalks-exact and
   lemma-weil-pbc-geometric-stalk-conservative). Over a field, ctf equals bc.
2. Apply lem-per-ctf-hom-coefficient-comparison to (M,K_A) and then (D_A M,K_A).
   This proves preservation and gives the evaluation-normalized coefficient comparisons.
3. Put beta = Hom(alpha_M inverse,1) alpha_(D M). Uncurrying beta T(delta_M)
   gives extended evaluation composed with 1 tensor alpha_M inverse. The defining
   evaluation identity for alpha makes this evaluation over A. Uniqueness of transpose
   gives beta T(delta_M)=delta_(T M), naturally in M.
4. Over any extension field, the biduality-isomorphism locus is closed under shifts,
   cones, finite sums and retracts, using lem-sf-hom-triangulated and the cohomology
   long exact sequence of lem-sf-derived-homology-long-exact.
5. The generators from lem-per-prime-field-tensor-devissage are finite sums of extended
   prime-field complexes. Step 3 proves biduality on them, hence on the whole category.
6. Reduce an A-complex modulo every maximal ideal. The comparison in Step 2 and tensor
   associativity identify the reduced biduality with field biduality from Step 5.
   By lem-kun-derived-tensor-triangulated, the reduced cone vanishes.
7. Each geometric stalk of the cone is bounded with finite cohomology over Noetherian A.
   Apply lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and then
   lem-weil-pbc-pseudocoherent-maximal-fibre-perfect with a=b=i+1 for each degree i.
   All stalk cohomology vanishes, so conservative exact stalks make the cone zero.
8. Naturality of evaluation gives the natural biduality isomorphisms. For finite fields,
   finite generation is finiteness of stalks and every bounded complex has finite Tor
   amplitude. Step 3 supplies the final displayed coefficient-compatibility equation.
-/
theorem coefficient_change_dualizing
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X)
    (hK : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X K)
    (hdual : ∀ N : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X N →
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X
          ((dual _ X K).obj (op N)) ∧ IsIso (biduality _ X K N))
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    [Algebra (ULift.{u + 1} (ZMod ℓ)) A] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
      ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K) ∧
    (∀ M : DerivedCategoryModule A X,
      DerivedCategory.boundedConstructibleFiniteTor A X M →
        DerivedCategory.boundedConstructibleFiniteTor A X
          ((dual A X
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).obj (op M)) ∧
        IsIso (biduality A X
          ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K) M)) ∧
    (∀ (M N : DerivedCategoryModule A X)
      (_hM : DerivedCategory.boundedConstructibleFiniteTor A X M)
      (_hN : DerivedCategory.boundedConstructibleFiniteTor A X N) (f : M ⟶ N),
      f ≫ biduality A X
          ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K) N =
        biduality A X
          ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K) M ≫
          ((dual A X
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).rightOp ⋙
            dual A X
              ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).map f) ∧
    (IsField A → ∀ [Finite A] (M : DerivedCategoryModule A X),
      DerivedCategory.isBoundedConstructible A X M →
        DerivedCategory.isBoundedConstructible A X
          ((dual A X
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).obj (op M)) ∧
        IsIso (biduality A X
          ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K) M)) ∧
    ∀ N : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X,
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X N →
      ∃ (α : (scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj
              ((dual _ X K).obj (op N)) ≅
            (dual A X
              ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).obj
                (op ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj N)))
        (β : (scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj
              ((dual _ X K).obj (op ((dual _ X K).obj (op N)))) ≅
            (dual A X
              ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).obj
                (op ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj
                  ((dual _ X K).obj (op N))))),
        α.hom = (homComparison X (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) K).app (op N) ∧
        β.hom = (homComparison X (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) K).app
          (op ((dual _ X K).obj (op N))) ∧
        (scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).map
            (biduality _ X K N) ≫ β.hom ≫
          (dual A X
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)).map α.inv.op =
          biduality A X
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj K)
            ((scalarExtension (algebraMap (ULift.{u + 1} (ZMod ℓ)) A) X).obj N) := by
  sorry

end AlgebraicGeometry.Etale.CoefficientChangeDualizing
