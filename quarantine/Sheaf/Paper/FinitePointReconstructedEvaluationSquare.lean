/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.FinitePointReconstructedHomModel
public import Sheaf.Paper.PointFibreDerivedTensor
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Paper.PointDerivedHomEvaluation
import Sheaf.SixFunctors.PointRingedEvaluationModel
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Signed evaluation for reconstructed finite-point Hom

Source: Weil blueprint, sec-six-functors/sk-thm-sf-package,
`lem-pod-point-dualizing-complex.proof.md`, second sentence; Stacks 0A8X, 0A95 and 07A4
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square).

Positive coefficient exponents are indexed by `n + 1`. The comparison below is the
recorded reconstruction counit followed by the recorded normalized Hom comparison.
The pairing uses the inverse of the recorded finite point tensorator and its unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct

namespace WeilConjectures.FinitePointEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

variable (L : ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1)) ⥤
    FinitePointHom.Mod D l E (n + 1))
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits (FinitePointHom.G D l E (n + 1))]
  [PreservesFiniteColimits (FinitePointHom.G D l E (n + 1))]
  (adj : L ⊣ FinitePointHom.G D l E (n + 1))
  (hr : FinitePointHom.Reconstruction D l E (n + 1) L
    (Nat.succ_le_succ (Nat.zero_le n)) adj)
  (q : (c : DerivedCategory (ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1)))) →
    DerivedCategory.pointFiniteCohomology (FinitePointHom.A l E (n + 1)) c →
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1))) →
      (FinitePointHom.qSource D l E (n + 1) L).obj (op c, V) ≅
        (FinitePointHom.qTarget D l E (n + 1)).obj (op c, V))

/-- The actual reconstructed Hom arrow: contravariant counit, then the normalized q.
Source: the formula Q in the recorded reconstructed Hom model
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square). -/
def reconstructedMap
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1))) :=
  (FinitePointHom.G D l E (n + 1)).mapDerivedCategory.map
      ((FinitePointHom.H D l E (n + 1)).map
        (Prod.mkHom (adj.mapDerivedCategoryAdjunction.counit.app C.obj).op (𝟙 V))) ≫
    (q _ (hr C.obj C.property.1).1 V).hom

/-- Beta is Q after the specified target isomorphism and the same point unit comparison.
Source: blueprint point duality, second sentence
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square). -/
def beta (S : PointFiniteTensorData D l E n)
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1)))
    (α : V ≅ (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit) :=
  (FinitePointHom.G D l E (n + 1)).mapDerivedCategory.map
      ((FinitePointHom.H D l E (n + 1)).map (Prod.mkHom (𝟙 (op C.obj)) α.hom)) ≫
    reconstructedMap D l E n L adj hr q C
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit ≫
    (ordinaryModuleDerivedInternalHom (FinitePointHom.A l E (n + 1))).map
      (Prod.mkHom (𝟙 (op ((FinitePointHom.G D l E (n + 1)).mapDerivedCategory.obj C.obj)))
        S.unitIso.hom)

/-- The specified sheaf evaluation pairing after the inverse point tensorator and unit.
Source: blueprint point duality, second sentence
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square). -/
def pairing (S : PointFiniteTensorData D l E n)
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1)))
    (α : V ≅ (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit)
    (hH : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Spec (.of D.k)) ((FinitePointHom.H D l E (n + 1)).obj (op C.obj, V))) :=
  (pointFiniteTensorComparison D l E n S
    ⟨(FinitePointHom.H D l E (n + 1)).obj (op C.obj, V), hH⟩ C).inv ≫
    (FinitePointHom.G D l E (n + 1)).mapDerivedCategory.map
      (finiteIntrinsicEvaluation l E (Spec (.of D.k)) n C.obj V ≫ α.hom) ≫
    S.unitIso.hom

/-- Transpose of the specified Hom-first pairing, using the coefficient Koszul braiding.
Source: Stacks 08J9, blueprint point duality, second sentence
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square). -/
def pairingTranspose (S : PointFiniteTensorData D l E n)
    (C : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1)))
    (α : V ≅ (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit)
    (hH : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Spec (.of D.k)) ((FinitePointHom.H D l E (n + 1)).obj (op C.obj, V))) :=
  MonoidalClosed.curry
    (((pointModuleDerivedBraiding (FinitePointHom.A l E (n + 1))).braiding
      ((FinitePointHom.G D l E (n + 1)).mapDerivedCategory.obj C.obj)
      ((FinitePointHom.G D l E (n + 1)).mapDerivedCategory.obj
        ((FinitePointHom.H D l E (n + 1)).obj (op C.obj, V)))).hom ≫
      pairing D l E n S C V α hH)

/-- Signed evaluation and derived naturality of the actual reconstructed Hom comparison.
All data parameters are the normalized witnesses supplied by the dependencies. In
particular q is constrained on resolving representatives, and S is constrained by
its K-flat generator model. No new tensorator or unit identification is selected.

Source: Weil blueprint, sec-six-functors/sk-thm-sf-package,
`lem-pod-point-dualizing-complex.proof.md`, second sentence; Stacks 0A8X, 0A95, 07A4
(blueprint: lem-coef-finite-point-reconstructed-evaluation-square).

Proof:
1. The coefficient unit has constructible cohomology and Tor amplitude [0,0]. Hence
   V, identified with it, has these properties. Apply finite constructible Hom on
   the zero-dimensional point to C,V to obtain the finite-Tor witnesses hH.
2. The normalized point derived-Hom evaluation supplies the chain comparison on a
   flat-term K-flat P and K-injective J. It evaluates x,h to (-1)^(i*j) h(1 tensor x).
   The ringed point evaluation model identifies its balancing map with the inverse
   canonical tensorator of pointFibreDerivedTensor, on every K-flat presentation.
3. Precompose this evaluation identity by Hom(e_C,B). Naturality of the closed
   counit and of the tensorator replaces Lc by C. The actual adjunction triangle
   Gamma(e_C) u_c = identity cancels the reconstruction unit. The resulting Hom
   arrow is exactly reconstructedMap, by its defining composite.
4. Apply target naturality to alpha. This gives the pairing equality for beta.
   Input-first evaluation has the sign in step 2 on both sides; Koszul braiding
   gives the Hom-first convention. The unit is S.unitIso throughout.
5. Naturality of reconstructed Q for every derived morphism and bifunctoriality
   of internal Hom give the displayed contravariant beta square. Localization
   gives it also for inverses of quasi-isomorphisms, without choosing chain maps.
6. The closed coefficient tensor-Hom adjunction is a bijection. Its inverse is
   evaluation after tensoring with identity, with the stated braiding. Applying
   this bijection to the pairing equality identifies beta with pairingTranspose.
-/
theorem finite_point_reconstructed_evaluation_square
    (_hl : l ≠ D.p)
    (hobj : ∀ M : ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1)),
      L.obj M = PointDerivedHom.extensionObject.{u, u} D.k
        (FinitePointHom.B D l E (n + 1)) (𝟙 _) M)
    (_hmap : ∀ {M N : ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1))} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ PointDerivedHom.extensionMorphism.{u, u} D.k
        (FinitePointHom.B D l E (n + 1)) (𝟙 _) f ≫ eqToHom (hobj N).symm)
    (_hex : PointDerivedHom.ExplicitAdjunction.{u, u} D.k
      (FinitePointHom.B D l E (n + 1)) (𝟙 _) L hobj adj)
    (_hq : FinitePointHom.Comparison D l E (n + 1) L hobj q)
    (_hrec : FinitePointHom.ReconstructedComparison D l E (n + 1) L
      (Nat.succ_le_succ (Nat.zero_le n)) adj q (fun C hC ↦ (hr C hC).1))
    (S : PointFiniteTensorData D l E n)
    (_hsource : PointFiniteSourceConstraints D l E n S)
    (_hcanonical : PointFiniteTensorCanonical D l E n S)
    (V : DerivedCategory (FinitePointHom.Mod D l E (n + 1)))
    (α : V ≅ (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit) :
    (∃ hH : ∀ C : finiteTorConstructibleCategory l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)),
        finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          (Spec (.of D.k)) ((FinitePointHom.H D l E (n + 1)).obj (op C.obj, V)),
      (∀ C, (beta D l E n L adj hr q S C V α ▷
          (finitePointFibreTensorSource D l E n).obj C) ≫
          DerivedCategory.perfectTraceEvaluation ((finitePointFibreTensorSource D l E n).obj C) =
        pairing D l E n S C V α (hH C)) ∧
      (∀ C, beta D l E n L adj hr q S C V α =
        pairingTranspose D l E n S C V α (hH C))) ∧
    (∀ (C C' : finiteTorConstructibleCategory l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))) (f : C ⟶ C'),
      (FinitePointHom.G D l E (n + 1)).mapDerivedCategory.map
          ((FinitePointHom.H D l E (n + 1)).map (Prod.mkHom f.hom.op (𝟙 V))) ≫
          beta D l E n L adj hr q S C V α =
        beta D l E n L adj hr q S C' V α ≫
          (ordinaryModuleDerivedInternalHom (FinitePointHom.A l E (n + 1))).map
            (Prod.mkHom
              (((FinitePointHom.G D l E (n + 1)).mapDerivedCategory.map f.hom).op)
              (𝟙 _))) ∧
    (∀ (C : finiteTorConstructibleCategory l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
      (P : CochainComplex (ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1))) ℤ)
      (_eP : DerivedCategory.Q.obj P ≅
        (FinitePointHom.G D l E (n + 1)).mapDerivedCategory.obj C.obj)
      (_hP : ∀ F : CochainComplex
          (ModuleCat.{u + 1} (FinitePointHom.A l E (n + 1))) ℤ,
        F.Acyclic → (PointDerivedHom.moduleTotal F P).Acyclic)
      (_hflat : ∀ i : ℤ, Module.Flat (FinitePointHom.A l E (n + 1)) (P.X i))
      (J : CochainComplex (FinitePointHom.Mod D l E (n + 1)) ℤ) [J.IsKInjective]
      (ι : (CochainComplex.singleFunctor (FinitePointHom.Mod D l E (n + 1)) 0).obj
        (SheafOfModules.unit (PointDerivedHom.ring.{u, u} D.k
          (FinitePointHom.B D l E (n + 1)))) ⟶ J) [QuasiIso ι]
      (qPJ : (PointDerivedHom.sectionComplex.{u, u} D.k
          (FinitePointHom.B D l E (n + 1)) (𝟙 _)).obj
          (PointDerivedHom.sheafHom.{u, u} D.k (FinitePointHom.B D l E (n + 1))
            ((PointDerivedHom.extensionComplex.{u, u} D.k
              (FinitePointHom.B D l E (n + 1)) (𝟙 _) L adj).obj P) J) ≅
        CochainComplex.moduleHomComplex P
          ((PointDerivedHom.sectionComplex.{u, u} D.k
            (FinitePointHom.B D l E (n + 1)) (𝟙 _)).obj J)),
      PointDerivedHom.IsComparison.{u, u} D.k (FinitePointHom.B D l E (n + 1))
        (𝟙 _) L hobj adj P J qPJ →
      PointDerivedHom.EvaluationCompatible.{u, u} D.k
        (FinitePointHom.B D l E (n + 1)) (𝟙 _) L hobj adj P J qPJ) := by
  sorry

end WeilConjectures.FinitePointEvaluation
