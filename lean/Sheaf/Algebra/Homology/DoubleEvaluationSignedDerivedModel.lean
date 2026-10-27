/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap
public import Sheaf.Algebra.Homology.RingedHomCompositionModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Signed double evaluation and its canonical derived representative

Source: Stacks Project, More on Algebra, Tags 0A60, 0A61 and 0A67
(blueprint: lem-trf-double-evaluation-signed-derived-model).

Ordinary modules are presented on the existing one-object bottom-topology ringed site.
The Hom products and tensor direct sums are the recorded constructions, and all comparison
maps are fixed by the existing K-injective augmentation and native localization tensorator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

namespace DerivedCategory

variable (R : Type u) [CommRing R]

/-- The source total tensor, on the one-object ringed site for ordinary modules.
Source: Stacks 0A60 (blueprint: lem-trf-double-evaluation-signed-derived-model). -/
abbrev signedDoubleEvaluationSource (P J I : CochainComplex (RingSiteModules R) ℤ) :=
  (coefficientTotalTensor.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)).obj
    (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I, P)

/-- The target product-total double Hom, retaining all integer degrees.
Source: Stacks 0A60 (blueprint: lem-trf-double-evaluation-signed-derived-model). -/
abbrev signedDoubleEvaluationTarget (P J I : CochainComplex (RingSiteModules R) ℤ) :=
  homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R)
    (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I

/-- The componentwise formula, using the actual product projections and pure tensor
summand inclusions. No infinite sum of Hom coordinates is taken.
Source: Stacks 0A60 and 0A61
(blueprint: lem-trf-double-evaluation-signed-derived-model). -/
def SignedDoubleEvaluationFormula (P J I : CochainComplex (RingSiteModules R) ℤ)
    (E : signedDoubleEvaluationSource R P J I ⟶ signedDoubleEvaluationTarget R P J I) :
    Prop :=
  ∀ (h s n k a b : ℤ) (hn : h + s = n) (ha : s + k = a)
    (hb : a + h = b) (hb' : k + n = b) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (g : ((homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I).X h).val.obj U)
    (x : (P.X s).val.obj U)
    (f : ((homComplex.{u, u, u, u}
      (R := CochainComplex.onePointRingSheaf R) P J).X k).val.obj U),
    (((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
        (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J)
        I n k b hb').val.app U
      ((E.f n).val.app U
        (coefficientTensorGenerator.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
          (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I)
          P h s n hn U g x))).app
            (op (Over.mk (𝟙 U.unop)))) f =
      (k * s).negOnePow •
        (((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
          J I h a b hb).val.app U g).app (op (Over.mk (𝟙 U.unop))))
            ((((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
              P J k s a ha).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x)

/-- The coefficient in the component indexing `J^(-r) → I^p`.
Source: Stacks 0A60 and 0A61
(blueprint: lem-trf-double-evaluation-signed-derived-model). -/
def doubleEvaluationSign (_p r s : ℤ) : ℤˣ := (s * (r + 1)).negOnePow

/-- The homogeneous and component signs agree, and the three differential sign identities
hold for all integer indices.
Source: Stacks 0A60, equations alpha and beta, and 0A61
(blueprint: lem-trf-double-evaluation-signed-derived-model).

Proof: with k = -r-s, ks = -rs-s² is congruent to s(r+1) modulo two. The exponent
is independent of p; replacing r by r-1 changes it by s, and replacing s by s+1
changes it by r+1. These give respectively the three displayed identities. -/
theorem doubleEvaluationSign_identities (p r s : ℤ) :
    ((-r - s) * s).negOnePow = doubleEvaluationSign p r s ∧
    doubleEvaluationSign p r s = doubleEvaluationSign (p + 1) r s ∧
    doubleEvaluationSign p r s = s.negOnePow * doubleEvaluationSign p (r - 1) s ∧
    doubleEvaluationSign p r (s + 1) = (r + 1).negOnePow * doubleEvaluationSign p r s := by
  sorry

variable [HasDerivedCategory.{u} (RingSiteModules R)]

/-- The unbounded signed chain map realizes exactly the canonical derived evaluation.
The three Hom comparisons are normalized by the fixed K-injective augmentation, and
`t` is normalized by the inverse native localization tensor comparison. Thus the final
equation specifies the actual morphism under canonical isomorphisms, not merely the
existence of unrelated isomorphisms of its source and target.
Source: Stacks 0A60, 0A61 and 0A67
(blueprint: lem-trf-double-evaluation-signed-derived-model).

Proof:
1. For h+s=n define the graded map on g tensor x, tested at f of degree k, by
   (-1)^(ks) g^(s+k)(f^s(x)). Tensor-Hom currying gives an R-linear map on each
   tensor summand. Extend over the direct sum: every input has finite support,
   and infinitely many Hom coordinates are accessed only by projections.
2. Expand both differentials. The three coefficients of d_I g(f(x)), g(d_J f(x)),
   and g(f(d_P x)) are respectively (-1)^(ks), -(-1)^(h+ks), and (-1)^(h+ks+k).
   They agree with E(d_H g tensor x)+(-1)^h E(g tensor d_P x), proving the chain law.
3. The preceding sign lemma gives epsilon(p,r,s)=(-1)^(s(r+1)) and its identities.
4. K-injectivity of I,J makes the fixed augmentation Hom comparison invertible
   for H=Hom(J,I), A=Hom(P,J), and B=Hom(A,I). Transport B along the comparison
   for A. K-flatness of P gives the native tensor comparison with arbitrary H
   (lem-pc-source-kflat-module-tensor-model, lem-sf-ringed-derived-native-tensor).
5. Choose a K-flat quasi-isomorphism U→H (lem-pc-kflat-resolution). Tensoring it
   with P is a quasi-isomorphism, and C=U tensor P is K-flat by reassociation and
   the two K-flat criteria (lem-sf-ringed-tensor-complex-constraints).
6. Uncurry E after this replacement. Swapping P past A and then applying the two
   ordinary evaluations gives exactly (-1)^(ks)u(z)(f(x)) on pure generators.
7. Apply lem-trf-module-one-kflat-uncurry-normalization to (C,A,I), (A,P,J), and
   (U,J,I). Each has a K-flat tensor factor and K-injective target. Native tensor
   comparison preserves the associator and braiding, so this is the derived
   composite of the two counits with the specified middle swap.
8. By lem-trf-closed-evaluation-naturality, its transpose is exactly the map of
   lem-trf-derived-evaluation-canonical-map, including its left-uncurrying
   normalization. Cancel the invertible replaced-source map and the natural
   tensor comparison. No invertibility of E or Q(E) is used or asserted. -/
theorem doubleEvaluation_signed_derived_model
    (P J I : CochainComplex (RingSiteModules R) ℤ)
    (hP : (HomologicalComplex.quasiIso (RingSiteModules R) (.up ℤ)).kFlat P)
    [J.IsKInjective] [I.IsKInjective] :
    ∃ E : signedDoubleEvaluationSource R P J I ⟶ signedDoubleEvaluationTarget R P J I,
      SignedDoubleEvaluationFormula R P J I E ∧
      ∃ (a : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) (Q.obj J)).obj (Q.obj I))
        (b : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) (Q.obj P)).obj (Q.obj J))
        (c : Q.obj (signedDoubleEvaluationTarget R P J I) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
            (Q.obj (homComplex.{u, u, u, u}
              (R := CochainComplex.onePointRingSheaf R) P J))).obj (Q.obj I))
        (t : Q.obj (signedDoubleEvaluationSource R P J I) ≅
          Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) ⊗ Q.obj P),
        a.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥ (CochainComplex.onePointRingSheaf R) J I ∧
        b.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥ (CochainComplex.onePointRingSheaf R) P J ∧
        c.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
          (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I ∧
        t.inv = Functor.LaxMonoidal.μ Q
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) P ≫
          Q.map (SignedRingedHom.totalTensorNativeIso ⊥ (CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) P).inv ∧
        Q.map E ≫ c.hom ≫
            (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
              (X := (op (Q.obj (homComplex.{u, u, u, u}
                (R := CochainComplex.onePointRingSheaf R) P J)), Q.obj I))
              (Y := (op ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
                (Q.obj P)).obj (Q.obj J)), Q.obj I))
              (b.inv.op, 𝟙 (Q.obj I)) =
          t.hom ≫ (a.hom ⊗ₘ 𝟙 (Q.obj P)) ≫
            (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
              ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
                (Q.obj P)).obj (Q.obj J))).homEquiv _ (Q.obj I)
              ((α_ _ _ _).hom ≫
                _ ◁ ((β_ (Q.obj P) _).hom ≫
                  (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
                    (Q.obj P)).counit.app (Q.obj J)) ≫
                (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
                  (Q.obj J)).counit.app (Q.obj I)) := by
  sorry

end DerivedCategory
