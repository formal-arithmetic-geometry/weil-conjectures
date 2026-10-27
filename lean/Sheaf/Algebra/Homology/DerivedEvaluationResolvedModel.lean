/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.Algebra.Homology.RingedHomCompositionModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.CategoryTheory.ClosedEvaluationNaturality
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.OneKFlatChainTranspose

/-! # Resolved model of the iterated derived evaluation transpose

Source: Stacks Project, more-algebra.tex, Tags 0A60, 0A61 and 0A67
(blueprint: lem-trf-derived-evaluation-resolved-model).

All complexes are on the one-object identity-covering ringed site for ordinary modules.
The Hom comparisons are fixed by the augmentation defining derived Hom. The tensor
comparison is the inverse native localization tensorator, with only its K-flat factor
assumed K-flat. The representative isomorphisms to K, L and M are explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

namespace DerivedCategory

/-- The signed double evaluation on unbounded representatives is the iterated
closed evaluation transpose, under the canonical representative identifications.
Here a, b and c are the three K-injective Hom comparisons, transported by the
specified representative isomorphisms. The inverse of t is the native tensorator.
Consequently lambda and rho are actual isomorphisms with prescribed maps.
Source: Stacks 0A60, 0A61, 0A67 (blueprint: lem-trf-derived-evaluation-resolved-model).

Proof:
1. Put A=Hom(J,I), B=Hom(P,J), T=Tot(A tensor P). For each pair of tensor
   degrees a,b and every Hom degree c, balanced linear evaluation sends h tensor x
   to the family f ↦ (-1)^(bc) h(f(x)). Extend over the tensor direct sum, whose
   elements have finite support. The target is a product over c, so no infinite
   sum in I is needed (def-pur-hom-complex, def-pc-tensor-complex-sheaves).
2. Expand the differential of E(h tensor x) at f. Its three terms have signs
   (-1)^(bc), -(-1)^(a+bc), and (-1)^(a+bc+c), multiplying respectively
   d_I h(f(x)), h(d_J f(x)), and h(f(d_P x)). Expanding E(dh tensor x) plus
   (-1)^a E(h tensor dx) gives the same terms, including negative degrees.
3. Hom into a K-injective target computes derived Hom, by
   def-pur-derived-internal-hom and lem-pur-rhom-well-defined. Apply this to
   (J,I), (P,J), and (B,I); then transport by eP,eJ,eI. Invert the localization
   tensorator at (A,P), using K-flatness of P and
   lem-sf-ringed-derived-native-tensor. These give lambda and rho below.
4. For every Y and K-injective N, ordinary evaluation v satisfies the counit
   normalization epsilon (gamma tensor 1)=Q(v) mu. Choose a flat-term K-flat
   resolution Y'→Y (lem-pc-kflat-resolution), precompose with 1 tensor Q(Y'→Y),
   and apply lem-sfb-hom-kflat-chain-transpose to precomposition Hom(Y,N)→Hom(Y',N).
   Naturality of mu and Hom quasi-isomorphism invariance give the formula after
   cancellation. This does not require Y K-flat or invert mu at (Hom(Y,N),Y).
5. Uncurrying E gives the chain composite swapping P past B followed by the two
   ordinary evaluations. Both maps have value (-1)^(bc)h(f(x)) on every tensor
   generator, using the Koszul braiding of
   lem-sf-ringed-derived-closed-symmetric-monoidal.
6. Localize this chain equality and precompose with the iterated lax tensorator.
   Its associativity and braiding coherence, together with step 4 for (B,I),
   (P,J) and (J,I), identify it with the swap-then-two-counit composite. The
   uniqueness of transposes in lem-trf-closed-evaluation-naturality gives the
   final equality. Only representative isomorphisms and mu at (A,P) are inverted.
   Transporting by eP,eJ,eI uses naturality of the adjunction in all variables. -/
theorem derived_evaluation_resolved_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    (K L M : DerivedCategory (RingSiteModules R))
    (P J I : CochainComplex (RingSiteModules R) ℤ)
    (hP : (HomologicalComplex.quasiIso (RingSiteModules R) (.up ℤ)).kFlat P)
    [J.IsKInjective] [I.IsKInjective]
    (eP : Q.obj P ≅ K) (eJ : Q.obj J ≅ L) (eI : Q.obj I ≅ M) :
    ∃ E : (coefficientTotalTensor.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)).obj
        (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I, P) ⟶
      homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R)
        (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I,
      (∀ (a b n c j i : ℤ) (hn : a + b = n) (hj : b + c = j)
        (hi : j + a = i) (hi' : c + n = i) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
        (h : ((homComplex.{u, u, u, u}
          (R := CochainComplex.onePointRingSheaf R) J I).X a).val.obj U)
        (x : (P.X b).val.obj U)
        (f : ((homComplex.{u, u, u, u}
          (R := CochainComplex.onePointRingSheaf R) P J).X c).val.obj U),
        (((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
          (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J)
          I n c i hi').val.app U
            ((E.f n).val.app U
              (coefficientTensorGenerator.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
                (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I)
                P a b n hn U h x))).app (op (Over.mk (𝟙 U.unop)))) f =
          (b * c).negOnePow •
            (((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
              J I a j i hi).val.app U h).app (op (Over.mk (𝟙 U.unop))))
                ((((coefficientHomComponent.{u, u, u} ⊥ (CochainComplex.onePointRingSheaf R)
                  P J c b j hj).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x)) ∧
      ∃ (a : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M)
        (b : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)
        (c : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
            (Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J))).obj M)
        (t : Q.obj ((coefficientTotalTensor.{u, u, u} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
              (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I, P)) ≅
          Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) ⊗ Q.obj P)
        (lambda : Q.obj ((coefficientTotalTensor.{u, u, u} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
              (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I, P)) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M ⊗ K)
        (rho : Q.obj (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I) ≅
          (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
            ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).obj M),
        a.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥
            (CochainComplex.onePointRingSheaf R) J I ≫
          (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (eJ.inv.op, eI.hom) ∧
        b.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥
            (CochainComplex.onePointRingSheaf R) P J ≫
          (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (eP.inv.op, eJ.hom) ∧
        c.hom = ringedHomRepresentativeMap.{u, u, u, u} ⊥
            (CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) P J) I ≫
          (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (X := (op (Q.obj (homComplex.{u, u, u, u}
              (R := CochainComplex.onePointRingSheaf R) P J)), Q.obj I))
            (Y := (op (Q.obj (homComplex.{u, u, u, u}
              (R := CochainComplex.onePointRingSheaf R) P J)), M))
            (𝟙 _, eI.hom) ∧
        t.inv = Functor.LaxMonoidal.μ Q
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) P ≫
          Q.map (SignedRingedHom.totalTensorNativeIso ⊥ (CochainComplex.onePointRingSheaf R)
            (homComplex.{u, u, u, u} (R := CochainComplex.onePointRingSheaf R) J I) P).inv ∧
        lambda.hom = t.hom ≫ (a.hom ⊗ₘ eP.hom) ∧
        rho.hom = c.hom ≫
          (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (X := (op (Q.obj (homComplex.{u, u, u, u}
              (R := CochainComplex.onePointRingSheaf R) P J)), M))
            (Y := (op ((SignedRingedHom.hom ⊥
              (CochainComplex.onePointRingSheaf R) K).obj L), M))
            (b.inv.op, 𝟙 M) ∧
        Q.map E ≫ rho.hom = lambda.hom ≫
          (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
            ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).homEquiv
            _ M ((α_ _ _ _).hom ≫
              _ ◁ ((β_ K _).hom ≫
                (SignedRingedHom.adjunction ⊥
                  (CochainComplex.onePointRingSheaf R) K).counit.app L) ≫
              (SignedRingedHom.adjunction ⊥
                (CochainComplex.onePointRingSheaf R) L).counit.app M) := by
  sorry

end DerivedCategory
