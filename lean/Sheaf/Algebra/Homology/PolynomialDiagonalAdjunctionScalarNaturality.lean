/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.TraceFormula.PolynomialDiagonalRhomReduction
public import Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart
public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Mathlib.RingTheory.FiniteType
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalClass

/-! # Scalar naturality of the normalized polynomial diagonal adjunction

Source: Stacks Project, dualizing.tex, Tags 0E2E, 0E2F, 0BZI and 0BZJ;
sites-cohomology.tex, Tag 08JA. The full Hom naturality square is the agent assembly
specified in the DAG, rather than a verbatim Stacks assertion.
(blueprint: lem-sfb-polynomial-diagonal-adjunction-scalar-naturality).

Bijective chart coordinates specify ordinary polynomial rings. The two pushout squares
present the base-changed algebras without imposing a particular carrier for a tensor
product. The existing chart model is coinduction of the top differential line in degree
-n, canonically coinduction of Omega^n followed by shift [n]. Its counit normalization
and its ordered graph class are the recorded constructions, including their actions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The allowable targets of the polynomial diagonal adjunction. This is just the
conjunction of the recorded pseudo-coherence and finite base-ring Tor-amplitude
predicates, after ordinary restriction of scalars. The Tor predicate tests every
base-ring module in degree zero, with one finite interval independent of that module.
Source: Stacks 0BZW and 0651; the target hypotheses in the DAG
(blueprint: lem-sfb-polynomial-diagonal-adjunction-scalar-naturality). -/
abbrev polynomialDiagonalAdjunctionTargets (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  fun T ↦ DerivedCategory.IsPseudoCoherent T ∧
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u} R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj T)

/-- The entire morphism adjunction admits simultaneous ordered-class normalization
and commutes with arbitrary Noetherian scalar extension. Here R,B,S,D are the node's
R,A,R',A'; the chart models C.model,E.model are its dualizing objects C,C'. The
normalized isomorphism c is precisely the coinduction exchange: IsComparison fixes
it by the extended evaluation-at-one counit and the ordered top-form comparison.
The diagonal comparison d is fixed on every ordinary element before deriving.
The final equation therefore uses the derived extension v' of every v, rather than
an arbitrary arrow with the same endpoints. Both rho families are chosen before T.

Source: Stacks 0E2E, 0E2F, 0BZI, 0BZJ, and 08JA; the scalar-naturality refinement
(blueprint: lem-sfb-polynomial-diagonal-adjunction-scalar-naturality).

Proof (the six DAG steps):
1. By lem-trf-algebraic-shriek-relative-perfect and lem-pur-rhom-global-sections,
the ordered-volume polynomial model is allowable and End(C)=A acting by scalars.
The same holds after base change. The base-changed finite presentation is obtained
by extending its finite relations. Flatness follows from N tensor_(R') A' =
N tensor_R A, and lem-weil-pbc-finite-type-algebra-noetherian gives Noetherianity.
2. By lem-trf-flat-polynomial-quotient-perfect, A is perfect over P. Resolve R'
freely over R. Tensoring with the R-flat P and A preserves exactness by
lem-weil-pbc-flat-tensor-exact, proving Tor independence of A and P' over P.
The counit-mate of lem-sfb-perfect-coinduction-tor-independent-exchange is thus
invertible, including the shifted ordered coefficient identification.
3. Choose the two ordered graph classes using lem-sfb-polynomial-koszul-diagonal-class.
They are the normalized affine pairs of lem-trf-relative-duality-polynomial-chart;
multiplication by each class is invertible. That node's evaluation-counit scalar
comparison gives c_1 times the extended class = the primed class exactly.
4. Take H^0 of lem-trf-polynomial-diagonal-rhom-reduction, using
lem-pur-rhom-global-sections. The resulting A-linear Hom bijections s_T are natural
in every allowable T. At C, s_C(xi)=u times 1_C for a unit u, since source and target
are free rank one. Precompose s_T with u inverse to obtain rho_T(xi)=1_C.
Apply the same construction over the primed base, simultaneously for all targets.
5. Naturality at f:C -> T gives rho_T(f_1 xi)=f rho_C(xi)=f. Bijectivity therefore
gives v=(rho_T(v))_1 xi for every v. This is the inverse formula for both families.
6. Extend that inverse formula along the map on both diagonal factors. Functoriality
from lem-pc-derived-tensor-second-factor-functor and the class square of step 3 give
v'=((rho_T(v) tensor_A^L A') composed with c inverse)_1 xi'. Apply the primed
inverse formula to obtain the final equality. Zero rings have only the unique maps;
for n=0 both the ordered wedge and Koszul contraction are empty identities.
-/
theorem polynomial_diagonal_adjunction_scalar_naturality {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [IsNoetherianRing R] [IsNoetherianRing B] [IsNoetherianRing S]
    (hflat : RingHom.Flat (algebraMap R B)) [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D)
    (hC : Function.Bijective C.coordinates) (hE : Function.Bijective E.coordinates)
    (F : KoszulDiagonalChartChange C E)
    (hbase : IsPushout (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom F.base)
      (CommRingCat.ofHom F.ring) (CommRingCat.ofHom (algebraMap S D)))
    (hquotient : IsPushout (CommRingCat.ofHom C.quotient.toRingHom)
      (CommRingCat.ofHom F.ambient) (CommRingCat.ofHom F.ring)
      (CommRingCat.ofHom E.quotient.toRingHom)) :
    ∃ (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model)
      (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
      (κ' : E.diagonalHom ≅ koszulDiagonalUnit D),
      F.IsComparison c ∧ IsKoszulDiagonalNormalization C κ ∧
      IsKoszulDiagonalNormalization E κ' ∧
      IsIso (relativeDualizingModuleClassMap R B C.firstPullback (C.diagonalClass κ)) ∧
      IsIso (relativeDualizingModuleClassMap S D E.firstPullback (E.diagonalClass κ')) ∧
      ∃ (ρ : ∀ (T : DerivedCategory (ModuleCat.{u} B)),
          polynomialDiagonalAdjunctionTargets R B T →
          (relativeDualizingModuleDiagonal R B ⟶ relativeDualizingModuleFirstPullback R B T) ≃
            (C.model ⟶ T))
        (ρ' : ∀ (T : DerivedCategory (ModuleCat.{u} D)),
          polynomialDiagonalAdjunctionTargets S D T →
          (relativeDualizingModuleDiagonal S D ⟶ relativeDualizingModuleFirstPullback S D T) ≃
            (E.model ⟶ T)),
        (∀ (T U : DerivedCategory (ModuleCat.{u} B))
          (hT : polynomialDiagonalAdjunctionTargets R B T)
          (hU : polynomialDiagonalAdjunctionTargets R B U) (f : T ⟶ U)
          (v : relativeDualizingModuleDiagonal R B ⟶ relativeDualizingModuleFirstPullback R B T),
          ρ U hU (v ≫ (relativeDualizingDerivedExtension
            (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom).map f) =
              ρ T hT v ≫ f) ∧
        (∀ (T U : DerivedCategory (ModuleCat.{u} D))
          (hT : polynomialDiagonalAdjunctionTargets S D T)
          (hU : polynomialDiagonalAdjunctionTargets S D U) (f : T ⟶ U)
          (v : relativeDualizingModuleDiagonal S D ⟶ relativeDualizingModuleFirstPullback S D T),
          ρ' U hU (v ≫ (relativeDualizingDerivedExtension
            (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom).map f) =
              ρ' T hT v ≫ f) ∧
        (∃ h : polynomialDiagonalAdjunctionTargets R B C.model,
          ρ C.model h (C.diagonalClass κ) = 𝟙 C.model) ∧
        (∃ h : polynomialDiagonalAdjunctionTargets S D E.model,
          ρ' E.model h (E.diagonalClass κ') = 𝟙 E.model) ∧
        ∃ (h : F.diagonalRing.comp
            (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom =
          (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom.comp F.ring)
          (d : (relativeDualizingDerivedExtension F.diagonalRing).obj
            (relativeDualizingModuleDiagonal R B) ≅ relativeDualizingModuleDiagonal S D),
          F.IsDiagonalComparison d ∧
          ∀ (T : DerivedCategory (ModuleCat.{u} B))
            (hT : polynomialDiagonalAdjunctionTargets R B T)
            (hT' : polynomialDiagonalAdjunctionTargets S D
              ((relativeDualizingDerivedExtension F.ring).obj T))
            (v : relativeDualizingModuleDiagonal R B ⟶
              relativeDualizingModuleFirstPullback R B T),
            ρ' ((relativeDualizingDerivedExtension F.ring).obj T) hT'
              (d.inv ≫ (relativeDualizingDerivedExtension F.diagonalRing).map v ≫
                (koszulDiagonalExtensionSquare
                  (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom F.ring
                  F.diagonalRing
                  (Algebra.TensorProduct.includeLeft : D →ₐ[S] D ⊗[S] D).toRingHom h).hom.app T) =
              c.inv ≫ (relativeDualizingDerivedExtension F.ring).map (ρ T hT v) := by
  sorry

end AlgebraicGeometry
