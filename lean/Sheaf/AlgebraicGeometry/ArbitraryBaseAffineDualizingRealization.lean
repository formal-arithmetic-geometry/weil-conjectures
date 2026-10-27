/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion
import Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel

/-! # Affine realization of relative dualizing pairs over arbitrary bases

Source: Stacks Project, duality.tex, Tag 0E2U, and perfect.tex, Tag 0A6H(3)(a).
(blueprint: lem-sfb-arbitrary-base-affine-dualizing-realization).

The two supplied pairs are indexed by `Fin 2`. The proposition below packages their
simultaneous affine realization and its comparison diagrams. It introduces no
alternative derived tensor, diagonal, internal Hom, or class multiplication.
There is no Noetherian hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

variable
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (E : Fin 2 → schemeDerivedCategory X)
    (ξ : ∀ i, DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj (E i))
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ jR)

/-- Proposition expressing the simultaneous affine realization diagrams of two supplied pairs.
`M 0` and `M 1` are the objects corresponding to their restrictions under the recorded
triangulated affine equivalence (therefore also their derived global sections).
The common diagonal comparison and the two natural pullback comparisons fix which
restricted classes are being compared. Open restriction recomputes algebraic Hom
by the evaluation-defined localization map.
Source: Stacks 0E2U and 0A6H(3)(a).
(blueprint: lem-sfb-arbitrary-base-affine-dualizing-realization). -/
def ArbitraryBaseAffineDualizingRealization : Prop :=
  ((algebraMap R A).Flat) ∧
  (Algebra.FinitePresentation R A) ∧
  ∃ (M : Fin 2 → DerivedCategory (ModuleCat.{u} A)),
  (∀ i, DerivedCategory.IsPseudoCoherent (M i)) ∧
  (∀ k, ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (n : ℤ),
    n < a ∨ b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj (M k)) ⊗
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q)))) ∧
  ∃ (realization : ∀ i, (derivedPullback jA).obj (E i) ≅
    (relativeDualizingAffineTilde A).obj (M i)),
  ∃ (diagonal : (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj
      (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)) ≅
    (relativeDualizingAffineTilde (A ⊗[R] A)).obj (relativeDualizingModuleDiagonal R A)),
  ∃ (restrictFirst : derivedPullback (pullback.fst f f) ⋙
      derivedPullback (relativeDualizingProductChart f R A jA jR h) ≅
    derivedPullback jA ⋙ derivedPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom))),
  ∃ (affineFirst : relativeDualizingAffineTilde A ⋙ derivedPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom)) ≅
    relativeDualizingDerivedExtension
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom ⋙
      relativeDualizingAffineTilde (A ⊗[R] A)),
  ∃ (first : ∀ i,
    (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj
      ((derivedPullback (pullback.fst f f)).obj (E i)) ≅
    (relativeDualizingAffineTilde (A ⊗[R] A)).obj
      (relativeDualizingModuleFirstPullback R A (M i))),
  (∀ i, (first i).hom = restrictFirst.hom.app (E i) ≫
    (derivedPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom))).map
        (realization i).hom ≫ affineFirst.hom.app (M i)) ∧
  ∃ (diagonalHom : ∀ i,
    (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj
      ((derivedInternalHom (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj
        (op (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)),
          (derivedPullback (pullback.fst f f)).obj (E i))) ≅
    (relativeDualizingAffineTilde (A ⊗[R] A)).obj
      (relativeDualizingModuleHom R A (M i))),
  ∃ (gamma : ∀ i, relativeDualizingModuleDiagonal R A ⟶
    relativeDualizingModuleFirstPullback R A (M i)),
  (∀ i,
    diagonal.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map (gamma i) =
      (derivedPullback (relativeDualizingProductChart f R A jA jR h)).map (ξ i) ≫
        (first i).hom) ∧
  (∀ i,
    diagonal.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map
      (relativeDualizingModuleClassMap R A
        (relativeDualizingModuleFirstPullback R A (M i)) (gamma i)) =
      (derivedPullback (relativeDualizingProductChart f R A jA jR h)).map
        (relativeDualizingClassMap f (E i) (ξ i)) ≫ (diagonalHom i).hom) ∧
  (∀ i, IsIso (relativeDualizingModuleClassMap R A
    (relativeDualizingModuleFirstPullback R A (M i)) (gamma i))) ∧
  ∃ (hom : ∀ i,
    (relativeDualizingAffineTilde A).obj ((ihom (M 0)).obj (M i)) ≅
      (derivedInternalHom (Opens.grothendieckTopology (Spec (.of A)))
        (Spec (.of A)).sheaf).obj
        (op ((derivedPullback jA).obj (E 0)), (derivedPullback jA).obj (E i))),
  (∀ (i j : Fin 2) (b : M i ⟶ M j),
    (relativeDualizingAffineTilde A).map ((ihom (M 0)).map b) ≫ (hom j).hom =
      (hom i).hom ≫
        (derivedInternalHom (Opens.grothendieckTopology (Spec (.of A)))
          (Spec (.of A)).sheaf).map
          (𝟙 (op ((derivedPullback jA).obj (E 0))),
            (realization i).hom ≫ (relativeDualizingAffineTilde A).map b ≫
              (realization j).inv)) ∧
  (∀ (i : Fin 2) (a : M 0 ⟶ M 0),
    (relativeDualizingAffineTilde A).map
        ((MonoidalClosed.internalHom.map a.op).app (M i)) ≫ (hom i).hom =
      (hom i).hom ≫
        (derivedInternalHom (Opens.grothendieckTopology (Spec (.of A)))
          (Spec (.of A)).sheaf).map
          (((realization 0).hom ≫ (relativeDualizingAffineTilde A).map a ≫
            (realization 0).inv).op, 𝟙 ((derivedPullback jA).obj (E i)))) ∧
  ∃ (unit : 𝟙_ (schemeDerivedCategory (Spec (.of A))) ≅
    (relativeDualizingAffineTilde A).obj (𝟙_ (DerivedCategory (ModuleCat.{u} A)))),
  ((relativeDualizingAffineTilde A).map
      (MonoidalClosed.curry (ρ_ (M 0)).hom) ≫ (hom 0).hom =
    unit.inv ≫ relativeDualizingScalarMap (Spec (.of A))
      ((derivedPullback jA).obj (E 0))) ∧
  ∃ (commShift : (relativeDualizingAffineTilde A).CommShift ℤ),
  (∀ (i : Fin 2) (n : ℤ), Function.Bijective
    (fun a : M 0 ⟶ (M i)⟦n⟧ ↦
      (realization 0).hom ≫ (relativeDualizingAffineTilde A).map a ≫
        (@Functor.commShiftIso _ _ _ _ (relativeDualizingAffineTilde A) ℤ _ _ _
          commShift n).hom.app (M i) ≫
        (shiftFunctor (schemeDerivedCategory (Spec (.of A))) n).map (realization i).inv)) ∧
  (∀ a : M 0 ≅ M 1,
    gamma 0 ≫ (relativeDualizingDerivedExtension
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).map a.hom =
      gamma 1 ↔
    (derivedPullback (relativeDualizingProductChart f R A jA jR h)).map (ξ 0) ≫
      restrictFirst.hom.app (E 0) ≫
      (derivedPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom))).map
          ((realization 0).hom ≫ (relativeDualizingAffineTilde A).map a.hom ≫
            (realization 1).inv) =
      (derivedPullback (relativeDualizingProductChart f R A jA jR h)).map (ξ 1) ≫
        restrictFirst.hom.app (E 1)) ∧
  (∀ (P Q : DerivedCategory (ModuleCat.{u} A)) (a : P ⟶ Q) (r : A)
    (s : RingCat.sectionsSubring ((Spec (.of A)).sheaf.obj ⋙ forget₂ CommRingCat RingCat)),
    s.val (op ⊤) = (Scheme.ΓSpecIso (.of A)).inv.hom r →
      (relativeDualizingAffineTilde A).map (r • a) =
        schemeDerivedScalar (Spec (.of A)) s ((relativeDualizingAffineTilde A).map a)) ∧
  (∀ (P Q : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) (a : P ⟶ Q)
    (r : A ⊗[R] A)
    (s : RingCat.sectionsSubring
      ((Spec (.of (A ⊗[R] A))).sheaf.obj ⋙ forget₂ CommRingCat RingCat)),
    s.val (op ⊤) = (Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv.hom r →
      (relativeDualizingAffineTilde (A ⊗[R] A)).map (r • a) =
        schemeDerivedScalar (Spec (.of (A ⊗[R] A))) s
          ((relativeDualizingAffineTilde (A ⊗[R] A)).map a)) ∧
  (∀ (C : Type u) [CommRing C]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)]
    (φ : (A ⊗[R] A) →+* C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))],
    ∃ τ : ∀ P Q : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)),
        (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
          (relativeDualizingDerivedExtension φ).obj P ⊗
            (relativeDualizingDerivedExtension φ).obj Q,
      IsRelativeDualizingExtensionTensorComparison φ τ ∧
    ∃ ρ : relativeDualizingAffineTilde (A ⊗[R] A) ⋙
        derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
      relativeDualizingDerivedExtension φ ⋙ relativeDualizingAffineTilde C,
    ∀ i, IsIso (relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
      (relativeDualizingModuleFirstPullback R A (M i))) ∧
      (relativeDualizingDerivedExtension φ).map
          (relativeDualizingModuleClassMap R A
            (relativeDualizingModuleFirstPullback R A (M i)) (gamma i)) ≫
          relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
            (relativeDualizingModuleFirstPullback R A (M i)) =
        relativeDualizingLocalizedClassMap R A C φ τ
          (relativeDualizingModuleFirstPullback R A (M i)) (gamma i) ∧
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map diagonal.hom ≫
          ρ.hom.app (relativeDualizingModuleDiagonal R A) ≫
          (relativeDualizingAffineTilde C).map
            (relativeDualizingLocalizedClassMap R A C φ τ
              (relativeDualizingModuleFirstPullback R A (M i)) (gamma i)) =
        (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
          ((derivedPullback (relativeDualizingProductChart f R A jA jR h)).map
            (relativeDualizingClassMap f (E i) (ξ i))) ≫
          (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map (diagonalHom i).hom ≫
          ρ.hom.app (relativeDualizingModuleHom R A (M i)) ≫
          (relativeDualizingAffineTilde C).map
            (relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
              (relativeDualizingModuleFirstPullback R A (M i)))) ∧
  (∀ (C : Type u) [CommRing C]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)]
    (φ : A →+* C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))],
    ∃ τ : ∀ P Q : DerivedCategory (ModuleCat.{u} A),
        (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
          (relativeDualizingDerivedExtension φ).obj P ⊗
            (relativeDualizingDerivedExtension φ).obj Q,
      IsRelativeDualizingExtensionTensorComparison φ τ ∧
    ∃ ρ : relativeDualizingAffineTilde A ⋙
        derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
      relativeDualizingDerivedExtension φ ⋙ relativeDualizingAffineTilde C,
    ∃ τS : ∀ P Q : schemeDerivedCategory (Spec (.of A)),
        (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj (P ⊗ Q) ≅
          (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj P ⊗
            (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj Q,
      IsCanonicalPullbackTensorComparison (Spec.map (CommRingCat.ofHom φ))
        (fun P Q ↦ (τS P Q).hom) ∧
    ∀ i, IsIso (relativeDualizingHomLocalization φ τ (M 0) (M i)) ∧
      ∃ (rH : (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
          ((derivedInternalHom (Opens.grothendieckTopology (Spec (.of A)))
            (Spec (.of A)).sheaf).obj
            (op ((derivedPullback jA).obj (E 0)), (derivedPullback jA).obj (E i))) ≅
        (derivedInternalHom (Opens.grothendieckTopology (Spec (.of C)))
          (Spec (.of C)).sheaf).obj
          (op ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
            ((derivedPullback jA).obj (E 0))),
            (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
              ((derivedPullback jA).obj (E i))))
        (eH : (relativeDualizingAffineTilde C).obj
          ((ihom ((relativeDualizingDerivedExtension φ).obj (M 0))).obj
            ((relativeDualizingDerivedExtension φ).obj (M i))) ≅
          (derivedInternalHom (Opens.grothendieckTopology (Spec (.of C)))
            (Spec (.of C)).sheaf).obj
            (op ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
              ((derivedPullback jA).obj (E 0))),
              (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
                ((derivedPullback jA).obj (E i)))),
        rH.hom = (schemeDerivedTensorHomEquiv (Spec (.of C)) _ _ _).symm
          ((τS
            ((derivedInternalHom (Opens.grothendieckTopology (Spec (.of A)))
              (Spec (.of A)).sheaf).obj
                (op ((derivedPullback jA).obj (E 0)), (derivedPullback jA).obj (E i)))
            ((derivedPullback jA).obj (E 0))).inv ≫
            (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
              (schemeDerivedTensorHomEquiv (Spec (.of A)) _ _ _ (𝟙 _))) ∧
        ρ.hom.app ((ihom (M 0)).obj (M i)) ≫
            (relativeDualizingAffineTilde C).map
              (relativeDualizingHomLocalization φ τ (M 0) (M i)) ≫ eH.hom =
          (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map (hom i).hom ≫ rH.hom)

/-- Simultaneous affine realization for two supplied coherent relative dualizing pairs,
without a Noetherian assumption. `Fin 2` simply indexes the two given pairs.
Source: Stacks Project, duality.tex, Tag 0E2U; perfect.tex, Tag 0A6H(3)(a).
(blueprint: lem-sfb-arbitrary-base-affine-dualizing-realization).

Proof (the accepted stage-1 split):
1. The affine flatness criterion applied to the specified opens gives flatness of R\to A. The
   affine-open characterization of local finite presentation gives
   A=R[x_1,\ldots,x_n]/(g_1,\ldots,g_m) for finite n,m. These results apply to the original U,V;
   no shrinking, properness or Noetherian hypothesis is needed.
2. Do the following for E=K,L. Pseudo-coherence restricts to U by restricting its local finite-
   free representatives. The pseudo-coherent quasi-coherence theorem makes E|_U an object of
   D_{\mathrm{QCoh}}(\mathcal O_U), so the affine equivalence defines T=R\Gamma(U,E|_U) and
   \widetilde T\cong E|_U. The affine pseudo-coherence criterion gives a bounded-above finite-
   free representative of T. Apply the affine relative Tor-amplitude criterion to U\to V: the
   supplied local finite Tor dimension is exactly its local hypothesis. Indeed (f^{-1}\mathcal
   O_S)|_U=(f|_U)^{-1}\mathcal O_V, and restriction of a local Tor bound follows by extending
   test modules from a smaller open by zero. Its conclusion is one finite R-Tor interval for T,
   despite the initially local bounds. Testing with Q=R shows that T is bounded, in particular
   bounded below.
3. The presentation in step 1 gives B=R[x_1,\ldots,x_n,y_1,\ldots,y_n]/(g(x),g(y)), so R\to B is
   finitely presented. Flat module base change makes B flat over the first A; also -\otimes_R
   B=(-\otimes_R A)\otimes_{A,p_1}B is a composite of exact functors, hence B is flat over R.
   Multiplication \mu:B\to A is surjective since \mu(a\otimes1)=a. Apply the flat finitely
   presented quotient pseudo-coherence lemma to R\to B\to A and the finite-free complex A[0]. It
   gives pseudo-coherence of A[0] over B, without assuming that either ring is Noetherian. For
   T=M,N, the flat-single tensor cohomology theorem (on the one-point ringed site of A) gives
   H^i(T_1)=H^i(T)\otimes_{A,p_1}B; thus T_1 is bounded below. These are the precise two
   hypotheses for the diagonal internal-Hom comparison.
4. Put W=U\times_VU. Since V\hookrightarrow S is an open monomorphism, W=U\times_SU is an open of
   X\times_SX. The affine fibre-product theorem identifies W=\operatorname{Spec}B and its first
   projection with p_1:a\mapsto a\otimes1. The diagonal is induced by \mu: both composites A\to
   B\to A are the identity. On a basic open D(b) its direct-image algebra has sections
   A_{\mu(b)}. The associated-sheaf section formula for the B-module A gives exactly these
   sections, actions and fraction restriction maps. Thus the restricted diagonal is
   \widetilde{A[0]}, including its algebra multiplication. The affine pullback comparison
   identifies the restricted Lp_1^*E with \widetilde{T_1}, naturally also on maps.
5. Restriction of derived internal Hom to W gives the Hom of the two restricted objects. Apply
   the affine algebra-class evaluation comparison with coefficient ring B, algebra C=A via \mu,
   and second object T_1. Step 3 verified pseudo-coherence of C[0] and bounded-below cohomology
   of T_1. Its evaluation-normalized isomorphism identifies that Hom with
   \widetilde{R\operatorname{Hom}_B(A,T_1)}. Full faithfulness over B gives the unique module
   classes \gamma,\theta corresponding to \xi|_W,\eta|_W. To check that these classes give the
   required isomorphisms, use the canonical tensor comparison for open restriction: on K-flat
   representatives it restricts the same total-tensor maps, multiplication and unit. The open-
   restriction evaluation mate is invertible. Naturality of tensor--Hom transposition says that,
   under this mate, restriction of the transpose of \xi\mu is the transpose of its restriction.
   Hence the supplied multiplication isomorphism restricts to the multiplication map of the
   restricted class. Finally the class-map identity in the affine algebra-class comparison
   identifies it with the sheafification of m_\gamma (respectively m_\theta). The affine
   equivalence reflects invertibility, proving both algebraic multiplication maps are
   isomorphisms.
6. For T=M,N, apply the affine pseudo-coherent Hom theorem to P=M and T. Step 2 gives the
   bounded-above finite-free first representative and bounded-below second cohomology required by
   its statement. This gives the asserted isomorphism in D(\mathcal O_U). Its normalization can
   be checked using the finite-free derived-Hom model on U and on the one-point ringed space of
   A: choose P^p=0 for p>b and a representative F^q=0 for q<c of T. In Hom degree n only c-n\le
   p\le b contribute. Each finite-free factor identifies
   \widetilde{\operatorname{Hom}_A(P^p,F^{p+n})} with \mathcal
   Hom(\widetilde{P^p},\widetilde{F^{p+n}}) by sending a map to its sheaf map; the finite sums
   and differential d_Fh-(-1)^n h d_P agree. Evaluation sends h\otimes x to h(x) on both sides.
   Thus this is precisely the transpose of sheafified derived evaluation under the canonical
   tensor comparison. This description before choosing representatives proves naturality for
   derived morphisms.
7. At T=M, the algebraic scalar map is the transpose of the unit action A[0]\otimes_A^{\mathbf
   L}M\to M. The evaluation normalization of step 6 sends it to the transpose of \mathcal
   O_U\otimes^{\mathbf L}K|_U\to K|_U, which is the scalar map in the definition of a supplied
   pair. It is also the restriction of the scalar map on X: the open-restriction evaluation mate
   identifies transposes, and the canonical tensor restriction comparison carries the unit action
   to the unit action. Thus the assertion identifies the actual maps, not just their targets.
8. The affine equivalence is fully faithful and triangulated, with target a full subcategory of
   D(\mathcal O_U). Applying it to M,N[i] gives the required Hom bijection for every integer i.
   It preserves inverses, and full faithfulness lifts an inverse and its two identity equations,
   so it also gives the isomorphism bijection. If \alpha corresponds to a:M\to N, the natural
   affine pullback comparison identifies the sheafification of a\otimes^{\mathbf L}_{A,p_1}B with
   Lp_{1,U}^*\alpha. Steps 4--5 identify \gamma,\theta with the restricted classes. Therefore
   sheafification of (a\otimes^{\mathbf L}B)\gamma=\theta is exactly
   (Lp_{1,U}^*\alpha)\xi|_W=\eta|_W. Faithfulness over B gives the converse. This proves the
   class-preservation equivalence.
9. The preceding choices are canonical: on representative maps, tilde sends rh to r\widetilde h
   and gh to \widetilde g\,\widetilde h. The same identities hold on roofs, since a quasi-
   isomorphism is sent to an invertible map. These identities prove scalar and composition
   compatibility. For smaller affine opens U'\subset U, V'\subset V with f(U')\subset V', their
   product W'=U'\times_{V'}U' is an affine open of W. The pullback comparison identifies
   restriction with derived extension of scalars on U' and on W'. The diagonal section
   calculation of step 4 identifies its restricted algebra with \mathcal O_{U'} pushed along its
   diagonal, including multiplication. For the class Hom comparison, the affine algebra-class
   comparison explicitly gives compatibility with every affine-open restriction, including
   successive ones. For the comparison of step 6, restriction of the same evaluation map and the
   invertible open-restriction evaluation mate give the smaller-chart comparison: both are the
   unique tensor--Hom transpose of that evaluation after the canonical tensor identifications.
   Thus scalar maps, Hom bijections and the class-preservation equation all commute with these
   restrictions. This applies to arbitrary affine open subcharts, not only principal ones.
10. If U is empty, A=B=0 and all its module and sheaf derived objects are zero; choose the
   interval [0,0]. All asserted equations and bijections are then the unique ones. For f the
   identity on an affine scheme, B=A, p_1 is the identity, and the formulas reduce to affine
   realization and the ordinary tensor unit and evaluation maps. The argument nowhere assumes
   nonemptiness or Noetherianity.
-/
theorem exists_arbitraryBaseAffineDualizingRealization
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (hE : ∀ i, IsCoherentRelativeDualizingPair f (E i) (ξ i))
    [IsOpenImmersion jA] [IsOpenImmersion jR] :
    ArbitraryBaseAffineDualizingRealization f E ξ R A jA jR h := by
  sorry

end AlgebraicGeometry
