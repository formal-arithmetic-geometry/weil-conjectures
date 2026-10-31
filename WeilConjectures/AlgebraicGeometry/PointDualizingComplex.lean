/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PointDualityCoefficientsFiber
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences
import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedPointBasisEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import WeilConjectures.AlgebraicGeometry.ContractibleLisseEvaluation
import WeilConjectures.AlgebraicGeometry.ContractibleEvaluationAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
/-! # Dualizing complex of the geometric point
Source: current blueprint, sec-six-functors/sk-thm-sf-package/
lem-pod-point-dualizing-complex.md (blueprint: lem-pod-point-dualizing-complex).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- The point assertion in the ordinary condensed derived category. The two functors
are the restriction of the actual identity compact-support composite and its right
adjoint. The last two natural isomorphisms are the fibre and realization dual formulas.
Source: current blueprint lem-pod-point-dualizing-complex, displayed formulas
(blueprint: lem-pod-point-dualizing-complex). -/
def PointDualizingComplexStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∃ (hu : (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (𝟙_ (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))))))
    (F G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
      ConstantModelConstructibleFiniteTor Λ (Spec (.of k))),
    Nonempty (F ⋙ (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ≅
      (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ
          (pointDualityCompactification k)) ∧
    Nonempty (F ⊣ G) ∧ Nonempty (G ≅ 𝟭 _) ∧
    Nonempty ((G.obj ⟨𝟙_ _, hu⟩).obj ≅ 𝟙_ _) ∧
    Nonempty (((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι.op ⋙
      (CondensedRing.derivedHom Λ (Spec (.of k))).flip.obj (G.obj ⟨𝟙_ _, hu⟩).obj) ⋙
        pointDualityFiber Λ k ≅
      ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ pointDualityFiber Λ k).op ⋙
        (Functor.curry.obj (ordinaryModuleDerivedInternalHom
          (condensedScalarRing Λ))).flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u + 1} (condensedScalarRing Λ)) 0).obj
                (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)))) ∧
    Nonempty ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι.op ⋙
      (CondensedRing.derivedHom Λ (Spec (.of k))).flip.obj (G.obj ⟨𝟙_ _, hu⟩).obj ≅
      (((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ pointDualityFiber Λ k).op ⋙
        (Functor.curry.obj (ordinaryModuleDerivedInternalHom
          (condensedScalarRing Λ))).flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u + 1} (condensedScalarRing Λ)) 0).obj
                (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)))) ⋙
        condensedScalarRealization Λ (Spec (.of k)))
/-- Identity exceptional inverse image and coefficient duality at the geometric point, for precisely
the four condensed coefficients. The definition-owned coefficient-family predicate specifies
the fixed finite extension, integral ring, finite quotient and finite-subextension algebraic
closure.
Source: current blueprint lem-pod-point-dualizing-complex, statement and proof (blueprint: lem-
pod-point-dualizing-complex).
Proof (the current DAG proof, in five steps):
1. For the identity choose the compactification $(\mathrm{id}_s,\mathrm{id}_s)$. Its lower
shriek is $R(\mathrm{id}_*)D(\mathrm{id}_!)=\mathrm{id}$ by [def-sfb-module-derived-lower-
shriek-compactification]: both underived functors are literally identities, hence exact. The
canonical compactification comparison [det-sf-comp-coherence-cocycle] identifies the chosen
$Ra_{s!}$ with this functor. Uses: def-sfb-module-derived-lower-shriek-compactification, det-sf-
comp-coherence-cocycle.
2. The restricted adjunction [sk-thm-existence](3),(4) gives natural bijections
$\Phi_K:\mathrm{Hom}(K,Ra_s^!L)\simeq\mathrm{Hom}(K,L)$. Set $u=\Phi_{Ra_s^!L}(1)$ and
$v=\Phi_L^{-1}(1)$. Naturality gives $uv=1$ and $\Phi_{Ra_s^!L}(vu)=\Phi_{Ra_s^!L}(1)$, so
$vu=1$. Naturality in $L$ gives $Ra_s^!\cong\mathrm{id}$ and $\omega_{s,\Lambda}\cong B$. Uses:
sk-thm-existence.
3. The algebraically closed point $s$ is w-contractible [sk-def-pe-wlocal], hence weakly
contractible [det-pe-weak-contractible-equivalences]. Point-basis evaluation [lem-weil-pbc-
condensed-point-basis-evaluation] gives $\Gamma(s,B)=\Lambda(*)=R$. The exact normalized
sections data [lem-zl-contractible-derived-sections-tensor] give $F_s\dashv G=R\Gamma(s,-)$ with
invertible unit [lem-zl-contractible-realization-adjunction]. The same data give the strong
monoidal perfect/lisse equivalence with inverse $G$ [lem-zl-contractible-lisse-evaluation].
Uses: sk-def-pe-wlocal, det-pe-weak-contractible-equivalences, lem-weil-pbc-condensed-point-
basis-evaluation, lem-zl-contractible-derived-sections-tensor, lem-zl-contractible-realization-
adjunction, lem-zl-contractible-lisse-evaluation.
4. Dualizable objects are closed under shifts and cones [lem-zl-derived-dualizable-stability],
and contain zero. Each local scalar-perfect model [def-sfb-locally-constant-perfect-complex] is
dualizable: scalar perfect complexes are dualizable [lem-zl-ring-derived-dualizable-perfect],
and strong monoidal realization and pro-etale locality preserve this [lem-zl-condensed-lisse-
proetale-locality]. On $s$ a locally closed subscheme is empty or $s$. Thus generation [det-thm-
sf-ctf-stability-internal-hom] makes $C$ dualizable. Step 3 gives $c\in\mathrm{Perf}(R)$ and
$F_sc\simeq C$. Uses: lem-zl-derived-dualizable-stability, def-sfb-locally-constant-perfect-
complex, lem-zl-ring-derived-dualizable-perfect, lem-zl-condensed-lisse-proetale-locality, det-
thm-sf-ctf-stability-internal-hom.
5. Write $H=R\mathcal Hom_B(C,B)$. For every $q\in D(R)$, the closed tensor adjunction [lem-sf-
ringed-derived-closed-symmetric-monoidal] and step 3 give naturally
$\mathrm{Hom}(q,GH)\cong\mat
hrm{Hom}(F_sq,H)\cong\mathrm{Hom}(F_s(q\otimes_R^Lc),B)\cong\mathrm{Hom}(q\otimes_R^Lc,R)\cong\m
athrm{Hom}(q,R\mathrm{Hom}_R(c,R))$.
Yoneda proves $GH\cong c^\vee$. Since $C$ is dualizable,
its dual is $H$ by this same closed adjunction; hence $H$ is dualizable, and step 3 also gives
$H\cong F_s(c^\vee)$. Step 2 replaces $B$ by $\omega_s$, proving both formulas. All maps are the
natural adjunction transposes. The unit $B$ is constructible and flat in degree zero, hence in
$D^b_{ctf}$. Applying internal-Hom closure [det-thm-sf-ctf-stability-internal-hom] to $C,B$ puts
$H$ in $D^b_{ctf}(s,\Lambda)$. Uses: lem-sf-ringed-derived-closed-symmetric-monoidal, det-thm-
sf-ctf-stability-internal-hom. -/
theorem point_dualizing_complex (P : WeilConjectures.PoincareDualityConventions.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : WeilConjectures.IsPointDualityCoefficient P Λ) :
    PointDualizingComplexStatement Λ.X P.datum.k := by
  sorry
end AlgebraicGeometry.ProEtale
