/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentHomLocalKernel
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation
import WeilConjectures.AlgebraicGeometry.StalkInternalHomEvaluation
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Affine and stalk tests for coherent reflexive modules

Source: Stacks Project, Divisors, Tags 0AY0 and 0AY3
(blueprint: lem-sfb-affine-reflexive-module-comparison).

The evaluation morphism is the existing `SheafOfModules.bidual`; its duals are the
`SheafOfModules.homObj` sheaves into the structure module. Algebraic reflexivity is
Mathlib's `Module.IsReflexive`, bijectivity of the actual double-dual evaluation.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Sheaf reflexivity, reflexivity on every affine open, and stalk reflexivity are equivalent.

Source: Stacks Project, Divisors, Tags 0AY0 and 0AY3
(blueprint: lem-sfb-affine-reflexive-module-comparison).

Proof:
1. First $\mathcal O_Y$ is coherent. On every affine chart $W=\operatorname{Spec}A$,
   [lem-weil-pbc-spec-tilde-free-module] with rank one identifies $\mathcal O_W$ with $\widetilde
   A$, so $\mathcal O_Y$ is quasi-coherent by [pqf-def-coherent]. It is of finite type, generated
   by $1$ on every open. Apply [pqf-lem-coherent-ft-locnoeth]. Open subschemes remain locally
   Noetherian by [pqf-def-locnoeth], and coherent modules restrict to coherent modules by
   [lem-weil-pbc-coherent-module-local-on-open-cover](1). These observations apply to all affine
   opens used below, including the empty open.
2. For any coherent module $H$ on $Y$, [lem-weil-pbc-coherent-hom-local-kernel] expresses $H^\vee$
   locally as a kernel of a map between finite sums of $\mathcal O_Y$. Those sums and kernels are
   coherent by [lem-weil-pbc-coherent-modules-kernel-cokernel-sum](1),(3); coherence glues by
   [lem-weil-pbc-coherent-module-local-on-open-cover](2). Apply this first to $H=F$ and then to
   $H=F^\vee$. Thus $F,F^\vee,F^{\vee\vee}$ are coherent and hence quasi-coherent by
   [pqf-lem-coherent-ft-locnoeth]. Moreover $F$ and $F^\vee$ are of finite presentation by
   [lem-weil-pbc-coherent-local-finite-presentation]: at each point its finite free cokernel
   presentation is exactly the condition of [def-weil-pbc-module-finite-type-presentation](2).
   Sheaf Hom restricts to sheaf Hom on each open, directly from its definition
   [def-pur-sheaf-hom].
3. Fix an affine open $W=\operatorname{Spec}A$ and write $M=F(W)$. For a quasi-coherent module $H$
   on $W$, [lem-weil-pbc-affine-tilde-gamma-adjunction](1),(3) identifies $H$ with
   $\widetilde{H(W)}$ and gives $\operatorname{Hom}_{\mathcal O_W}(H,\mathcal
   O_W)\cong\operatorname{Hom}_A(H(W),A)$. The bijection takes a sheaf morphism $\varphi$ to its
   section map $\varphi_W$, as follows from the stated adjunction formula and the counit
   corresponding to the identity. It is $A$-linear because addition and scalar multiplication of
   morphisms are sectionwise. By [def-pur-sheaf-hom], applying this to $F|_W$ gives
   $F^\vee(W)\cong M^*$, where $M^*=\operatorname{Hom}_A(M,A)$. Applying it to $F^\vee|_W$ and
   precomposing with the inverse of this isomorphism gives $F^{\vee\vee}(W)\cong M^{**}$. Under
   these isomorphisms the section map of evaluation $e:F\to F^{\vee\vee}$ is $M\to M^{**}$: for
   $s\in F(W)$ and $\varphi\in F^\vee(W)$ its value is $\varphi_W(s)$, by the definition of
   evaluation.
4. If $e$ is an isomorphism, each $e_W$ is an isomorphism, so step 3 proves (ii). Conversely,
   assume (ii). Step 3 says $e_W$ is an isomorphism for every affine open $W$. Both $F|_W$ and
   $F^{\vee\vee}|_W$ are quasi-coherent by step 2, so the natural counits of
   [lem-weil-pbc-affine-tilde-gamma-adjunction](3) identify $e|_W$ with $\widetilde{e_W}$; it is
   therefore an isomorphism. The inverses on the affine cover agree on every overlap because both
   invert $e$ there. By [lem-weil-pbc-glue-sheaves-of-modules](1) they glue to an inverse of $e$,
   and the two inverse identities can be checked on that cover. This proves (i) if and only if
   (ii). In particular, on a single affine scheme it suffices that evaluation on global sections
   is an isomorphism.
5. Fix $y\in Y$ and put $R=\mathcal O_{Y,y}$. Since $F$ and $F^\vee$ are finitely presented by
   step 2, [lem-weil-pbc-stalk-internal-hom-finite-presentation] gives canonical linear
   isomorphisms $c:(F^\vee)_y\xrightarrow{\sim}\operatorname{Hom}_R(F_y,R)$ and
   $d:(F^{\vee\vee})_y\xrightarrow{\sim}\operatorname{Hom}_R((F^\vee)_y,R)$. Precomposing $d$ with
   $c^{-1}$ identifies the latter target with
   $\operatorname{Hom}_R(\operatorname{Hom}_R(F_y,R),R)$. This identifies $e_y$ with module
   evaluation: given $s_y\in F_y$ and $\psi\in\operatorname{Hom}_R(F_y,R)$, surjectivity of $c$
   writes $\psi=c(\varphi_y)$ for a germ of a local sheaf morphism $\varphi$. Represent $s_y$ and
   $\varphi_y$ on a common neighbourhood. By [lem-weil-pbc-stalk-internal-hom-evaluation], the
   image of $e_y(s_y)$ evaluated on $\psi$ is $(\varphi(s))_y=\psi(s_y)$. Thus the comparison
   preserves the actual evaluation map, not merely the two double-dual objects.
6. By step 5, condition (iii) says exactly that $e_y$ is bijective for every point $y$. By
   [lem-weil-pbc-module-iso-on-stalks] this is equivalent to $e$ being an isomorphism. This proves
   (i) if and only if (iii), and together with step 4 proves the three-way equivalence. -/
theorem affine_stalk_reflexive_module_comparison
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Y.Modules) (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    (IsIso (SheafOfModules.bidual (R := Y.sheaf) F) ↔
      ∀ (W : Y.Opens), IsAffineOpen W → Module.IsReflexive Γ(Y, W) Γ(F, W)) ∧
    (IsIso (SheafOfModules.bidual (R := Y.sheaf) F) ↔
      ∀ (y : Y), Module.IsReflexive (Y.presheaf.stalk y)
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj F)) := by
  sorry

/-- A finite module over a Noetherian domain is reflexive exactly when its tilde sheaf is.

Source: Stacks Project, Divisors, Tags 0AY0 and 0AY3
(blueprint: lem-sfb-affine-reflexive-module-comparison).

Proof:
1. Finally let $A$ be a Noetherian domain and $M$ a finite $A$-module. The scheme
   $X=\operatorname{Spec}A$ is locally Noetherian by the one-chart definition [pqf-def-locnoeth],
   and integral by [lem-weil-pbc-spec-domain-stalks-function-field](2). The associated sheaf
   $\widetilde M$ is quasi-coherent by [lem-weil-pbc-spec-module-tilde-sections] and has global
   sections $M$ by [lem-weil-pbc-affine-tilde-gamma-adjunction](2). It is of finite type by
   [lem-weil-pbc-quasi-coherent-finite-type-affine](a), hence coherent by
   [pqf-lem-coherent-ft-locnoeth]. Step 3 identifies its evaluation on global sections with $M\to
   M^{**}$. The single-affine conclusion of step 4 therefore proves that $\widetilde M$ is
   reflexive exactly when $M$ is reflexive. When $M=0$ all the evaluation maps are the unique
   isomorphisms of zero modules; on an empty affine open the sheaf modules and their duals are
   likewise zero, so no exception to the assertions is needed. -/
theorem isIso_bidual_tilde_iff_isReflexive
    (A : CommRingCat.{u}) [IsNoetherianRing A] [IsDomain A]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsIso (SheafOfModules.bidual (R := (Spec A).sheaf) (tilde M)) ↔
      Module.IsReflexive A M := by
  sorry

end AlgebraicGeometry
