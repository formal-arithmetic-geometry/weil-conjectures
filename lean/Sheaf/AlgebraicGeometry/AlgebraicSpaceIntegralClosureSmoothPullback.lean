/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAlgebraTensorPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Integral closure commutes with smooth pullback on algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 082E
(blueprint: lem-sfb-space-integral-closure-smooth-pullback).

The closures are subobjects in commutative algebra sheaves, characterized by the existing
Tag 0820 theorem. The isomorphism commutes with the actual pulled-back inclusion. Its
uniqueness expresses the identification as subalgebras, retaining compatibility with
algebra isomorphisms, identity pullback and composite smooth pullbacks: after the
normalized tensor transports these comparisons have the same ambient inclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smooth tensor pullback identifies the integral closures through their inclusions.
The unique isomorphism is over the pulled-back ambient algebra, not an abstract
isomorphism of modules. The two hypotheses on C and D are exactly the characterization
of the uniquely existing subobjects in existsUnique_quasiCoherent_integralClosure.
Source: Stacks Project, More on Morphisms of Spaces, Tag 082E
(blueprint: lem-sfb-space-integral-closure-smooth-pullback).

Proof:
1. Put C = IC_X(B). Its underlying module is quasi-coherent by Tag 0820. Pullback
preserves quasi-coherence by lem-sfb-space-module-pullback-quasicoherent. Choose affine
etale charts V of X covering X, then affine etale charts U covering Y times_X V.
Chartwise smoothness gives a smooth scheme map U to V. The normalized comparison of
lem-trf-space-chart-adjunction-tensor-realization, affine chart calculus, the scheme
Zariski/etale comparison and exists_tensorPullback_affine_sections identify the pulled
inclusion on U with T tensor_R C(V) to T tensor_R B(V), t tensor c mapping to t tensor c.
The algebra tensor normalization makes multiplication on these sections the product
of tensor factors.
2. Apply TensorProduct.toIntegralClosure_bijective_of_smooth. This identifies the
source with IC_T(T tensor_R B(V)), through the same tensor inclusion, and needs no
injectivity, finiteness or reducedness assumption on R to B(V). By Tag 0820 these
are exactly the affine sections of D. Thus the pulled inclusion is injective and
has image D, locally as a map of quasi-coherent sheaves by affine chart calculus.
3. The local factorizations through D agree on overlaps: their composites with the
monomorphism Subobject.arrow D agree. The sheaf axiom glues them and their inverses
to an algebra isomorphism e, with the displayed equation. Monicity of the inclusion
proves uniqueness.
4. Algebra isomorphisms preserve monic equations and therefore the closure inclusions.
The identity tensor transport sends a tensor c to ac. The composite tensor transport
sends a tensor (b tensor c) to a h-sharp(b) tensor c. Consequently the identity,
isomorphism and successive-pullback comparisons have the same composite with the
ambient inclusion as the comparison just constructed. The same uniqueness proves
all stated compatibilities, including the identity and arbitrary normalized models. -/
theorem integralClosure_smooth_pullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : Y ⟶ X)
    (hg : ∀ (U : Y.EtaleSite) (V : X.EtaleSite) (a : U.obj.left ⟶ V.obj.left),
      yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ g.hom.hom → Smooth a.left)
    (B : X.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    (C : Subobject B)
    (hC : (C : X.CommAlgebraSheaf).toModule.IsQuasicoherent ∧
      ∀ (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) →
        ∀ b : B.right.obj.obj (op V),
          b ∈ Set.range ((Subobject.arrow C).right.hom.app (op V)) ↔
            (B.hom.hom.app (op V)).hom.IsIntegralElem b)
    (P : AlgebraTensorPullbackModel g)
    (D : Subobject (P.functor.obj B))
    (hD : (D : Y.CommAlgebraSheaf).toModule.IsQuasicoherent ∧
      ∀ (U : Y.EtaleSite), IsAffine (Y.etaleForget.obj U) →
        ∀ b : (P.functor.obj B).right.obj.obj (op U),
          b ∈ Set.range ((Subobject.arrow D).right.hom.app (op U)) ↔
            ((P.functor.obj B).hom.hom.app (op U)).hom.IsIntegralElem b) :
    ∃! e : P.functor.obj (C : X.CommAlgebraSheaf) ≅ (D : Y.CommAlgebraSheaf),
      e.hom ≫ Subobject.arrow D = P.functor.map (Subobject.arrow C) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
