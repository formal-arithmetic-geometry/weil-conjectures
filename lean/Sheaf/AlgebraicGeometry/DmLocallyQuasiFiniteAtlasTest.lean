/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks

/-! # Étale atlas test for local quasi-finiteness of DM stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 06UF, 06PU and 06UC;
Tag 06N3 for the Deligne--Mumford étale presentations
(blueprint: lem-sfb-dm-lqf-atlas-test).

The intrinsic predicate retains local finite type, the locally quasi-finite
relative diagonal and discrete field fibres. The universal test allows
nonsurjective étale charts. The existential test requires both maps to be atlases.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Intrinsic local quasi-finiteness is equivalent both to the test on every étale
scheme chart after every scheme base change and to the existence of suitable
étale scheme atlases. The projection comparison specifies the actual composite
scheme morphism; it is not an arbitrary morphism between the two chart schemes.
Source: Stacks Project, Tags 06UF (1), (2), (4), 06PU, 06UC and 06N3
(blueprint: lem-sfb-dm-lqf-atlas-test).

Proof:
1. Assume intrinsic local quasi-finiteness and fix V → Y and an étale chart
   U → X ×_Y V. The DM atlas calculus gives the DM base change. The stack
   finite-type calculus and chartwise smooth/étale calculus show that U → V
   is locally of finite type: the chart is étale, hence smooth, hence locally
   finitely presented and locally of finite type, and local finite type is
   preserved under base change and composition.
2. For Spec k → V the field fibre X_k has discrete point space. Apply
   lem-sfb-dm-field-etale-chart-quasifinite to its base-changed chart U_k.
   It is locally quasi-finite over k. At v ∈ V take k = κ(v). The isolation
   assertion of lem-weil-pbc-quasi-finite-at-point-isolated makes every point
   of U_v isolated. Apply lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs
   to U → V, already locally of finite type, on affine neighbourhoods of
   each u and its image. This proves the universal test without surjectivity.
3. Conversely, the universal test applies to an étale scheme atlas V of Y
   and an étale scheme atlas U of X ×_Y V, chosen by
   lem-sfb-dm-etale-atlas-calculus. It gives the existential test.
4. Assume these two atlases and local quasi-finiteness of h:U → V.
   By lem-weil-pbc-lqf-locally-finite-type, h is locally of finite type.
   The chartwise calculus makes both étale atlases smooth. The smooth
   presentation clause of lem-sfb-stack-finite-type-calculus makes f locally
   of finite type. The lemma lem-sfb-dm-relative-diagonal-quasifinite supplies
   its locally quasi-finite relative diagonal without extra assumptions on f.
5. For Spec k → Y put P = V ×_Y Spec k, choose an étale scheme atlas W of P,
   and set T = U ×_V W. The DM atlas calculus makes W → Spec k étale and
   surjective. The projection-compatible associativity of 2-fibre products
   identifies U ×_V P with the pullback of U over
   Q = X_k ×_k P. The maps T → U ×_V P, U ×_V P → Q and Q → X_k
   are base changes of the three étale surjective atlas maps. Their composite
   T → X_k is therefore an étale surjective scheme atlas.
6. By lem-a1-etale-space-locally-quasi-finite, W → Spec k is locally
   quasi-finite, so its points are isolated by the isolation lemma, and W
   is discrete. By lem-weil-pbc-separated-lqf-base-change, T → W is locally
   quasi-finite. Each singleton in its fibre is open; since its image singleton
   in W is open, that singleton is open in T. Thus T is discrete.
   The atlas topology of lem-sfb-stack-topology-open-substacks makes every
   subset of |X_k| open. This gives the discrete field fibres and finishes
   intrinsic local quasi-finiteness. -/
theorem locallyQuasiFinite_moduli_iff_etale_atlas {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor F G) :
    (IsLocallyQuasiFiniteModuliMap f ↔
      ∀ (V : Over S) (v : BasedFunctor (discreteModuli (yoneda.obj V)) G)
        (U : Over S)
        (a : BasedFunctor (discreteModuli (yoneda.obj U)) (moduliTwoFiberProduct v f))
        (p : U ⟶ V),
        IsEtaleModuliMap a →
          Nonempty (ModuliTwoIso (a.comp (moduliTwoFiberFst v f))
            (discreteModuliMap (yoneda.map p))) →
          Scheme.Hom.IsLocallyQuasiFinite p.left) ∧
    (IsLocallyQuasiFiniteModuliMap f ↔
      ∃ (V : Over S) (v : BasedFunctor (discreteModuli (yoneda.obj V)) G)
        (U : Over S)
        (a : BasedFunctor (discreteModuli (yoneda.obj U)) (moduliTwoFiberProduct v f))
        (p : U ⟶ V),
        IsEtaleModuliAtlas v ∧ IsEtaleModuliAtlas a ∧
          Nonempty (ModuliTwoIso (a.comp (moduliTwoFiberFst v f))
            (discreteModuliMap (yoneda.map p))) ∧
          Scheme.Hom.IsLocallyQuasiFinite p.left) := by
  sorry

end CategoryTheory
