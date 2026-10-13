/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleRecoveryComparisonIso
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Normalization of one tensor recovery comparison
Source: Stacks Project, Tags 0095 and 0096. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A single recovery comparison, followed by the inverse base-chart comparison,
is ordinary pullback along the total chart path preceded by the unique comparison
of left adjoints for the total base map.
Source: Stacks Project, Tags 0095 and 0096; step 1 of
lem-pc-open-cover-tensor-comparison-coherence.
(blueprint: lem-pc-open-cover-tensor-recovery-normalization).
Proof: Transpose the tensor composition comparison under the chosen adjunctions.
Its transpose is pushforwardComp followed by pushforwardCongr. Replace each tensor
left adjoint by the ordinary left adjoint using leftAdjointUniq. Conjugation respects
composition and whiskering, and the ordinary inverse composition has the same
transpose, by conjugateEquiv_pullbackComp_inv. Injectivity therefore identifies
these comparisons. Expand the two chart comparisons and moduleRecoveryComparisonIso.
Move the unique comparisons across whiskering by naturality and cancel each inverse
pair. Ordinary pullback associativity then identifies the three factors with the
explicit rho below; the equality H records the two chart projection equations.
All constructions exist for arbitrary modules and charts, including empty charts
and the zero module, and no invertibility of the scheme maps is required. -/
theorem openCover_tensor_recovery_normalization
    {X Y W : Scheme.{u}} (q : Y ⟶ X) (p : W ⟶ Y) (h : W ⟶ X)
    (w : p ≫ q = h) (U : X.OpenCover.{u}) (a : U.I₀)
    (H : (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a) ≫ U.f a =
      ((U.pullback₁ q).pullback₁ p).f a ≫ h)
    (c : tensorPullback h ≅ pullback h)
    (hc : c = Adjunction.leftAdjointUniq
      (Classical.choose (exists_tensorPullbackAdjunction h)) (pullbackPushforwardAdjunction h))
    (t : pullback (U.f a) ⋙ pullback (U.pullbackHom q a) ≅
      tensorPullback q ⋙ pullback ((U.pullback₁ q).f a))
    (ht : t = openCoverTensorPullbackComparison q U a)
    (ck : tensorPullback h ⋙ pullback (((U.pullback₁ q).pullback₁ p).f a) ≅
      (tensorPullback q ⋙ pullback ((U.pullback₁ q).f a)) ⋙
        pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
    (hck : ck = moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
      (tensorPullback p) (pullback ((U.pullback₁ q).f a))
      (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
      (pullback (((U.pullback₁ q).pullback₁ p).f a))
      (tensorPullbackCompositionIso p q h w)
      (openCoverTensorPullbackComparison p (U.pullback₁ q) a))
    (rho : pullback h ⋙ pullback (((U.pullback₁ q).pullback₁ p).f a) ≅
      (pullback (U.f a) ⋙ pullback (U.pullbackHom q a)) ⋙
        pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
    (hrho : rho = pullbackComp (((U.pullback₁ q).pullback₁ p).f a) h ≪≫
      (pullbackCongr H).symm ≪≫
      (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫
        U.pullbackHom q a) (U.f a)).symm ≪≫
      Functor.isoWhiskerLeft (pullback (U.f a))
        (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
          (U.pullbackHom q a)).symm ≪≫
      (Functor.associator (pullback (U.f a)) (pullback (U.pullbackHom q a))
        (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))).symm)
    (M : X.Modules) :
    ck.hom.app M ≫ (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).map
        (t.inv.app M) =
      (pullback (((U.pullback₁ q).pullback₁ p).f a)).map (c.hom.app M) ≫
        rho.hom.app M := by sorry

end AlgebraicGeometry.Scheme.Modules
