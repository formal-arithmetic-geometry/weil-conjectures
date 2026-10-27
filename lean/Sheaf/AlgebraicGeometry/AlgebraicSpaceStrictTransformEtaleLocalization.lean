/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStrictTransformPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus

/-! # Etale localization of algebraic-space strict transforms

Source: Stacks Project, Divisors on Spaces, Tag 0863(1)-(3), lemma-strict-transform-local;
Topologies on Algebraic Spaces, Tag 041F(3)
(blueprint: lem-sfb-space-strict-transform-etale-localization).

Schemes A and W are encoded by algebraic spaces with scheme-representable underlying
presheaves. Cartesian squares retain both projections of the canonical comparisons.
The module comparison is normalized on local tensors and on the quotient maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Strict transforms commute with etale localization, including module quotients and
surjectivity of transformed covering charts. The image factorization k specifies the
extended centre on A; it is not an independently chosen blowup centre.
Source: Stacks Project, Divisors on Spaces, Tag 0863(1)-(3); Topologies on Algebraic
Spaces, Tag 041F(3) (blueprint: lem-sfb-space-strict-transform-etale-localization).

Proof:
1. By lem-sfb-space-fppf-covering-calculus, the etale map A to T is flat. Apply
   lem-sfb-space-blowup-chart-properties to identify its blowup with A times_T B.
   Thus v is etale. Associativity identifies the chart ambient space with
   W times_X P.ambient, and lem-trf-space-fibre-products-etale-covers makes h etale.
   The exceptional ideals agree, since each is the image of the same pulled-back K.
2. Apply lem-trf-space-etale-module-pushforward-restriction to the cartesian square
   with vertical maps P.toSource and PA.toSource. Its tensor comparison lambda
   has the displayed local-section normalization. On every localized etale test,
   the two torsion kernels consist of the same sections killed locally by a power
   of that same exceptional ideal. Restriction preserves these kernels and the
   sheaf quotients, since both are computed locally. Hence the quotient comparison
   e exists, with the displayed commuting triangle; epimorphic quotient maps make
   it unique. No flatness of f or of M is used.
3. Apply the kernel identification to the structure sheaf. It preserves functions
   and multiplication, so the closed subspaces agree after base change. On affine
   tests this is B tensor_R (R/I) = B/IB. The resulting map j commutes with the
   closed inclusions and exhibits PA.space as P.space times_X W.
4. If A to T and W to X times_T A cover on field-valued points, base change and
   composition show W to X is surjective. Applying
   lem-trf-space-fibre-products-etale-covers to these singleton etale covers gives
   surjectivity of v and h. A further base change gives surjectivity of j.
   Zero and unit centres, empty charts, arbitrary module torsion and noncartesian
   original squares are all included. -/
theorem strictTransform_etale_localization
    {S : Scheme.{u}} {X T A W : AlgebraicSpace S}
    (f : X ⟶ T) (a : A ⟶ T) (w : W ⟶ X) (g : W ⟶ A)
    (comm : w ≫ f = g ≫ a)
    (hA : ∃ A₀ : Over S, Nonempty (A.obj.obj ≅ yoneda.obj A₀))
    (hW : ∃ W₀ : Over S, Nonempty (W.obj.obj ≅ yoneda.obj W₀))
    (ha : IsEtale a.hom.hom) (hw : IsEtale w.hom.hom)
    (K : QuasiCoherentIdeal T) (hK : (K.val : T.Modules).IsFiniteType)
    (B : BlowupPresentation K) (P : StrictTransformPresentation f K B) :
    ∃ (KA : QuasiCoherentIdeal A)
      (k : (moduleTensorPullback a).obj (K.val : T.Modules) ⟶ (KA.val : A.Modules)),
      Epi k ∧ k ≫ KA.val.arrow = idealTensorMap a K ∧
      ∃ (BA : BlowupPresentation KA) (PA : StrictTransformPresentation g KA BA)
        (v : BA.space ⟶ B.space) (h : PA.ambient ⟶ P.ambient)
        (hv : IsEtale v.hom.hom) (hh : IsEtale h.hom.hom)
        (hp : IsPullback h.hom PA.toSource.hom P.toSource.hom w.hom),
        IsPullback BA.projection.hom v.hom a.hom B.projection.hom ∧
        h ≫ P.toBlowup = PA.toBlowup ≫ v ∧
        ∃ (j : PA.space ⟶ P.space),
          j ≫ P.inclusion = PA.inclusion ≫ h ∧
          IsPullback j.hom (PA.inclusion ≫ PA.toSource).hom
            (P.inclusion ≫ P.toSource).hom w.hom ∧
          (∀ (M : X.Modules), M.IsQuasicoherent →
            ∃ (Q : ModuleStrictTransformPresentation f K B P M)
              (QW : ModuleStrictTransformPresentation g KA BA PA ((pullback w hw).obj M))
              (c : (pullback h hh).obj ((moduleTensorPullback P.toSource).obj M) ≅
                (moduleTensorPullback PA.toSource).obj ((pullback w hw).obj M)),
              (∀ (V : W.EtaleSite) (q : ModuleChart PA.toSource V)
                (b d : PA.ambient.structureSheaf.obj.obj (op q.left))
                (m : M.val.obj (op ((etaleMap w hw).obj V))),
                c.hom.val.app (op q.left)
                  (b • moduleTensorSection P.toSource M ((etaleMap w hw).obj V)
                    (moduleChartBaseChange P.toSource w h PA.toSource hw hh hp.w V q) d m) =
                  moduleTensorSection PA.toSource ((pullback w hw).obj M) V q (b * d) m) ∧
              ∃! e : (pullback h hh).obj Q.module ≅ QW.module,
                (pullback h hh).map Q.quotient ≫ e.hom = c.hom ≫ QW.quotient) ∧
          (IsJointlySurjective (fun _ : Unit ↦ a.hom.hom) →
            IsJointlySurjective (fun _ : Unit ↦
              Limits.pullback.lift w.hom.hom g.hom.hom
                (congrArg (fun z ↦ z.hom.hom) comm)) →
            IsJointlySurjective (fun _ : Unit ↦ v.hom.hom) ∧
              IsJointlySurjective (fun _ : Unit ↦ h.hom.hom) ∧
              IsJointlySurjective (fun _ : Unit ↦ j.hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
