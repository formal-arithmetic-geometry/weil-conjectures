/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.RingTheory.SquareZeroEtaleExtensionCriterion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Scheme charts of an étale square-zero ring extension

Source: Stacks Project, Tags 05YV and 05ZT, lemma-first-order-thickening;
Tag 05YT, lemma-lift-etale-infinitesimal
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction).

The auxiliary definitions are the literal restriction of the given ring presheaf
and its quotient to the Zariski opens of a chart. No scheme or lift is chosen.
The theorem supplies marked realizations and the compatible equivalence of sites.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

/-- The Zariski opens of an étale chart, viewed as objects of the original site.
Source: Stacks Tag 05ZT, second proof paragraph
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction). -/
def etaleSquareZeroChartOpens {T : Scheme.{u}} (U : T.Etale) :
    U.left.Opens ⥤ T.Etale :=
  MorphismProperty.Comma.lift (U.left.restrictFunctor ⋙ Over.map U.hom)
    (fun W ↦ inferInstanceAs (Etale (W.ι ≫ U.hom)))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The top open of a chart is canonically that chart, not a second site object.
Source: Stacks Tag 05ZT, compatibility of the affine and open constructions
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction). -/
def etaleSquareZeroChartTopIso {T : Scheme.{u}} (U : T.Etale) :
    (etaleSquareZeroChartOpens U).obj ⊤ ≅ U :=
  MorphismProperty.Over.isoMk U.left.topIso (by rfl)

/-- The prescribed space and prescribed ring presheaf, before proving it is a scheme.
Source: Stacks Tags 05YV and 05ZT, restriction to the Zariski site
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction). -/
def etaleSquareZeroChartSpace {T : Scheme.{u}}
    (A : Sheaf T.smallEtaleTopology CommRingCat.{u}) (U : T.Etale) :
    PresheafedSpace CommRingCat.{u} where
  carrier := U.left.carrier
  presheaf := (etaleSquareZeroChartOpens U).op ⋙ A.obj

/-- The quotient on a chart, with identity point map. The final isomorphism identifies
regular functions on an open subscheme with sections on that open.
Source: Stacks Tags 05YV and 05ZT
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction). -/
def etaleSquareZeroChartReduction {T : Scheme.{u}}
    {A : Sheaf T.smallEtaleTopology CommRingCat.{u}}
    (p : A.obj ⟶ T.etaleStructurePresheaf) (U : T.Etale) :
    U.left.toPresheafedSpace ⟶ etaleSquareZeroChartSpace A U where
  base := 𝟙 U.left.carrier
  c := Functor.whiskerLeft (etaleSquareZeroChartOpens U).op p ≫
    U.left.restrictFunctorΓ.hom

/-- A square-zero ring extension with quasi-coherent kernel has functorial scheme charts.
Source: Stacks Tags 05YV, 05YT and 05ZT
(blueprint: lem-sfb-scheme-etale-square-zero-chart-construction).

Proof:
1. Apply lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to the kernel M.
Its restriction on an étale V is the étale realization of the Zariski pullback.
By lem-sc-etale-affine-qcoherent, its H¹ vanishes on every affine chart. The
long exact sequence (lem-weil-pbc-sheaf-ext-cohomology-long-exact), the Ext/derived
comparison (lem-weil-pbc-sheafH-ext-derived-comparison), and the natural H⁰ section
identification (lem-weil-pbc-cohomology-pullback-degree-zero) make p surjective
on affine sections. Kernel exactness already holds sectionwise. This also proves
exactness on each restricted Zariski site. A need not be an O_T-module.
2. On U = Spec B put R = A(U) and K = M(U), so B = R/K and K² = 0. Every
prime contains K. Inverse image and quotient identify Spec B and Spec R,
including their principal-open bases (def-weil-affine-spectrum).
3. For r in R, its image on D(r mod K) is invertible: lift the inverse modulo K
and correct a product 1+k with 1-k. Restriction gives R_r → A(D(r mod K)).
Localize the exact section row (lem-sc-p1-localization-short-exact). Its outer
comparisons are isomorphisms by the principal-open localization formula
(lem-weil-pbc-affine-open-section-vanishing-prime), quasi-coherence, and
lem-weil-pbc-module-pullback-affine-sections. The additive short five lemma
(lem-weil-pbc-short-five-lemma) makes the middle ring map an isomorphism.
These maps commute with restrictions because they use the original restrictions.
4. Glue these compatible basis isomorphisms to identify the prescribed ringed
space with Spec R on each affine open. They agree on overlaps, covered by affine
opens without assuming the overlaps affine. Thus the prescribed space is a scheme
(def-pc-scheme). Its quotient defines the identity-on-points closed immersion
(def-weil-closed-immersion) with square-zero ideal. The affine case gives the
canonical spectrum comparison and section surjectivity.
5. Apply this to every étale chart. Restriction maps give maps of ringed spaces;
they are local on stalks because a unit modulo a square-zero ideal is a unit.
They respect identities and composition because the original restrictions do.
6. On affine charts of V → U, the kernel comparison K tensor_B C → L is the
canonical isomorphism k tensor c ↦ c k|_V by the quasi-coherent equivalence and
lem-weil-pbc-module-pullback-affine-sections. Apply
lem-sfb-square-zero-etale-extension-criterion to the exact square-zero section
extensions. Étaleness of B → C follows from target and source locality
(lem-weil-pbc-closed-finite-etale-zariski-local and lem-weil-pbc-etale-local-on-source).
The kernel L is KS since sections of C lift to S. Hence S tensor_R B = C.
The affine spectrum adjunction and tensor-product pullback formula
(lem-weil-pbc-morphism-into-affine-scheme and lem-weil-pbc-fibre-product-affine-spectra)
identify the actual arrows, so the affine square is cartesian.
7. Cover source and target by these affine charts. The same locality lemmas make
the lifted arrow étale. The canonical affine cartesian identifications glue,
proving the global pullback square (def-pc-fibre-product).
8. By sbc-lem-thickening-etale-site, these lifts form the inverse of base change.
Their structure rings are A(U), and their restriction maps are those of A by
step 5. Thus the entire ring sheaf, quotient and kernel are recovered, including
the marked Zariski identifications. Covering families remain jointly surjective
because the point maps are unchanged. Base change preserves finite limits
(lem-weil-pbc-etale-base-change-finite-limits), and full faithfulness reflects
their universal properties, so the inverse preserves these diagrams as well. -/
theorem scheme_etale_square_zero_chart_construction (T : Scheme.{u})
    (A : Sheaf T.smallEtaleTopology CommRingCat.{u})
    (p : A.obj ⟶ T.etaleStructurePresheaf)
    (M : CategoryTheory.ringedSiteModules.{u} (Scheme.Modules.smallEtaleModuleRing T))
    [M.IsQuasicoherent]
    (j : ∀ U : T.Etale, M.val.obj (op U) →+ A.obj.obj (op U))
    (hj : ∀ (U V : T.Etale) (f : U ⟶ V) (m : M.val.obj (op V)),
      A.obj.map f.op (j V m) = j U (M.val.map f.op m))
    (hinj : ∀ U : T.Etale, Function.Injective (j U))
    (hker : ∀ (U : T.Etale) (a : A.obj.obj (op U)),
      p.app (op U) a = 0 ↔ ∃ m : M.val.obj (op U), j U m = a)
    (hsurj : ∀ (U : T.Etale) (a : T.etaleStructurePresheaf.obj (op U)),
      ∃ R : Sieve U, R ∈ T.smallEtaleTopology U ∧
        ∀ (V : T.Etale) (f : V ⟶ U), R f →
          ∃ b : A.obj.obj (op V), p.app (op V) b = T.etaleStructurePresheaf.map f.op a)
    (hsq : ∀ (U : T.Etale) (m n : M.val.obj (op U)), j U m * j U n = 0)
    (hscalar : ∀ (U : T.Etale) (a : A.obj.obj (op U)) (m : M.val.obj (op U)),
      j U (p.app (op U) a • m) = a * j U m) :
    ∃ (Tplus : Scheme.{u}) (i : T ⟶ Tplus),
      IsFirstOrderThickening i ∧ IsHomeomorph i.base ∧
      ∃ eT : Tplus.toPresheafedSpace ≅
          etaleSquareZeroChartSpace A (Scheme.Etale.mk (𝟙 T)),
        i.toLRSHom.toHom ≫ eT.hom =
          etaleSquareZeroChartReduction p (Scheme.Etale.mk (𝟙 T)) ∧
        (IsAffine T →
          Function.Surjective (p.app (op (Scheme.Etale.mk (𝟙 T)))) ∧
          IsIso (Tplus.toSpecΓ ≫ Spec.map
            (A.obj.map (etaleSquareZeroChartTopIso (Scheme.Etale.mk (𝟙 T))).hom.op ≫
              PresheafedSpace.Γ.map eT.hom.op))) ∧
      ∃ (E : T.Etale ≌ Tplus.Etale)
        (r : Scheme.Etale.forget T ⋙ Over.forget T ⟶
          E.functor ⋙ Scheme.Etale.forget Tplus ⋙ Over.forget Tplus)
        (γ : A.obj ≅ E.functor.op ⋙ Tplus.etaleStructurePresheaf)
        (ε : E.functor ⋙ i.Etale ≅ 𝟭 T.Etale),
        E.functor.IsContinuous T.smallEtaleTopology Tplus.smallEtaleTopology ∧
        E.inverse.IsContinuous Tplus.smallEtaleTopology T.smallEtaleTopology ∧
        PreservesFiniteLimits E.functor ∧
        (∀ U : T.Etale,
          IsFirstOrderThickening (r.app U) ∧
          IsPullback U.hom (r.app U) i (E.functor.obj U).hom ∧
          (ε.inv.app U).left ≫ pullback.fst (E.functor.obj U).hom i = r.app U ∧
          (ε.inv.app U).left ≫ pullback.snd (E.functor.obj U).hom i = U.hom ∧
          γ.hom.app (op U) ≫ Scheme.Γ.map (r.app U).op = p.app (op U) ∧
          ∃ e : (E.functor.obj U).left.toPresheafedSpace ≅ etaleSquareZeroChartSpace A U,
            (r.app U).toLRSHom.toHom ≫ e.hom = etaleSquareZeroChartReduction p U ∧
            A.obj.map (etaleSquareZeroChartTopIso U).hom.op ≫
              PresheafedSpace.Γ.map e.hom.op = γ.hom.app (op U)) ∧
        (∀ U : T.Etale, IsAffine U.left →
          Function.Surjective (p.app (op U)) ∧
          IsIso ((E.functor.obj U).left.toSpecΓ ≫ Spec.map (γ.hom.app (op U)))) ∧
        (∀ (J : Type v) (U : T.Etale) (V : J → T.Etale) (f : ∀ k : J, V k ⟶ U),
          (∀ x : U.left, ∃ (k : J) (y : (V k).left), (f k).left y = x) →
          ∀ x : (E.functor.obj U).left,
            ∃ (k : J) (y : (E.functor.obj (V k)).left), (E.functor.map (f k)).left y = x) := by
  sorry

end

end AlgebraicGeometry
