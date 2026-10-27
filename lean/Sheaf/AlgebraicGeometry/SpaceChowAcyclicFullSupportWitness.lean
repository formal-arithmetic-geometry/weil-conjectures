/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # An acyclic faithful coherent Chow twist

Source: Stacks Project, spaces-cohomology.tex, Tag 08AR, condition (3), from weak Chow
through the full-support calculation; Tags 089J, 08AQ and 02O4
(blueprint: lem-sfb-space-chow-acyclic-full-support-witness).

All clauses concern one choice of cover and exponent. The scheme tensor power is
specified on every étale chart of its representable space. The map to the product
is specified by both projections. The annihilator condition tests every local scalar
on every further restriction, so it is the sheaf annihilator rather than only the
annihilator of a global-section module. Higher images use the fixed small-model
derived direct image, transported back to the original module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- One projective Chow twist is coherent, faithful, of full support and g-acyclic.
Source: Stacks Project, Tag 08AR, construction for condition (3), with projective
inputs Tags 089J, 08AQ and 02O4
(blueprint: lem-sfb-space-chow-acyclic-full-support-witness).

Proof:
1. The étale charts of Z are locally of finite type over Spec A, hence locally
   Noetherian by pqf-lem-locnoeth-lft. Properness gives quasi-compactness and the
   closed relative diagonal gives quasi-separatedness over the affine base
   (lem-weil-pbc-affine-scheme-qcqs). Apply lem-sfb-space-weak-chow to get T, pi, j.
2. The composite h = g pi is proper (lem-sfb-space-proper-composition). Proper
   cancellation against the separated proper projective projection makes j proper
   (lem-sfb-space-proper-cancellation). Its immersion is closed by
   lem-weil-pbc-proper-immersion-closed. Scheme tests identify the chart and
   topological quasi-compactness conventions, using finite affine covers and the
   closed diagonal, so pi has the asserted chartwise properness.
3. The graph of pi is a base change of the closed diagonal of g. Compose it with
   the base change of j: lem-weil-pbc-closed-immersion-base-change and
   lem-weil-pbc-closed-immersion-products give the closed map (j,pi). Its twist and
   j's twist agree because their standard-chart transition functions are identical.
4. The powers of L are locally free of rank one. Apply
   lem-sfb-space-projective-serre-vanishing to both projective embeddings and take
   the maximum of their two bounds and zero. For this d, positive higher images
   under pi and h vanish. Put G = pi_* (L.tensorPow d).
5. On affine étale charts use lem-trf-space-etale-module-pushforward-restriction
   and lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to identify G with
   the scheme projective direct image. Its finite type follows from
   lem-pc-m1-projective-pushforward-finite-type-independent, and its coherence from
   pqf-lem-coherent-ft-locnoeth. The same argument makes h_* (L.tensorPow d) coherent.
   Quasi-coherence is part of the same projective scheme calculation.
6. In lem-sfb-ringed-topos-relative-leray all rows q>0 vanish. All incoming and
   outgoing differentials of row zero vanish, so the finite filtration has just
   one graded piece: R^p g_* G is isomorphic to R^p h_* (L.tensorPow d).
   This gives positive-degree vanishing and coherent degree-zero direct image.
7. The coordinate sections generate L and their d-th powers generate its d-th
   tensor power (use 1 for d=0): lem-weil-pbc-projective-ample-invertible. Above
   any z choose t and a generating section. The counit carries the pullback of
   this section of G to that generator. The stalk tensor formula
   lem-sfb-ringed-topos-pullback-stalk therefore makes G's geometric stalk nonzero.
   Lem-sfb-space-etale-chart-support identifies this with full ordinary chart support.
8. Each affine étale chart is reduced. For its finite module N, full support gives
   V(Ann N)=Spec R by lem-weil-pbc-finite-type-module-support-closed. The equality
   of radicals (lem-weil-pbc-zero-locus-eq-iff-radical-eq) and reducedness imply
   Ann N=0. Apply this on principal opens and descend to obtain the zero sheaf
   annihilator. All properties use the same n,d,T,pi,j. -/
theorem exists_chow_acyclic_fullSupport_witness
    {S : Scheme.{u}} (A : CommRingCat.{u}) [IsNoetherianRing A]
    (a : Spec A ⟶ S) (Z : AlgebraicSpace S)
    (g : Z ⟶ schemeSpace (Over.mk a))
    (hg : MapIsProper g)
    (hne : Nonempty (Point Z.obj.obj))
    (hred : ∀ U : Z.EtaleSite, IsReduced (Z.etaleForget.obj U))
    (hirr : IrreducibleSpace (Point Z.obj.obj))
    [HasDerivedCategory.{w} Z.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace (Over.mk a)).SmallModules] :
    ∃ (n d : ℕ) (T : Over S)
      (j : T ⟶ Over.mk
        ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A) ≫ a))
      (π : schemeSpace T ⟶ Z),
      MapIsProper π ∧ Function.Surjective (mapPoint π.hom.hom) ∧
      IsClosedImmersion j.left ∧
      ∃ (p : Over.mk
          ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A) ≫ a) ⟶
          Over.mk a)
        (k : yoneda.obj T ⟶ Limits.pullback (yoneda.map p) g.hom.hom),
        p.left = (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A) ∧
        k ≫ Limits.pullback.fst (yoneda.map p) g.hom.hom = yoneda.map j ∧
        k ≫ Limits.pullback.snd (yoneda.map p) g.hom.hom = π.hom.hom ∧
        IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) k ∧
        ∃ M : (schemeSpace T).Modules,
          M.IsQuasicoherent ∧
          (∀ U : (schemeSpace T).EtaleSite,
            Nonempty (((schemeSpace T).schemeRestriction U).obj M ≅
              (Scheme.Modules.tensorPullback (chartToScheme T (𝟙 _) U)).obj
                (((Scheme.Modules.tensorPullback j.left).obj
                  (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec A) 1)).tensorPow d))) ∧
          ∃ G : Z.Modules,
            Nonempty (G ≅ (moduleDirectImage π).obj M) ∧
            G.IsQuasicoherent ∧
            (∀ U : Z.EtaleSite,
              RingedSpace.IsCoherent (Z.etaleForget.obj U).toRingedSpace
                ((Z.schemeRestriction U).obj G)) ∧
            moduleSupport G = Set.univ ∧
            (∀ (U : Z.EtaleSite) (r : Z.structureSheaf.obj.obj (op U)),
              (∀ (V : Z.EtaleSite) (f : V ⟶ U) (s : G.val.obj (op V)),
                Z.structureSheaf.obj.map f.op r • s = 0) → r = 0) ∧
            ((moduleDirectImage g).obj G).IsQuasicoherent ∧
            (∀ U : (schemeSpace (Over.mk a)).EtaleSite,
              RingedSpace.IsCoherent
                ((schemeSpace (Over.mk a)).etaleForget.obj U).toRingedSpace
                (((schemeSpace (Over.mk a)).schemeRestriction U).obj
                  ((moduleDirectImage g).obj G))) ∧
            ∀ q : ℕ, 0 < q →
              IsZero (((schemeSpace (Over.mk a)).smallModuleEquivalence.inverse).obj
                ((DerivedCategory.homologyFunctor
                  (schemeSpace (Over.mk a)).SmallModules (q : ℤ)).obj
                  ((derivedDirectImage g).obj
                    ((DerivedCategory.singleFunctor Z.SmallModules 0).obj
                      (Z.smallModuleRestriction.obj G))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
