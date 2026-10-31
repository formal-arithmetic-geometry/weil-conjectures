/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.SmoothDVRGenericLineExtension
import WeilConjectures.AlgebraicGeometry.InvertibleAffineLimitDescent
import WeilConjectures.CategoryTheory.SiteModuleSheafGluing

/-! # Extending a rigidified line over a big open of a normal base

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.2.2--3.2.3,
codimension-one reduction; the agent spreading formulation in the DAG, using
Stacks Project, Tags 00PD, 0BD9, 0B8W, 01ZR and 04TR
(blueprint: lem-sfb-rigidified-line-big-open-extension).

The isomorphism over the original open preserves the specified rigidification,
using the existing canonical tensor composition and structure-module maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonObj

namespace AlgebraicGeometry

/-- A rigidified line on the restriction of a smooth separated finitely presented
commutative group scheme with connected geometric fibres extends over an open containing
all points of local-ring dimension at most one in a normal integral locally Noetherian base.

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.2.2--3.2.3,
codimension-one reduction, agent spreading formulation; Stacks Project, Tags 00PD,
0BD9, 0B8W, 01ZR and 04TR
(blueprint: lem-sfb-rigidified-line-big-open-extension).

Proof:
1. The generic point belongs to the dense open U. By
   lem-sc-scheme-stalk-dimension-generalization-chains, it is the only point of
   local-ring dimension zero. At each dimension-one point s outside U the local
   ring is a DVR by lem-sc-normal-dim1-dvr: affine Noetherianity and the localization
   description give Noetherian stalks (pqf-lem-affine-open-locnoeth and
   lem-weil-pbc-affine-open-stalk-localization). Its fraction field is the function
   field, so the inverse image of U is the generic point of this trait.
2. A Noetherian affine neighbourhood has finitely many boundary components
   (lem-sc-noetherian-closed-subset-finite-components). Their generic points exist
   by lem-weil-pbc-scheme-sober. The dimension-one chain bound says the only boundary
   component containing s has generic point s. Remove the other components, then
   shrink to an affine neighbourhood. The boundary is now the closure of s.
3. By lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods and
   lem-weil-pbc-scheme-over-limit the schemes G_W have limit G over this local ring,
   and the schemes G_(U intersect W) have limit its generic fibre, with affine transitions.
4. Finite presentation and separatedness give finite type and separated base changes
   (lem-pod-separated-finite-type-base-change). The affine bases and G_W are Noetherian
   by pqf-lem-affine-open-locnoeth and lem-weil-pbc-finite-type-over-noetherian.
   Their opens are quasi-compact by lem-sfb-noetherian-open-immersion-qc and
   quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated.
5. Smoothness survives base change (lem-pc-proper-base-change). Apply
   lem-sfb-smooth-dvr-generic-line-extension over the trait, then descend its line
   to G_W by lem-trf-invertible-affine-limit-descent.
6. Descend the specified generic-fibre isomorphism and its inverse after shrinking W
   by lem-trf-fp-module-limit-isomorphism-descent. Lines are finitely presented.
7. Normalize H on G_W to H tensor p_W-star((e_W-star H)-dual). Evaluation rigidifies
   it. On U intersect W the original rigidification and the descended comparison
   identify e_W-star H with the unit. The resulting comparison sends h tensor lambda
   to lambda(t-inverse(1)) times alpha(h), so preserves the given rigidification.
8. Neighbourhoods chosen for distinct boundary dimension-one points overlap only
   in U. Otherwise their boundary generic points form, with the generic point of S,
   a strict chain of length two, contradicting the dimension-one chain bound.
9. Set V to U union these neighbourhoods. Glue N and the normalized local extensions
   using their specified comparisons over U. Distinct overlaps lie in U; transitions
   are composites through N and satisfy the cocycle by cancellation. Apply
   lem-weil-pbc-site-module-sheaf-gluing on G_V. Local rank one gives invertibility.
10. The compatible rigidifications and their inverses glue as maps of sheaves. The
    resulting comparison over G_U preserves precisely r. All dimension-zero and
    dimension-one points are in V; hence its complement has local-ring dimension
    at least two. With no boundary dimension-one points take V = U.
-/
theorem exists_rigidified_line_big_open_extension
    (S : Scheme.{u}) [IsIntegral S] [IsLocallyNoetherian S]
    (hnormal : ∀ s : S,
      IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (U : S.Opens) (hU : Dense (U : Set S))
    (N : (pullback G.hom U.ι).Modules) [N.IsInvertible]
    (r : (Scheme.Modules.tensorPullback
        (sectionBaseChange G.hom η[G].left (by simp) (Over.mk U.ι))).obj N ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ∃ (V : S.Opens) (hUV : U ≤ V),
      (∀ s : S, ringKrullDim (S.presheaf.stalk s) ≤ 1 → s ∈ V) ∧
      ∃ N_V : (pullback G.hom V.ι).Modules, N_V.IsInvertible ∧
      ∃ r_V : (Scheme.Modules.tensorPullback
          (sectionBaseChange G.hom η[G].left (by simp) (Over.mk V.ι))).obj N_V ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf,
      ∃ α : (Scheme.Modules.tensorPullback
          (baseChangeMap G.hom (Over.homMk (U := Over.mk U.ι) (V := Over.mk V.ι)
            (S.homOfLE hUV) (S.homOfLE_ι hUV)))).obj
            N_V ≅ N,
        (Scheme.Modules.tensorPullback
            (sectionBaseChange G.hom η[G].left (by simp) (Over.mk U.ι))).map α.hom ≫
            r.hom =
          (Scheme.Modules.tensorPullbackCompositionIso
            (sectionBaseChange G.hom η[G].left (by simp) (Over.mk U.ι))
            (baseChangeMap G.hom (Over.homMk (U := Over.mk U.ι) (V := Over.mk V.ι)
            (S.homOfLE hUV) (S.homOfLE_ι hUV)))
            (S.homOfLE hUV ≫
              sectionBaseChange G.hom η[G].left (by simp) (Over.mk V.ι))
            (sectionBaseChange_comp_baseChangeMap G.hom η[G].left (by simp)
              (Over.homMk (U := Over.mk U.ι) (V := Over.mk V.ι)
            (S.homOfLE hUV) (S.homOfLE_ι hUV)))).inv.app N_V ≫
          (Scheme.Modules.tensorPullbackCompositionIso (S.homOfLE hUV)
            (sectionBaseChange G.hom η[G].left (by simp) (Over.mk V.ι))
            (S.homOfLE hUV ≫
              sectionBaseChange G.hom η[G].left (by simp) (Over.mk V.ι)) rfl).hom.app N_V ≫
          (Scheme.Modules.tensorPullback (S.homOfLE hUV)).map r_V.hom ≫
          Scheme.Modules.tensorPullbackObjUnitToUnit (S.homOfLE hUV) := by
  sorry

end AlgebraicGeometry
