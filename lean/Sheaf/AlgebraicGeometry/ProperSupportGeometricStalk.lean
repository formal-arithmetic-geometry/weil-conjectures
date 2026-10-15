/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.ProperGeometricPointExchange
import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk

/-! # Geometric stalks of a proper-support subsheaf

Source: Stacks Project, Tag 0F76, including the restriction normalization in the first
paragraph of its proof (blueprint: lem-cbc-proper-support-geometric-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The restriction of direct-image germs to the geometric fibre is natural in the
module sheaf. On every proper-support subsheaf it induces a linear isomorphism onto
exactly the submodule of properly supported fibre sections. The displayed factorization
identifies its composite with the inclusion with ordinary restriction, and the germ
formula specifies that restriction on every representative.
Source: Stacks Project, Tag 0F76
(blueprint: lem-cbc-proper-support-geometric-stalk).

Proof:
1. Pull representatives to the fibre. Properness survives base change, so their supports
remain proper; inverse-image germ compatibility identifies these with their actual supports.
2. Extension by zero across an open subscheme preserves proper support: the proper-to-separated
triangle makes the support closed in the larger scheme, and sheaf gluing extends by zero.
3. Work locally on the base, then take the filtered union of quasi-compact opens of X.
Quasi-compactness of every proper support puts both representative and fibre sections in
some such open. Exactness of geometric stalks makes the source a union of these submodules.
4. For X quasi-compact and Y affine, Nagata compactification gives X open in a proper scheme.
Extend F by zero, using its unit isomorphism and zero stalks outside X.
5. Restriction identifies the proper direct image of this extension with the given G:
its sections have closed proper support inside X, and conversely gluing with zero extends
any section with such support. These operations commute with restrictions and sheaf maps.
6. The same gluing on the geometric fibre identifies global sections of the extension with
properly supported fibre sections. Base change for extension by zero preserves this formula.
7. Proper geometric-point exchange and the pullback-stalk comparison identify the proper
stalk map with restriction on representatives. Steps 3--6 give the asserted isomorphism.
A linear map shrinks support, so preserves proper support; both naturality paths restrict
the image of the same representative, giving naturality and the displayed normalization. -/
theorem properSupport_geometricStalk
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
        upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
          (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (Scheme.Etale.mk (𝟙 (pullback f y)))),
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
        (v : (Scheme.pointSmallEtale y).fiber.obj V),
        (Scheme.pointSmallEtale y).toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
          geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v) ∧
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F), Mono i →
        (∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
          (∃ t, i.hom.app (op V) t = s) ↔
            SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s) →
        ∃ S : Submodule Λ
            (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F).obj.obj
              (op (Scheme.Etale.mk (𝟙 (pullback f y))))),
          (∀ s, s ∈ S ↔ SectionHasProperSupport Λ
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
            (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s) ∧
          ∃ e : (Scheme.pointSmallEtale y).sheafFiber.obj G ≅ ModuleCat.of Λ S,
            e.hom ≫ ModuleCat.ofHom S.subtype =
              (Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F := by
  sorry

end AlgebraicGeometry.Etale
