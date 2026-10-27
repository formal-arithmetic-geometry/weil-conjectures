/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.ZariskiSquareZeroExtension
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.Sheaves.Stalks
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated

/-! # Schemes from Zariski square-zero ring extensions

Source: Stacks Project, Tag 05YV, lemma-first-order-thickening
(blueprint: lem-sfb-zariski-square-zero-scheme-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A marked realization on an arbitrary open subset; both structure maps are normalized
against the original quotient and base algebra structure.
Source: Stacks Project, Tag 05YV, restriction of the affine-local construction
(blueprint: lem-sfb-zariski-square-zero-scheme-realization). -/
def ZariskiSquareZeroExtension.RealizesOpen {X B : Scheme.{u}} {f : X ⟶ B}
    {G : X.Modules} (D : ZariskiSquareZeroExtension f G) (U : X.Opens)
    (Y : Scheme.{u})
    (e : Y.toSheafedSpace ≅ D.space.restrict U.isOpenEmbedding)
    (j : U.toScheme ⟶ Y) (q : Y ⟶ B) : Prop :=
  IsFirstOrderThickening j ∧ j ≫ q = U.ι ≫ f ∧
    schemeToRinged.map j ≫ e.hom = D.reductionOpen U ∧
    e.hom ≫ D.space.ofRestrict U.isOpenEmbedding ≫ D.toBase = schemeToRinged.map q

/-- A map of restricted extensions, with identity reduced map and the specified base action.
Its sheaf map runs in the opposite direction to this ringed-space arrow.
Source: Stacks Project, Tag 05YV and Tag 01HB
(blueprint: lem-sfb-zariski-square-zero-scheme-realization). -/
def ZariskiSquareZeroExtension.IsOpenExtensionMap {X B : Scheme.{u}} {f : X ⟶ B}
    {G H : X.Modules} (D : ZariskiSquareZeroExtension f G)
    (E : ZariskiSquareZeroExtension f H) (U : X.Opens)
    (a : D.space.restrict U.isOpenEmbedding ⟶ E.space.restrict U.isOpenEmbedding) : Prop :=
  a.hom.base = 𝟙 (TopCat.of U) ∧
    a ≫ E.space.ofRestrict U.isOpenEmbedding ≫ E.toBase =
      D.space.ofRestrict U.isOpenEmbedding ≫ D.toBase ∧
    D.reductionOpen U ≫ a = E.reductionOpen U


/-- Realization, actual-kernel converse, canonical affine charts, and the contravariant
bijection on maps, on every open and compatibly with further restrictions.
Source: Stacks Project, Tag 05YV, statement and entire affine construction
(blueprint: lem-sfb-zariski-square-zero-scheme-realization).

Proof:
1. By lem-sc-abelian-sheaf-short-exact-stalkwise the stalk sequence is exact.
Units lift across a square-zero ideal: correct an inverse modulo the ideal by 1-k.
Thus the extension stalks are local, and the quotient morphism is local.
2. On each affine U, pqf-lem-affine-vanishing and
lem-sc-zariski-module-abelian-cohomology-agree give H¹(U,G)=0.
Apply lem-weil-pbc-right-derived-universal-delta-functor to get the surjection
E(U) → O(U), with its specified kernel and square-zero multiplication.
3. Use lem-a1-locally-ringed-space-affine-adjunction with the identity of E(U).
The quotient spectrum is a homeomorphism since every prime contains the nilpotent ideal.
4. Localize the section sequence using lem-sc-p1-localization-short-exact.
The kernel and quotient comparisons are isomorphisms by
lem-sbc-affine-module-germ-localization and lem-weil-pbc-spec-domain-stalks-function-field.
The middle comparison is an isomorphism by lem-weil-pbc-short-five-lemma.
5. Apply lem-weil-pbc-sets-sheaf-iso-on-stalks to get the canonical affine isomorphism.
These affine neighborhoods make the original ringed space a scheme; the quotient
is a closed immersion with square-zero ideal, hence a first order thickening.
6. The base map is local because its composite with the quotient is the original
scheme map, and the quotient reflects units. Algebra compatibility gives the base triangle.
7. Conversely the actual defining ideal of any first order thickening is quasi-coherent.
Apply lem-weil-pbc-closed-immersion-pushforward-annihilated to that ideal itself:
its square-zero property makes the quotient action a quasi-coherent O_X-module action.
Identify spaces by the thickening homeomorphism; its actual kernel gives the extension.
8. A ring-sheaf map reducing to the identity is local on stalks by the unit criterion.
It therefore gives the unique scheme map over B, and forgetting gives its inverse.
The structure-sheaf composition rule gives contravariance.
9. Restrict the same ringed space, kernel and structure maps to any open.
The canonical affine maps are natural, and the map correspondence uses exactly the
same sheaf components. Consequently all restriction squares commute, including on
nonaffine intersections. The open models below state this compatibility explicitly. -/
theorem zariski_square_zero_scheme_realization {X B : Scheme.{u}} (f : X ⟶ B) :
    (∀ (G : X.Modules) [G.IsQuasicoherent] (D : ZariskiSquareZeroExtension f G),
      (∃ (Y : Scheme.{u}) (e : Y.toSheafedSpace ≅ D.space)
        (j : X ⟶ Y) (q : Y ⟶ B), D.Realizes Y e j q) ∧
      (∀ (U : X.Opens), IsAffineOpen U →
        Function.Surjective (D.quotient.app (op U)) ∧
        ∃ (L : LocallyRingedSpace.{u})
          (e : L.toSheafedSpace ≅ D.space.restrict U.isOpenEmbedding),
          ∃ h : L ⟶ Spec.toLocallyRingedSpace.obj (op (D.algebra.obj.obj (op U))),
            IsIso h ∧
            toSpecΓ (D.algebra.obj.obj (op U)) ≫ LocallyRingedSpace.Γ.map h.op =
              D.algebra.obj.map (eqToHom U.isOpenEmbedding_obj_top).op ≫
                e.hom.hom.c.app (op ⊤)) ∧
      (∀ U : X.Opens, ∃ (Y : Scheme.{u})
        (e : Y.toSheafedSpace ≅ D.space.restrict U.isOpenEmbedding)
        (j : U.toScheme ⟶ Y) (q : Y ⟶ B), D.RealizesOpen U Y e j q) ∧
      (∀ (U V : X.Opens) (h : V ≤ U)
        (Y Z : Scheme.{u})
        (e : Y.toSheafedSpace ≅ D.space.restrict U.isOpenEmbedding)
        (d : Z.toSheafedSpace ≅ D.space.restrict V.isOpenEmbedding)
        (j : U.toScheme ⟶ Y) (k : V.toScheme ⟶ Z) (q : Y ⟶ B) (r : Z ⟶ B),
        D.RealizesOpen U Y e j q → D.RealizesOpen V Z d k r →
        ∃! a : Z ⟶ Y,
          IsOpenImmersion a ∧ a ≫ q = r ∧ k ≫ a = X.homOfLE h ≫ j ∧
          schemeToRinged.map a ≫ e.hom ≫ D.space.ofRestrict U.isOpenEmbedding =
            d.hom ≫ D.space.ofRestrict V.isOpenEmbedding)) ∧
    (∀ (Y : Scheme.{u}) (j : X ⟶ Y) (q : Y ⟶ B),
      IsFirstOrderThickening j → j ≫ q = f →
      ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (D : ZariskiSquareZeroExtension f G)
        (e : Y.toSheafedSpace ≅ D.space), D.Realizes Y e j q) ∧
    (∀ (G H : X.Modules) [G.IsQuasicoherent] [H.IsQuasicoherent]
      (D : ZariskiSquareZeroExtension f G) (E : ZariskiSquareZeroExtension f H)
      (U : X.Opens) (Y Z : Scheme.{u})
      (e : Y.toSheafedSpace ≅ D.space.restrict U.isOpenEmbedding)
      (d : Z.toSheafedSpace ≅ E.space.restrict U.isOpenEmbedding)
      (j : U.toScheme ⟶ Y) (k : U.toScheme ⟶ Z) (q : Y ⟶ B) (r : Z ⟶ B),
      D.RealizesOpen U Y e j q → E.RealizesOpen U Z d k r →
      (∀ a : D.space.restrict U.isOpenEmbedding ⟶ E.space.restrict U.isOpenEmbedding,
        D.IsOpenExtensionMap E U a →
        ∃! g : Y ⟶ Z, j ≫ g = k ∧ g ≫ r = q ∧
          schemeToRinged.map g ≫ d.hom = e.hom ≫ a) ∧
      (∀ g : Y ⟶ Z, j ≫ g = k → g ≫ r = q →
        D.IsOpenExtensionMap E U (e.inv ≫ schemeToRinged.map g ≫ d.hom))) := by
  sorry

end AlgebraicGeometry
