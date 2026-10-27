/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q38, R2
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
import Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons
import Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsFullFaithful
import Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsEssSurj

/-! Étale comparison for invertible modules, by full faithfulness and effective descent. -/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- Ordinary invertible modules and étale line modules are equivalent by the specified
section functor, naturally for module morphisms and étale restriction.

Source: Stacks Project, Descent, Tags 03DX (2), 05VG (finite local freeness, rank one),
03LC (1) (blueprint: lem-trf-scheme-etale-invertible-comparison).

Proof:
1. Invertible modules are quasi-coherent. `lem-sc-etale-qcoherent-descent` makes the
   canonical tensor-sections presheaf a sheaf. Semilinearity and functoriality of its
   restrictions (`lem-sc-etale-qcoherent-presheaf-functorial`) give its module action.
   Naturality of the tensor-pullback adjunction gives the component formula for maps.
   The tensor-unit map `a ⊗ b ↦ a u♯(b)`, inverse `a ↦ a ⊗ 1`, identifies the units.
2. At `w : W → Y`, the restriction comparison is sections of the inverse of the
   unit-normalized `tensorSectionsComp w.hom v`. Naturality of this comparison gives
   compatibility with module maps. Its identity and associativity laws follow by
   multiplying scalars on local tensor generators, with identity inserting `1`.
3. A Zariski trivializing cover is an étale cover by
   `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`. Open-immersion tensor
   pullback is restriction (`lem-weil-pbc-open-immersion-module-pullback-restriction`),
   so the images are line modules.
4. Evaluate a map of associated line modules on open immersions to obtain an ordinary
   module map. On a local frame linearity and restriction naturality force its value
   on any étale object to be the displayed tensor-pullback map. Sheaf separatedness
   glues these equalities. Evaluation on opens also gives uniqueness, hence the Hom
   bijection for every module map.
5. For an étale trivializing family of a line module, transitions are multiplication
   by units: a module endomorphism of the structure sheaf is multiplication by its
   value at `1`. The triple-overlap identity gives the ordinary descent cocycle.
6. The family is fpqc (`lem-weil-pbc-fpqc-finer-than-etale`). Invertible-module fpqc
   descent (`lem-pc-fpqc-descent`) gives an ordinary invertible module and compatible
   local frames, using the structure-unit and composition comparisons from steps 1–2.
7. Glue the local identifications sectionwise on the pullbacks of the covering family,
   using the site axioms (`def-weil-pbc-sites-and-cohomology`). Their inverses glue too,
   so every line module is isomorphic to an associated one.
8. Full faithfulness and essential surjectivity give the stated equivalences. Lift
   conjugated maps by the Hom bijection to construct the inverse functor; uniqueness
   gives functor laws and triangle identities. Steps 1–2 supply the structure-module
   and coherent restriction comparisons. Empty schemes and arbitrary covers are allowed.
-/
theorem scheme_etale_invertible_comparison :
    ∃ (E : ∀ X : Scheme.{u}, TrfInvertibleModules X ≌ TrfEtaleLineModules X)
      (α : ∀ (X : Scheme.{u}) (L : TrfInvertibleModules X),
        trfLineSections ((E X).functor.obj L) ≅ trfInvertibleSections L),
      (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (U : X.Etale)
        (r : Γ(U.left, ⊤)) (s : ((E X).functor.obj L).obj.val.obj (op U)),
        (α X L).hom.hom.app (op U) (r • s) =
          (((Modules.tensorPullback U.hom).obj L.obj).smul r).hom
            ((α X L).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (L K : TrfInvertibleModules X) (h : L.obj ⟶ K.obj)
        (U : X.Etale) (s : ((E X).functor.obj L).obj.val.obj (op U)),
        (α X K).hom.hom.app (op U)
          ((trfComparisonMap (E X).functor h).val.app (op U) s) =
        ((Modules.tensorPullback U.hom).map h).app ⊤ ((α X L).hom.hom.app (op U) s)) ∧
      (∃ ε : ∀ X : Scheme.{u},
          ((E X).functor.obj (trfStructureInvertible X)).obj ≅
            SheafOfModules.unit (trfEtaleStructureRing X),
        ∀ (X : Scheme.{u}) (U : X.Etale)
          (s : ((E X).functor.obj (trfStructureInvertible X)).obj.val.obj (op U)),
          (ε X).hom.val.app (op U) s = (trfTensorUnit U.hom).hom.app ⊤
            ((α X (trfStructureInvertible X)).hom.hom.app (op U) s)) ∧
      ∃ (p : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          ((Modules.tensorPullback v).obj L.obj).IsInvertible)
        (β : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          (PresheafOfModules.pushforward₀ (trfEtaleCompose v)
            (trfEtaleStructureRing X).obj).obj ((E X).functor.obj L).obj.val ≅
          ((E Y).functor.obj ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).obj.val),
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X)
          (W : Y.Etale) (s : ((E X).functor.obj L).obj.val.obj
            (op ((trfEtaleCompose v).obj W))),
          (α Y ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).hom.hom.app (op W)
              ((β X Y v L).hom.app (op W) s) =
            ((Modules.tensorSectionsComp W.hom v).inv.app L.obj).app ⊤
              ((α X L).hom.hom.app (op ((trfEtaleCompose v).obj W)) s)) ∧
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L K : TrfInvertibleModules X)
          (h : L.obj ⟶ K.obj) (W : Y.Etale),
          (β X Y v L).hom.app (op W) ≫
            (trfComparisonMap (E Y).functor
              (L := ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩)
              (K := ⟨(Modules.tensorPullback v).obj K.obj, p X Y v K⟩)
              ((Modules.tensorPullback v).map h)).val.app (op W) =
          (trfComparisonMap (E X).functor h).val.app
              (op ((trfEtaleCompose v).obj W)) ≫ (β X Y v K).hom.app (op W)) ∧
        (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (W : X.Etale)
          (s : ((E X).functor.obj L).obj.val.obj
            (op ((trfEtaleCompose (𝟙 X)).obj W))),
          (trfComparisonMap (E X).functor
            (L := ⟨(Modules.tensorPullback (𝟙 X)).obj L.obj, p X X (𝟙 X) L⟩)
            (K := L) ((trfTensorId X).hom.app L.obj)).val.app (op W)
              ((β X X (𝟙 X) L).hom.app (op W) s) =
            ((E X).functor.obj L).obj.val.map (trfEtaleIdArrow W).op s) ∧
        (∀ (X Y Z : Scheme.{u}) (v : Y ⟶ X) (w : Z ⟶ Y) [Etale v] [Etale w]
          (L : TrfInvertibleModules X) (W : Z.Etale)
          (s : ((E X).functor.obj L).obj.val.obj
            (op ((trfEtaleCompose v).obj ((trfEtaleCompose w).obj W)))),
          (trfComparisonMap (E Z).functor
            (L := ⟨(Modules.tensorPullback w).obj ((Modules.tensorPullback v).obj L.obj),
              p Y Z w ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩⟩)
            (K := ⟨(Modules.tensorPullback (w ≫ v)).obj L.obj, p X Z (w ≫ v) L⟩)
            ((Modules.tensorSectionsComp w v).hom.app L.obj)).val.app (op W)
              ((β Y Z w ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).hom.app (op W)
                ((β X Y v L).hom.app (op ((trfEtaleCompose w).obj W)) s)) =
          (β X Z (w ≫ v) L).hom.app (op W)
            (((E X).functor.obj L).obj.val.map (trfEtaleCompArrow v w W).op s)) := by
  classical
  obtain ⟨A, α, ε, p, β, hscalar, hmap, hunit, _, hrestrict, hnatural,
    hid, hcomp, _, _⟩ := etale_line_sections_normalized_comparisons.{u}
  have hfull (X : Scheme.{u}) : (A X).Full ∧ (A X).Faithful :=
    etale_line_sections_fullFaithful (A X) (α X) (hscalar X) (hmap X)
  have hess (X : Scheme.{u}) : (A X).EssSurj :=
    etale_line_sections_essSurj (A X) (α X) (hscalar X)
  have (X : Scheme.{u}) : (A X).IsEquivalence :=
    ⟨(hfull X).2, (hfull X).1, hess X⟩
  exact ⟨fun X ↦ (A X).asEquivalence, α, hscalar, hmap,
    ⟨ε, hunit⟩, p, β, hrestrict, hnatural, hid, hcomp⟩

end AlgebraicGeometry.Scheme
