/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsCoordinates
import Sheaf.SixFunctors.TraceFormula.TensorSectionsCoordinateCoherence
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Normalized tensor-section comparisons for line modules

Source: Stacks Project, Descent, Tags 03DX (2), 03LC (1), 05VG, and
remark-change-topologies-ringed-sites
(blueprint: lem-trf-etale-line-sections-normalized-comparisons).

The existing `trf` definitions are reused. No equivalence of categories is asserted or
used: the functor carries all module morphisms, with its specified section coordinates.
Restriction is expressed on module presheaves; the target is a module sheaf and the
isomorphism therefore also supplies the sheaf condition on its source.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

/-- The section functor, normalized unit and restriction comparisons, their coherence,
and the frames from every Zariski trivialization.

Source: Stacks Project, Descent, Tags 03DX (2), 03LC (1), 05VG; Sheaves, Tags 0095–0097
(blueprint: lem-trf-etale-line-sections-normalized-comparisons).

Proof:
1. The normalized restrictions of `lem-sc-etale-qcoherent-presheaf-functorial` are
   semilinear. Invertibility gives quasi-coherence, and
   `lem-sc-etale-qcoherent-descent` makes these exact section groups a sheaf.
   Naturality of the adjunction unit and composition comparison makes sectionwise
   pullback of every module map natural. Pullback preserves identities and composition.
2. The adjoint structure map of `lem-weil-pbc-module-pullback-structure-sheaf` sends
   a local tensor `a ⊗ b` to `a u♯(b)`, and its inverse sends `a` to `a ⊗ 1`.
   The balanced relation verifies both inverse equations locally.
   `lem-sc-etale-tensor-unit-restriction-equation` proves restriction naturality,
   and linearity makes these maps module-sheaf isomorphisms.
3. Pull back a Zariski frame of the line module. On each inverse-image open its
   tensor pullback is the structure module, by multiplication with inverse inserting
   `1`. The inverse-image opens cover, so the tensor pullback is invertible.
4. Define beta at `w` by sections of `tensorSectionsComp w v` inverse.
   `lem-sc-left-adjoint-composition-iso-associativity` gives its restriction square.
   Naturality of the adjunction unit moves pullback of a section past the comparison;
   naturality of the comparison itself gives the module-morphism equation.
5. For identity pullback, its tensor-unit comparison and the composition comparison
   have the same adjoint by the unit equation. Uniqueness in
   `lem-weil-pbc-conjugate-iso-unit-equation` identifies them; cancelling the inverse
   proves the identity equation, including the canonical site-object identification.
6. Evaluate the composition equation at each test object. Rearrange the associativity
   equation from `lem-sc-left-adjoint-composition-iso-associativity` and take sections.
   The site associativity arrow supplies the canonical iterated-restriction transport.
7. The two structure comparisons have the same adjoint, namely the composite ring
   map. The injectivity of the adjunction bijection gives
   `e_w w^*(e_v) c_{w,v}^{-1} = e_{wv}`, proving unit compatibility.
8. Every Zariski cover is etale by
   `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`. Compose beta, the image
   of each chosen frame, and epsilon. Their inverses are the required local frames.
   This works for arbitrary covers and for the empty scheme and its empty cover.
-/
theorem etale_line_sections_normalized_comparisons :
    ∃ (A : ∀ X : Scheme.{u}, TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
      (α : ∀ (X : Scheme.{u}) (L : TrfInvertibleModules X),
        trfLineSections ((A X).obj L) ≅ trfInvertibleSections L)
      (ε : ∀ X : Scheme.{u},
          ((A X).obj (trfStructureInvertible X)).obj ≅
            SheafOfModules.unit (trfEtaleStructureRing X))
      (p : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          ((Modules.tensorPullback v).obj L.obj).IsInvertible)
        (β : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          (PresheafOfModules.pushforward₀ (trfEtaleCompose v)
            (trfEtaleStructureRing X).obj).obj ((A X).obj L).obj.val ≅
          ((A Y).obj ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).obj.val),
      (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (U : X.Etale)
        (r : Γ(U.left, ⊤)) (s : ((A X).obj L).obj.val.obj (op U)),
        (α X L).hom.hom.app (op U) (r • s) =
          (((Modules.tensorPullback U.hom).obj L.obj).smul r).hom
            ((α X L).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (L K : TrfInvertibleModules X) (h : L.obj ⟶ K.obj)
        (U : X.Etale) (s : ((A X).obj L).obj.val.obj (op U)),
        (α X K).hom.hom.app (op U)
          ((trfComparisonMap (A X) h).val.app (op U) s) =
        ((Modules.tensorPullback U.hom).map h).app ⊤ ((α X L).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (U : X.Etale)
        (s : ((A X).obj (trfStructureInvertible X)).obj.val.obj (op U)),
        (ε X).hom.val.app (op U) s = (trfTensorUnit U.hom).hom.app ⊤
          ((α X (trfStructureInvertible X)).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (U : X.Etale) (a : Γ(U.left, ⊤)),
        (α X (trfStructureInvertible X)).hom.hom.app (op U)
          ((ε X).inv.val.app (op U) a) = (trfTensorUnit U.hom).inv.app ⊤ a) ∧
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X)
          (W : Y.Etale) (s : ((A X).obj L).obj.val.obj
            (op ((trfEtaleCompose v).obj W))),
          (α Y ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).hom.hom.app (op W)
              ((β X Y v L).hom.app (op W) s) =
            ((Modules.tensorSectionsComp W.hom v).inv.app L.obj).app ⊤
              ((α X L).hom.hom.app (op ((trfEtaleCompose v).obj W)) s)) ∧
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L K : TrfInvertibleModules X)
          (h : L.obj ⟶ K.obj) (W : Y.Etale),
          (β X Y v L).hom.app (op W) ≫
            (trfComparisonMap (A Y)
              (L := ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩)
              (K := ⟨(Modules.tensorPullback v).obj K.obj, p X Y v K⟩)
              ((Modules.tensorPullback v).map h)).val.app (op W) =
          (trfComparisonMap (A X) h).val.app
              (op ((trfEtaleCompose v).obj W)) ≫ (β X Y v K).hom.app (op W)) ∧
        (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (W : X.Etale)
          (s : ((A X).obj L).obj.val.obj
            (op ((trfEtaleCompose (𝟙 X)).obj W))),
          (trfComparisonMap (A X)
            (L := ⟨(Modules.tensorPullback (𝟙 X)).obj L.obj, p X X (𝟙 X) L⟩)
            (K := L) ((trfTensorId X).hom.app L.obj)).val.app (op W)
              ((β X X (𝟙 X) L).hom.app (op W) s) =
            ((A X).obj L).obj.val.map (trfEtaleIdArrow W).op s) ∧
        (∀ (X Y Z : Scheme.{u}) (v : Y ⟶ X) (w : Z ⟶ Y) [Etale v] [Etale w]
          (L : TrfInvertibleModules X) (W : Z.Etale)
          (s : ((A X).obj L).obj.val.obj
            (op ((trfEtaleCompose v).obj ((trfEtaleCompose w).obj W)))),
          (trfComparisonMap (A Z)
            (L := ⟨(Modules.tensorPullback w).obj ((Modules.tensorPullback v).obj L.obj),
              p Y Z w ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩⟩)
            (K := ⟨(Modules.tensorPullback (w ≫ v)).obj L.obj, p X Z (w ≫ v) L⟩)
            ((Modules.tensorSectionsComp w v).hom.app L.obj)).val.app (op W)
              ((β Y Z w ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).hom.app (op W)
                ((β X Y v L).hom.app (op ((trfEtaleCompose w).obj W)) s)) =
          (β X Z (w ≫ v) L).hom.app (op W)
            (((A X).obj L).obj.val.map (trfEtaleCompArrow v w W).op s)) ∧
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (W : Y.Etale)
          (s : ((A X).obj (trfStructureInvertible X)).obj.val.obj
            (op ((trfEtaleCompose v).obj W))),
          (ε Y).hom.val.app (op W)
            ((trfComparisonMap (A Y)
              (L := ⟨(Modules.tensorPullback v).obj
                (SheafOfModules.unit X.ringCatSheaf), p X Y v (trfStructureInvertible X)⟩)
              (K := trfStructureInvertible Y) (trfTensorUnit v).hom).val.app (op W)
                ((β X Y v (trfStructureInvertible X)).hom.app (op W) s)) =
            (ε X).hom.val.app (op ((trfEtaleCompose v).obj W)) s) ∧
        (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (I : Type (u + 1))
          (V : I → X.Opens) (_hV : ∀ x : X, ∃ i, x ∈ V i)
          (frame : ∀ i, (Modules.tensorPullback (V i).ι).obj L.obj ≅
            SheafOfModules.unit (V i).toScheme.ringCatSheaf),
          X.smallEtaleTopology.CoversTop (fun i ↦ Scheme.Etale.mk (V i).ι) ∧
          ∃ τ : ∀ i,
            (PresheafOfModules.pushforward₀ (trfEtaleCompose (V i).ι)
              (trfEtaleStructureRing X).obj).obj ((A X).obj L).obj.val ≅
                (SheafOfModules.unit (trfEtaleStructureRing (V i).toScheme)).val,
            ∀ (i : I) (W : (V i).toScheme.Etale)
              (s : ((A X).obj L).obj.val.obj
                (op ((trfEtaleCompose (V i).ι).obj W))),
              (τ i).hom.app (op W) s =
                (ε (V i).toScheme).hom.val.app (op W)
                  ((trfComparisonMap (A (V i).toScheme)
                    (L := ⟨(Modules.tensorPullback (V i).ι).obj L.obj,
                      p X (V i).toScheme (V i).ι L⟩)
                    (K := trfStructureInvertible (V i).toScheme) (frame i).hom).val.app (op W)
                      ((β X (V i).toScheme (V i).ι L).hom.app (op W) s))) := by
  obtain ⟨A, α, ε, p, β, hscalar, hmap, hunit, hβ⟩ := etale_line_sections_coordinates
  obtain ⟨hid, hcomp, hunitcomp⟩ := trf_tensor_sections_coordinate_coherence
  have hinjective (X : Scheme.{u}) (L : TrfInvertibleModules X) (U : X.Etale) :
      Function.Injective ((α X L).hom.hom.app (op U)) :=
    (ConcreteCategory.bijective_of_isIso ((α X L).hom.hom.app (op U))).injective
  refine ⟨A, α, ε, p, β, hscalar, hmap, hunit, ?_, hβ, ?_, ?_, ?_, ?_, ?_⟩
  · intro X U a
    have he := hunit X U ((ε X).inv.val.app (op U) a)
    have hε : (ε X).hom.val.app (op U) ((ε X).inv.val.app (op U) a) = a := by
      exact congrArg (fun f ↦ f.val.app (op U) a) (ε X).inv_hom_id
    have ht := congrArg ((trfTensorUnit U.hom).inv.app ⊤) (he.symm.trans hε)
    simpa only [← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app,
      Iso.hom_inv_id, Modules.Hom.id_app, ConcreteCategory.id_apply] using ht
  · intro X Y v hv L K h W
    ext s
    apply hinjective Y ⟨(Modules.tensorPullback v).obj K.obj, p X Y v K⟩ W
    change (α Y ⟨(Modules.tensorPullback v).obj K.obj, p X Y v K⟩).hom.hom.app (op W)
        ((trfComparisonMap (A Y) ((Modules.tensorPullback v).map h)).val.app (op W)
          ((β X Y v L).hom.app (op W) s)) =
      (α Y ⟨(Modules.tensorPullback v).obj K.obj, p X Y v K⟩).hom.hom.app (op W)
        ((β X Y v K).hom.app (op W)
          ((trfComparisonMap (A X) h).val.app (op ((trfEtaleCompose v).obj W)) s))
    erw [hmap, hβ, hβ, hmap]
    exact (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.app ⊤) ((Modules.tensorSectionsComp W.hom v).inv.naturality h))
        ((α X L).hom.hom.app (op ((trfEtaleCompose v).obj W)) s)).symm
  · intro X L W s
    apply hinjective X L W
    erw [hmap, hβ]
    have hn := ConcreteCategory.congr_hom
      ((α X L).hom.hom.naturality (trfEtaleIdArrow W).op) s
    exact (hid X L.obj W _).trans hn.symm
  · intro X Y Z v w hv hw L W s
    apply hinjective Z
      ⟨(Modules.tensorPullback (w ≫ v)).obj L.obj, p X Z (w ≫ v) L⟩ W
    erw [hmap, hβ X Z (w ≫ v) L W,
      hβ Y Z w ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩ W,
      hβ X Y v L ((trfEtaleCompose w).obj W)]
    have hn := ConcreteCategory.congr_hom
      ((α X L).hom.hom.naturality (trfEtaleCompArrow v w W).op) s
    erw [hn]
    exact hcomp X Y Z v w L.obj W _
  · intro X Y v hv W s
    erw [hunit Y, hmap, hβ X Y v (trfStructureInvertible X) W, hunit X]
    exact hunitcomp X Y v W _
  · intro X L I V hV frame
    have hcover : X.smallEtaleTopology.CoversTop
        (fun i ↦ Scheme.Etale.mk (V i).ι) := by
      erw [GrothendieckTopology.coversTop_iff_of_isTerminal X.smallEtaleTopology
        (Scheme.Etale.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@Etale) X)]
      let f (i : I) : Scheme.Etale.mk (V i).ι ⟶ Scheme.Etale.mk (𝟙 X) :=
        MorphismProperty.Over.homMk (V i).ι (Category.comp_id _)
      apply X.smallEtaleTopology.superset_covering _
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr ?_)
      · rintro Y g ⟨i, b, e⟩
        rcases e with ⟨g', ⟨j⟩, hgj⟩
        exact ⟨j, ⟨b⟩⟩
      · apply Set.eq_univ_of_forall
        intro x
        obtain ⟨i, hx⟩ := hV x
        exact Set.mem_iUnion.mpr ⟨i, ⟨⟨x, hx⟩, rfl⟩⟩
    refine ⟨hcover, ?_⟩
    let e (i : I) :
        ((A (V i).toScheme).obj
          ⟨(Modules.tensorPullback (V i).ι).obj L.obj, p X (V i).toScheme (V i).ι L⟩).obj ≅
        ((A (V i).toScheme).obj (trfStructureInvertible (V i).toScheme)).obj :=
      (ObjectProperty.ι _).mapIso ((A (V i).toScheme).mapIso
        (ObjectProperty.isoMk (fun M : (V i).toScheme.Modules ↦ M.IsInvertible) (frame i)))
    refine ⟨fun i ↦ β X (V i).toScheme (V i).ι L ≪≫
      (SheafOfModules.forget _).mapIso (e i) ≪≫
      (SheafOfModules.forget _).mapIso (ε (V i).toScheme), ?_⟩
    intro i W s
    rfl

end AlgebraicGeometry.Scheme
