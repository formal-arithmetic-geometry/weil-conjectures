/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Étale comparison for invertible modules

Source: Stacks Project, Descent, Tags 03DX (2), 05VG and 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison).

The auxiliary definitions give the structure ring, the two full subcategories, and
postcomposition on the small étale site. The theorem specifies the comparison by its
canonical additive section sheaf, scalar action, and map on every module morphism.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The underlying structure-ring presheaf is a sheaf, without a universe-small
sheafification assumption. Source: Stacks Project, Descent, Tag 03DR
(blueprint: lem-trf-scheme-etale-invertible-comparison).

Proof: the structure presheaf is already a sheaf of commutative rings by étale descent.
A matching family of ring maps glues on every element by the set-valued sheaf axiom;
separatedness checks that the glued function preserves addition, multiplication, zero
and one. The resulting ring map is the unique amalgamation. -/
theorem trfEtaleStructureRing_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- The structure ring on the small étale site, evaluated as `Γ(U, 𝒪_U)`.
Source: Stacks Project, Descent, Tag 03DR
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfEtaleStructureRing (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology RingCat.{u} :=
  ⟨X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    trfEtaleStructureRing_isSheaf X⟩

/-- Ordinary invertible modules with all module morphisms.
Source: Stacks Project, Descent, Tag 03DX (2), specialized using Tag 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
abbrev TrfInvertibleModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun L : X.Modules ↦ L.IsInvertible)

/-- A line module is trivial on the localized sites of a jointly surjective étale
family. `CoversTop` expresses precisely this covering condition, with no finiteness
or nonemptiness restriction. Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def TrfIsEtaleLine {X : Scheme.{u}}
    (M : ringedSiteModules.{u} (trfEtaleStructureRing X)) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
    ∀ i, Nonempty (M.over (U i) ≅ SheafOfModules.unit ((trfEtaleStructureRing X).over (U i)))

/-- Étale line modules with all module morphisms, as a full subcategory.
Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
abbrev TrfEtaleLineModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (@TrfIsEtaleLine X)

/-- The canonical additive section sheaf of an ordinary invertible module.
This uses exactly the recorded associated-sheaf declaration, with its existing
quasi-coherence instance. Source: Stacks Project, Descent, Tag 03DU
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfInvertibleSections {X : Scheme.{u}} (L : TrfInvertibleModules X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  @Modules.etaleTensorSectionsSheaf _ L.obj
    (@Modules.IsInvertible.isQuasicoherent _ L.obj L.property)

/-- Restriction of an étale site along `v` evaluates at `w` by `w ≫ v`.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleCompose {Y X : Scheme.{u}} (v : Y ⟶ X) [Etale v] : Y.Etale ⥤ X.Etale where
  obj W := Scheme.Etale.mk (W.hom ≫ v)
  map {U V} g := MorphismProperty.Over.homMk g.left
    (by simp [← Category.assoc, MorphismProperty.Over.w g])

/-- Identity comparison on tensor pullback, normalized by the recorded adjunction unit.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfTensorId (X : Scheme.{u}) : Modules.tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  Adjunction.leftAdjointIdIso (Classical.choose (Modules.exists_tensorPullbackAdjunction (𝟙 X)))
    (Modules.pushforwardId X)

/-- Identity postcomposition changes only the structure arrow of a site object.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleIdArrow {X : Scheme.{u}} (W : X.Etale) :
    W ⟶ (trfEtaleCompose (𝟙 X)).obj W :=
  MorphismProperty.Over.homMk (𝟙 W.left) (by simp [trfEtaleCompose])

/-- Associativity identifies successive and composite postcomposition of site objects.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleCompArrow {X Y Z : Scheme.{u}} (v : Y ⟶ X) (w : Z ⟶ Y) [Etale v] [Etale w]
    (W : Z.Etale) : (trfEtaleCompose (w ≫ v)).obj W ⟶
      (trfEtaleCompose v).obj ((trfEtaleCompose w).obj W) :=
  MorphismProperty.Over.homMk (𝟙 W.left)
    (by change (𝟙 W.left) ≫ ((W.hom ≫ w) ≫ v) = W.hom ≫ (w ≫ v)
        simp only [Category.id_comp, Category.assoc])

/-- The ordinary structure module, as an object of the invertible full subcategory.
Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfStructureInvertible (X : Scheme.{u}) : TrfInvertibleModules X :=
  ⟨SheafOfModules.unit X.ringCatSheaf, Modules.isInvertible_tensorUnit⟩

/-- Tensor pullback of the structure module, normalized by the canonical adjunction.
This is the unique comparison to Mathlib's pullback followed by its structure-unit map.
Source: Stacks Project, Descent, Tag 03LC (1); Sheaves, Tag 0096
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfTensorUnit {Y X : Scheme.{u}} (v : Y ⟶ X) :
    (Modules.tensorPullback v).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  ((Classical.choose (Modules.exists_tensorPullbackAdjunction v)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction v)).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      Modules.pullbackObjUnitIso v

/-- The underlying additive sheaf of a line module.
Source: Stacks Project, Modules on Sites, sheaves of modules; Descent, Tag 03DX
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfLineSections {X : Scheme.{u}} (M : TrfEtaleLineModules X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf _).obj M.obj

/-- The underlying module map of the comparison on any ordinary module morphism.
The full subcategory retains all morphisms, including zero and noninvertible maps.
Source: Stacks Project, Descent, Tag 03DX (2)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfComparisonMap {X : Scheme.{u}}
    (A : TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
    {L K : TrfInvertibleModules X} (h : L.obj ⟶ K.obj) :
    (A.obj L).obj ⟶ (A.obj K).obj :=
  (A.map (ObjectProperty.homMk h)).hom

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
  sorry

end AlgebraicGeometry.Scheme
