/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.GroupTheory.FineMonoidUnitSplitting
import Sheaf.GroupTheory.FineMonoidFiniteSaturation
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections
import Sheaf.AlgebraicGeometry.AffineFanHomUniversal

/-!
# Sharpening and fan desingularization rules

Source: ILO, Exposé VIII, Lemma 3.1.25, Lemma 3.1.26, Theorem 3.1.27 and
Remark 3.1.28, printed p.102 (blueprint: lem-trf-sharpening-fan-bijection).
-/

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace
namespace AlgebraicGeometry
namespace Monoscheme

/-- The corrected domain of monoscheme desingularization rules: both the ordinary
and sharpened stalk group completions are torsion free, and a finite affine cover
is supplied. Source: ILO VIII, 3.1.26 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure ResolutionInput where
  monoscheme : Fine.{u}
  torsionFree : monoscheme.IsTorsionFree
  sharpTorsionFree : (Fine.toFan monoscheme).IsTorsionFree
  finiteCover : ∃ n : ℕ, ∃ c : Fin n → Chart monoscheme.space,
    ∀ x : monoscheme.space, ∃ i : Fin n, x ∈ (c i).openSet

/-- A finite saturated monoscheme blowup tower with smooth final object.
Source: ILO VIII, 3.1.22--3.1.26 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure Resolution (F : ResolutionInput.{u}) where
  length : ℕ
  tower : Tower.{u} length
  base : tower.level 0 = F.monoscheme
  smooth : (tower.level (Fin.last length)).IsSmooth

/-- A canonical comparison with the contracted recursive pullback of a monoscheme
resolution. Source: ILO VIII, 3.1.22--3.1.26 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure ResolutionComparison {F G : ResolutionInput.{u}}
    (R : Resolution F) (S : Resolution G)
    (g : Hom G.monoscheme F.monoscheme) where
  pulled : Tower.{u} R.length
  base : pulled.level 0 = G.monoscheme
  pullback : PullbackTower R.tower pulled
  baseMap : (pullback.lift 0).map =
    eqToHom (congrArg Fine.space base) ≫ g.map ≫
      eqToHom (congrArg Fine.space R.base.symm)
  contraction : Contraction pulled S.tower
  baseIso : (contraction.iso 0).hom =
    eqToHom (congrArg Fine.space (base.trans S.base.symm)) ≫
      eqToHom (congrArg (fun j ↦ (S.tower.level j).space)
        contraction.first.symm)

/-- The comparison map on each level after undoing contraction.
Source: ILO VIII, 3.1.26 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def ResolutionComparison.levelMap
    {F G : ResolutionInput.{u}} {R : Resolution F} {S : Resolution G}
    {g : Hom G.monoscheme F.monoscheme}
    (c : ResolutionComparison R S g) (i : Fin (R.length + 1)) :
    (S.tower.level (c.contraction.index i)).space ⟶ (R.tower.level i).space :=
  (c.contraction.iso i).inv ≫ (c.pullback.lift i).map

/-- Smooth-functorial saturated desingularization rules on the corrected monoscheme
category. Identity and composition fields record the compatibility required for the
rule bijection. Source: ILO VIII, 3.1.26--3.1.27 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure SmoothFunctorialDesingularization where
  resolution : ∀ F : ResolutionInput.{u}, Resolution F
  comparison : ∀ {F G : ResolutionInput.{u}}
    (g : Hom G.monoscheme F.monoscheme),
    g.IsSmooth → ResolutionComparison (resolution F) (resolution G) g
  identityIndex : ∀ (F : ResolutionInput.{u})
    (g : Hom F.monoscheme F.monoscheme) (hg : g.IsSmooth)
    (_h : g.map = 𝟙 F.monoscheme.space)
    (i : Fin ((resolution F).length + 1)),
    (comparison g hg).contraction.index i = i
  identityMap : ∀ (F : ResolutionInput.{u})
    (g : Hom F.monoscheme F.monoscheme) (hg : g.IsSmooth)
    (_h : g.map = 𝟙 F.monoscheme.space)
    (i : Fin ((resolution F).length + 1)),
    HEq ((comparison g hg).levelMap i)
      (𝟙 ((resolution F).tower.level i).space)
  compositionIndex : ∀ {F G H : ResolutionInput.{u}}
    (g : Hom G.monoscheme F.monoscheme)
    (h : Hom H.monoscheme G.monoscheme)
    (k : Hom H.monoscheme F.monoscheme)
    (hg : g.IsSmooth) (hh : h.IsSmooth) (hk : k.IsSmooth)
    (_hc : k.map = h.map ≫ g.map)
    (i : Fin ((resolution F).length + 1)),
    (comparison k hk).contraction.index i =
      (comparison h hh).contraction.index
        ((comparison g hg).contraction.index i)
  compositionMap : ∀ {F G H : ResolutionInput.{u}}
    (g : Hom G.monoscheme F.monoscheme)
    (h : Hom H.monoscheme G.monoscheme)
    (k : Hom H.monoscheme F.monoscheme)
    (hg : g.IsSmooth) (hh : h.IsSmooth) (hk : k.IsSmooth)
    (_hc : k.map = h.map ≫ g.map)
    (i : Fin ((resolution F).length + 1)),
    HEq ((comparison k hk).levelMap i)
      ((comparison h hh).levelMap ((comparison g hg).contraction.index i) ≫
        (comparison g hg).levelMap i)

end Monoscheme

namespace FineFan

/-- Coherence with zero generators allowed, so the empty ideal is included.
Source: ILO VIII 3.1.18, 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection). -/
def IsCoherentIdeal {F : Fan.{u}} (I : IdealFamily F) : Prop :=
  IsIdealSheaf I ∧ ∀ x : F.space,
    ∃ (U : TopologicalSpace.Opens F.space) (_hx : x ∈ U) (n : ℕ)
      (s : Fin n → F.space.presheaf.obj (op U)),
      (∀ i, s i ∈ I U) ∧
      ∀ (y : F.space) (hy : y ∈ U) (t : stalk F.space.presheaf y),
        t ∈ idealStalk I y ↔ ∃ (i : Fin n) (q : stalk F.space.presheaf y),
          t = germ F.space.presheaf U y hy (s i) * q

/-- Identification of ordered towers, retaining every center, arrow and index.
Source: ILO VIII 3.1.25(iii) (blueprint: lem-trf-sharpening-fan-bijection). -/
structure TowerIdentification {n m : ℕ} (T : Tower.{u} n) (S : Tower.{u} m) where
  index : Fin (n + 1) ≃o Fin (m + 1)
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  iso : ∀ i : Fin (n + 1), (T.level i).space ≅ (S.level (index i)).space
  arrows : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (h₁ : index i.succ = k.succ),
    (T.arrow i).map ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₁) ≫
        (S.arrow k).map ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀.symm)
  centers : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (_h₁ : index i.succ = k.succ),
    T.center i = pullbackAlong
      ((iso i.castSucc).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀))
        (S.center k)

end FineFan
namespace Monoscheme

/-- The map λ: first take `Associates.mk`, then the sheafification unit.
Source: ILO VIII 3.1.11, 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def sharpSection (M : Fine.{u}) (U : TopologicalSpace.Opens M.space) :
    M.space.presheaf.obj (op U) →* (Fine.toFan M).space.presheaf.obj (op U) :=
  (((toSheafify (Opens.grothendieckTopology M.space.carrier)
    (FineFan.sharpPresheaf M.space.presheaf)).app (op U)).hom).comp
      Associates.mkMonoidHom

/-- The sheaf image under λ: a section locally lifts to an ideal section.
Source: ILO VIII 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def sharpIdeal {M : Fine.{u}} (I : IdealFamily M) :
    FineFan.IdealFamily (Fine.toFan M) :=
  fun U ↦ {s | ∀ (x : M.space) (_hx : x ∈ U),
    ∃ (V : TopologicalSpace.Opens M.space) (_hxV : x ∈ V) (h : V ≤ U)
      (t : M.space.presheaf.obj (op V)),
      t ∈ I V ∧ sharpSection M V t =
        (Fine.toFan M).space.presheaf.map (homOfLE h).op s}

/-- The inverse operation is the sectionwise inverse image under λ.
Source: ILO VIII 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def unsharpIdeal {M : Fine.{u}}
    (J : FineFan.IdealFamily (Fine.toFan M)) : IdealFamily M :=
  fun U ↦ {s | sharpSection M U s ∈ J U}

/-- The ideal correspondence, including empty ideals, is inverse in both directions;
coherence, nonempty centers and the whole sheaf are preserved.
Source: ILO VIII 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection).
Proof: ideals are invariant under units and their inverses. Thus inverse image of
image, and image of inverse image, recover the original ideals on germs. Sheaf
membership gives equality on sections. Finite generators descend, and finitely many
local representatives of sharp generators generate the inverse ideal. Positive
numbers of generators and the whole ideal are preserved by the same calculation. -/
theorem sharpIdeal_properties (M : Fine.{u}) :
    (∀ I : IdealFamily M, IsCoherentIdeal I →
      FineFan.IsCoherentIdeal (sharpIdeal I) ∧ unsharpIdeal (sharpIdeal I) = I ∧
      (FineFan.IsNonemptyCoherentIdeal (sharpIdeal I) ↔ IsNonemptyCoherentIdeal I) ∧
      (sharpIdeal I = FineFan.wholeIdeal (Fine.toFan M) ↔ I = wholeIdeal M)) ∧
    (∀ J : FineFan.IdealFamily (Fine.toFan M), FineFan.IsCoherentIdeal J →
      IsCoherentIdeal (unsharpIdeal J) ∧ sharpIdeal (unsharpIdeal J) = J) := by
  sorry

/-- The actual coherent-ideal equivalence has prescribed forward and inverse functions.
Source: ILO VIII 3.1.25(i) (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def sharpIdealEquiv (M : Fine.{u}) :
    {I : IdealFamily M // IsCoherentIdeal I} ≃
      {J : FineFan.IdealFamily (Fine.toFan M) // FineFan.IsCoherentIdeal J} where
  toFun I := ⟨sharpIdeal I.1, ((sharpIdeal_properties M).1 I.1 I.2).1⟩
  invFun J := ⟨unsharpIdeal J.1, ((sharpIdeal_properties M).2 J.1 J.2).1⟩
  left_inv I := Subtype.ext (((sharpIdeal_properties M).1 I.1 I.2).2.1)
  right_inv J := Subtype.ext (((sharpIdeal_properties M).2 J.1 J.2).2)

/-- The defining square for a sharpened sheafed-space map, including its continuous map.
`HEq` transports only along equality of the two continuous maps.
Source: ILO VIII 3.1.11, 3.1.25 (blueprint: lem-trf-sharpening-fan-bijection). -/
def IsSharpMap {N M : Fine.{u}} (f : N.space ⟶ M.space)
    (g : (Fine.toFan N).space ⟶ (Fine.toFan M).space) : Prop :=
  g.hom.base = f.hom.base ∧
    ∀ (U : TopologicalSpace.Opens M.space) (s : M.space.presheaf.obj (op U)),
      HEq (g.hom.c.app (op U) (sharpSection M U s))
        (sharpSection N ((TopologicalSpace.Opens.map f.hom.base).obj U)
          (f.hom.c.app (op U) s))

/-- The universal property determines the sharpened map uniquely, even for maps
between levels which are not smooth.
Source: ILO VIII 3.1.11, 3.1.25 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: descend each section map modulo units and then extend through sheafification.
These maps commute with restriction and have the given continuous map. Local
representability under the sheafification unit proves uniqueness. -/
theorem existsUnique_sharpMap {N M : Fine.{u}} (f : N.space ⟶ M.space) :
    ∃! g : (Fine.toFan N).space ⟶ (Fine.toFan M).space, IsSharpMap f g := by
  sorry

/-- The uniquely determined map induced by quotienting by units and sheafifying.
Source: ILO VIII 3.1.11, 3.1.25 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def sharpSpaceMap {N M : Fine.{u}} (f : N.space ⟶ M.space) :
    (Fine.toFan N).space ⟶ (Fine.toFan M).space :=
  (existsUnique_sharpMap f).choose

/-- Canonical-map laws, locality and the valid forward smoothness assertion.
Source: ILO VIII 3.1.11, 3.1.15, 3.1.25 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: the chosen map satisfies its defining square. Identity and composite maps
satisfy the same square, so uniqueness proves the laws. Local stalk maps descend
to local maps of sharp stalks. A smooth stalk product loses its free group factor. -/
theorem sharpSpaceMap_properties :
    (∀ (N M : Fine.{u}) (f : N.space ⟶ M.space), IsSharpMap f (sharpSpaceMap f)) ∧
    (∀ M : Fine.{u}, sharpSpaceMap (𝟙 M.space) = 𝟙 (Fine.toFan M).space) ∧
    (∀ (L N M : Fine.{u}) (f : L.space ⟶ N.space) (g : N.space ⟶ M.space),
      sharpSpaceMap (f ≫ g) = sharpSpaceMap f ≫ sharpSpaceMap g) ∧
    (∀ (N M : Fine.{u}) (f : Hom N M), FineFan.IsLocalMorphism (sharpSpaceMap f.map)) ∧
    (∀ (N M : Fine.{u}) (f : Hom N M), f.IsSmooth →
      ∀ g : FineFan.Hom (Fine.toFan N) (Fine.toFan M),
        g.map = sharpSpaceMap f.map → g.IsSmooth) := by
  sorry

/-- Sharpening of a local monoscheme morphism, with its canonical section maps.
Source: ILO VIII 3.1.11, 3.1.25 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def Hom.toFan {N M : Fine.{u}} (f : Hom N M) :
    FineFan.Hom (Fine.toFan N) (Fine.toFan M) where
  map := sharpSpaceMap f.map
  isLocal := sharpSpaceMap_properties.2.2.2.1 N M f

/-- Sharpening saturated blowups preserves the specified center. In particular a
whole-ideal stage is deleted exactly when the original stage is an isomorphism.
Source: ILO VIII 3.1.25(ii) (blueprint: lem-trf-sharpening-fan-bijection).
Proof: quotienting fraction charts by units gives the fraction charts for the
image ideal. Saturation commutes with localization and sharpening (ILO 3.1.17).
The overlap maps localize at the same fractions, so the chart comparisons glue.
This proves the stated saturated blowup property without choosing a new object. -/
theorem sharp_blowup {B M : Fine.{u}} (b : Hom B M) (I : IdealFamily M)
    (hb : IsSaturatedBlowup b I) :
    FineFan.IsSaturatedBlowup b.toFan (sharpIdeal I) := by
  sorry

/-- The sharpened ordered tower has the same length and the image of each center.
Its data use the given tower and the canonical quotient map, without choosing levels.
Source: ILO VIII 3.1.25(iii) (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def Tower.toFan {n : ℕ} (T : Tower.{u} n) : FineFan.Tower.{u} n where
  level i := Fine.toFan (T.level i)
  center i := sharpIdeal (T.center i)
  arrow i := (T.arrow i).toFan
  blowup i := sharp_blowup (T.arrow i) (T.center i) (T.blowup i)

/-- The sharp fan of a rule input has a finite affine cover.
Source: ILO VIII 3.1.11, 3.1.26 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: sharpen each member of the finite affine monoscheme cover. The underlying
opens are unchanged and hence still cover, including for the empty cover. -/
theorem sharp_finiteCover (M : Fine.{u}) : (Fine.toFan M).HasFiniteAffineCover := by
  sorry

/-- The sharp input uses exactly the prescribed torsion-free sharp stalks.
Source: ILO VIII 3.1.26--3.1.27 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def ResolutionInput.toFan (M : ResolutionInput.{u}) :
    FineFan.ResolutionInput.{u} where
  fan := Fine.toFan M.monoscheme
  torsionFree := M.sharpTorsionFree
  finiteCover := sharp_finiteCover M.monoscheme

/-- Identification of a sharpened resolution, pinned over the original sharp base.
Source: ILO VIII 3.1.25--3.1.27 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure SharpResolutionIdentification {M : ResolutionInput.{u}}
    (R : Resolution M) (S : FineFan.Resolution M.toFan) extends
      FineFan.TowerIdentification R.tower.toFan S.tower where
  baseIso : (iso 0).hom =
    eqToHom (congrArg (fun N : Fine.{u} ↦ (Fine.toFan N).space) R.base) ≫
      eqToHom (congrArg FineFan.Fan.space S.base.symm) ≫
        eqToHom (congrArg (fun j ↦ (S.tower.level j).space) first.symm)

/-- A rule correspondence is required to sharpen the actual towers AND their
contracted pullback comparisons. The index and map equations give naturality.
Source: ILO VIII 3.1.26--3.1.27 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure RuleSharpens (R : SmoothFunctorialDesingularization.{u})
    (Q : FineFan.SmoothFunctorialDesingularization.{u}) where
  identification : ∀ M : ResolutionInput.{u},
    SharpResolutionIdentification (R.resolution M) (Q.resolution M.toFan)
  comparisonIndex : ∀ {M N : ResolutionInput.{u}} (g : Hom N.monoscheme M.monoscheme)
    (hg : g.IsSmooth) (hsg : g.toFan.IsSmooth)
    (i : Fin ((R.resolution M).length + 1)),
    (identification N).index ((R.comparison g hg).contraction.index i) =
      (Q.comparison (F := M.toFan) (G := N.toFan) g.toFan hsg).contraction.index
        ((identification M).index i)
  comparisonMap : ∀ {M N : ResolutionInput.{u}} (g : Hom N.monoscheme M.monoscheme)
    (hg : g.IsSmooth) (hsg : g.toFan.IsSmooth)
    (i : Fin ((R.resolution M).length + 1)),
    sharpSpaceMap ((R.comparison g hg).levelMap i) ≫ ((identification M).iso i).hom =
      ((identification N).iso ((R.comparison g hg).contraction.index i)).hom ≫
        eqToHom (congrArg (fun j ↦ ((Q.resolution N.toFan).tower.level j).space)
          (comparisonIndex g hg hsg i)) ≫
            (Q.comparison (F := M.toFan) (G := N.toFan) g.toFan hsg).levelMap
              ((identification M).index i)

end Monoscheme
namespace Monoscheme

/-- Identification of monoscheme towers, with every ordered center and arrow retained.
Source: ILO VIII 3.1.25(iii) (blueprint: lem-trf-sharpening-fan-bijection). -/
structure TowerIdentification {n m : ℕ} (T : Tower.{u} n) (S : Tower.{u} m) where
  index : Fin (n + 1) ≃o Fin (m + 1)
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  iso : ∀ i : Fin (n + 1), (T.level i).space ≅ (S.level (index i)).space
  arrows : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (h₁ : index i.succ = k.succ),
    (T.arrow i).map ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₁) ≫
        (S.arrow k).map ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀.symm)
  centers : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (_h₁ : index i.succ = k.succ),
    T.center i = pullbackAlong
      ((iso i.castSucc).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀))
        (S.center k)

/-- A lift of an ordered fan tower is identified over the specified base, not merely
by an abstract isomorphism of its levels.
Source: ILO VIII 3.1.25(iii) (blueprint: lem-trf-sharpening-fan-bijection). -/
def IsSharpTowerLift {n : ℕ} (M : ResolutionInput.{u}) (S : FineFan.Tower.{u} n)
    (hS : S.level 0 = M.toFan.fan) (T : Tower.{u} n) (hT : T.level 0 = M.monoscheme) :
    Prop :=
  ∃ c : FineFan.TowerIdentification T.toFan S,
    (c.iso 0).hom =
      eqToHom (congrArg (fun N : Fine.{u} ↦ (Fine.toFan N).space) hT) ≫
        eqToHom (congrArg FineFan.Fan.space hS.symm) ≫
          eqToHom (congrArg (fun j ↦ (S.level j).space) c.first.symm)

/-- An affine chart, considered as a monoscheme, has a one-member affine cover.
Source: ILO VIII 3.1.3--3.1.4 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: use the whole open and the chart isomorphism to the displayed affine spectrum.
The restriction to the whole open is canonically the same sheafed space. -/
theorem Chart.source_finiteCover {M : Fine.{u}} (c : Chart M.space) :
    ∃ n : ℕ, ∃ d : Fin n → Chart (M.space.restrict c.openSet.isOpenEmbedding),
      ∀ x : M.space.restrict c.openSet.isOpenEmbedding,
        ∃ i : Fin n, x ∈ (d i).openSet := by
  sorry

/-- The actual open affine monoscheme given by a chart.
Source: ILO VIII 3.1.4 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def Chart.asFine {M : Fine.{u}} (c : Chart M.space) : Fine.{u} where
  space := M.space.restrict c.openSet.isOpenEmbedding
  finiteCover := c.source_finiteCover

/-- The displayed affine monoid spectrum has its one-member affine atlas.
Source: ILO VIII 3.1.3 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: the whole open is the affine chart, using the restriction-to-top isomorphism. -/
theorem affine_finiteCover (P : CommMonCat.{u}) (hP : FineFan.IsFine P) :
    ∃ n : ℕ, ∃ c : Fin n → Chart (affine P),
      ∀ x : affine P, ∃ i : Fin n, x ∈ (c i).openSet := by
  sorry

/-- The unsharpened spectrum of the given fine monoid, with its actual sheaf of fractions.
Source: ILO VIII 3.1.3 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def affineFine (P : CommMonCat.{u}) (hP : FineFan.IsFine P) : Fine.{u} where
  space := affine P
  finiteCover := affine_finiteCover P hP

/-- Affine open inclusions are local maps of monoschemes.
Source: ILO VIII 3.1.4--3.1.6 (blueprint: lem-trf-sharpening-fan-bijection).
Proof: restriction to an open does not change the stalks at its points; the induced
stalk maps are isomorphisms and hence local. -/
theorem Chart.inclusion_local {M : Fine.{u}} (c : Chart M.space) :
    FineFan.IsLocalMorphism (SheafedSpace.ofRestrict M.space c.openSet.isOpenEmbedding) := by
  sorry

/-- The canonical inclusion of the open chart as a local monoscheme morphism.
Source: ILO VIII 3.1.4 (blueprint: lem-trf-sharpening-fan-bijection). -/
noncomputable def Chart.inclusion {M : Fine.{u}} (c : Chart M.space) : Hom c.asFine M where
  map := SheafedSpace.ofRestrict M.space c.openSet.isOpenEmbedding
  isLocal := c.inclusion_local

/-- A finite affine fan cover and its finite disjoint union of sharp affine
monoscheme lifts. The chart equation pins the covering map to sharpening of the
unsharpened chart isomorphisms. Thus this is a cover lift, not a global lift of F.
Source: ILO VIII 3.1.26--3.1.27, 2.3.5(ii)
(blueprint: lem-trf-sharpening-fan-bijection). -/
structure AffineLiftCover (F : FineFan.ResolutionInput.{u}) where
  size : ℕ
  fanChart : Fin size → FineFan.Chart F.fan.space
  coversFan : ∀ x : F.fan.space, ∃ i : Fin size, x ∈ (fanChart i).openSet
  sharp : ∀ i : Fin size, FineFan.IsSharp (fanChart i).monoid
  total : ResolutionInput.{u}
  monoChart : Fin size → Chart total.monoscheme.space
  sameMonoid : ∀ i : Fin size, (monoChart i).monoid = (fanChart i).monoid
  disjoint : ∀ i j : Fin size, i ≠ j →
    Disjoint (monoChart i).openSet (monoChart j).openSet
  coversTotal : ∀ x : total.monoscheme.space, ∃ i : Fin size, x ∈ (monoChart i).openSet
  map : FineFan.Hom total.toFan.fan F.fan
  smooth : map.IsSmooth
  surjective : Function.Surjective map.map.hom.base
  onChart : ∀ i : Fin size,
    ((monoChart i).inclusion.toFan).map ≫ map.map =
      sharpSpaceMap (N := (monoChart i).asFine)
        (M := affineFine (monoChart i).monoid (monoChart i).fine)
        (monoChart i).iso.hom ≫
      eqToHom (congrArg (fun P : CommMonCat.{u} ↦ FineFan.affine P) (sameMonoid i)) ≫
        (fanChart i).iso.inv ≫
          SheafedSpace.ofRestrict F.fan.space (fanChart i).openSet.isOpenEmbedding

/-- Local reconstruction from the single finite tower on the disjoint union of
sharp affine lifts. The identification is uncontracted, so all local centers retain
their inherited indices. The base map is the actual affine covering map.
Source: ILO VIII 3.1.26--3.1.27, 2.3.5(ii)
(blueprint: lem-trf-sharpening-fan-bijection). -/
def IsLocalRuleDescent (R : SmoothFunctorialDesingularization.{u})
    (Q : FineFan.SmoothFunctorialDesingularization.{u})
    (F : FineFan.ResolutionInput.{u}) (C : AffineLiftCover F) : Prop :=
  ∃ P : FineFan.Tower.{u} (Q.resolution F).length,
    ∃ pb : FineFan.PullbackTower (Q.resolution F).tower P,
      ∃ c : FineFan.TowerIdentification P (R.resolution C.total).tower.toFan,
        (pb.lift 0).map = (c.iso 0).hom ≫
          eqToHom (congrArg
            (fun j ↦ ((R.resolution C.total).tower.toFan.level j).space) c.first) ≫
          eqToHom (congrArg (fun N : Fine.{u} ↦ (Fine.toFan N).space)
            (R.resolution C.total).base) ≫ C.map.map ≫
          eqToHom (congrArg FineFan.Fan.space (Q.resolution F).base.symm)

/-- All geometric preservation clauses in the sharpening correspondence. The
lifting clause is bijectivity on towers over a fixed base up to their canonical
base-preserving identifications, the meaning of equality of blowup towers.
Source: ILO VIII 3.1.25--3.1.28 (blueprint: lem-trf-sharpening-fan-bijection). -/
structure SharpeningGeometry : Prop where
  ideals : ∀ M : ResolutionInput.{u},
    (∀ I : IdealFamily M.monoscheme, IsCoherentIdeal I →
      FineFan.IsCoherentIdeal (sharpIdeal I) ∧ unsharpIdeal (sharpIdeal I) = I ∧
      (FineFan.IsNonemptyCoherentIdeal (sharpIdeal I) ↔ IsNonemptyCoherentIdeal I) ∧
      (sharpIdeal I = FineFan.wholeIdeal M.toFan.fan ↔ I = wholeIdeal M.monoscheme)) ∧
    (∀ J : FineFan.IdealFamily M.toFan.fan, FineFan.IsCoherentIdeal J →
      IsCoherentIdeal (unsharpIdeal J) ∧ sharpIdeal (unsharpIdeal J) = J)
  idealPullback : ∀ {M N : Fine.{u}} (f : Hom N M) (I : IdealFamily M),
    IsCoherentIdeal I →
      sharpIdeal (pullbackIdeal f I) = FineFan.pullbackIdeal f.toFan (sharpIdeal I)
  towersExist : ∀ (M : ResolutionInput.{u}) (n : ℕ) (S : FineFan.Tower.{u} n)
    (hS : S.level 0 = M.toFan.fan),
    ∃ T : Tower.{u} n, ∃ hT : T.level 0 = M.monoscheme, IsSharpTowerLift M S hS T hT
  towersUnique : ∀ (M : ResolutionInput.{u}) (n : ℕ) (S : FineFan.Tower.{u} n)
    (hS : S.level 0 = M.toFan.fan) (T T' : Tower.{u} n)
    (hT : T.level 0 = M.monoscheme) (hT' : T'.level 0 = M.monoscheme),
    IsSharpTowerLift M S hS T hT → IsSharpTowerLift M S hS T' hT' →
      ∃ c : TowerIdentification T T',
        (c.iso 0).hom = eqToHom (congrArg Fine.space (hT.trans hT'.symm)) ≫
          eqToHom (congrArg (fun j ↦ (T'.level j).space) c.first.symm)
  closedDomain : ∀ (M : ResolutionInput.{u}) (n : ℕ) (T : Tower.{u} n),
    T.level 0 = M.monoscheme →
      ∀ i : Fin (n + 1), (T.level i).IsTorsionFree ∧ (Fine.toFan (T.level i)).IsTorsionFree
  smoothLast : ∀ (M : ResolutionInput.{u}) (n : ℕ) (T : Tower.{u} n),
    T.level 0 = M.monoscheme →
      ((T.level (Fin.last n)).IsSmooth ↔ (T.toFan.level (Fin.last n)).IsSmooth)
  unitStages : ∀ (M : ResolutionInput.{u}) (n : ℕ) (T : Tower.{u} n),
    T.level 0 = M.monoscheme → ∀ i : Fin n,
      (T.center i = wholeIdeal (T.level i.castSucc) ∧ IsIso (T.arrow i).map ↔
        T.toFan.center i = FineFan.wholeIdeal (T.toFan.level i.castSucc) ∧
          IsIso (T.toFan.arrow i).map)
  recursivePullback : ∀ (n : ℕ) (T S : Tower.{u} n) (p : PullbackTower T S),
    ∃ q : FineFan.PullbackTower T.toFan S.toFan,
      ∀ i : Fin (n + 1), q.lift i = (p.lift i).toFan
  contraction : ∀ (M N : ResolutionInput.{u}) (n m : ℕ)
    (T : Tower.{u} n) (S : Tower.{u} m),
    T.level 0 = M.monoscheme → S.level 0 = N.monoscheme →
      ∀ c : Contraction T S,
        ∃ d : FineFan.Contraction T.toFan S.toFan, d.index = c.index ∧
          ∀ i : Fin (n + 1), HEq (d.iso i).hom (sharpSpaceMap (c.iso i).hom)

end Monoscheme

/-- Sharpening bijects coherent ideals and ordered saturated towers, and gives the
natural correspondence of desingularization rules, with both functions pinned to
sharpening their towers and comparisons. Its local clause quantifies over ALL affine
lift covers, so it includes fans without a global monoscheme lift and independence
of the finite cover, with every uncontracted center and index retained.
Source: ILO VIII 3.1.25--3.1.28, printed p.102; 2.3.5(ii), p.92
(blueprint: lem-trf-sharpening-fan-bijection).

Proof: (1) Ideals are invariant under units, so λ image and inverse image are inverse
on germs and on coherent ideal sheaves. Finite local generators give coherence,
nonempty centers and unit-ideal preservation. (2) Split units using
lem-trf-fine-monoid-unit-splitting. The fraction charts are B[J-a] times the unit
group, and their saturations are (B[J-a])^sat times that group. The same localized
fractions identify overlaps; lem-trf-fine-monoid-finite-saturation and
lem-trf-fs-face-sharpening keep all levels in the corrected domain. (3) Induct over
the tower: lift each ideal by inverse image, then use the chart identification at
the next level. Uniqueness over the base follows stagewise from these charts.
Generated image ideals commute with λ, proving recursive pullback compatibility.
(4) Smooth stalks have free sharp monoid and free unit group. Unit splitting gives
reflection of object smoothness. For a whole-ideal blowup, the product calculation
reflects whether saturation is an isomorphism, so exactly the same indices contract,
including retaining nonidentity initial saturation. (5) A smooth surjection loses
no stage: localness reflects whole ideals and a smooth product reflects saturation.
Identity functoriality makes every assigned tower already contracted. (6) Apply the
rule to Y disjoint union X with the two maps f disjoint union id and g disjoint union
id. Smooth surjectivity synchronizes their full pullbacks, before contraction.
(7) A fan rule lifts stagewise to a monoscheme rule by (1)--(4), including its
comparisons and identity/composition equations. (8) Conversely take any finite
affine fan cover, lift its sharp monoids, and apply the monoscheme rule ONCE to their
finite disjoint union. Restrict without contraction. (9) On the smallest affine
neighborhood of an overlap, lem-trf-affine-fan-localization-sections identifies the
sharp localized monoid B. Unit splitting supplies a common smooth product lift of
the two unsharp models. By (6) their full pulled-back towers agree with centers and
indices, and these identifications satisfy the cocycle condition. (10) Glue the
coherent ideals, blowup charts and each next-stage ideal for the common finite number
of stages; the last fan is smooth. (11) Compare two covers via their combined cover.
A removable stage is removable on either subcover exactly when removable globally,
so the glued tower is cover independent. (12) For a smooth fan map, use
lem-trf-affine-fan-hom-universal on the smallest neighborhoods and lift the smooth
sharp stalk maps. Synchronize source and target covers by (6); (1)--(4) identify the
contracted recursive pullbacks. (13) Generated ideals and fraction substitutions
respect identities and composites; iterated contraction removes the same indices
as one contraction. These give RuleSharpens, including the comparison-map equations.
(14) Lift then sharpen recovers each fan tower locally; sharpen then lift recovers
each monoscheme tower by unit splitting and smooth-surjective synchronization.
The same comparisons recover identity/composition laws, giving the inverse functions
of the displayed equivalence and the asserted local clause for every affine lift cover. -/
theorem sharpening_fan_bijection :
    Monoscheme.SharpeningGeometry.{u} ∧
    (∀ F : FineFan.ResolutionInput.{u}, Nonempty (Monoscheme.AffineLiftCover F)) ∧
    ∃ e : Monoscheme.SmoothFunctorialDesingularization.{u} ≃
        FineFan.SmoothFunctorialDesingularization.{u},
      (∀ R : Monoscheme.SmoothFunctorialDesingularization.{u},
        Nonempty (Monoscheme.RuleSharpens R (e R))) ∧
      (∀ Q : FineFan.SmoothFunctorialDesingularization.{u},
        Nonempty (Monoscheme.RuleSharpens (e.symm Q) Q)) ∧
      (∀ (R : Monoscheme.SmoothFunctorialDesingularization.{u})
        (F : FineFan.ResolutionInput.{u}) (C : Monoscheme.AffineLiftCover F),
        Monoscheme.IsLocalRuleDescent R (e R) F C) ∧
      (∀ (Q : FineFan.SmoothFunctorialDesingularization.{u})
        (F : FineFan.ResolutionInput.{u}) (C : Monoscheme.AffineLiftCover F),
        Monoscheme.IsLocalRuleDescent (e.symm Q) Q F C) := by
  sorry

end AlgebraicGeometry
