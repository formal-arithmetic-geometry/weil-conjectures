/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.SiteMorphismComposition
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
/-! # Open restriction and the direct-image counit.
Source: Stacks Project, pro-etale functoriality (09A5), Sites (00XZ, 03CB, 03CF),
and Modules on Sites (03D3, 04J0)
(blueprint: lem-sfb-proetale-open-restriction-counit).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProEtaleOpenRestriction

/-- The inverse-image coefficient ring on X. Source: Stacks `proetale.tex`, Tag 09A5
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on W. Source: Stacks `proetale.tex`, Tag 09A5
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RW {Y W : Scheme.{u}} (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on the fibre product X_W. Source: Stacks
Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RXW {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1}).obj (RX f R)

/-- The type of coefficient comparisons; `coefficientIso` fixes the canonical one.
Source: Stacks
Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev CoeffCmp {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  RW (pullback.snd f h) (RW h R) ≅ RXW f h R

/-- The category of modules over the inverse-image ring on X. Source: Stacks Modules
on Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev ModX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  proEtaleRingModules X (RX f R)

/-- Direct image along f followed by restriction along h. Source: Stacks Modules on
Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev Left {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules X (RX f R) ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _) ⋙
    proEtaleRingModulePullback h R (RW h R) (Iso.refl _)

/-- Pullback along the fibre-product projection followed by direct image. Source:
Stacks Modules on Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev Right {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : CoeffCmp f h R) :
    proEtaleRingModules X (RX f R) ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _) ⋙
    proEtaleRingModuleDirectImage (pullback.snd f h) (RW h R) (RXW f h R) c

/-- The composite pullback from Y via X to X_W. Source: Stacks Modules on Sites, Tag 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AlphaL {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules Y R ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback f R (RX f R) (Iso.refl _) ⋙
    proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _)

/-- The composite pullback from Y via W to X_W. Source: Stacks Modules on Sites,
Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AlphaR {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : CoeffCmp f h R) :
    proEtaleRingModules Y R ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback h R (RW h R) (Iso.refl _) ⋙
    proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Pullback along the first fibre-product projection. Source: Stacks Sites, Tag 03CB
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PFst {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules X (RX f R) ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _)

/-- Pullback along the second fibre-product projection. Source: Stacks Sites, Tag 03CB
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PSnd {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : CoeffCmp f h R) :
    proEtaleRingModules W (RW h R) ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Pullback along the open immersion h. Source: Stacks Sites, Tag 03CB (blueprint:
lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PH {X Y W : Scheme.{u}} (_f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules Y R ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModulePullback h R (RW h R) (Iso.refl _)

/-- The module adjunction for f. Source: Stacks Modules on Sites, Tag 03D3
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AdjF {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R (RX f R) (Iso.refl _) ⊣
      proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _) :=
  proEtaleRingModuleAdjunction f R (RX f R) (Iso.refl _)

/-- The module adjunction for the second fibre-product projection. Source: Stacks
Modules on Sites, Tag 03D3 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AdjSnd {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : CoeffCmp f h R) :
    proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c ⊣
      proEtaleRingModuleDirectImage (pullback.snd f h) (RW h R) (RXW f h R) c :=
  proEtaleRingModuleAdjunction (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Base-change associativity around the cartesian square, with its canonical projections.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def squareSiteIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleBaseChange f ⋙ proEtaleBaseChange (pullback.fst f h) ≅
      proEtaleBaseChange h ⋙ proEtaleBaseChange (pullback.snd f h) :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (pullback.fst f h) f).symm ≪≫
  eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) (pullback.condition (f := f) (g := h))) ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (pullback.snd f h) h

/-- The inverse-image comparison is the mate of the projection-preserving site isomorphism.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def ringSquareIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage h CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.snd f h) CommRingCat.{u + 1} :=
  letI := Functor.isContinuous_comp (proEtaleBaseChange h)
    (proEtaleBaseChange (pullback.snd f h)) (ProEt.topology Y) (ProEt.topology W)
      (ProEt.topology (pullback f h))
  ((conjugateIsoEquiv
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1}))
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1}))).symm
    ((Functor.sheafPushforwardContinuousComp' (eFG := squareSiteIso f h)
      CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)
        (ProEt.topology (pullback f h))) ≪≫
      (Functor.sheafPushforwardContinuousComp (proEtaleBaseChange h)
        (proEtaleBaseChange (pullback.snd f h)) CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology W)
            (ProEt.topology (pullback f h))).symm)).symm

/-- The coefficient comparison is fixed, not an existentially supplied automorphism.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def coefficientIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) : CoeffCmp f h R :=
  (ringSquareIso f h).symm.app R

/-- Composition sends an object over the source of a weakly etale map to the target site.
Source: Stacks Sites, Tag 00XZ (blueprint: lem-sfb-proetale-open-restriction-counit). -/
abbrev objectComposition {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map (f := h) ⊤ (inferInstance : WeaklyEtale h)

/-- The canonical section coprojection, defined using the module unit and the distinguished
index point `(E → Y, (id, str))`. It is the inverse of the open-slice identification.
Source: Stacks Sites, Tags 00VC, 00XZ; Modules on Sites, Tag 03D3
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def objectCoprojection {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : proEtaleRingModules Y R) (E : X.ProEt)
    (s : M.val.obj (op ((objectComposition h).obj E))) :
    ((proEtaleRingModulePullback h R (RW h R) (Iso.refl _)).obj M).val.obj (op E) :=
  ((proEtaleRingModulePullback h R (RW h R) (Iso.refl _)).obj M).val.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial).unit.app E).op
      (((proEtaleRingModuleAdjunction h R (RW h R) (Iso.refl _)).unit.app M).val.app
        (op ((objectComposition h).obj E)) s)

/-- The canonical fibre-product arrow `(E ×[W] X_W → X) → (E ×[Y] X → X)`.
The map is the identity on E and the first projection on X_W; thus it is the specified
fibre-product identification, rather than a freely supplied section equivalence.
Source: Stacks Sites, Tag 03CF (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def sectionArrow {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (E : W.ProEt) :
    (objectComposition (pullback.fst f h)).obj
        ((proEtaleBaseChange (pullback.snd f h)).obj E) ⟶
      (proEtaleBaseChange f).obj ((objectComposition h).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom (pullback.snd f h) (E.hom ≫ h) f
      (𝟙 E.left) (pullback.fst f h) h (Category.id_comp _).symm (pullback.condition ..).symm)
    (pullback.lift_snd _ _ _)

/-- The sectionwise assertion with both canonical open-slice identifications explicit.
Bijectivity asserts these are identifications; the final equation fixes beta as pullback
along the displayed fibre-product arrow on every section, for every module and object.
Source: Stacks Sites, Tag 03CF; Modules on Sites, Tag 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
def Sectionwise {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (β : Left f h R ≅ Right f h R (coefficientIso f h R)) : Prop :=
  (∀ (M : proEtaleRingModules Y R) (E : W.ProEt),
    Function.Bijective (objectCoprojection h R M E)) ∧
  (∀ (M : ModX f R) (E : (pullback f h).ProEt),
    Function.Bijective (objectCoprojection (pullback.fst f h) (RX f R) M E)) ∧
  ∀ (M : ModX f R) (E : W.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj ((objectComposition h).obj E)))),
    (β.hom.app M).val.app (op E)
        (objectCoprojection h R
          ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) E s) =
      objectCoprojection (pullback.fst f h) (RX f R) M
        ((proEtaleBaseChange (pullback.snd f h)).obj E)
          (M.val.map (sectionArrow f h E).op s)

/-- Unit normalization uniquely fixes the inverse-image comparison alpha. The two iterated
units at V agree after alpha and the canonical site square. This excludes twists by an
arbitrary natural automorphism and is exactly adjunction-compatible composition.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
def AlphaNormalization {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) : Prop :=
  ∀ (F : proEtaleRingModules Y R) (V : Y.ProEt) (m : F.val.obj (op V)),
    (α.hom.app F).val.app
        (op ((proEtaleBaseChange (pullback.fst f h)).obj ((proEtaleBaseChange f).obj V)))
      (((AdjF (pullback.fst f h) (RX f R)).unit.app
        ((proEtaleRingModulePullback f R (RX f R) (Iso.refl _)).obj F)).val.app
          (op ((proEtaleBaseChange f).obj V)) (((AdjF f R).unit.app F).val.app (op V) m)) =
    ((AlphaR f h R (coefficientIso f h R)).obj F).val.map
      ((squareSiteIso f h).hom.app V).op
        (((AdjSnd f h R (coefficientIso f h R)).unit.app ((PH f h R).obj F)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (((AdjF h R).unit.app F).val.app (op V) m))

/-- The counit equality as an equality of actual module-sheaf morphisms on X_W.
Source: Stacks Modules on Sites, Tags 03D3 and 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
def CounitEquation {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (β : Left f h R ≅ Right f h R (coefficientIso f h R))
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) : Prop :=
  ∀ M : ModX f R,
    (PFst f h R).map ((AdjF f R).counit.app M) =
      (α.hom.app ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M)) ≫
        (PSnd f h R (coefficientIso f h R)).map (β.hom.app M) ≫
        (AdjSnd f h R (coefficientIso f h R)).counit.app ((PFst f h R).obj M)

/--
The canonical open restriction comparison, its sectionwise fibre-product formula, and
its counit mate equation (blueprint: lem-sfb-proetale-open-restriction-counit).

Step 1 (site and coefficient setup): the base-change functors for h and g are
continuous, and the base change of the open immersion h is an open immersion.  The
ringed-site module adjunctions provide the displayed counits.  The unit-compatible
composition comparison from `lem-weil-pbc-site-morphism-composition` identifies
the two composite inverse-image functors and gives `α`; the identity coefficient
maps make the module counits the underlying sheaf counits.

Step 2 (sectionwise comparison): `lem-weil-pbc-proetale-ringed-open-comparison`
identifies actual inverse images with open-slice restriction.  At `E → W`, the
left direct image evaluates on `X ×_Y E`, while the base-changed direct image
evaluates on `X_W ×_W E`.  The fibre-product universal property gives the
component of `β`; these components are natural, bijective and module-linear,
and the distinguished unit coprojections are bijections. The equation in
`Sectionwise` identifies beta with restriction along `sectionArrow`.

Step 3 (counit normalization): set N = f_*M and w = u_g u_f. The composition
comparison identifies the source with (w_p N)^#. By the sheafification universal
property and the colimit defining w_p, it suffices to evaluate on generators
[s]_(V,psi), where U' is over X_W, psi : U' → u_g(u_f(V)), and s is in
N(V) = M(u_f(V)). The continuous-functor adjunction counit sends a coprojection
indexed by (V,phi) to phi^*s, and its unit uses (V,id). Hence the composition
comparison sends [s]_(V,psi) to the iterated coprojection
[[s]_(V,id)]_(u_f(V),psi); compatibility with the units uniquely determines it.
The left counit composite sends this generator to the restriction of s along
bar(psi) : U' → u_f(V). On the right, alpha replaces psi with c_V psi, where
c_V is `squareSiteIso` and E = u_h(V). The h restriction identifies the inner
coprojection with s restricted along the map u_f(E → Y) → u_f(V). Beta then
transports along X_W ×_W E ≅ X ×_Y E, and the f_W counit restricts along
c_V psi. Both fibre-product comparisons commute with the projection to u_f(V),
so this composite arrow U' → u_f(V) is bar(psi) by pullback uniqueness. The maps
agree on every generator, hence after sheafification. Forgetting module actions
is faithful, so the equality holds as module morphisms, giving `CounitEquation`.

The proof uses `def-pc-fibre-product`,
`def-weil-pbc-sheafification`, `def-weil-proetale-inverse-image`,
`def-weil-proetale-module-direct-image`,
`lem-sfb-proetale-object-inverse-image-restriction`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`lem-weil-pbc-open-immersion-base-change`,
`lem-weil-pbc-proetale-ringed-open-comparison`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, and
`lem-weil-pbc-site-morphism-composition`.
Source: Stacks Project `proetale.tex`, Tags 09A5, 00XZ and 03CB, and Modules on
Sites Tags 03D3 and 04J0 (and Sites Tag 03CF).
-/
theorem proEtaleOpenRestrictionCounit {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ β : Left f h R ≅ Right f h R (coefficientIso f h R),
      Sectionwise f h R β ∧
      ∃ α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R),
        AlphaNormalization f h R α ∧ CounitEquation f h R β α := by
  sorry

end AlgebraicGeometry.Scheme.ProEtaleOpenRestriction
