/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSupportPlusAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.PNat.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-! # Supported finite torsion layers of a divisible injective resolution

Source: Stacks Project, Tags 0DD7 and 09XQ; finite-coefficient refinement for
ILO, Expose XVI, Proposition 3.3.2, printed p.245
(blueprint: lem-per-divisible-torsion-supported-injective-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.DivisibleTorsion

/-- The finite coefficient ring, lifted to the small-etale coefficient universe.
Source: Stacks 0DD7, finite-exponent refinement
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev A (l : ℕ) (r : ℕ+) := ULift.{u + 1} (ZMod (l ^ (r : ℕ)))

/-- Finiteness of the specified coefficient ring.
Source: Stacks 0DD7, finite-exponent refinement
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
instance finiteA (l : ℕ) [Fact l.Prime] (r : ℕ+) : Finite (A.{u} l r) := by
  let : NeZero (l ^ (r : ℕ)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  infer_instance

/-- Ordinary module sheaves on the recorded small-etale site.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Mod (X : Scheme.{u}) (l : ℕ) (r : ℕ+) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} l r))

/-- Abelian sheaves on the same site.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- Forget coefficients, retaining the actual underlying abelian sheaf.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev forget (X : Scheme.{u}) (l : ℕ) (r : ℕ+) : Mod X l r ⥤ Ab X :=
  sheafCompose X.smallEtaleTopology (forget₂ _ AddCommGrpCat.{u + 1})

/-- The canonical quotient of finite coefficient rings.
Source: ILO XVI 3.3.2, coefficient rows
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def quotient (l : ℕ) {N r : ℕ+} (h : r ≤ N) : A.{u} l N →+* A.{u} l r :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((ZMod.castHom (pow_dvd_pow l h) _).comp ULift.ringEquiv.toRingHom)

/-- Ordinary restriction along that quotient, computed sectionwise.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev res (X : Scheme.{u}) (l : ℕ) {N r : ℕ+} (h : r ≤ N) :
    Mod X l r ⥤ Mod X l N := Sheaf.restrictScalars X.smallEtaleTopology (quotient l h)

/-- The recorded module-valued supported inverse image, using the canonical open complement.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev H {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) (r : ℕ+) :=
  closedUpperShriek (ModuleCat.{u + 1} (A.{u} l r)) i (closedSupportOpenComplement i).ι

/-- Localization of bounded-below complexes through the homotopy category.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Q (C : Type v) [Category.{w} C] [Abelian C] [HasDerivedCategory C] :=
  HomotopyCategory.Plus.quotient C ⋙ _root_.DerivedCategory.Plus.Qh

/-- A sheaf in degree zero, as a bounded-below complex.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def single (C : Type v) [Category.{w} C] [Abelian C] (M : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩

/-- Global sections of a module sheaf, evaluated at the terminal small-etale object.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev sections (X : Scheme.{u}) (l : ℕ) (r : ℕ+) :
    Mod X l r ⥤ ModuleCat.{u + 1} (A.{u} l r) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))

/-- A coefficient-valued presentation of the actual kernel of multiplication by `l^r`.
The kernel fork fixes both the object and its inclusion; this is not an arbitrary
choice of an object killed by `l^r`. The functor laws give its canonical action on maps.
Source: Stacks 0DD7, first paragraph
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
structure Layer (X : Scheme.{u}) (l : ℕ) (r : ℕ+) where
  functor : Ab X ⥤ Mod X l r
  additive : functor.Additive
  inclusion : functor ⋙ forget X l r ⟶ 𝟭 (Ab X)
  condition (M : Ab X) : inclusion.app M ≫ (l ^ (r : ℕ) • 𝟙 M) = 0
  isKernel (M : Ab X) : IsLimit (KernelFork.ofι (inclusion.app M) (condition M))

attribute [instance] Layer.additive

/-- The actual torsion subcomplex, with its coefficient action.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev J {X : Scheme.{u}} {l : ℕ} {r : ℕ+} (T : Layer X l r)
    (I : CochainComplex.Plus (Ab X)) := T.functor.mapCochainComplexPlus.obj I

/-- The actual supported torsion complex.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev K {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {r : ℕ+} (T : Layer X l r) (I : CochainComplex.Plus (Ab X)) :=
  (H i l r).mapCochainComplexPlus.obj (J T I)

/-- Its actual global-section complex.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev E {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {r : ℕ+} (T : Layer X l r) (I : CochainComplex.Plus (Ab X)) :=
  (sections Z l r).mapCochainComplexPlus.obj (K i T I)

/-- The kernel augmentation induced by a fixed augmented complex, including the
canonical commutation of a functor with a complex concentrated in degree zero.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def augmentation {X : Scheme.{u}} {l : ℕ} {r : ℕ+} (T : Layer X l r)
    {M : Ab X} {I : CochainComplex.Plus (Ab X)} (a : single (Ab X) M ⟶ I) :
    single (Mod X l r) (T.functor.obj M) ⟶ J T I :=
  ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex T.functor (.up ℤ) 0).inv.app M ≫
    (T.functor.mapHomologicalComplex (.up ℤ)).map a.hom)

/-- The fixed-ring right-derived unit on a bounded-below complex.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev derivedUnit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) [Fact l.Prime] (r : ℕ+) (L : CochainComplex.Plus (Mod X l r)) :=
  (H i l r).rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj L)

/-- An actual coefficient system of torsion kernels. Each map is fixed on underlying
abelian sheaves by its inclusion into the original sheaf. This determines the maps
uniquely and supplies both inclusions and reductions without arbitrary choices.
Source: Stacks 0DD7 and ILO XVI 3.3.2
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
structure Layers (X : Scheme.{u}) (l : ℕ) where
  layer (r : ℕ+) : Layer X l r
  incl {N r : ℕ+} (h : r ≤ N) :
    (layer r).functor ⋙ res X l h ⟶ (layer N).functor
  red {N r : ℕ+} (h : r ≤ N) :
    (layer N).functor ⟶ (layer r).functor ⋙ res X l h
  incl_normalization {N r : ℕ+} (h : r ≤ N) (M : Ab X) :
    (forget X l N).map ((incl h).app M) ≫ (layer N).inclusion.app M =
      (layer r).inclusion.app M
  red_normalization {N r : ℕ+} (h : r ≤ N) (M : Ab X) :
    (forget X l N).map ((red h).app M) ≫ (layer r).inclusion.app M =
      (layer N).inclusion.app M ≫ (l ^ ((N : ℕ) - (r : ℕ)) • 𝟙 M)

/-- The same kernel complex, regarded over the common larger coefficient ring.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Jr {X : Scheme.{u}} {l : ℕ} (T : Layers X l) (I : CochainComplex.Plus (Ab X))
    {N r : ℕ+} (h : r ≤ N) := (res X l h).mapCochainComplexPlus.obj (J (T.layer r) I)

/-- Its supported image in the common coefficient category.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Kr {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} (T : Layers X l) (I : CochainComplex.Plus (Ab X))
    {N r : ℕ+} (h : r ≤ N) := (H i l N).mapCochainComplexPlus.obj (Jr T I h)

/-- The restricted augmentation, using the canonical functorial degree-zero model.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev ar {X : Scheme.{u}} {l : ℕ} (T : Layers X l)
    {M : Ab X} {I : CochainComplex.Plus (Ab X)} (a : single (Ab X) M ⟶ I)
    {N r : ℕ+} (h : r ≤ N) :=
  ((T.layer r).functor ⋙ res X l h).mapCochainComplexPlus.map a

/-- The common-ring degree-zero torsion sheaf; the canonical single-complex
commutation identifies this with the torsion sheaf concentrated in degree zero.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev Fr {X : Scheme.{u}} {l : ℕ} (T : Layers X l) (M : Ab X)
    {N r : ℕ+} (h : r ≤ N) := Jr T (single (Ab X) M) h

/-- The derived object of the supported complex in a common coefficient category.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev QKr {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} (T : Layers X l) (I : CochainComplex.Plus (Ab X))
    {N r : ℕ+} (h : r ≤ N) := (Q (Mod Z l N)).obj (Kr i T I h)

/-- The canonical chain maps induced by any natural transformation between coefficient
functors. This includes exactly the kernel inclusions and multiplication reductions.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def map {X : Scheme.{u}} {l : ℕ} {N : ℕ+}
    {F G : Ab X ⥤ Mod X l N} [F.Additive] [G.Additive] (f : F ⟶ G)
    (I : CochainComplex.Plus (Ab X)) :
    F.mapCochainComplexPlus.obj I ⟶ G.mapCochainComplexPlus.obj I :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex f (.up ℤ)).app I.obj)

/-- The constant rank-one coefficient sheaf.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev unitSheaf (Z : Scheme.{u}) (l : ℕ) (r : ℕ+) : Mod Z l r :=
  (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} l r))).obj
    (ModuleCat.of (A.{u} l r) (A.{u} l r))

/-- Evaluation at one of a sheaf-valued Hom cocycle, via the canonical constant-sheaf
adjunction. This is the actual section represented by that cocycle.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def evalOne {Z : Scheme.{u}} {l : ℕ} {r : ℕ+}
    {L : CochainComplex (Mod Z l r) ℤ} {m : ℤ}
    (χ : CochainComplex.HomComplex.Cocycle (single (Mod Z l r) (unitSheaf Z l r)).obj L m) :
    (sections Z l r).obj (L.X m) :=
  ((constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} l r))
    (Scheme.Etale.isTerminalMkId Z)).homEquiv _ _
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (unitSheaf Z l r)).inv ≫
        χ.val.v 0 m (zero_add m))) 1

/-- The localized morphism represented by a sheaf-valued cocycle, with the canonical
localization/shift comparison and the chosen normalized supported comparison.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def cocycleMap {Z : Scheme.{u}} {l : ℕ} {r : ℕ+}
    {L : CochainComplex.Plus (Mod Z l r)}
    {D : _root_.DerivedCategory.Plus (Mod Z l r)} (c : (Q (Mod Z l r)).obj L ≅ D)
    {m : ℤ}
    (χ : CochainComplex.HomComplex.Cocycle
      (single (Mod Z l r) (unitSheaf Z l r)).obj L.obj m) :
    ((Q (Mod Z l r)).obj (single (Mod Z l r) (unitSheaf Z l r))).obj ⟶ D.obj⟦m⟧ :=
  _root_.DerivedCategory.Qh.map
    (CochainComplex.HomComplex.CohomologyClass.toHom
      (CochainComplex.HomComplex.CohomologyClass.mk χ)) ≫
    _root_.DerivedCategory.Qh.map
      (((HomotopyCategory.quotient (Mod Z l r) (.up ℤ)).commShiftIso m).hom.app L.obj) ≫
    (_root_.DerivedCategory.Qh.commShiftIso m).hom.app
      ((HomotopyCategory.quotient _ _).obj L.obj) ≫ c.hom.hom⟦m⟧'

/-- The cocycle isomorphism, normalized on every cycle by sending one to that section.
This normalization determines it uniquely; it also forces naturality under chain maps.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def CocycleComparison {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {r : ℕ+} (T : Layer X l r) (I : CochainComplex.Plus (Ab X))
    (D : _root_.DerivedCategory.Plus (Mod Z l r))
    (c : (Q (Mod Z l r)).obj (K i T I) ≅ D) : Prop :=
  ∀ m : ℕ, ∃ η : (E i T I).obj.homology (m : ℤ) ≃+
    (((Q (Mod Z l r)).obj (single (Mod Z l r) (unitSheaf Z l r))).obj ⟶ D.obj⟦(m : ℤ)⟧),
    ∀ (z : (E i T I).obj.cycles (m : ℤ))
      (χ : CochainComplex.HomComplex.Cocycle
        (single (Mod Z l r) (unitSheaf Z l r)).obj (K i T I).obj (m : ℤ)),
      evalOne χ = (E i T I).obj.iCycles (m : ℤ) z →
        η ((E i T I).obj.homologyπ (m : ℤ) z) = cocycleMap c χ

/-- The canonical scalar comparison for the closed right adjoints, explicitly the mate
of the inverse ordinary direct-image comparison for the fixed closed adjunctions.
Its formula includes the closed-support counits and fixes its identity normalization.
Source: Stacks 09XQ and ILO XVI 3.3.2
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def coefficientMate {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) [Fact l.Prime] {N r : ℕ+} (h : r ≤ N)
    (F : _root_.DerivedCategory.Plus (Mod X l r)) :
    (res Z l h).mapDerivedCategoryPlus.obj ((closedSupportPlus (A.{u} l r) i).obj F) ⟶
      (closedSupportPlus (A.{u} l N) i).obj ((res X l h).mapDerivedCategoryPlus.obj F) :=
  (closedSupportPlusAdjunction (A.{u} l N) i).unit.app _ ≫
    (closedSupportPlus (A.{u} l N) i).map
      (inv ((rightDerivedLowerStarRestrictScalars (quotient l h) i).app
        ((closedSupportPlus (A.{u} l r) i).obj F)) ≫
      (res X l h).mapDerivedCategoryPlus.map
        ((closedSupportPlusCounit (A.{u} l r) i).app F))

/-- The canonical underived scalar-support identification, specified uniquely by its
counit equation. Direct image commutes with restriction of scalars literally.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
structure SupportRestriction {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) {N r : ℕ+} (h : r ≤ N) where
  iso : H i l r ⋙ res Z l h ≅ res X l h ⋙ H i l N
  counit (F : Mod X l r) :
    (lowerStar (ModuleCat.{u + 1} (A.{u} l N)) i).map (iso.hom.app F) ≫
      (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} (A.{u} l N)) i
        (closedSupportOpenComplement i).ι
        (by rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm)).counit.app
          ((res X l h).obj F) =
      (res X l h).map
        ((lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} (A.{u} l r)) i
          (closedSupportOpenComplement i).ι
          (by rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm)).counit.app F)

/-- The induced scalar-support comparison on the actual torsion complexes.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def supportComplexIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {N r : ℕ+} {h : r ≤ N} (s : SupportRestriction i l h)
    (T : Layers X l) (I : CochainComplex.Plus (Ab X)) :
    (res Z l h).mapCochainComplexPlus.obj (K i (T.layer r) I) ≅ Kr i T I h :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex s.iso (.up ℤ)).app (J (T.layer r) I).obj)

/-- The canonical single-complex identification for the torsion-kernel functor.
Source: Stacks 0DD7 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def singleIso {X : Scheme.{u}} {l : ℕ} {r : ℕ+} (T : Layer X l r) (M : Ab X) :
    T.functor.mapCochainComplexPlus.obj (single (Ab X) M) ≅
      single (Mod X l r) (T.functor.obj M) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex T.functor (.up ℤ) 0).app M)

/-- The canonical comparison between scalar restriction after localization and
localization of the degree-zero torsion complex with restricted scalars.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def sourceRestrictionIso {X : Scheme.{u}} {l : ℕ} (T : Layers X l) (M : Ab X)
    {N r : ℕ+} (h : r ≤ N) :
    (res X l h).mapDerivedCategoryPlus.obj
      ((Q (Mod X l r)).obj (single (Mod X l r) ((T.layer r).functor.obj M))) ≅
      (Q (Mod X l N)).obj (Fr T M h) :=
  (res X l h).mapDerivedCategoryPlusFactorsh.app
    ((HomotopyCategory.Plus.quotient _).obj (single _ ((T.layer r).functor.obj M))) ≪≫
    (Q (Mod X l N)).mapIso
      ((res X l h).mapCochainComplexPlus.mapIso (singleIso (T.layer r) M).symm)

/-- The actual coefficient row of complexes in the common ring A_(a+b).
The two maps are obtained from the normalized inclusion and reduction transformations.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def row {X : Scheme.{u}} {l : ℕ} (T : Layers X l)
    (I : CochainComplex.Plus (Ab X)) (a b : ℕ+)
    (w : (map (T.incl (N := a + b) (r := a) (Nat.le_add_right (a : ℕ) (b : ℕ))) I).hom ≫
      (map (T.red (N := a + b) (r := b) (Nat.le_add_left (b : ℕ) (a : ℕ))) I).hom = 0) :
    ShortComplex (CochainComplex (Mod X l (a + b)) ℤ) :=
  ShortComplex.mk (map (T.incl (N := a + b) (r := a) (Nat.le_add_right (a : ℕ) (b : ℕ))) I).hom
    (map (T.red (N := a + b) (r := b) (Nat.le_add_left (b : ℕ) (a : ℕ))) I).hom w

/-- The connecting arrow of a degreewise short exact row, in the bounded-below
localization. It is the usual cone connecting arrow, transported by the canonical
quotient/localization and shift isomorphisms.
Source: Stacks derived-category short-exact triangle
(blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def connecting {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    {L₁ L₂ L₃ : CochainComplex.Plus C} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃)
    (wfg : f.hom ≫ g.hom = 0) (h : (ShortComplex.mk f.hom g.hom wfg).ShortExact) :
    (Q C).obj L₃ ⟶ ((Q C).obj L₁)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk
    ((_root_.DerivedCategory.quotientCompQhIso C).hom.app L₃.obj ≫
      _root_.DerivedCategory.triangleOfSESδ h ≫
      ((_root_.DerivedCategory.quotientCompQhIso C).inv.app L₁.obj)⟦(1 : ℤ)⟧' ≫
      (_root_.DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app ((Q C).obj L₁))



/-- View a bounded-below complex as its object in the plus localization.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev q {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    (L : CochainComplex.Plus C) := (Q C).obj L

/-- The right-adjoint shift identification for the fixed closed-support adjunction.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def supportShift {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) [Fact l.Prime] (r : ℕ+)
    (D : _root_.DerivedCategory.Plus (Mod X l r)) (m : ℤ) :
    (closedSupportPlus (A.{u} l r) i).obj (D⟦m⟧) ≅
      ((closedSupportPlus (A.{u} l r) i).obj D)⟦m⟧ := by
  letI := closedSupportPlusCommShift (A.{u} l r) i
  exact (Functor.commShiftIso (closedSupportPlus (A.{u} l r) i) m).app D

/-- A comparison for a coefficient row, including the connecting arrow. Each component
is fixed by its derived-unit normalization, so the row is the derived supported image
of the actual coefficient row rather than an unrelated distinguished triangle.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
def RowComparison {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) [Fact l.Prime] (N : ℕ+)
    (L₁ L₂ L₃ B₁ B₂ B₃ : CochainComplex.Plus (Mod X l N))
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) (wfg : f.hom ≫ g.hom = 0)
    (bf : B₁ ⟶ B₂) (bg : B₂ ⟶ B₃) (wb : bf.hom ≫ bg.hom = 0)
    (a₁ : B₁ ⟶ L₁) (a₂ : B₂ ⟶ L₂) (a₃ : B₃ ⟶ L₃)
    (_hL : (ShortComplex.mk f.hom g.hom wfg).ShortExact)
    (hB : (ShortComplex.mk bf.hom bg.hom wb).ShortExact)
    (hK : ((ShortComplex.mk f.hom g.hom wfg).map
      ((H i l N).mapHomologicalComplex (.up ℤ))).ShortExact) : Prop :=
  ∃ (e₁ : q ((H i l N).mapCochainComplexPlus.obj L₁) ≅
        (closedSupportPlus (A.{u} l N) i).obj (q B₁))
    (e₂ : q ((H i l N).mapCochainComplexPlus.obj L₂) ≅
        (closedSupportPlus (A.{u} l N) i).obj (q B₂))
    (e₃ : q ((H i l N).mapCochainComplexPlus.obj L₃) ≅
        (closedSupportPlus (A.{u} l N) i).obj (q B₃)),
    e₁.hom ≫ (closedSupportPlus (A.{u} l N) i).map ((Q _).map a₁) =
        derivedUnit i l N L₁ ∧
    e₂.hom ≫ (closedSupportPlus (A.{u} l N) i).map ((Q _).map a₂) =
        derivedUnit i l N L₂ ∧
    e₃.hom ≫ (closedSupportPlus (A.{u} l N) i).map ((Q _).map a₃) =
        derivedUnit i l N L₃ ∧
    (Q _).map ((H i l N).mapCochainComplexPlus.map f) ≫ e₂.hom =
      e₁.hom ≫ (closedSupportPlus (A.{u} l N) i).map ((Q _).map bf) ∧
    (Q _).map ((H i l N).mapCochainComplexPlus.map g) ≫ e₃.hom =
      e₂.hom ≫ (closedSupportPlus (A.{u} l N) i).map ((Q _).map bg) ∧
    connecting ((H i l N).mapCochainComplexPlus.map f)
        ((H i l N).mapCochainComplexPlus.map g)
        (by
          change ((H i l N).mapHomologicalComplex (.up ℤ)).map f.hom ≫
            ((H i l N).mapHomologicalComplex (.up ℤ)).map g.hom = 0
          rw [← Functor.map_comp, wfg, Functor.map_zero]) hK ≫
        e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ (closedSupportPlus (A.{u} l N) i).map (connecting bf bg wb hB) ≫
        (supportShift i l N (q B₁) 1).hom

/-- Inclusion in a coefficient row in A_(a+b).
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev rowIncl {X : Scheme.{u}} {l : ℕ} (T : Layers X l)
    (I : CochainComplex.Plus (Ab X)) (a b : ℕ+) :=
  map (T.incl (N := a + b) (r := a) (Nat.le_add_right (a : ℕ) (b : ℕ))) I

/-- Reduction in a coefficient row in A_(a+b), multiplication by l^a.
Source: ILO XVI 3.3.2 (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev rowRed {X : Scheme.{u}} {l : ℕ} (T : Layers X l)
    (I : CochainComplex.Plus (Ab X)) (a b : ℕ+) :=
  map (T.red (N := a + b) (r := b) (Nat.le_add_left (b : ℕ) (a : ℕ))) I

/-- A row after applying the recorded supported functor termwise.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev supportRow {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {N : ℕ+} (S : ShortComplex (CochainComplex (Mod X l N) ℤ)) :=
  S.map ((H i l N).mapHomologicalComplex (.up ℤ))

/-- A row after taking global supported sections termwise.
Source: Stacks 09XQ (blueprint: lem-per-divisible-torsion-supported-injective-models). -/
abbrev sectionRow {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {l : ℕ} {N : ℕ+} (S : ShortComplex (CochainComplex (Mod X l N) ℤ)) :=
  (supportRow i S).map ((sections Z l N).mapHomologicalComplex (.up ℤ))

/-- Supported finite torsion layers of any injective resolution of an l-divisible sheaf.
Source: Stacks Project 0DD7, first paragraph, and 09XQ; the finite-layer refinement
of ILO XVI 3.3.2, printed p.245
(blueprint: lem-per-divisible-torsion-supported-injective-models).

Proof:
1. Represent sections by maps from the sheafified free abelian sheaf on a site object
   (lem-trf-site-free-sheaf-sections). Multiplication by a positive integer is monic
   there, also after exact sheafification (lem-weil-pbc-sheafification-exact).
   Injectivity extends maps along it, so injective sheaves are divisible on sections.
2. The kernel complex of l^r on I has cohomology F_r in degree zero and zero otherwise,
   by the long exact sequence (lem-weil-pbc-complex-ses-homology-long-exact) and
   divisibility of M. Extension of maps into I lands in its l^r kernel when the
   source is killed by l^r, proving injectivity over A_r.
3. Exact closed direct image and the supported-kernel adjunction
   (lem-pur-etale-supported-kernel-adjunction) preserve injectives on the right.
   Exact inverse image (prop-weil-pbc-inverse-image-exact) commutes with the torsion
   kernel. Thus K_r is the torsion kernel of a complex of injective abelian sheaves.
4. Enough injectives (lem-weil-pbc-module-sheaves-enough-injectives) and the canonical
   right-derived unit (lem-weil-pbc-right-derived-plus-injective) give the fixed-ring
   comparison. It is normalized by the support inclusion and hence by the counit of
   def-per-closed-support-plus-adjunction.
5. Bounded-below injective complexes are K-injective
   (lem-weil-pbc-bounded-below-injectives-kinjective), so homotopy classes compute
   derived maps (lem-weil-pbc-kinjective-hom-derived). The free rank-one universal
   property (lem-trf-free-module-sheaf-universal-property) identifies maps with
   sections by evaluation at one; cocycles and boundaries give the cohomology group.
6. For a divisible group D, the row D[l^a] -> D[l^(a+b)] -> D[l^b] is exact,
   since one divides a section by l^a. Apply on every section of I and of its
   supported injective sheaves, including global sections. Kernels are sectionwise
   (lem-weil-pbc-sheafification-exact). This proves all three strict coefficient rows.
7. The same local lifting argument applies to M, since sheaf epimorphisms are locally
   surjective (lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective), giving the
   coefficient row and its commuting augmentation to the J row.
8. Over A_N the restricted J_s terms are support-acyclic: the rows with indices
   s,N-s, whose supported maps are epic by step 6, and the derived long exact
   sequence (lem-weil-pbc-derived-functor-long-exact) prove vanishing by dimension
   shifting simultaneously in s. The acyclic-resolution comparison (sk-thm-acyclicity)
   makes the same derived unit invertible, compatibly with the support counit.
9. Naturality of that unit gives all coefficient-map and composition compatibilities.
   For the coefficient triangles (lem-weil-pbc-complex-ses-triangle), the cone of an
   inclusion has finite sums of support-acyclic terms; support preserves that cone.
   Its map to the quotient is an isomorphism after derivation, so the connecting
   arrow agrees as well. Inclusion and multiplication compose as their literal
   coefficient maps, and support inclusions commute with all of them.
-/
theorem supported_injective_models
    {Z X : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (l : ℕ) [Fact l.Prime] (M : Ab X) [Epi (l • 𝟙 M)]
    (I : CochainComplex.Plus (Ab X)) [I.obj.IsStrictlyGE 0]
    (_hI : ∀ q : ℤ, Injective (I.obj.X q))
    (a : single (Ab X) M ⟶ I) (_ha : QuasiIso a.hom) :
    ∃ T : Layers X l,
      (∀ r : ℕ+, QuasiIso (augmentation (T.layer r) a).hom ∧
        (∀ q : ℤ, Injective ((J (T.layer r) I).obj.X q)) ∧
        (∀ q : ℤ, Injective ((K i (T.layer r) I).obj.X q))) ∧
      ∃ (c : ∀ r : ℕ+, (Q (Mod Z l r)).obj (K i (T.layer r) I) ≅
          (closedSupportPlus (A.{u} l r) i).obj
            ((Q (Mod X l r)).obj (single _ ((T.layer r).functor.obj M))))
        (d : ∀ (N r : ℕ+) (h : r ≤ N), QKr i T I h ≅
          (closedSupportPlus (A.{u} l N) i).obj ((Q (Mod X l N)).obj (Fr T M h)))
        (s : ∀ (N r : ℕ+) (h : r ≤ N), SupportRestriction i l h),
        (∀ r : ℕ+, (c r).hom ≫ (closedSupportPlus (A.{u} l r) i).map
          ((Q (Mod X l r)).map (augmentation (T.layer r) a)) =
            derivedUnit i l r (J (T.layer r) I)) ∧
        (∀ (N r : ℕ+) (h : r ≤ N), (d N r h).hom ≫
          (closedSupportPlus (A.{u} l N) i).map
            ((Q (Mod X l N)).map (ar T a h)) = derivedUnit i l N (Jr T I h)) ∧
        (∀ r : ℕ+, CocycleComparison i (T.layer r) I _ (c r)) ∧
        (∀ (N r : ℕ+) (h : r ≤ N),
          (res Z l h).mapDerivedCategoryPlusFactorsh.hom.app
              ((HomotopyCategory.Plus.quotient _).obj (K i (T.layer r) I)) ≫
            (Q (Mod Z l N)).map (supportComplexIso i (s N r h) T I).hom ≫
              (d N r h).hom =
          (res Z l h).mapDerivedCategoryPlus.map (c r).hom ≫
            coefficientMate i l h _ ≫
              (closedSupportPlus (A.{u} l N) i).map (sourceRestrictionIso T M h).hom) ∧
        (∀ (N r t : ℕ+) (hr : r ≤ N) (ht : t ≤ N)
          (f : (T.layer r).functor ⋙ res X l hr ⟶
            (T.layer t).functor ⋙ res X l ht),
          (Q (Mod Z l N)).map ((H i l N).mapCochainComplexPlus.map (map f I)) ≫
              (d N t ht).hom =
            (d N r hr).hom ≫ (closedSupportPlus (A.{u} l N) i).map
              ((Q (Mod X l N)).map (map f (single (Ab X) M)))) ∧
        (∀ (N r t v₀ : ℕ+) (hr : r ≤ N) (ht : t ≤ N) (hv : v₀ ≤ N)
          (f : (T.layer r).functor ⋙ res X l hr ⟶
            (T.layer t).functor ⋙ res X l ht)
          (g : (T.layer t).functor ⋙ res X l ht ⟶
            (T.layer v₀).functor ⋙ res X l hv),
          map f I ≫ map g I = map (f ≫ g) I) ∧
        (∀ a₀ b₀ : ℕ+,
          ∃ (wI : (map (T.incl (N := a₀ + b₀) (r := a₀)
                (Nat.le_add_right (a₀ : ℕ) (b₀ : ℕ))) I).hom ≫
              (map (T.red (N := a₀ + b₀) (r := b₀)
                (Nat.le_add_left (b₀ : ℕ) (a₀ : ℕ))) I).hom = 0)
            (wM : (map (T.incl (N := a₀ + b₀) (r := a₀)
                (Nat.le_add_right (a₀ : ℕ) (b₀ : ℕ))) (single (Ab X) M)).hom ≫
              (map (T.red (N := a₀ + b₀) (r := b₀)
                (Nat.le_add_left (b₀ : ℕ) (a₀ : ℕ))) (single (Ab X) M)).hom = 0),
            ∃ (hJ : (row T I a₀ b₀ wI).ShortExact)
              (hK : (supportRow i (row T I a₀ b₀ wI)).ShortExact)
              (hF : (row T (single (Ab X) M) a₀ b₀ wM).ShortExact),
              (sectionRow i (row T I a₀ b₀ wI)).ShortExact ∧
              RowComparison i l (a₀ + b₀)
                (Jr T I (N := a₀ + b₀) (r := a₀)
                  (Nat.le_add_right (a₀ : ℕ) (b₀ : ℕ)))
                (J (T.layer (a₀ + b₀)) I)
                (Jr T I (N := a₀ + b₀) (r := b₀)
                  (Nat.le_add_left (b₀ : ℕ) (a₀ : ℕ)))
                (Fr T M (N := a₀ + b₀) (r := a₀)
                  (Nat.le_add_right (a₀ : ℕ) (b₀ : ℕ)))
                (J (T.layer (a₀ + b₀)) (single (Ab X) M))
                (Fr T M (N := a₀ + b₀) (r := b₀)
                  (Nat.le_add_left (b₀ : ℕ) (a₀ : ℕ)))
                (rowIncl T I a₀ b₀) (rowRed T I a₀ b₀) wI
                (rowIncl T (single (Ab X) M) a₀ b₀)
                (rowRed T (single (Ab X) M) a₀ b₀) wM
                (ar T a (N := a₀ + b₀) (r := a₀)
                  (Nat.le_add_right (a₀ : ℕ) (b₀ : ℕ)))
                ((T.layer (a₀ + b₀)).functor.mapCochainComplexPlus.map a)
                (ar T a (N := a₀ + b₀) (r := b₀)
                  (Nat.le_add_left (b₀ : ℕ) (a₀ : ℕ))) hJ hF hK) := by
  sorry

end AlgebraicGeometry.Etale.DivisibleTorsion
