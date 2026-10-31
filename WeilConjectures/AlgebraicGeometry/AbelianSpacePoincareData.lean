/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularGroupSpace
public import WeilConjectures.AlgebraicGeometry.RigidifiedLines
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import WeilConjectures.AlgebraicGeometry.SpaceDerivedTensorPullback
public import WeilConjectures.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.LineAlgebraicEquivalence
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Relative abelian spaces and normalized Poincare data

Source: Milne, Abelian Varieties, I Sections 8--9; Stacks, Tags 03G7 and 039Z
(blueprint: def-sfb-abelian-space-poincare-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace.Poincare

variable {S : Scheme.{u}}

/-- The existing small affine model carries its usual sheaf tensor product.
Source: Stacks 03EK and 039Z (blueprint: def-sfb-abelian-space-poincare-data). -/
instance smallMonoidal (X : AlgebraicSpace S) : MonoidalCategory X.SmallModules :=
  SheafOfModules.monoidalCategory X.smallStructureSheaf

/-- The actual internal Hom into the structure module, in the original universe.
Source: Stacks 03EK (blueprint: def-sfb-abelian-space-poincare-data). -/
abbrev dual (X : AlgebraicSpace S) (L : X.SmallModules) : X.SmallModules :=
  SheafOfModules.homObj (R := X.smallStructureSheaf) L (𝟙_ X.SmallModules)

/-- The line predicate is transported through the recorded restriction equivalence.
Source: Stacks 039Z (blueprint: def-sfb-abelian-space-poincare-data). -/
def IsLine (X : AlgebraicSpace S) (L : X.SmallModules) : Prop :=
  X.IsLineModule (X.smallModuleEquivalence.inverse.obj L)

/-- The section-normalized compositor, conjugated by the existing basis equivalences.
Source: Stacks 03D7 and 039Z (blueprint: def-sfb-abelian-space-poincare-data). -/
def pullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.SmallModules) :
    (smallModuleTensorPullback f).obj ((smallModuleTensorPullback g).obj L) ≅
      (smallModuleTensorPullback (f ≫ g)).obj L :=
  X.smallModuleRestriction.mapIso
    ((moduleTensorPullback f).mapIso
      (Y.smallModuleEquivalence.unitIso.app
        ((moduleTensorPullback g).obj (Z.smallModuleEquivalence.inverse.obj L))).symm ≪≫
      (moduleTensorComposition f g).app (Z.smallModuleEquivalence.inverse.obj L))

/-- Multiplication identifies tensor inverse image of the structure module with the unit.
Source: Stacks 03D7 and 039Z (blueprint: def-sfb-abelian-space-poincare-data). -/
def pullbackUnit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (smallModuleTensorPullback f).obj (𝟙_ Y.SmallModules) ≅ 𝟙_ X.SmallModules :=
  X.smallModuleRestriction.mapIso
    ((moduleTensorPullback f).mapIso
      (Y.smallModuleEquivalence.inverse.mapIso (smallModuleUnitIso Y) ≪≫
        (Y.smallModuleEquivalence.unitIso.app (SheafOfModules.unit Y.structureSheaf)).symm)
      ≪≫ rigidifiedUnitIso f) ≪≫ (smallModuleUnitIso X).symm

/-- Fibre products are the published sheaf fibre products, with their actual projections.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
abbrev product {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B) :=
  enlargedFibreProduct f g

/-- First projection of the existing fibre product.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def fst {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B) : product f g ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)

/-- Second projection of the existing fibre product.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def snd {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B) : product f g ⟶ Y :=
  ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)

/-- The canonical map into a fibre product.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def pair {X Y B Z : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B}
    (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) : Z ⟶ product f g :=
  ObjectProperty.homMk (Limits.pullback.lift a.hom b.hom (congrArg (fun h ↦ h.hom) w))

/-- A space over a base with its specified section.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
structure Pointed (B : AlgebraicSpace S) where
  X : AlgebraicSpace S
  p : X ⟶ B
  e : B ⟶ X
  section_eq : e ≫ p = 𝟙 B

/-- The identity section in a parameter family.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def parameterSection {B T : AlgebraicSpace S} (A : Pointed B) (b : T ⟶ B) :
    T ⟶ product A.p b :=
  pair (b ≫ A.e) (𝟙 T) (by simp [Category.assoc, A.section_eq])

/-- Restriction of a rigidification through a commuting square, with canonical compositors.
Source: Stacks 03D7; Milne I Section 8
(blueprint: def-sfb-abelian-space-poincare-data). -/
def rigidificationPullback {X Y T U : AlgebraicSpace S}
    (e : T ⟶ X) (e' : U ⟶ Y) (a : U ⟶ T) (b : Y ⟶ X)
    (w : e' ≫ b = a ≫ e) (L : X.SmallModules)
    (r : (smallModuleTensorPullback e).obj L ≅ 𝟙_ T.SmallModules) :
    (smallModuleTensorPullback e').obj ((smallModuleTensorPullback b).obj L) ≅
      𝟙_ U.SmallModules :=
  pullbackComp e' b L ≪≫
    (eqToIso (congrArg (fun f ↦ (smallModuleTensorPullback f).obj L) w)) ≪≫
    (pullbackComp a e L).symm ≪≫ (smallModuleTensorPullback a).mapIso r ≪≫ pullbackUnit a

/-- The identity chart of a represented scheme.
Source: Stacks 03ED (blueprint: def-sfb-abelian-space-poincare-data). -/
abbrev schemeIdentityChart (T : Over S) : (schemeSpace T).EtaleSite := by
  let I := (Scheme.fppfTopology.over S).yonedaCompSheafToPresheaf.app T
  refine ⟨CostructuredArrow.mk (Y := T) I.inv, ?_⟩
  intro U a
  refine ⟨U, 𝟙 U, a ≫ I.hom, ?_, inferInstance⟩
  change IsPullback (a ≫ I.hom) (yoneda.map (𝟙 U)) I.inv a
  have h := IsPullback.of_vert_isIso (fst := a ≫ I.hom)
    (snd := 𝟙 (yoneda.obj U)) (f := I.inv) (g := a) ⟨by
      rw [Category.assoc, I.hom_inv_id]
      exact (Category.comp_id a).trans (Category.id_comp a).symm⟩
  have hi : yoneda.map (𝟙 U) = 𝟙 (yoneda.obj U) := yoneda.map_id U
  rw [hi]
  exact h

/-- The existing Zariski restriction on the identity chart of a represented scheme.
Source: Stacks 03G7 (blueprint: def-sfb-abelian-space-poincare-data). -/
def schemeModule (T : Over S) : (schemeSpace T).SmallModules ⥤ T.left.Modules :=
  (schemeSpace T).smallModuleEquivalence.inverse ⋙
    schemeRestriction (schemeSpace T) (schemeIdentityChart T)

/-- A field-scheme model, still viewed over the ambient base.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
abbrev fieldModel {K : Type u} [Field K] (s : Spec (.of K) ⟶ S)
    (Z : Over (Spec (.of K))) : Over S := Over.mk (Z.hom ≫ s)

/-- Projection of a field-scheme model to its field.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def fieldProjection {K : Type u} [Field K] (s : Spec (.of K) ⟶ S)
    (Z : Over (Spec (.of K))) : schemeSpace (fieldModel s Z) ⟶ schemeSpace (Over.mk s) :=
  groupSchemeMap (Over.homMk Z.hom rfl)

/-- Every geometric fibre is represented by an abelian variety. Its group law is inherited
from the given group space; the predicate for the representing scheme is the upstream one.
Source: Milne I Sections 1 and 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def HasAbelianFibres {X B : AlgebraicSpace S} (f : X ⟶ B) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (b : schemeSpace (Over.mk s) ⟶ B),
    ∃ (Z : Over (Spec (.of K))) (j : schemeSpace (fieldModel s Z) ⟶ X),
      IsAbelianVariety Z ∧ IsPullback j.hom (fieldProjection s Z).hom f.hom b.hom

/-- Proper, smooth, finitely presented, with abelian geometric fibres. Separatedness is
part of properness, so the quasi-separatedness needed for finite presentation is included.
Source: Milne I Section 8; Stacks 03MM and 0410
(blueprint: def-sfb-abelian-space-poincare-data). -/
def IsAbelianFamily {X B : AlgebraicSpace S} (f : X ⟶ B) : Prop :=
  MapIsProper f ∧ MapIsLocally (@Smooth) f ∧
    MapIsLocallyOfFinitePresentation f ∧ HasAbelianFibres f

/-- Algebraic triviality is tested on every geometric fibre and every scheme model of it.
The relation is exactly the existing equivalence relation generated by smooth connected
line-module families, including isomorphisms of representatives.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def FibrewiseTrivial {X T : AlgebraicSpace S} (f : X ⟶ T) (L : X.SmallModules) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (t : schemeSpace (Over.mk s) ⟶ T) (Z : Over (Spec (.of K)))
    (j : schemeSpace (fieldModel s Z) ⟶ X),
    IsPullback j.hom (fieldProjection s Z).hom f.hom t.hom →
      Scheme.Modules.AreAlgebraicallyEquivalent Z
        ((schemeModule (fieldModel s Z)).obj ((smallModuleTensorPullback j).obj L))
        (SheafOfModules.unit Z.left.ringCatSheaf)

/-- The first identity axis of a product of pointed spaces.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def leftAxis {B : AlgebraicSpace S} (A D : Pointed B) : D.X ⟶ product A.p D.p :=
  pair (D.p ≫ A.e) (𝟙 D.X) (by simp [Category.assoc, A.section_eq])

/-- The second identity axis of a product of pointed spaces.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def rightAxis {B : AlgebraicSpace S} (A D : Pointed B) : A.X ⟶ product A.p D.p :=
  pair (𝟙 A.X) (A.p ≫ D.e) (by simp [Category.assoc, D.section_eq])

/-- Specified trivializations of both axes, agreeing at their intersection. The equality
is read through the canonical pullback compositors, not an arbitrary comparison.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
structure Axes {B : AlgebraicSpace S} (A D : Pointed B)
    (L : (product A.p D.p).SmallModules) where
  left : (smallModuleTensorPullback (leftAxis A D)).obj L ≅ 𝟙_ D.X.SmallModules
  right : (smallModuleTensorPullback (rightAxis A D)).obj L ≅ 𝟙_ A.X.SmallModules
  intersection : ∀ w : D.e ≫ leftAxis A D = A.e ≫ rightAxis A D,
    ((pullbackComp D.e (leftAxis A D) L).symm ≪≫
      (smallModuleTensorPullback D.e).mapIso left ≪≫ pullbackUnit D.e).hom =
    ((eqToIso (congrArg (fun f ↦ (smallModuleTensorPullback f).obj L) w)) ≪≫
      (pullbackComp A.e (rightAxis A D) L).symm ≪≫
      (smallModuleTensorPullback A.e).mapIso right ≪≫ pullbackUnit A.e).hom

/-- An isomorphism preserves the two specified axis trivializations.
Source: Milne I Sections 8--9 (blueprint: def-sfb-abelian-space-poincare-data). -/
def PreservesAxes {B : AlgebraicSpace S} {A D : Pointed B}
    {L M : (product A.p D.p).SmallModules} (r : Axes A D L) (s : Axes A D M)
    (v : L ≅ M) : Prop :=
  (smallModuleTensorPullback (leftAxis A D)).map v.hom ≫ s.left.hom = r.left.hom ∧
    (smallModuleTensorPullback (rightAxis A D)).map v.hom ≫ s.right.hom = r.right.hom

/-- Normalized equality of line families: all compatible axis normalizations admit the
unique normalization-preserving isomorphism. This includes the canonical tensor and
cancellation normalizations without choosing additional unnormalized isomorphisms.
Source: Milne I Sections 8--9 (blueprint: def-sfb-abelian-space-poincare-data). -/
def AxisEquivalent {B : AlgebraicSpace S} (A D : Pointed B)
    (L M : (product A.p D.p).SmallModules) : Prop :=
  Nonempty (Axes A D L) ∧ Nonempty (Axes A D M) ∧
    ∀ (r : Axes A D L) (s : Axes A D M), ∃! v : L ≅ M, PreservesAxes r s v

/-- The actual map of parameter families defined by a map to the proposed dual.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def familyMap {B T : AlgebraicSpace S} (A D : Pointed B) (b : T ⟶ B)
    (a : T ⟶ D.X) (w : a ≫ D.p = b) : product A.p b ⟶ product A.p D.p :=
  pair (fst A.p b) (snd A.p b ≫ a) (by
    apply ObjectProperty.hom_ext
    change (Limits.pullback.fst A.p.hom b.hom) ≫ A.p.hom =
      (Limits.pullback.snd A.p.hom b.hom) ≫ a.hom ≫ D.p.hom
    change Limits.pullback.fst A.p.hom b.hom ≫ A.p.hom =
      Limits.pullback.snd A.p.hom b.hom ≫ (a ≫ D.p).hom
    rw [w]
    exact Limits.pullback.condition)

/-- A rigidified isomorphism from the pulled-back universal family to the given family.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def Classifies {B T : AlgebraicSpace S} (A D : Pointed B)
    (P : (product A.p D.p).SmallModules) (rP : Axes A D P)
    (b : T ⟶ B) (L : (product A.p b).SmallModules)
    (r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅ 𝟙_ T.SmallModules)
    (a : T ⟶ D.X) : Prop :=
  ∃ w : a ≫ D.p = b,
    ∃ v : (smallModuleTensorPullback (familyMap A D b a w)).obj P ≅ L,
      ∃ h : parameterSection A b ≫ familyMap A D b a w = a ≫ leftAxis A D,
        (smallModuleTensorPullback (parameterSection A b)).map v.hom ≫ r.hom =
          (rigidificationPullback (leftAxis A D) (parameterSection A b)
            a (familyMap A D b a w) h P rP.left).hom

/-- The representing property for all scheme parameters, with no reducedness assumption.
Source: Milne I Section 8; relative form in Deligne Section 4.1
(blueprint: def-sfb-abelian-space-poincare-data). -/
def Represents {B : AlgebraicSpace S} (A D : Pointed B)
    (P : (product A.p D.p).SmallModules) (rP : Axes A D P) : Prop :=
  IsLine (product A.p D.p) P ∧ FibrewiseTrivial (snd A.p D.p) P ∧
    ∀ (T : Over S) (b : schemeSpace T ⟶ B) (L : (product A.p b).SmallModules),
      IsLine (product A.p b) L → FibrewiseTrivial (snd A.p b) L →
      ∀ r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅
          𝟙_ (schemeSpace T).SmallModules,
        ∃! a : schemeSpace T ⟶ D.X, Classifies A D P rP b L r a

/-- Rigidity concerns every line, including those outside the neutral Picard functor.
Source: Stacks 0E0S; Milne I Section 8
(blueprint: def-sfb-abelian-space-poincare-data). -/
def RigidAutomorphisms {B : AlgebraicSpace S} (A : Pointed B) : Prop :=
  ∀ (T : Over S) (b : schemeSpace T ⟶ B) (L : (product A.p b).SmallModules),
    IsLine (product A.p b) L →
    ∀ (r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅
        𝟙_ (schemeSpace T).SmallModules) (v : L ≅ L),
      (smallModuleTensorPullback (parameterSection A b)).map v.hom ≫ r.hom = r.hom →
        v = Iso.refl L

/-- A base change retains the actual fibre product and its pulled-back section.
Source: Stacks 02X2; Milne I Section 8
(blueprint: def-sfb-abelian-space-poincare-data). -/
def Pointed.baseChange {B B' : AlgebraicSpace S} (A : Pointed B) (g : B' ⟶ B) :
    Pointed B' where
  X := product A.p g
  p := snd A.p g
  e := parameterSection A g
  section_eq := by
    apply ObjectProperty.hom_ext
    exact Limits.pullback.lift_snd _ _ _

/-- The canonical projection of a pointed base change.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def Pointed.baseChangeMap {B B' : AlgebraicSpace S} (A : Pointed B) (g : B' ⟶ B) :
    (A.baseChange g).X ⟶ A.X := fst A.p g

/-- The canonical map of the two-factor products in a base change.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def baseChangeProductMap {B B' : AlgebraicSpace S} (A D : Pointed B) (g : B' ⟶ B) :
    product (A.baseChange g).p (D.baseChange g).p ⟶ product A.p D.p :=
  pair (fst (A.baseChange g).p (D.baseChange g).p ≫ A.baseChangeMap g)
    (snd (A.baseChange g).p (D.baseChange g).p ≫ D.baseChangeMap g) (by
      apply ObjectProperty.hom_ext
      dsimp [Pointed.baseChangeMap, fst, snd, Pointed.baseChange]
      simp only [Category.assoc, Limits.pullback.condition]
      rw [← Category.assoc, ← Category.assoc]
      rw [Limits.pullback.condition])

/-- A normalized comparison of two representing duals consists of its actual space
isomorphism and its actual universal-line isomorphism, respecting both axes.
Source: Milne I Section 8, Remark 8.7(a)
(blueprint: def-sfb-abelian-space-poincare-data). -/
structure DualComparison {B : AlgebraicSpace S} (A D E : Pointed B)
    (P : (product A.p D.p).SmallModules) (Q : (product A.p E.p).SmallModules)
    (r : Axes A D P) (s : Axes A E Q) where
  space : D.X ≅ E.X
  over_base : space.hom ≫ E.p = D.p
  identity : D.e ≫ space.hom = E.e
  line : (smallModuleTensorPullback (familyMap A E D.p space.hom over_base)).obj Q ≅ P
  left_eq : ∀ h : leftAxis A D ≫ familyMap A E D.p space.hom over_base =
      space.hom ≫ leftAxis A E,
    (smallModuleTensorPullback (leftAxis A D)).map line.hom ≫ r.left.hom =
      (rigidificationPullback (leftAxis A E) (leftAxis A D) space.hom
        (familyMap A E D.p space.hom over_base) h Q s.left).hom
  right_eq : ∀ h : rightAxis A D ≫ familyMap A E D.p space.hom over_base =
      rightAxis A E,
    (smallModuleTensorPullback (rightAxis A D)).map line.hom ≫ r.right.hom =
      (pullbackComp (rightAxis A D) (familyMap A E D.p space.hom over_base) Q ≪≫
        eqToIso (congrArg (fun f ↦ (smallModuleTensorPullback f).obj Q) h) ≪≫ s.right).hom

/-- Canonical comparisons are unique. This formulation includes identity and composition:
any two comparisons between the same universal rigidified families are equal, so both
identity comparisons and the two composites of base-change comparisons coincide.
Source: Milne I Section 8, Remark 8.7(a)
(blueprint: def-sfb-abelian-space-poincare-data). -/
def ComparisonCoherence {B : AlgebraicSpace S} (A D : Pointed B)
    (P : (product A.p D.p).SmallModules) (r : Axes A D P) : Prop :=
  ∀ (E : Pointed B) (Q : (product A.p E.p).SmallModules) (s : Axes A E Q),
    Represents A E Q s → Nonempty (DualComparison A D E P Q r s) ∧
      Subsingleton (DualComparison A D E P Q r s)

/-- A group algebraic space with its existing identity and structure maps.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def pointedGroup (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A) :
    Pointed (groupSpaceBase S) where
  X := A
  p := groupSpaceProjection A
  e := g.identity
  section_eq := by
    apply ObjectProperty.hom_ext
    apply Sheaf.hom_ext
    ext T x
    apply Over.OverMorphism.ext
    change T.unop.hom = x.left
    simpa using x.w.symm

/-- Multiplication of the existing natural commutative group law on its fibre product.
Multiplicative notation here denotes the addition written in the source.
Source: Milne I Section 8 (blueprint: def-sfb-abelian-space-poincare-data). -/
def addition (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A) :
    product (groupSpaceProjection A) (groupSpaceProjection A) ⟶ A :=
  ObjectProperty.homMk ⟨{
    app := fun T ↦ ↾fun x ↦ @Mul.mul _ (g.group T).toMul
      ((Limits.pullback.fst (groupSpaceProjection A).hom
        (groupSpaceProjection A).hom).hom.app T x)
      ((Limits.pullback.snd (groupSpaceProjection A).hom
        (groupSpaceProjection A).hom).hom.app T x)
    naturality := by
      intro T U f
      ext x
      change @Mul.mul _ (g.group U).toMul
        (((fst (groupSpaceProjection A) (groupSpaceProjection A)).hom.hom.app U)
          ((product (groupSpaceProjection A) (groupSpaceProjection A)).obj.obj.map f x))
        (((snd (groupSpaceProjection A) (groupSpaceProjection A)).hom.hom.app U)
          ((product (groupSpaceProjection A) (groupSpaceProjection A)).obj.obj.map f x)) =
        A.obj.obj.map f (@Mul.mul _ (g.group T).toMul
          (((fst (groupSpaceProjection A) (groupSpaceProjection A)).hom.hom.app T) x)
          (((snd (groupSpaceProjection A) (groupSpaceProjection A)).hom.hom.app T) x))
      rw [g.map_mul]
      congr 1
      · exact ConcreteCategory.congr_hom
          ((Limits.pullback.fst (groupSpaceProjection A).hom
            (groupSpaceProjection A).hom).hom.naturality f) x
      · exact ConcreteCategory.congr_hom
          ((Limits.pullback.snd (groupSpaceProjection A).hom
            (groupSpaceProjection A).hom).hom.naturality f) x }⟩

/-- A map is a homomorphism for the given, rather than an unspecified, group structures.
Source: Milne I Section 9 (blueprint: def-sfb-abelian-space-poincare-data). -/
def IsHom {A D : AlgebraicSpace S} (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D) (a : A ⟶ D) : Prop :=
  (∀ T : (Over S)ᵒᵖ, a.hom.hom.app T (@One.one _ (g.group T).toOne) =
    @One.one _ (h.group T).toOne) ∧
    ∀ (T : (Over S)ᵒᵖ) (x y : A.obj.obj.obj T),
      a.hom.hom.app T (@Mul.mul _ (g.group T).toMul x y) =
        @Mul.mul _ (h.group T).toMul (a.hom.hom.app T x) (a.hom.hom.app T y)

/-- Products with their product identity section.
Source: Milne I Sections 8--9 (blueprint: def-sfb-abelian-space-poincare-data). -/
def pointedProduct {B : AlgebraicSpace S} (A D : Pointed B) : Pointed B where
  X := product A.p D.p
  p := fst A.p D.p ≫ A.p
  e := pair A.e D.e (by rw [A.section_eq, D.section_eq])
  section_eq := by
    apply ObjectProperty.hom_ext
    dsimp [pair, fst]
    rw [← Category.assoc, Limits.pullback.lift_fst]
    exact congrArg (fun f ↦ f.hom) A.section_eq

/-- Every map to the represented base is the structural map.
Source: Stacks 025Y and Yoneda (blueprint: def-sfb-abelian-space-poincare-data).
Proof: on each scheme test an element of the represented base is a scheme map to S
whose composite with the identity is the test's structure map, so it is uniquely that
structure map. Equality on all tests is equality of natural transformations. -/
theorem baseMap_eq {X : AlgebraicSpace S} (a b : X ⟶ groupSpaceBase S) : a = b := by
  sorry

/-- The canonical product map over the represented base.
Source: Stacks 02X2 (blueprint: def-sfb-abelian-space-poincare-data). -/
def productMap (A D E F : Pointed (groupSpaceBase S)) (a : A.X ⟶ E.X)
    (b : D.X ⟶ F.X) : product A.p D.p ⟶ product E.p F.p :=
  pair (fst A.p D.p ≫ a) (snd A.p D.p ≫ b) (baseMap_eq _ _)

/-- The axes in a base change are precisely the pullbacks of the original axes, using
only the specified module compositors and multiplication unit comparison.
Source: Milne I Section 8, Remark 8.7(b)
(blueprint: def-sfb-abelian-space-poincare-data). -/
def IsBaseChangedAxes {B B' : AlgebraicSpace S} (A D : Pointed B) (g : B' ⟶ B)
    (P : (product A.p D.p).SmallModules) (r : Axes A D P)
    (s : Axes (A.baseChange g) (D.baseChange g)
      ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj P)) : Prop :=
  (∃ w : leftAxis (A.baseChange g) (D.baseChange g) ≫ baseChangeProductMap A D g =
      D.baseChangeMap g ≫ leftAxis A D,
    s.left = rigidificationPullback (leftAxis A D)
      (leftAxis (A.baseChange g) (D.baseChange g)) (D.baseChangeMap g)
      (baseChangeProductMap A D g) w P r.left) ∧
  (∃ w : rightAxis (A.baseChange g) (D.baseChange g) ≫ baseChangeProductMap A D g =
      A.baseChangeMap g ≫ rightAxis A D,
    s.right = rigidificationPullback (rightAxis A D)
      (rightAxis (A.baseChange g) (D.baseChange g)) (A.baseChangeMap g)
      (baseChangeProductMap A D g) w P r.right)

/-- A normalized comparison and its compatibility with every locally Noetherian
base change. The actual comparison after pullback is the image of the original iso;
uniqueness in AxisEquivalent identifies it with the target's normalized comparison.
Source: Milne I Sections 8--9; Deligne Section 4.1
(blueprint: def-sfb-abelian-space-poincare-data). -/
def CanonicalAxisEquivalent {B : AlgebraicSpace S} (A D : Pointed B)
    (L M : (product A.p D.p).SmallModules) : Prop :=
  AxisEquivalent A D L M ∧
    ∀ (T : Over S) [IsLocallyNoetherian T.left] (g : schemeSpace T ⟶ B),
      AxisEquivalent (A.baseChange g) (D.baseChange g)
        ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj L)
        ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj M) ∧
      ∀ (r : Axes A D L) (s : Axes A D M) (v : L ≅ M), PreservesAxes r s v →
        ∀ (r' : Axes (A.baseChange g) (D.baseChange g)
            ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj L))
          (s' : Axes (A.baseChange g) (D.baseChange g)
            ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj M)),
          IsBaseChangedAxes A D g L r r' → IsBaseChangedAxes A D g M s s' →
            PreservesAxes r' s'
              ((smallModuleTensorPullback (baseChangeProductMap A D g)).mapIso v)

/-- Biadditivity on the two actual triple products, with normalization on both axes.
Source: Milne I Sections 8--9 (blueprint: def-sfb-abelian-space-poincare-data). -/
def Biadditive (A D : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D)
    (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules) : Prop :=
  CanonicalAxisEquivalent
    (pointedProduct (pointedGroup A g) (pointedGroup A g)) (pointedGroup D h)
    ((smallModuleTensorPullback (productMap
      (pointedProduct (pointedGroup A g) (pointedGroup A g)) (pointedGroup D h)
      (pointedGroup A g) (pointedGroup D h) (addition A g) (𝟙 D))).obj P)
    (((smallModuleTensorPullback (productMap
      (pointedProduct (pointedGroup A g) (pointedGroup A g)) (pointedGroup D h)
      (pointedGroup A g) (pointedGroup D h)
      (fst (groupSpaceProjection A) (groupSpaceProjection A)) (𝟙 D))).obj P) ⊗
      ((smallModuleTensorPullback (productMap
        (pointedProduct (pointedGroup A g) (pointedGroup A g)) (pointedGroup D h)
        (pointedGroup A g) (pointedGroup D h)
        (snd (groupSpaceProjection A) (groupSpaceProjection A)) (𝟙 D))).obj P)) ∧
  CanonicalAxisEquivalent
    (pointedGroup A g) (pointedProduct (pointedGroup D h) (pointedGroup D h))
    ((smallModuleTensorPullback (productMap
      (pointedGroup A g) (pointedProduct (pointedGroup D h) (pointedGroup D h))
      (pointedGroup A g) (pointedGroup D h) (𝟙 A) (addition D h))).obj P)
    (((smallModuleTensorPullback (productMap
      (pointedGroup A g) (pointedProduct (pointedGroup D h) (pointedGroup D h))
      (pointedGroup A g) (pointedGroup D h)
      (𝟙 A) (fst (groupSpaceProjection D) (groupSpaceProjection D)))).obj P) ⊗
      ((smallModuleTensorPullback (productMap
        (pointedGroup A g) (pointedProduct (pointedGroup D h) (pointedGroup D h))
        (pointedGroup A g) (pointedGroup D h)
        (𝟙 A) (snd (groupSpaceProjection D) (groupSpaceProjection D)))).obj P))

/-- The displayed four-factor difference family, with the literal internal dual.
The last factor is pullback along q followed by the identity section; the canonical
compositor identifies it with q-star e-star L.
Source: Milne I Section 8, p.40 (blueprint: def-sfb-abelian-space-poincare-data). -/
def difference (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (L : A.SmallModules) : (product (groupSpaceProjection A)
        (groupSpaceProjection A)).SmallModules :=
  (((smallModuleTensorPullback (addition A g)).obj L ⊗
    (smallModuleTensorPullback
      (fst (groupSpaceProjection A) (groupSpaceProjection A))).obj (dual A L)) ⊗
    (smallModuleTensorPullback
      (snd (groupSpaceProjection A) (groupSpaceProjection A))).obj (dual A L)) ⊗
    (smallModuleTensorPullback
      (fst (groupSpaceProjection A) (groupSpaceProjection A) ≫
        groupSpaceProjection A ≫ g.identity)).obj L

/-- The literal normalized universal-family comparison for the difference family.
Source: Milne I Section 8, p.40 (blueprint: def-sfb-abelian-space-poincare-data). -/
def ClassifiesDifference (A D : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D)
    (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules)
    (L : A.SmallModules) (phi : A ⟶ D) : Prop :=
  AxisEquivalent (pointedGroup A g) (pointedGroup A g) (difference A g L)
    ((smallModuleTensorPullback (productMap
      (pointedGroup A g) (pointedGroup A g)
      (pointedGroup A g) (pointedGroup D h) (𝟙 A) phi)).obj P)

/-- The normalized difference classifies exactly one homomorphism; restriction at x is
precisely the translated line divided by L with its identity-line normalization.
The displayed isomorphism itself commutes with base change.
Source: Milne I Section 8, p.40 (blueprint: def-sfb-abelian-space-poincare-data). -/
def DifferenceHomomorphisms (A D : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D)
    (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules) : Prop :=
  ∀ L : A.SmallModules, IsLine A L →
    ∃ phi : A ⟶ D, IsHom g h phi ∧
      (∀ psi : A ⟶ D, ClassifiesDifference A D g h P L psi ↔ psi = phi) ∧
      CanonicalAxisEquivalent (pointedGroup A g) (pointedGroup A g) (difference A g L)
        ((smallModuleTensorPullback (productMap
          (pointedGroup A g) (pointedGroup A g)
          (pointedGroup A g) (pointedGroup D h) (𝟙 A) phi)).obj P)

/-- A proposed dual map identifies the two specified pullbacks of universal lines,
with both identity-axis normalizations.
Source: Milne I Section 9, p.41 (blueprint: def-sfb-abelian-space-poincare-data). -/
def Dualizes (A D B E : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D) (gB : CommutativeSpaceGroup B)
    (gE : CommutativeSpaceGroup E)
    (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules)
    (Q : (product (groupSpaceProjection B) (groupSpaceProjection E)).SmallModules)
    (a : A ⟶ B) (b : E ⟶ D) : Prop :=
  AxisEquivalent (pointedGroup A g) (pointedGroup E gE)
    ((smallModuleTensorPullback (productMap
      (pointedGroup A g) (pointedGroup E gE)
      (pointedGroup B gB) (pointedGroup E gE) a (𝟙 E))).obj Q)
    ((smallModuleTensorPullback (productMap
      (pointedGroup A g) (pointedGroup E gE)
      (pointedGroup A g) (pointedGroup D h) (𝟙 A) b)).obj P)

/-- Pullback defines the unique dual homomorphism. Its normalized universal-line
isomorphism is preserved by base change. Both duals are arbitrary representing data.
Source: Milne I Section 9, p.41 (blueprint: def-sfb-abelian-space-poincare-data). -/
def DualHomomorphisms (A D : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (h : CommutativeSpaceGroup D)
    (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules) : Prop :=
  ∀ (B E : AlgebraicSpace S) (gB : CommutativeSpaceGroup B) (gE : CommutativeSpaceGroup E)
    (Q : (product (groupSpaceProjection B) (groupSpaceProjection E)).SmallModules)
    (rQ : Axes (pointedGroup B gB) (pointedGroup E gE) Q),
    IsAbelianFamily (groupSpaceProjection B) → IsAbelianFamily (groupSpaceProjection E) →
    Represents (pointedGroup B gB) (pointedGroup E gE) Q rQ →
    ∀ a : A ⟶ B, IsHom g gB a →
      ∃ aDual : E ⟶ D, IsHom gE h aDual ∧
        (∀ b : E ⟶ D, Dualizes A D B E g h gB gE P Q a b ↔ b = aDual) ∧
        CanonicalAxisEquivalent (pointedGroup A g) (pointedGroup E gE)
          ((smallModuleTensorPullback (productMap
            (pointedGroup A g) (pointedGroup E gE)
            (pointedGroup B gB) (pointedGroup E gE) a (𝟙 E))).obj Q)
          ((smallModuleTensorPullback (productMap
            (pointedGroup A g) (pointedGroup E gE)
            (pointedGroup A g) (pointedGroup D h) (𝟙 A) aDual)).obj P)

/-- The dual and its universal line after any locally Noetherian scheme base change,
including every geometric fibre. The line and both rigidifications are the actual
pullbacks; normalized comparisons with any other dual are unique. Thus identity and
iterated-base-change comparisons coincide, including their universal-line maps.
Source: Deligne Section 4.1; Milne I Section 8, Remark 8.7
(blueprint: def-sfb-abelian-space-poincare-data). -/
def UniversalBaseChange {B : AlgebraicSpace S} (A D : Pointed B)
    (P : (product A.p D.p).SmallModules) (r : Axes A D P) : Prop :=
  ∀ (T : Over S) [IsLocallyNoetherian T.left] (g : schemeSpace T ⟶ B),
    IsAbelianFamily (A.baseChange g).p ∧ IsAbelianFamily (D.baseChange g).p ∧
      RigidAutomorphisms (A.baseChange g) ∧
      ∃ s : Axes (A.baseChange g) (D.baseChange g)
          ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj P),
        IsBaseChangedAxes A D g P r s ∧
        Represents (A.baseChange g) (D.baseChange g)
          ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj P) s ∧
        ComparisonCoherence (A.baseChange g) (D.baseChange g)
          ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj P) s

end AlgebraicGeometry.AlgebraicSpace.Poincare
