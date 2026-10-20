/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Interfaces for coefficient projection cocycles

Source: Stacks Project, Cohomology on Sites, Tags 07A7 and 0E47; Tags 0D6D,
0D6E and 07A6 for the canonical comparisons and adjunctions
(blueprint: def-pur-ringed-coefficient-projection-data).

The auxiliary records present the specified geometric operations, comparison and
unit maps. Ordinary insertion and K-flat computation fix all comparisons; the
cocycle is a conclusion, never part of the input. The same assertion is stated
on the actual vertical sequence sites, before evaluation or derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open scoped ChangeOfRings

namespace SheafOfModules.RingedCoefficientProjection

open WeilConjectures.SemilinearSections (Mod D)

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedComposeRings (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedComposeSets (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r}) := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedComposeModules (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{r}) := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedSheafifyModules (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{r} := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedWeakSheafifyModules (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{r} := inferInstance

/-- Cache an already inferred sheaf instance on an essentially small site.
Source: Mathlib site transport and sheafification instances. The proof is typeclass inference.
(blueprint: def-pur-ringed-coefficient-projection-data). -/
instance (priority := 100000) cachedLocalEquivalences (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{r} := inferInstance

/-- The existing underlying set-sheaf functor, used to normalize scalar insertion.
Source: Stacks 03D7 (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev underlying (R : Sheaf J CommRingCat.{r}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

/-- Presentations of all K-flat derived scalar extensions on this site.
Source: Stacks 06YY (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Scalars (J : GrothendieckTopology C) :=
  ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    _root_.SheafOfModules.SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a

/-- The normalized unit insertion into the recorded ordinary scalar extension.
Source: Stacks 07A6 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def insertion {p : Scalars.{c, v, r} J}
    (n : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := J) p)
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R) :
    (underlying R).obj M ⟶ (underlying S).obj ((p a).ordinary.obj M) :=
  (underlying R).map ((n.ordinaryAdjunction a).unit.app M)

/-- The canonical K-flat computation arrow of the recorded universal derived pair.
Source: Stacks 06YY (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev computation {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : _root_.SheafOfModules.SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a)
    (P : CochainComplex (Mod J R) ℤ) :=
  derivedPullbackComplexComparison p.ordinary p.derived p.counit P

/-- A presentation of the geometric inverse images and their actual module adjunctions.
The ring maps and module operations are transported by AlgebraicInverseImage. The
underlying unit fixes the ordinary adjunction; its canonical derived adjunction is
used below. These are presentation witnesses for the operations of the statement.
Source: Stacks 03D7, 07A6 (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure Geometry
    (uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)) (adj : uInv ⊣ uPush) where
  rings : Sheaf J CommRingCat.{r} ⥤ Sheaf K CommRingCat.{r}
  inverse : ∀ R : Sheaf J CommRingCat.{r}, AlgebraicInverseImage uInv R (rings.obj R)
  rings_naturality : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a) ≫
        (inverse S).ringUnderlying.hom =
      (inverse R).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map (rings.map a)
  [inverseAdditive : ∀ R, (inverse R).modules.Additive]
  [inverseLimits : ∀ R, PreservesFiniteLimits (inverse R).modules]
  [inverseColimits : ∀ R, PreservesFiniteColimits (inverse R).modules]
  push : ∀ R : Sheaf J CommRingCat.{r}, Mod K (rings.obj R) ⥤ Mod J R
  [pushAdditive : ∀ R, (push R).Additive]
  [kInjective : ∀ R : Sheaf J CommRingCat.{r},
    Abelian.HasKInjectiveResolutions (Mod K (rings.obj R))]
  ordinaryAdjunction : ∀ R, (inverse R).modules ⊣ push R
  pushUnderlying : ∀ R,
    push R ⋙ underlying R ≅ underlying (rings.obj R) ⋙ uPush
  unit_underlying : ∀ (R : Sheaf J CommRingCat.{r}) (M : Mod J R),
    (underlying R).map ((ordinaryAdjunction R).unit.app M) ≫
        (pushUnderlying R).hom.app ((inverse R).modules.obj M) ≫
        uPush.map ((inverse R).moduleUnderlying.hom.app M) =
      adj.unit.app ((underlying R).obj M)

attribute [instance] Geometry.inverseAdditive Geometry.inverseLimits Geometry.inverseColimits
  Geometry.pushAdditive Geometry.kInjective

variable {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)

/-- Exact coefficient inverse image on ordinary unbounded derived categories.
Source: Stacks 07A6 (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Geometry.left (R : Sheaf J CommRingCat.{r}) := (g.inverse R).modules.mapDerivedCategory

/-- The actual K-injective derived module direct image.
Source: Stacks 0D6E (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Geometry.right (R : Sheaf J CommRingCat.{r}) := (g.push R).rightDerivedFunctor

/-- The canonical derived adjunction, with no independently chosen unit or counit.
Source: Stacks 07A6 (blueprint: def-pur-ringed-coefficient-projection-data). -/
abbrev Geometry.adjunction (R : Sheaf J CommRingCat.{r}) :=
  (g.ordinaryAdjunction R).mapDerivedCategoryRightDerivedAdjunction

variable {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
      (J := K) pX)

/-- The canonical inverse-image/scalar comparison. The ordinary insertion equation
fixes the inverse-image tensor map. Its derived comparison is fixed on common
flat-term K-flat representatives by the universal computation arrows.
Source: Stacks 0D6D, 0G7E (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure Comparisons where
  ordinary : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).ordinary ⋙ (g.inverse S).modules ≅
      (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary
  ordinary_insertion : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R),
    uInv.map (insertion nY a M) ≫
        (g.inverse S).moduleUnderlying.inv.app ((pY a).ordinary.obj M) ≫
        (underlying (g.rings.obj S)).map ((ordinary a).hom.app M) =
      (g.inverse R).moduleUnderlying.inv.app M ≫
        insertion nX (g.rings.map a) ((g.inverse R).modules.obj M)
  derived : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).derived ⋙ g.left S ≅ g.left R ⋙ (pX (g.rings.map a)).derived
  representative : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
    (derived a).hom.app (DerivedCategory.Q.obj P) ≫
        (pX (g.rings.map a)).derived.map
          ((g.inverse R).modules.mapDerivedCategoryFactors.hom.app P) ≫
        computation (pX (g.rings.map a))
          (((g.inverse R).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (g.left S).map (computation (pY a) P) ≫
        (g.inverse S).modules.mapDerivedCategoryFactors.hom.app
          (((pY a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinary a).hom (.up ℤ)).app P)

/-- Scalar multiplication is the coefficient-unit identification, on sheaves and
on K-flat representatives, rather than an arbitrary self-equivalence.
Source: Stacks 03EL, 0D6D (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure ScalarUnits {p : Scalars.{c, v, r} J} where
  ordinary : ∀ R : Sheaf J CommRingCat.{r}, (p (𝟙 R)).ordinary ≅ 𝟭 (Mod J R)
  multiplication : ∀ (R : Sheaf J CommRingCat.{r}) (M : Mod J R) (U : Cᵒᵖ)
    (s : R.obj.obj U) (x : M.val.obj U),
    ((ordinary R).hom.app M).val.app U
      (_root_.SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U s x) = s • x
  derived : ∀ R : Sheaf J CommRingCat.{r}, (p (𝟙 R)).derived ≅ 𝟭 (D J R)
  representative : ∀ (R : Sheaf J CommRingCat.{r}) (P : CochainComplex (Mod J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
    (derived R).hom.app (DerivedCategory.Q.obj P) =
      computation (p (𝟙 R)) P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinary R).hom (.up ℤ)).app P)

variable (e : Comparisons g nY nX)

/-- The specified coefficient projection is exactly the mate under the B-adjunction.
It is not assumed invertible. The mate formula gives the unit--comparison--counit
word, whose transpose is S_a applied to the A-counit after the comparison.
Source: Stacks 07A7 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def comparison {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.right R ⋙ (pY a).derived ⟶ (pX (g.rings.map a)).derived ⋙ g.right S :=
  (mateEquiv (g.adjunction R) (g.adjunction S)
    (TwoSquare.mk _ _ _ _ (e.derived a).hom)).natTrans

/-- Balanced associativity on X, including the functorial equality of inverse-image
ring maps. Source: Stacks 0D6D
(blueprint: def-pur-ringed-coefficient-projection-data). -/
def targetAssociator {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (pX (g.rings.map a)).derived ⋙ (pX (g.rings.map b)).derived ≅
      (pX (g.rings.map (a ≫ b))).derived :=
  nX.derived (g.rings.map a) (g.rings.map b) ≪≫
    eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_comp a b).symm)

/-- The successive comparison with both balanced identifications inserted.
Source: Stacks 0E47 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def successive {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : D K (g.rings.obj R)) :
    (pY (a ≫ b)).derived.obj ((g.right R).obj M) ⟶
      (g.right T).obj ((pX (g.rings.map (a ≫ b))).derived.obj M) :=
  (nY.derived a b).inv.app ((g.right R).obj M) ≫
    (pY b).derived.map ((comparison g nY nX e a).app M) ≫
    (comparison g nY nX e b).app ((pX (g.rings.map a)).derived.obj M) ≫
    (g.right T).map ((targetAssociator g nX a b).hom.app M)

/-- All equalities are in the changed coefficient category, with arbitrary derived
inputs. The commuting-square formula is also coefficient-map naturality of the
family, and explicitly retains the equality of the two composite ring maps.
Source: Stacks 0E47, 07A7 (blueprint: def-pur-ringed-coefficient-projection-data). -/
structure Laws (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) : Prop where
  cocycle : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : D K (g.rings.obj R)),
    (nY.derived a b).hom.app ((g.right R).obj M) ≫
        (comparison g nY nX e (a ≫ b)).app M =
      (pY b).derived.map ((comparison g nY nX e a).app M) ≫
        (comparison g nY nX e b).app ((pX (g.rings.map a)).derived.obj M) ≫
        (g.right T).map ((targetAssociator g nX a b).hom.app M)
  identity : ∀ (R : Sheaf J CommRingCat.{r}) (M : D K (g.rings.obj R)),
    (comparison g nY nX e (𝟙 R)).app M ≫
        (g.right R).map
          ((eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
            uX.derived (g.rings.obj R)).hom.app M) =
      (uY.derived R).hom.app ((g.right R).obj M)
  square : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ V) (a' : R ⟶ T) (b' : T ⟶ V)
    (h : a ≫ b = a' ≫ b') (M : D K (g.rings.obj R)),
    successive g nY nX e a b M ≫
        (g.right V).map (eqToHom
          (congrArg (fun f ↦ (pX (g.rings.map f)).derived.obj M) h)) =
      eqToHom (congrArg (fun f ↦ (pY f).derived.obj ((g.right R).obj M)) h) ≫
        successive g nY nX e a' b' M

/-- Canonical cochain shifts on the scalar functors are fixed by their universal
computation counits. The comparison, balanced associators, units, and the actual
projection mates commute with these shifts in their target coefficient categories.
Source: Stacks 07A6; direct signed-cochain calculation
(blueprint: def-pur-ringed-coefficient-projection-data). -/
structure ShiftLaws (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) where
  [scalarY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S), (pX a).derived.CommShift ℤ]
  canonicalY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pY a).counit ℤ
  canonicalX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pX a).counit ℤ
  inverseScalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (e.derived a).hom ℤ
  mate : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (comparison g nY nX e a) ℤ
  associatorY : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nY.derived a b).hom ℤ
  associatorX : ∀ {R S T : Sheaf K CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nX.derived a b).hom ℤ
  unitY : ∀ R : Sheaf J CommRingCat.{r}, NatTrans.CommShift (uY.derived R).hom ℤ
  unitX : ∀ R : Sheaf K CommRingCat.{r}, NatTrans.CommShift (uX.derived R).hom ℤ

/-- The full assertion on a pair of small sites; all presentations are quantified,
so none of the canonical comparisons can be replaced by an arbitrary isomorphism.
Source: Stacks 07A7, 0E47 (blueprint: def-pur-ringed-coefficient-projection-data). -/
def Assertion (J : GrothendieckTopology C) (K : GrothendieckTopology X) : Prop :=
  ∀ (uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)) (adj : uInv ⊣ uPush),
    PreservesFiniteLimits uInv →
    ∀ (g : Geometry uInv uPush adj)
      (pY : Scalars.{c, v, r} J) (pX : Scalars.{c, v, r} K)
      (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
        (J := J) pY)
      (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r, max c v (r + 1)}
        (J := K) pX),
    ∃ (e : Comparisons g nY nX) (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)),
      Laws g nY nX e uY uX ∧ Nonempty (ShiftLaws g nY nX e uY uX)

end SheafOfModules.RingedCoefficientProjection
