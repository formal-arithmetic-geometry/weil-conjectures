/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.CondensedLisseDualOperations
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.DeligneLaumon.FiniteToCondensedSmoothAdjunctionTransport

/-! # Lisse dual cohomology with condensed coefficients

Source: latest blueprint, thm-a1-curve-perverse-heart.proof.md, Step 2
(blueprint: def-per-condensed-lisse-duality-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseDual

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- The existing full bounded constructible subcategory.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
abbrev BC (T : Scheme.{u}) := ConstantModelBoundedConstructible (c.obj ell) T

/-- The existing localizing closure, without a completeness condition.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
abbrev loc (T : Scheme.{u}) := localizingClosureProEtale (c.obj ell) T

/-- All bounded constructible complexes whose cohomology sheaves are lisse.
This is a full subcategory, so the comparisons below include naturality in all maps.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def lisseProperty (T : Scheme.{u}) : ObjectProperty (D ell c T) :=
  constantModelBoundedConstructible (c.obj ell) T ⊓ fun K ↦
    ∀ n : ℤ, IsLisseCoefficientModule (c.obj ell)
      ((DerivedCategory.homologyFunctor (Modules ell c T) n).obj K)

/-- Smooth separated finite-type spaces, including the empty scheme; the dimension
can be either zero or one. The compactification is arbitrary presentation data for
compact support, as in the statement, rather than an added geometric assumption.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
structure Space (k : Type u) [Field k] where
  scheme : Scheme.{u}
  map : scheme ⟶ Spec (.of k)
  dim : Fin 2
  [smooth : SmoothOfRelativeDimension dim.val map]
  [finiteType : LocallyOfFiniteType map]
  [quasiCompact : QuasiCompact map]
  [separated : IsSeparated map]
  compactification : Compactification map

attribute [instance] Space.smooth Space.finiteType Space.quasiCompact Space.separated

/-- The actual compact-support composite restricted to the specified localizing
categories; membership is proof data only.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def support {k : Type u} [Field k] (T : Space k)
    (h : ∀ K, loc ell c T.scheme K → loc ell c (Spec (.of k))
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).obj K)) :
    (loc ell c T.scheme).FullSubcategory ⥤ (loc ell c (Spec (.of k))).FullSubcategory :=
  (loc ell c (Spec (.of k))).lift
    ((loc ell c T.scheme).ι ⋙ CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) T.compactification) (fun K ↦ h K.obj K.property)

/-- Right-adjoint data for the actual compact-support functor. The coefficient unit
belongs to the localizing category, so its exceptional inverse image is defined.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
structure AdjointData {k : Type u} [Field k] (T : Space k) where
  support_mem : ∀ K, loc ell c T.scheme K → loc ell c (Spec (.of k))
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) T.compactification).obj K)
  exceptional : (loc ell c (Spec (.of k))).FullSubcategory ⥤
    (loc ell c T.scheme).FullSubcategory
  adjunction : support ell c T support_mem ⊣ exceptional
  unit_mem : loc ell c (Spec (.of k)) (𝟙_ (D ell c (Spec (.of k))))

/-- The dualizing object is the value of the right adjoint on the coefficient unit.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def AdjointData.omega {k : Type u} [Field k] {T : Space k} (A : AdjointData ell c T) :
    D ell c T.scheme :=
  (A.exceptional.obj ⟨𝟙_ _, A.unit_mem⟩).obj

/-- Verdier duality uses the actual internal Hom with the exceptional coefficient unit.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def AdjointData.dual {k : Type u} [Field k] {T : Space k} (A : AdjointData ell c T) :
    (D ell c T.scheme)ᵒᵖ ⥤ D ell c T.scheme :=
  (CondensedRing.derivedHom (c.obj ell) T.scheme).flip.obj (A.omega ell c)


/-- The two sides of the cohomology formula, as functors on the full lisse subcategory.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def dualCohomology {k : Type u} [Field k] {T : Space k}
    (A : AdjointData ell c T) (a : ℤ) :=
  (lisseProperty ell c T.scheme).ι.op ⋙ A.dual ell c ⋙
    DerivedCategory.homologyFunctor (Modules ell c T.scheme) a

/-- The source cohomology has index -2d-a, with the cohomological shift convention.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def reversedCohomology {k : Type u} [Field k] (T : Space k) (a : ℤ) :=
  ((lisseProperty ell c T.scheme).ι ⋙
    DerivedCategory.homologyFunctor (Modules ell c T.scheme) (-2 * (T.dim.val : ℤ) - a)).op ⋙
      linearDualTwist ell c T.scheme T.dim.val

/-- The canonical closed-functor comparison followed by the specified comparison
of dualizing objects. Its formula fixes the arrow, rather than postulating an
arbitrary isomorphism between the two derived objects.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def restrictionMap {k : Type u} [Field k] {V T : Space k}
    (AV : AdjointData ell c V) (AT : AdjointData ell c T) (j : V.scheme ⟶ T.scheme)
    (e : (pull ell c j).obj (AT.omega ell c) ≅ AV.omega ell c) (M : D ell c T.scheme) :
    (pull ell c j).obj ((AT.dual ell c).obj (op M)) ⟶
      (AV.dual ell c).obj (op ((pull ell c j).obj M)) :=
  (Functor.LaxMonoidal.ihomComparison (pull ell c j) M).natTrans.app (AT.omega ell c) ≫
    (ihom ((pull ell c j).obj M)).map e.hom

/-- The smooth-purity trace is the counit at the coefficient unit, precomposed
with purity. This equation makes the normalization below about the actual adjunction.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def purityTrace {k : Type u} [Field k] {T : Space k} (A : AdjointData ell c T)
    (p : A.omega ell c ≅ c.derivedLine
      ell T.scheme T.dim.val) :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj ell) T.compactification).map p.inv ≫
      (A.adjunction.counit.app ⟨𝟙_ _, A.unit_mem⟩).hom

/-- The canonical unit comparison for the existing twisted inverse image.
The tensor unit is compared by its strong monoidal structure before applying
purity; this retains the actual domain of the normalized finite trace.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def smoothUnit (s : GeneralFieldSmoothTransport.Index.{u} ell) :
    (c.smoothSource ell s.f s.dim.val).obj (𝟙_ _) ≅
      c.derivedLine ell s.X.left s.dim.val :=
  tensorIso
      (Functor.Monoidal.εIso
        (CondensedRing.upperStar (c.obj ell) s.f).leftDerivedFunctor).symm
      (Iso.refl _) ≪≫ λ_ _

/-- The transported normalized trace, with both the source pullback-unit and
coefficient-unit presentation isomorphisms inserted explicitly.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def transportedTrace (N : GeneralFieldSmoothTransport.Family.{u} ell)
    (s : GeneralFieldSmoothTransport.Index.{u} ell)
    (U : c.ctf ell s.Y.left) (e : U.obj ≅ 𝟙_ _) :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj ell) s.compactification).map
      ((smoothUnit ell c s).inv ≫
        (c.smoothSource ell s.f s.dim.val).map e.inv) ≫
      (N c s).trace ell U ≫ e.hom

/-- An orientation is normalized by precisely the existing finite diagonal/DNC
traces and their scalar transport. Equality is in the actual ambient derived category;
HEq only transports the named geometric index and coefficient-unit presentation.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def Normalized {k : Type u} [Field k]
    (A : ∀ T : Space k, AdjointData ell c T)
    (p : ∀ T : Space k, (A T).omega ell c ≅
      c.derivedLine ell T.scheme T.dim.val) : Prop :=
  ∃ N : GeneralFieldSmoothTransport.Family.{u} ell,
    GeneralFieldSmoothTransport.FiniteNormalized ell N ∧
    GeneralFieldSmoothTransport.Scalars ell N ∧
    GeneralFieldSmoothTransport.Isomorphisms ell N ∧
    ∀ T : Space k, ∃ s : GeneralFieldSmoothTransport.Index.{u} ell,
      s.base.carrier = k ∧ s.X.left = T.scheme ∧ s.Y.left = Spec (.of k) ∧
      HEq s.f T.map ∧ s.dim = T.dim ∧ HEq s.compactification T.compactification ∧
      ∃ (U : c.ctf ell s.Y.left) (e : U.obj ≅ 𝟙_ _),
        HEq (purityTrace ell c (A T) (p T)) (transportedTrace ell c N s U e)

/-- A component of the natural cohomology comparison, with its two cohomology
objects written explicitly. This is only evaluation of the given natural map.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def cohomologyMap {k : Type u} [Field k] {T : Space k} (A : AdjointData ell c T)
    (a : ℤ) (e : dualCohomology ell c A a ≅ reversedCohomology ell c T a)
    (M : (lisseProperty ell c T.scheme).FullSubcategory) :
    (DerivedCategory.homologyFunctor (Modules ell c T.scheme) a).obj
        ((A.dual ell c).obj (op M.obj)) ⟶
      (linearDualTwist ell c T.scheme T.dim.val).obj
        (op ((DerivedCategory.homologyFunctor (Modules ell c T.scheme)
          (-2 * (T.dim.val : ℤ) - a)).obj M.obj)) :=
  e.hom.app (op M)

/-- The type of smooth-purity isomorphisms for the supplied actual adjoints.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
abbrev PurityComparisons {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T) :=
  ∀ T : Space k, (adjoints T).omega ell c ≅
    c.derivedLine ell T.scheme T.dim.val

/-- The type of natural cohomology isomorphisms on the full lisse subcategories.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
abbrev CohomologyComparisons {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T) :=
  ∀ (T : Space k) (a : ℤ),
    dualCohomology ell c (adjoints T) a ≅ reversedCohomology ell c T a

/-- The type of dualizing-object comparisons for compatible open maps.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
abbrev OpenDualizingComparisons {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T) :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j],
    (∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) →
      ((pull ell c j).obj ((adjoints T).omega ell c) ≅ (adjoints V).omega ell c)

/-- DualLisse clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def DualLisse {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T) : Prop :=
  ∀ (T : Space k) (M : (lisseProperty ell c T.scheme).FullSubcategory) (a : ℤ),
    IsLisseCoefficientModule (c.obj ell)
      ((DerivedCategory.homologyFunctor (Modules ell c T.scheme) a).obj
        (((adjoints T).dual ell c).obj (op M.obj)))

/-- DualVanishing clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def DualVanishing {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T) : Prop :=
  ∀ (T : Space k) (M : (lisseProperty ell c T.scheme).FullSubcategory) (a : ℤ),
    IsZero ((DerivedCategory.homologyFunctor (Modules ell c T.scheme) a).obj
        (((adjoints T).dual ell c).obj (op M.obj))) ↔
      IsZero ((DerivedCategory.homologyFunctor (Modules ell c T.scheme)
        (-2 * (T.dim.val : ℤ) - a)).obj M.obj)

/-- OpenNormalized clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def OpenNormalized {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T)
    (purity : PurityComparisons ell c adjoints)
    (openOmega : OpenDualizingComparisons ell c adjoints) : Prop :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (q : PurityTransport.LinePullCoordinates ell c j),
    V.dim = T.dim →
    HEq ((openOmega V T j hj).hom ≫ (purity V).hom)
      ((pull ell c j).map (purity T).hom ≫
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (c.obj ell) j).inv.app _ ≫ (q.derived ell T.dim.val).hom)

/-- OpenComposition clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def OpenComposition {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T)
    (openOmega : OpenDualizingComparisons ell c adjoints) : Prop :=
  ∀ (W V T : Space k) (i : W.scheme ⟶ V.scheme)
    (j : V.scheme ⟶ T.scheme) [IsOpenImmersion i] [IsOpenImmersion j]
    (hi : ∃ b : Spec (.of k) ≅ Spec (.of k), i ≫ V.map = W.map ≫ b.hom)
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (hij : ∃ b : Spec (.of k) ≅ Spec (.of k), (i ≫ j) ≫ T.map = W.map ≫ b.hom),
    (pullComp ell c i j).hom.app ((adjoints T).omega ell c) ≫
        (pull ell c i).map (openOmega V T j hj).hom ≫ (openOmega W V i hi).hom =
      (openOmega W T (i ≫ j) hij).hom

/-- OpenLisse clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def OpenLisse (k : Type u) [Field k] : Prop :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
    (M : (lisseProperty ell c T.scheme).FullSubcategory),
    lisseProperty ell c V.scheme ((pull ell c j).obj M.obj)

/-- OpenIsomorphism clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def OpenIsomorphism {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T)
    (openOmega : OpenDualizingComparisons ell c adjoints) : Prop :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (M : BC ell c T.scheme),
    IsIso (restrictionMap ell c (adjoints V) (adjoints T) j (openOmega V T j hj) M.obj)

/-- OpenNaturality clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def OpenNaturality {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T)
    (openOmega : OpenDualizingComparisons ell c adjoints) : Prop :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (M N : BC ell c T.scheme) (f : M ⟶ N),
    (pull ell c j).map (((adjoints T).dual ell c).map f.hom.op) ≫
        restrictionMap ell c (adjoints V) (adjoints T) j (openOmega V T j hj) M.obj =
      restrictionMap ell c (adjoints V) (adjoints T) j (openOmega V T j hj) N.obj ≫
        ((adjoints V).dual ell c).map ((pull ell c j).map f.hom).op

/-- The coefficient-parametric right-hand composite of the equivariance square.
It is ordinary pullback of the duality comparison, then the evaluation-defined
line comparison, then contravariance in the cohomology pullback map.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def coefficientCohomologySide (c : PurityTransport.Coefficient ell)
    {V T : Scheme.{u}} (j : V ⟶ T) (q : PurityTransport.LinePullCoordinates ell c j)
    (d : ℕ)
    (P M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T))
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (c.obj ell) V))
    (g : P ⟶ (coefficientLinearDual ell c T d).obj (op M))
    (h : N ⟶ (CondensedRing.upperStar (c.obj ell) j).obj M) :
    (CondensedRing.upperStar (c.obj ell) j).obj P ⟶
      (coefficientLinearDual ell c V d).obj (op N) :=
  (CondensedRing.upperStar (c.obj ell) j).map g ≫
    coefficientLinearPull ell c j q d M ≫
    (coefficientLinearDual ell c V d).map h.op

/-- Restrict duality, take cohomology, and apply the comparison on the open.
This is the left-hand composite of the equivariance square.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def cohomologyRestrictionSide {k : Type u} [Field k] {V T : Space k}
    (AV : AdjointData ell c V) (AT : AdjointData ell c T) (j : V.scheme ⟶ T.scheme)
    (e : (pull ell c j).obj (AT.omega ell c) ≅ AV.omega ell c)
    (M : D ell c T.scheme) (hM : lisseProperty ell c V.scheme ((pull ell c j).obj M))
    (a : ℤ) (cV : dualCohomology ell c AV a ≅ reversedCohomology ell c V a) :=
  (cohomPull ell c j a).hom.app ((AT.dual ell c).obj (op M)) ≫
    (DerivedCategory.homologyFunctor (Modules ell c V.scheme) a).map
      (restrictionMap ell c AV AT j e M) ≫
    cohomologyMap ell c AV a cV ⟨(pull ell c j).obj M, hM⟩

/-- Specialization of the coefficient-parametric composite to the actual
cohomology objects and their published exact-inverse-image comparison.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def cohomologyDualSide {k : Type u} [Field k] {V T : Space k}
    (AT : AdjointData ell c T) (j : V.scheme ⟶ T.scheme)
    (q : PurityTransport.LinePullCoordinates ell c j)
    (M : (lisseProperty ell c T.scheme).FullSubcategory) (a : ℤ)
    (cT : dualCohomology ell c AT a ≅ reversedCohomology ell c T a) :
    (CondensedRing.upperStar (c.obj ell) j).obj
        ((DerivedCategory.homologyFunctor (Modules ell c T.scheme) a).obj
          ((AT.dual ell c).obj (op M.obj))) ⟶
      (coefficientLinearDual ell c V.scheme T.dim.val).obj
        (op ((DerivedCategory.homologyFunctor (Modules ell c V.scheme)
          (-2 * (T.dim.val : ℤ) - a)).obj ((pull ell c j).obj M.obj))) :=
  coefficientCohomologySide ell c j q T.dim.val
    ((DerivedCategory.homologyFunctor (Modules ell c T.scheme) a).obj
      ((AT.dual ell c).obj (op M.obj)))
    ((DerivedCategory.homologyFunctor (Modules ell c T.scheme)
      (-2 * (T.dim.val : ℤ) - a)).obj M.obj)
    ((DerivedCategory.homologyFunctor (Modules ell c V.scheme)
      (-2 * (T.dim.val : ℤ) - a)).obj ((pull ell c j).obj M.obj))
    (cohomologyMap ell c AT a cT M)
    (cohomPullBack ell c j (-2 * (T.dim.val : ℤ) - a) M.obj)

/-- CohomologyEquivariant clause of the condensed lisse duality assertion.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def CohomologyEquivariant {k : Type u} [Field k]
    (adjoints : ∀ T : Space k, AdjointData ell c T)
    (cohomology : CohomologyComparisons ell c adjoints)
    (openOmega : OpenDualizingComparisons ell c adjoints) : Prop :=
  ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme)
    [IsOpenImmersion j]
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (q : PurityTransport.LinePullCoordinates ell c j)
    (M : (lisseProperty ell c T.scheme).FullSubcategory)
    (hM : lisseProperty ell c V.scheme ((pull ell c j).obj M.obj)) (a : ℤ),
    V.dim = T.dim →
    HEq
      (cohomologyRestrictionSide ell c (adjoints V) (adjoints T) j
        (openOmega V T j hj) M.obj hM a (cohomology V a))
      (cohomologyDualSide ell c (adjoints T) j q M a (cohomology T a))

/-- All clauses of condensed lisse duality, with the actual adjunction and
canonical-map witnesses existentially quantified. Open restriction has no lisse
hypothesis. Compatible semilinear isomorphisms include geometric Frobenius.
Source: Step 2 (blueprint: def-per-condensed-lisse-duality-comparisons). -/
def Comparisons (k : Type u) [Field k] : Prop :=
  ∃ adjoints : (∀ T : Space k, AdjointData ell c T),
  ∃ purity : PurityComparisons ell c adjoints,
    Normalized ell c adjoints purity ∧
  ∃ cohomology : CohomologyComparisons ell c adjoints,
    DualLisse ell c adjoints ∧ DualVanishing ell c adjoints ∧
  ∃ openOmega : OpenDualizingComparisons ell c adjoints,
    OpenNormalized ell c adjoints purity openOmega ∧
    OpenComposition ell c adjoints openOmega ∧ OpenLisse ell c k ∧
    OpenIsomorphism ell c adjoints openOmega ∧ OpenNaturality ell c adjoints openOmega ∧
    CohomologyEquivariant ell c adjoints cohomology openOmega

end AlgebraicGeometry.ProEtale.CondensedLisseDual
