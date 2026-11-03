/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PodCondensedAutomorphismCompactExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SmoothPurity.WeilVerdierModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.CategoryTheory.NormalizedClosedExchange.NormalizedClosedAdjunctionExchange
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.Picard.WeilOperationsOrdinary
public import WeilConjectures.AlgebraicGeometry.Picard.WeilTruncationLift

/-! # Six operations on Weil complexes

Source: the node's `source.document`:
`literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-lefschetz-verdier/sec-frobenius/sec-purity-duality-and-frobenius/`
`sk-thm-frobenius/prop-weil-operations.md` and its five-step proof.
(blueprint: prop-weil-operations).

All operation carriers are the ordinary condensed module operations. The exchange
maps below are fixed constructions. A lift's structure is required to be that exchange
followed by the input structure. The compact-support dependency supplies the proper/open
exchange and its constructible exceptional mate, also for nonseparated schemes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v uA vA uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The full subcategory of fixed pairs with the specified carrier property. This is
exactly the full-subcategory presentation used by `condensedStrictWeilComplex`.
Source: prop-weil-operations, paragraph defining Weil pairs (blueprint: prop-weil-operations). -/
abbrev WOPairs {C : Type uC} [Category.{vC} C] (p : ObjectProperty C) (P : C ⥤ C) :=
  ObjectProperty.FullSubcategory (fun K : Endofunctor.IsoAlgebra P ↦ p K.carrier)

/-- Forget the pair and then its carrier restriction. Source: prop-weil-operations,
underlying-object clause (blueprint: prop-weil-operations). -/
def woForget {C : Type uC} [Category.{vC} C] (p : ObjectProperty C) (P : C ⥤ C) :
    WOPairs p P ⥤ C :=
  (ObjectProperty.ι _) ⋙ Endofunctor.IsoAlgebra.forget P

/-- A lift with a fixed structure arrow on each actual carrier. The equation transports
its output structure along the carrier comparison; it is not an existential exchange.
The natural isomorphism also fixes the action on every arrow.
Source: prop-weil-operations, exchange-then-theta and forgetting clauses
(blueprint: prop-weil-operations). -/
def WOCanonicalLift {A : Type uA} [Category.{vA} A]
    {C : Type uC} [Category.{vC} C] (p : ObjectProperty C) (P : C ⥤ C)
    (F : A ⥤ C) (θ : ∀ K : A, P.obj (F.obj K) ⟶ F.obj K) : Prop :=
  ∃ L : A ⥤ WOPairs p P, ∃ e : L ⋙ woForget p P ≅ F,
    ∀ K : A, P.map (e.hom.app K) ≫ θ K =
      (L.obj K).obj.str.hom ≫ e.hom.app K

/-- Preservation and the normalized lift of one specified operation and exchange.
Preservation is asserted for all constructible carriers, including those without a Weil
structure. Source: prop-weil-operations, six-operation preservation and lift clauses
(blueprint: prop-weil-operations). -/
def WOUnary {C : Type uC} [Category.{vC} C] {B : Type uD} [Category.{vD} B]
    (p : ObjectProperty C) (q : ObjectProperty B) (P : C ⥤ C) (Q : B ⥤ B)
    (F : C ⥤ B) (ex : F ⋙ Q ⟶ P ⋙ F) : Prop :=
  (∀ K : C, p K → q (F.obj K)) ∧ IsIso ex ∧
    WOCanonicalLift q Q (woForget p P ⋙ F)
      (fun K ↦ ex.app K.obj.carrier ≫ F.map K.obj.str.hom)

/-- The actual square for a specified raw comparison arrow, and its image under every
cohomology functor. Unlike a strict morphism's stored law, this predicate requires proving
that the supplied comparison arrow commutes with the supplied structures.
Source: prop-weil-operations, last sentence (blueprint: prop-weil-operations). -/
def WOEquivariant {C : Type uC} [Category.{vC} C] (P : C ⥤ C)
    {A B : C} (θA : P.obj A ⟶ A) (θB : P.obj B ⟶ B) (a : A ⟶ B) : Prop :=
  P.map a ≫ θB = θA ≫ a ∧
    ∀ ha : IsIso a, letI := ha
      P.map (inv a) ≫ θA = θB ≫ inv a

/-- The ordinary module derived category, with the pulled-back condensed ring.
Source: prop-weil-operations, coefficient paragraph (blueprint: prop-weil-operations). -/
abbrev WODerived (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

section Operations
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Canonical Frobenius-square pullback exchange in the exact-action coordinates of
strict pairs. The two epsilon maps only change exact/left-derived coordinates.
Source: prop-weil-operations, first proof step (blueprint: prop-weil-operations). -/
def woPullExchange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) :
    moduleObjectDerivedPullback Λ f ⋙ (upperStar Λ gX).mapDerivedCategory ⟶
      (upperStar Λ gY).mapDerivedCategory ⋙ moduleObjectDerivedPullback Λ f :=
  Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ gX).inv ≫
    (moduleObjectDerivedPullbackSquareComparison Λ sq).inv ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ gY).hom _

/-- The specified Ex_* in the exact-action coordinates, not a free exchange iso.
Source: prop-weil-operations, displayed Rf_* formula (blueprint: prop-weil-operations). -/
def woPushExchange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) :
    moduleObjectDerivedPushforward Λ f ⋙ (upperStar Λ gY).mapDerivedCategory ⟶
      (upperStar Λ gX).mapDerivedCategory ⋙ moduleObjectDerivedPushforward Λ f :=
  Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ gY).inv ≫
    (FrobeniusSquareExchange.direct ⟨Λ⟩ f sq) ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ gX).hom _

/-- Tensor and internal Hom preserve the entire constructible domain and lift with the
specified tensorator and evaluation-transpose structures, naturally in both inputs.
The Hom structure uses the inverse structure in its contravariant input.
Source: prop-weil-operations, six-operation list and first proof step
(blueprint: prop-weil-operations). -/
def WOBinary (X : Scheme.{u}) (g : X ⟶ X) [IsIso g] : Prop :=
  let p := boundedConstructible (condensedRingObj Λ X)
  let P := (upperStar Λ g).mapDerivedCategory
  let U := woForget p P
  let T := wfCondensedTensor Λ X
  let H := Functor.uncurry.obj (derivedHom Λ X)
  (∀ K L : WODerived Λ X, p K → p L → p (T.obj (K, L)) ∧ p (H.obj (op K, L))) ∧
  WOCanonicalLift p P (U.prod U ⋙ T)
    (fun KL ↦ (wfCondensedTensorFrobenius Λ g KL.1.obj KL.2.obj).hom) ∧
  WOCanonicalLift p P (U.op.prod U ⋙ H)
    (fun KL ↦ (leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app _ ≫
      weilVerdierHomTheta Λ g KL.1.unop KL.2)

/-- Cohomology equivariance of an actual raw square. In particular this applies to all
named comparison maps in the comparison clauses below, including their inverses when isomorphisms.
Source: prop-weil-operations, final cohomology assertion (blueprint: prop-weil-operations). -/
def WOCohomology (X : Scheme.{u}) (g : X ⟶ X) : Prop :=
  ∀ (A B : WODerived Λ X)
    (θA : ((upperStar Λ g).mapDerivedCategory).obj A ⟶ A)
    (θB : ((upperStar Λ g).mapDerivedCategory).obj B ⟶ B) (a : A ⟶ B),
    WOEquivariant (upperStar Λ g).mapDerivedCategory θA θB a →
    ∀ n : ℤ,
      let H := DerivedCategory.homologyFunctor _ n
      let e := (upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n
      H.map (((upperStar Λ g).mapDerivedCategory).map a) ≫ H.map θB =
        H.map θA ≫ H.map a ∧
      (upperStar Λ g).map (H.map a) ≫ e.hom.app B ≫ H.map θB =
        e.hom.app A ≫ H.map θA ≫ H.map a

end Operations

/-- Standard truncations on the actual constructible category, with the unique counit/unit
normalized Frobenius comparisons. The functors on pairs are exactly `mapOfNatIso c`,
so their structures are tau(theta) c. The two explicit squares retain the ordinary
truncation maps and hence the standard truncation triangles after forgetting.
Source: prop-weil-operations, truncation paragraph and proof step 3
(blueprint: prop-weil-operations). -/
def WOTruncations (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (g : X ⟶ X) [IsIso g] : Prop :=
  let R := condensedRingObj Λ X
  let p := boundedConstructible R
  let P := (upperStar Λ g).mapDerivedCategory
  ∃ ht : p.IsTriangulated,
  letI := ht
  OrdinaryConstructibleExchange R R (moduleObjectDerivedPullback Λ g) ∧
  ∃ hP : ∀ K : BoundedConstructible R, p (P.obj K.obj),
  let Q := p.lift (p.ι ⋙ P) hP
  ∃ t : TStructure (BoundedConstructible R), OrdinaryConstructibleTruncations R t ∧
    ConstructibleTruncationCompatibility t t Q ∧
    ∃ (cLE : ∀ m : ℤ, t.truncLE m ⋙ Q ≅ Q ⋙ t.truncLE m)
      (cGE : ∀ m : ℤ, t.truncGE m ⋙ Q ≅ Q ⋙ t.truncGE m),
    ∃ sQ : Q.CommShift ℤ,
    letI := sQ
    (∀ (K : BoundedConstructible R),
      p.ι.map ((Q.commShiftIso (1 : ℤ)).hom.app K) =
        P.map ((p.ι.commShiftIso (1 : ℤ)).hom.app K) ≫
          (P.commShiftIso (1 : ℤ)).hom.app K.obj ≫
          (p.ι.commShiftIso (1 : ℤ)).inv.app (Q.obj K)) ∧
    ∀ m : ℤ,
      (∀ K, (cLE m).hom.app K ≫ (t.truncLEι m).app (Q.obj K) =
        Q.map ((t.truncLEι m).app K)) ∧
      (∀ K, Q.map ((t.truncGEπ m).app K) ≫ (cGE m).hom.app K =
        (t.truncGEπ m).app (Q.obj K)) ∧
      (∀ K : Endofunctor.IsoAlgebra Q,
        WOEquivariant Q
          (((Endofunctor.IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom)
          K.str.hom ((t.truncLEι m).app K.carrier) ∧
        WOEquivariant Q K.str.hom
          (((Endofunctor.IsoAlgebra.mapOfNatIso (cGE m)).obj K).str.hom)
          ((t.truncGEπ m).app K.carrier) ∧
        WOEquivariant Q
          (((Endofunctor.IsoAlgebra.mapOfNatIso (cGE (m + 1))).obj K).str.hom)
          ((Q.commShiftIso (1 : ℤ)).hom.app ((t.truncLE m).obj K.carrier) ≫
            (shiftFunctor (BoundedConstructible R) (1 : ℤ)).map
              (((Endofunctor.IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom))
          ((t.truncGEδLE m (m + 1) rfl).app K.carrier))

/-- The geometric-fibre morphism, as an Over morphism rather than an arbitrary map.
Source: prop-weil-operations, geometric-fibre paragraph (blueprint: prop-weil-operations). -/
def geometricFiberMap (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    D.geometricFiber X₀ ⟶ D.geometricFiber Y₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀

section Comparisons
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Exchange followed by an input arrow, also usable before its invertibility has been
proved. Source: prop-weil-operations, displayed formula (blueprint: prop-weil-operations). -/
def woStructure {C : Type uC} [Category.{vC} C] {B : Type uD} [Category.{vD} B]
    {P : C ⥤ C} {Q : B ⥤ B} (F : C ⥤ B) (ex : F ⋙ Q ⟶ P ⋙ F)
    {K : C} (θ : P.obj K ⟶ K) : Q.obj (F.obj K) ⟶ F.obj K :=
  ex.app K ≫ F.map θ

/-- The named pullback and direct-image compositors are equivariant for the canonical
structures of the composite and of the iterated operation.
Source: prop-weil-operations, comparison clause and proof step 2
(blueprint: prop-weil-operations). -/
def WOComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    (gX : X ⟶ X) (gY : Y ⟶ Y) (gZ : Z ⟶ Z)
    [IsIso gX] [IsIso gY] [IsIso gZ]
    (sf : CommSq gX f f gY) (sh : CommSq gY h h gZ) : Prop :=
  let sx := sf.vert_comp sh
  (∀ K : Endofunctor.IsoAlgebra (upperStar Λ gZ).mapDerivedCategory,
    WOEquivariant (upperStar Λ gX).mapDerivedCategory
      (woStructure (moduleObjectDerivedPullback Λ (f ≫ h))
        (woPullExchange Λ (f ≫ h) gX gZ sx) K.str.hom)
      (woStructure (moduleObjectDerivedPullback Λ f) (woPullExchange Λ f gX gY sf)
        (woStructure (moduleObjectDerivedPullback Λ h)
          (woPullExchange Λ h gY gZ sh) K.str.hom))
      ((leftDerivedUpperStarComp Λ f h).hom.app K.carrier)) ∧
  (∀ K : Endofunctor.IsoAlgebra (upperStar Λ gX).mapDerivedCategory,
    WOEquivariant (upperStar Λ gZ).mapDerivedCategory
      (woStructure (moduleObjectDerivedPushforward Λ h) (woPushExchange Λ h gY gZ sh)
        (woStructure (moduleObjectDerivedPushforward Λ f)
          (woPushExchange Λ f gX gY sf) K.str.hom))
      (woStructure (moduleObjectDerivedPushforward Λ (f ≫ h))
        (woPushExchange Λ (f ≫ h) gX gZ sx) K.str.hom)
      ((rightDerivedLowerStarComp Λ f h).hom.app K.carrier))

/-- The canonical unit-square-counit base-change arrow is equivariant. It is meaningful
also before a proper/smooth base-change theorem proves that this particular arrow is an
isomorphism. Source: prop-weil-operations, base-change clause
(blueprint: prop-weil-operations). -/
def WOBaseChange {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (v : Y' ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) (gX' : X' ⟶ X') (gY' : Y' ⟶ Y')
    [IsIso gX] [IsIso gY] [IsIso gX'] [IsIso gY']
    (sf : CommSq gX f f gY) (sf' : CommSq gX' f' f' gY')
    (sa : CommSq gX' a a gX) (sv : CommSq gY' v v gY)
    (sq : CommSq a f' f v) : Prop :=
  ∀ K : Endofunctor.IsoAlgebra (upperStar Λ gX).mapDerivedCategory,
    WOEquivariant (upperStar Λ gY').mapDerivedCategory
      (woStructure (moduleObjectDerivedPullback Λ v) (woPullExchange Λ v gY' gY sv)
        (woStructure (moduleObjectDerivedPushforward Λ f)
          (woPushExchange Λ f gX gY sf) K.str.hom))
      (woStructure (moduleObjectDerivedPushforward Λ f') (woPushExchange Λ f' gX' gY' sf')
        (woStructure (moduleObjectDerivedPullback Λ a)
          (woPullExchange Λ a gX' gX sa) K.str.hom))
      ((moduleObjectDerivedExchange Λ sq).app K.carrier)

end Comparisons

/-- The coefficient presentation used by the current condensed purity theorem is exactly
E or Qbar, with no integral or common-stage datum.
Source: prop-weil-operations, coefficients and purity clause (blueprint: prop-weil-operations). -/
def woPurityCoefficient {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    AlgebraicGeometry.ProEtale.PurityTransport.Coefficient ell :=
  match c with
  | .finite E => .rational E
  | .qbar => .closure

/-- Base change preserves the finite-type model condition. Source: prop-weil-operations,
geometric-fibre convention (blueprint: prop-weil-operations). -/
instance woFiberLft (D : FiniteFieldDatum.{u}) (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    LocallyOfFiniteType (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance

/-- Base change preserves quasi-compactness. Source: prop-weil-operations,
geometric-fibre convention (blueprint: prop-weil-operations). -/
instance woFiberQc (D : FiniteFieldDatum.{u}) (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    QuasiCompact (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance

/-- Separatedness is used only on the cited separated presentation domains.
Source: prop-weil-operations, proof step 4 domains (blueprint: prop-weil-operations). -/
instance woFiberSeparated (D : FiniteFieldDatum.{u}) (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    IsSeparated (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance


open AlgebraicGeometry.ProEtale.PurityTransport

/-- The smooth geometric-fibre index with the model's specified compactification.
All fields are the existing base changes of the item data; this does not choose an
adjunction or a purity map. Source: prop-weil-operations, proof step 4, smooth-purity
geometric domain (blueprint: prop-weil-operations). -/
def woSmoothIndex (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (d : ℕ) [SmoothOfRelativeDimension d ((geometricFiberMap D f₀).left)]
    (c₀ : Compactification f₀.left) : SmoothDatum D := by
  let X := D.geometricFiber X₀
  let Y := D.geometricFiber Y₀
  let f := geometricFiberMap D f₀
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  exact { X := X, Y := Y, map := f.left, dim := d
          compactification := podGeometricCompactification D c₀ }

/-- The independently prescribed purity-source Weil structure: inverse-image exchange,
monoidal tensorator, root-normalized shifted Tate comparison, then the input structure.
Neither gamma nor the exceptional structure is used to define this arrow.
Source: prop-weil-operations, proof step 4, and def-pur-tate-datum
(blueprint: prop-weil-operations). -/
def woPurityStructure (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (sq : CommSq gX f f gY) (d : ℕ)
    (T : LinePullCoordinates ell c gX) {K : c.derived ell Y}
    (θ : ((upperStar (c.obj ell) gY).mapDerivedCategory).obj K ⟶ K) :
    ((upperStar (c.obj ell) gX).mapDerivedCategory).obj
        ((c.smoothSource ell f d).obj K) ⟶ (c.smoothSource ell f d).obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gX).inv.app _ ≫
    (Functor.Monoidal.μIso (upperStar (c.obj ell) gX).leftDerivedFunctor _ _).inv ≫
    (MonoidalCategory.tensorIso
      ((moduleObjectDerivedPullbackSquareComparison (c.obj ell) sq).symm.app K)
      (T.derived ell d)).hom ≫
    (c.smoothSource ell f d).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gY).hom.app K ≫ θ)

section Duality
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
open MonoidalCategory MonoidalClosed

/-- The fixed evaluation-transpose structure on internal Hom for arbitrary input Weil
isomorphisms. This is the same construction as `weilVerdierHomTheta`, transported to exact
Frobenius coordinates. Source: prop-weil-operations, proof steps 1 and 5
(blueprint: prop-weil-operations). -/
def woHomStructure {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    {K L : WODerived Λ X}
    (θK : ((upperStar Λ g).mapDerivedCategory).obj K ≅ K)
    (θL : ((upperStar Λ g).mapDerivedCategory).obj L ≅ L) :
    ((upperStar Λ g).mapDerivedCategory).obj (((derivedHom Λ X).obj (op K)).obj L) ⟶
      ((derivedHom Λ X).obj (op K)).obj L :=
  let ε := leftDerivedUpperStarIsoMapDerivedCategory Λ g
  ε.inv.app _ ≫ weilVerdierHomComparison Λ g K L ≫
    ((derivedHom Λ X).map ((ε.app K ≪≫ θK).inv.op)).app
      (((upperStar Λ g).leftDerivedFunctor).obj L) ≫
    ((derivedHom Λ X).obj (op K)).map (ε.app L ≪≫ θL).hom

end Duality


section SupportComposition
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
open OperationComparisons

/-- The recorded normalized compact-support exchange, restricted to Dctf. The coherent
system's proper/open and refinement equations fix this map on arbitrary compactifications.
Source: prop-weil-operations, composition and compact-support clauses
(blueprint: prop-weil-operations). -/
def woCtfExchange {k : Type u} [Field k]
    (H : CompactSupportComposition.CoherentData Λ k)
    {X Y : SepFinType k} (f : X ⟶ Y)
    (gX : X.obj.left ⟶ X.obj.left) (gY : Y.obj.left ⟶ Y.obj.left)
    [IsIso gX] [IsIso gY] (sq : CommSq gX f.hom.left f.hom.left gY) :
    lower (Λ := ⟨Λ⟩) H f ⋙ pull (Λ := ⟨Λ⟩) H Y Y gY ≅
      pull (Λ := ⟨Λ⟩) H X X gX ⋙ lower (Λ := ⟨Λ⟩) H f :=
  OperationComparisons.exchange (Λ := ⟨Λ⟩) H (IsPullback.of_horiz_isIso sq)

/-- The specified compact-support compositor and its exceptional-adjoint conjugate are
morphisms of Weil pairs. The exceptional exchanges are required to be the mates of the
same normalized compact-support exchanges; no Frobenius law on the compositor is assumed.
The right adjoints here can be any of the recorded constructible presentations, since the
adjunction fixes them up to its unique counit-compatible isomorphism.
Source: prop-weil-operations, comparison clause and proof steps 2 and 5
(blueprint: prop-weil-operations). -/
def WOCtfComposition {k : Type u} [Field k]
    (H : CompactSupportComposition.CoherentData Λ k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (h : Y ⟶ Z)
    (gX : X.obj.left ⟶ X.obj.left) (gY : Y.obj.left ⟶ Y.obj.left)
    (gZ : Z.obj.left ⟶ Z.obj.left) [IsIso gX] [IsIso gY] [IsIso gZ]
    (sf : CommSq gX f.hom.left f.hom.left gY)
    (sh : CommSq gY h.hom.left h.hom.left gZ) : Prop :=
  let P := pull (Λ := ⟨Λ⟩) H X X gX
  let Q := pull (Λ := ⟨Λ⟩) H Y Y gY
  let S := pull (Λ := ⟨Λ⟩) H Z Z gZ
  let F := lower (Λ := ⟨Λ⟩) H f
  let G := lower (Λ := ⟨Λ⟩) H h
  let FG := lower (Λ := ⟨Λ⟩) H (f ≫ h)
  let af := woCtfExchange Λ H f gX gY sf
  let ah := woCtfExchange Λ H h gY gZ sh
  let afg := woCtfExchange Λ H (f ≫ h) gX gZ (sf.vert_comp sh)
  (∀ K : Endofunctor.IsoAlgebra P,
    WOEquivariant S (woStructure G ah.hom (woStructure F af.hom K.str.hom))
      (woStructure FG afg.hom K.str.hom)
      ((OperationComparisons.composition (Λ := ⟨Λ⟩) H f h).hom.app K.carrier)) ∧
  ∀ (R : ConstantModelConstructibleFiniteTor Λ Y.obj.left ⥤
        ConstantModelConstructibleFiniteTor Λ X.obj.left)
    (T : ConstantModelConstructibleFiniteTor Λ Z.obj.left ⥤
        ConstantModelConstructibleFiniteTor Λ Y.obj.left)
    (RT : ConstantModelConstructibleFiniteTor Λ Z.obj.left ⥤
        ConstantModelConstructibleFiniteTor Λ X.obj.left)
    (adjF : F ⊣ R) (adjG : G ⊣ T) (adjFG : FG ⊣ RT)
    (bf : R ⋙ P ≅ Q ⋙ R) (bh : T ⋙ Q ≅ S ⋙ T) (bfg : RT ⋙ P ≅ S ⋙ RT)
    (_hf : (mateEquiv adjF adjF (TwoSquare.mk _ _ _ _ af.inv)).natTrans = bf.hom)
    (_hh : (mateEquiv adjG adjG (TwoSquare.mk _ _ _ _ ah.inv)).natTrans = bh.hom)
    (_hfg : (mateEquiv adjFG adjFG (TwoSquare.mk _ _ _ _ afg.inv)).natTrans = bfg.hom)
    (L : Endofunctor.IsoAlgebra S),
    WOEquivariant P (woStructure RT bfg.hom L.str.hom)
      (woStructure R bf.hom (woStructure T bh.hom L.str.hom))
      ((conjugateIsoEquiv adjFG (adjF.comp adjG)
        (OperationComparisons.composition (Λ := ⟨Λ⟩) H f h)).hom.app L.carrier)

end SupportComposition

/-- On the published separated domains the literal `ctfLowerShriek` and
`currentExceptionalInverseImage` have the same prescribed Weil lifts. In each presentation
Ex_! is the coherent system's normalized proper/open exchange on the canonical
compactification, transported through epsilon; b is its actual exceptional mate.
The right-adjoint and pair categories here are the recorded ones, not identity carriers.
Source: prop-weil-operations, constructible exceptional convention and proof step 2
(blueprint: prop-weil-operations). -/
def WOPublishedAdjunctions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k) (hL : IsLocalizingAdmissibleCoefficient ell Λ)
    (hN : IsNativeExceptionalCoefficient ell Λ)
    (H : CompactSupportComposition.CoherentData Λ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (gX : X.left ≅ X.left) (gY : Y.left ≅ Y.left)
    (sq : IsPullback gX.hom f.left f.left gY.hom) : Prop :=
  let cd := exceptionalCurrentFieldCD ell k hk
  let c := compactificationOverField f
  let F := rightDerivedLowerShriekOfCompactification Λ c
  let ex := H.exchange (f := SepFinType.homMk f) (f' := SepFinType.homMk f) sq c c
  let εX := leftDerivedUpperStarIsoMapDerivedCategory Λ gX.hom
  let εY := leftDerivedUpperStarIsoMapDerivedCategory Λ gY.hom
  (let P := StrictWeilCondensed.smallAction Λ gX
   let Q := StrictWeilCondensed.smallAction Λ gY
   let Fc := ctfLowerShriek Λ ell k cd f hL
   let Rc := ctfExceptionalInverseImage Λ ell k cd f hL
   let adj := ctfExceptionalAdjunction Λ ell k cd f hL
   ∃ a : Fc ⋙ Q ≅ P ⋙ Fc,
     (∀ K, (a.hom.app K).hom = εY.inv.app (F.obj K.obj) ≫
       ex.hom.app ⟨K.obj, (sixOperationsLocalizingAdjunction Λ ell k cd f hL).source_mem
         K.obj K.property⟩ ≫ F.map (εX.hom.app K.obj)) ∧
   ∃ b : Rc ⋙ P ≅ Q ⋙ Rc,
     (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans = b.hom ∧
   ∃ adjW : Endofunctor.IsoAlgebra.mapOfNatIso a ⊣ Endofunctor.IsoAlgebra.mapOfNatIso b,
     (∀ K, (adjW.unit.app K).hom.f = adj.unit.app K.carrier) ∧
     (∀ L, (adjW.counit.app L).hom.f = adj.counit.app L.carrier)) ∧
  (let p := constantModelBoundedConstructible Λ X.left
   let q := constantModelBoundedConstructible Λ Y.left
   let PX := (upperStar Λ gX.hom).mapDerivedCategory
   let PY := (upperStar Λ gY.hom).mapDerivedCategory
   ∃ (hPX : ∀ K : p.FullSubcategory, p (PX.obj K.obj))
     (hPY : ∀ K : q.FullSubcategory, q (PY.obj K.obj))
     (hLoc : p ≤ localizingClosureProEtale Λ X.left),
   let P := p.lift (p.ι ⋙ PX) hPX
   let Q := q.lift (q.ι ⋙ PY) hPY
   let Fn := nativeConstructibleLowerShriek Λ ell k cd f hN
   let Rn := currentExceptionalInverseImage Λ ell k hk f hN
   let adj := currentExceptionalAdjunction Λ ell k hk f hN
   ∃ a : Fn ⋙ Q ≅ P ⋙ Fn,
     (∀ K, (a.hom.app K).hom = εY.inv.app (F.obj K.obj) ≫
       ex.hom.app ⟨K.obj, hLoc K.obj K.property⟩ ≫ F.map (εX.hom.app K.obj)) ∧
   ∃ b : Rn ⋙ P ≅ Q ⋙ Rn,
     (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans = b.hom ∧
   ∃ adjW : Endofunctor.IsoAlgebra.mapOfNatIso a ⊣ Endofunctor.IsoAlgebra.mapOfNatIso b,
     (∀ K, (adjW.unit.app K).hom.f = adj.unit.app K.carrier) ∧
     (∀ L, (adjW.counit.app L).hom.f = adj.counit.app L.carrier))

set_option maxHeartbeats 1600000 in
-- This simultaneous statement elaborates all six native derived-operation endpoints.
set_option maxHeartbeats 1600000 in
-- The package contains all operation and comparison endpoints simultaneously.
end WeilConjectures

namespace WeilConjectures

private theorem woCohomology (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (g : X ⟶ X) :
    WOCohomology Λ X g := by
  intro A B θA θB a h n
  let H := DerivedCategory.homologyFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) n
  let e := (upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n
  have hH : H.map (((upperStar Λ g).mapDerivedCategory).map a) ≫ H.map θB =
      H.map θA ≫ H.map a := by
    simpa only [Functor.map_comp] using congrArg H.map h.1
  refine ⟨hH, ?_⟩
  change (upperStar Λ g).map (H.map a) ≫ e.hom.app B ≫ H.map θB = _
  have hn := e.hom.naturality a
  change (upperStar Λ g).map (H.map a) ≫ e.hom.app B =
    e.hom.app A ≫ H.map (((upperStar Λ g).mapDerivedCategory).map a) at hn
  rw [← Category.assoc, hn, Category.assoc, hH]

private theorem woTruncations_coefficient
    (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (g : X ⟶ X) [IsIso g] : WOTruncations (WeilCoefficient.ab c) X g := by
  cases c with
  | finite E =>
    obtain ⟨t, ht⟩ := (condensedConstructibleTruncations_exists ell X).1 E |>.1
    exact woTruncations_of_standard _ X g t ht
  | qbar =>
    obtain ⟨t, ht⟩ := (condensedConstructibleTruncations_exists ell X).2.1
    exact woTruncations_of_standard _ X g t ht

end WeilConjectures
