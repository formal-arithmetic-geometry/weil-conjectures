/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurrentTraceCup.CurrentTraceCup
public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical maps in the top-degree trace statement

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/sk-cor-trace/_section.md,
statement and complements.
(blueprint: def-pd-top-degree-trace-maps).
These are the recorded trace--cup constructions over an arbitrary algebraically closed
base, retaining their root-line, shift and adjunction normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The coefficient unit; source: sk-cor-trace, Lambda_X
(blueprint: def-pd-top-degree-trace-maps). -/
abbrev U (T : Scheme.{u}) := unit ell c T

/-- Ordinary scalar cohomology, with the actual condensed coefficients.
Source: sk-cor-trace, H^i(X,Lambda_X) (blueprint: def-pd-top-degree-trace-maps). -/
abbrev H {k : Type u} [Field k] (X : Over (Spec (.of k))) (i : ℤ) :=
  (condensedRingOrdinaryCohomology (c.obj.{u} ell) X.hom i).obj (U ell c X.left)

/-- The canonical proper compactification and smooth index.
Source: sk-cor-trace, a_X (blueprint: def-pd-top-degree-trace-maps). -/
def geometry {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    GeneralPurityTransport.SmoothDatum k where
  X := X
  Y := Over.mk (𝟙 (Spec (.of k)))
  yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))
  ySeparated := inferInstanceAs (IsSeparated (𝟙 _))
  map := X.hom
  isOver := ⟨Category.comp_id _⟩
  dim := d
  compactification := Compactification.ofIsProper X.hom

-- Use the scalar localization fixed by the published trace--cup interface.
attribute [-instance] residueLisseAlgebraHasDerivedCategory in
/-- The coefficient Tate line without a choice of basis.
Source: sk-cor-trace, Lambda(-d) (blueprint: def-pd-top-degree-trace-maps). -/
abbrev Value (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :=
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (c.obj.{u} ell))) 0).obj
    ((TraceCupPoint.fiber (c.obj.{u} ell) k).obj
      (CurrentTraceCup.derivedLine ell c (Spec (.of k)) (-(d : ℤ))))

/-- The invertibility of ell at all residue fields is transported from k.
Source: the standing prime-to-characteristic setting (blueprint: def-pd-top-degree-trace-maps). -/
@[instance_reducible]
def residueInverse {k : Type u} [Field k] (hEll : IsUnit (ell : k))
    (T : Over (Spec (.of k))) : ∀ x : T.left, Invertible (ell : T.left.residueField x) :=
  fun x ↦ (map_natCast (T.hom.residueFieldAlgebraMap x) ell) ▸
    (hEll.map (T.hom.residueFieldAlgebraMap x)).invertible

/-- The actual untwisted smooth trace before scalar sections: inverse root-line
cancellation followed by the named normalized smooth counit at Lambda_s(-d).
Source: sk-cor-trace, the definition of tr_X (blueprint: def-pd-top-degree-trace-maps). -/
def untwisted {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell)
      (Compactification.ofIsProper X.hom)).obj ((U ell c X.left) ⟦2 * (d : ℤ)⟧) ⟶
      CurrentTraceCup.derivedLine ell c (Spec (.of k)) (-(d : ℤ)) := by
  let s := geometry X d
  letI := residueInverse ell hEll s.X
  letI := residueInverse ell hEll s.Y
  letI := CurrentTraceCup.cancellation_isIso ell c s.map d
  exact (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) s.compactification).map
      (inv (CurrentTraceCup.cancellation ell c s.map d)) ≫
    GeneralPurityTransport.ExplicitAdjunction.trace
      ((GeneralPurityTransport.smooth_purity_transport ell k
        (Or.inr inferInstance) hEll).choose c s)
      ⟨_, CurrentTraceCup.tateLine_mem ell c s.Y.left (-(d : ℤ))⟩

/-- The trace on actual ordinary top cohomology, using the proper comparison.
Source: sk-cor-trace, tr_X (blueprint: def-pd-top-degree-trace-maps). -/
def trace {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : H ell c X (2 * (d : ℤ))) : Value ell c k d := by
  let C := Compactification.ofIsProper X.hom
  let F := TraceCupPoint.fiber (c.obj.{u} ell) k
  let M := (condensedRingCompactCoefficientComplex (c.obj.{u} ell) C).obj (U ell c X.left)
  let N := F.obj (CurrentTraceCup.derivedLine ell c (Spec (.of k)) (-(d : ℤ)))
  let z := ((TraceCupProper.cohomology (c.obj.{u} ell) X.hom (2 * (d : ℤ))).inv.app
    (U ell c X.left)) x
  let r := (CurrentTraceCup.classEquiv (Λ := c.obj.{u} ell) M (2 * (d : ℤ))).symm z
  let t := r ≫ ((Functor.commShiftIso
    (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) C ⋙ F)
      (2 * (d : ℤ))).app (U ell c X.left)).inv ≫ F.map (untwisted ell c hEll X d)
  exact CurrentTraceCup.classEquiv (Λ := c.obj.{u} ell) N 0
    (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

/-- The ordinary cup product through the fixed mixed-support cup and proper comparison.
Source: sk-cor-trace, complement (iii) (blueprint: def-pd-top-degree-trace-maps). -/
def cup {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (i j : ℤ)
    (x : H ell c X i) (y : H ell c X j) : H ell c X (i + j) := by
  let a := X.hom
  let C := Compactification.ofIsProper a
  let K := U ell c X.left
  let M := (condensedRingOrdinaryCoefficientComplex (c.obj.{u} ell) a).obj K
  let Mc := (condensedRingCompactCoefficientComplex (c.obj.{u} ell) C).obj K
  let h (n : ℤ) : CurrentTraceCup.Classes (c.obj.{u} ell) Mc n ≃
      CurrentTraceCup.Classes (c.obj.{u} ell) M n :=
    (Iso.refl _).homCongr ((shiftFunctor _ n).mapIso
      ((Functor.isoWhiskerRight (TraceCupProper.comparison (c.obj.{u} ell) a)
        (TraceCupPoint.fiber (c.obj.{u} ell) k)).app K))
  let m : K ⊗ K ⟶ K :=
    ((DerivedCategory.singleFunctorObjUnitIso _).hom ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
  exact CurrentTraceCup.classEquiv (Λ := c.obj.{u} ell) M (i + j)
    (h (i + j) (CurrentTraceCup.product
      (TraceCupMixed.cup (c.bundled ell) k C K K ≫
        (condensedRingCompactCoefficientComplex (c.obj.{u} ell) C).map m) i j
      ((h i).symm ((CurrentTraceCup.classEquiv (Λ := c.obj.{u} ell) M i).symm x))
      ((CurrentTraceCup.classEquiv (Λ := c.obj.{u} ell) M j).symm y)))

/-- The actual trace--cup pairing, with its integer degree transport.
Source: sk-cor-trace, complement (iii) (blueprint: def-pd-top-degree-trace-maps). -/
def pairing {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (i : ℤ) (x : H ell c X i) (y : H ell c X (2 * (d : ℤ) - i)) :
    Value ell c k d :=
  trace ell c hEll X d
    ((eqToHom (congrArg (H ell c X)
      ((add_sub_assoc i (2 * (d : ℤ)) i).symm.trans
        (add_sub_cancel_left i (2 * (d : ℤ)))))) (cup ell c X i _ x y))

/-- The chosen normalized smooth adjunction, with no new orientation parameter.
Source: the smooth purity identifications of sk-cor-trace
(blueprint: def-pd-top-degree-trace-maps). -/
def smoothAdjunction {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    GeneralPurityTransport.ExplicitAdjunction ell k c (geometry X d) :=
  (GeneralPurityTransport.smooth_purity_transport ell k (Or.inr inferInstance) hEll).choose
    c (geometry X d)

/-- The ordinary unit section before scalar realization.
Source: H^0 = Lambda, the constant unit (blueprint: def-pd-top-degree-trace-maps). -/
def unitSection {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    U ell c (Spec (.of k)) ⟶ (actualPush (c.obj.{u} ell) X.hom).obj (U ell c X.left) :=
  traceSupportedUnit ell c X.hom

/-- Twisted top-degree classes represented on the base point. The target already
contains [2d]; exact point sections identify these maps with H^{2d}(X,Lambda(d)).
Source: the representative c in complement (i) (blueprint: def-pd-top-degree-trace-maps). -/
abbrev TwistedClasses {k : Type u} [Field k] (X : Over (Spec (.of k))) (d : ℕ) :=
  U ell c (Spec (.of k)) ⟶
    (actualPush (c.obj.{u} ell) X.hom).obj (c.derivedLine ell X.left d)

/-- The normalized twisted derived trace, expressed through sourceUnit.
Source: Tr_X at Lambda_s (blueprint: def-pd-top-degree-trace-maps). -/
def twistedDerived {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell)
      (Compactification.ofIsProper X.hom)).obj (c.derivedLine ell X.left d) ⟶
        U ell c (Spec (.of k)) := by
  let s := geometry X d
  letI := residueInverse ell hEll s.Y
  exact (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) s.compactification).map
      (sourceUnit ell c s.map d).inv ≫
    GeneralPurityTransport.ExplicitAdjunction.trace
      ((GeneralPurityTransport.smooth_purity_transport ell k
        (Or.inr inferInstance) hEll).choose c s)
      ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩

/-- The twisted trace of a class; its value is an endomorphism of Lambda_s,
hence the scalar obtained by applying it to 1.
Source: tr_X(d) in the point-normalization and complement (i)
(blueprint: def-pd-top-degree-trace-maps). -/
def twistedTrace {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : TwistedClasses ell c X d) :=
  z ≫ (TraceCupProper.comparison (c.obj.{u} ell) X.hom).inv.app _ ≫
    twistedDerived ell c hEll X d

/-- The degree-zero duality map assembled from ordinary adjunction, the same
purity orientation, exceptional adjunction and proper comparison. Its source
and target are the canonical point-site representatives of the displayed scalar
Hom spaces, so no trivialization of a Tate line is introduced.
Source: complement (i) (blueprint: def-pd-top-degree-trace-maps). -/
def dualityMap {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : TwistedClasses ell c X d) :
    (actualPush (c.obj.{u} ell) X.hom).obj (U ell c X.left) ⟶
      U ell c (Spec (.of k)) := by
  let s := geometry X d
  letI := residueInverse ell hEll s.X
  letI := residueInverse ell hEll s.Y
  let a := smoothAdjunction ell c hEll X d
  let K : c.ctf ell s.Y.left :=
    ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩
  let L : c.ctf ell s.X.left :=
    ⟨U ell c s.X.left, CurrentTraceCup.tateLine_mem ell c s.X.left 0⟩
  let v := ((derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) X.hom).homEquiv
    K.obj (c.derivedLine ell X.left d)).symm z
  let w : L ⟶ (source ell c s.map d a.source_closed).obj K :=
    ⟨(tracePullUnit ell c X.hom).inv ≫ v ≫ (sourceUnit ell c s.map d).inv⟩
  exact (TraceCupProper.comparison (c.obj.{u} ell) X.hom).inv.app L.obj ≫
    ((a.adjunction.homEquiv L K).symm w).hom

/-- Proper direct-image composition along a rational point is the identity,
with the unital compositor fixed before using the smooth adjunction.
Source: a_X x = id in the point-class paragraph (blueprint: def-pd-top-degree-trace-maps). -/
def pointReturn {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (x : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _) :
    (actualPush (c.obj.{u} ell) X.hom).obj
      ((actualPush (c.obj.{u} ell) x).obj (U ell c (Spec (.of k)))) ≅
        U ell c (Spec (.of k)) :=
  (lowerComp (c.obj.{u} ell) x X.hom).symm.app _ ≪≫
    (eqToIso (congrArg (actualPush (c.obj.{u} ell)) hx)).app _ ≪≫
    (tracePushIdentity ell c (Spec (.of k))).app _

/-- The unit has the one-generator scalar presentation, on the trivial stratification.
Source: sk-cor-trace, point-supported constant coefficients
(blueprint: def-pd-top-degree-trace-maps). -/
private theorem regular_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] :
    constantModelBoundedConstructible Λ T
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) := by
  apply single_constructible Λ T
  rw [IsConstantModelConstructible, if_pos
    (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
  apply stratified_of_finiteModel Λ T
  refine ⟨.singleton (𝟙 T) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  refine ⟨Mod.regular Λ, ?_, ⟨?_⟩⟩
  · refine ⟨1, 0, 0, ⟨?_⟩⟩
    let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
    exact e.symm ≪≫ cokernelZeroIsoTarget.symm
  · exact (Functor.Monoidal.εIso (upperStar Λ (𝟙 T))).symm ≪≫
      (mapRegularIso (upperStarFromPoint T) Λ).symm

private theorem closed_constantModel_preserves_local
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X : Scheme.{u}} [IsNoetherian X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) (hK : constantModelBoundedConstructible Λ Z K) :
    constantModelBoundedConstructible Λ X ((lowerStar Λ i).rightDerivedFunctor.obj K) := by
  classical
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hij : Set.range i = (Set.range U.ι)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  let := closedSupport_lowerStarExact Λ i U.ι hij
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  apply ObjectProperty.prop_of_iso _
    ((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app K).symm
  refine ⟨(lowerStar Λ i).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  apply ObjectProperty.prop_of_iso _
    (((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n).app K)
  have h := stratified_closedPush Λ i _ (by
    simpa only [IsConstantModelConstructible, if_pos
      (show CompactSpace Z ∧ QuasiSeparatedSpace Z from ⟨inferInstance, inferInstance⟩)]
      using hK.2 n)
  simpa only [IsConstantModelConstructible, if_pos
    (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩),
    Functor.comp_obj] using h

/-- Exact closed image preserves the unit's finite constant models. The closed
projection identifies every tensor test with exact image of a degree-zero pullback.
Source: sk-cor-trace, closed-point counit construction (blueprint: def-pd-top-degree-trace-maps). -/
private theorem closed_unit_mem
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X : Scheme.{u}} [IsNoetherian X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    constantModelBoundedConstructible Λ X
        ((lowerStar Λ i).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((lowerStar Λ i).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
  classical
  let V := Scheme.openComplementOfIsClosedImmersion i
  have hij : Set.range i = (Set.range V.ι)ᶜ := by
    simp [V, Scheme.openComplementOfIsClosedImmersion]
  let := closedSupport_lowerStarExact Λ i V.ι hij
  let P := (DerivedCategory.singleFunctor (supportModules Λ Z) 0).obj (𝟙_ _)
  let F := lowerStar Λ i
  let G := supportPullback Λ i
  refine ⟨closed_constantModel_preserves_local Λ i P (regular_constructible Λ Z), ?_⟩
  apply (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso
    (F.rightDerivedFunctorIsoMapDerivedCategory.app P).symm
  refine ⟨0, 0, fun N ↦ ?_⟩
  let Q := (DerivedCategory.singleFunctor (supportModules Λ X) 0).obj N
  let := (openClosedSupportProjectionFormula Λ i V.ι hij).1 P Q
  let e : F.mapDerivedCategory.obj P ⊗ Q ≅
      F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj (G.obj N)) :=
    asIso (closedSupportProjection Λ i P Q) ≪≫
      F.mapDerivedCategory.mapIso
        (tensorIso (DerivedCategory.singleFunctorObjUnitIso _) (Iso.refl _) ≪≫
          λ_ _ ≪≫ (G.mapDerivedCategorySingleFunctor 0).app N)
  apply (DerivedCategory.homologyConcentratedIn 0 0).prop_of_iso e.symm
  exact F.homologyConcentratedIn_mapDerivedCategory_obj ⟨inferInstance, inferInstance⟩


/-- The point-supported unit is constructible and finite-Tor.
Source: the closed-point counit in sk-cor-trace (blueprint: def-pd-top-degree-trace-maps).
Proof: proper finite type over k makes X Noetherian, so the point and its open
complement form a constructible stratification. The unit at the algebraically
closed point is a finite free rank-one local
model in degree zero. A closed immersion has exact direct image. The finite
stratification by this point and its complement therefore has the constant model
Lambda on the point and zero on the complement. Tensor projection identifies its
tensor with any sheaf with the same exact point-supported tensor, giving Tor
amplitude [0,0]. Thus this is the actual Dctf source of the displayed counit. -/
theorem pointSupport_mem {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [IsProper X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x] :
    property ell c X.left
      ((actualPush (c.obj.{u} ell) x).obj (U ell c (Spec (.of k)))) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  exact closed_unit_mem (c.obj ell) x

/-- The supported counit class, obtained by transposing the canonical map
Ra_! Rx_* Lambda -> Lambda under the normalized smooth adjunction. Under
x^!a^! Lambda = (ax)^! Lambda this is exactly the closed-support counit;
sourceUnit reads its target as Lambda_X(d)[2d]. No point class is selected by its
trace value. Source: the point-class construction (blueprint: def-pd-top-degree-trace-maps). -/
def pointMap {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) :
    (actualPush (c.obj.{u} ell) x).obj (U ell c (Spec (.of k))) ⟶
      c.derivedLine ell X.left d := by
  let s := geometry X d
  letI := residueInverse ell hEll s.Y
  let a := smoothAdjunction ell c hEll X d
  let K : c.ctf ell s.Y.left :=
    ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩
  let L : c.ctf ell s.X.left :=
    ⟨(actualPush (c.obj.{u} ell) x).obj K.obj, pointSupport_mem ell c X x⟩
  let v : (support ell c s.compactification a.support_closed).obj L ⟶ K :=
    ⟨(TraceCupProper.comparison (c.obj.{u} ell) X.hom).hom.app L.obj ≫
      (pointReturn ell c X x hx).hom⟩
  exact ((a.adjunction.homEquiv L K) v).hom ≫ (sourceUnit ell c s.map d).hom

/-- Forget supports in the supported counit class. This represents its image of 1
in H^{2d}(X,Lambda_X(d)), through the fixed proper direct-image compositor.
Source: [x] in the point-class paragraph (blueprint: def-pd-top-degree-trace-maps). -/
def pointClass {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) : TwistedClasses ell c X d :=
  (pointReturn ell c X x hx).inv ≫
    (actualPush (c.obj.{u} ell) X.hom).map (pointMap ell c hEll X d x hx)

/-- Integer parity sign, including negative cohomological degrees.
Source: (-1)^i and (-1)^{i(2d-i)} in complement (iii) (blueprint: def-pd-top-degree-trace-maps). -/
def sign (i : ℤ) : ℤ := ((-1 : ℤˣ) ^ i : ℤˣ)

/-- Centered etale coordinates whose zero fibre is the given point. Both squares
are actual pullbacks, so the supported classes restrict to the same support.
Source: complement (ii), etale locally at x (blueprint: def-pd-top-degree-trace-maps). -/
structure PointCoordinates {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (d : ℕ) (x : Spec (.of k) ⟶ X.left) where
  U : Over (Spec (.of k))
  v : U.left ⟶ X.left
  t : U.left ⟶ iteratedAffineLine (Spec (.of k)) d
  z : Spec (.of k) ⟶ U.left
  etaleV : Etale v
  etaleT : Etale t
  overV : v ≫ X.hom = U.hom
  overT : t ≫ iteratedAffineLineProj (Spec (.of k)) d = U.hom
  squareX : IsPullback z (𝟙 _) v x
  squareT : IsPullback z (𝟙 _) t (AffineZeroPurity.zero (Spec (.of k)) d)

/-- The ordered product of coordinate Cartier classes, or of their negative
Kummer boundaries, with its length read as d. The empty product is retained.
Source: complement (ii), ordered frame product (blueprint: def-pd-top-degree-trace-maps). -/
def coordinateProduct (C : TraceCartierFamily.{u} ell) (negative : Bool)
    (B : Scheme.{u}) (d : ℕ)
    [∀ y : iteratedAffineLine B d, Invertible (ell : (iteratedAffineLine B d).residueField y)]
    (hT : IsUnit (ell : Γ(iteratedAffineLine B d, ⊤))) :
    traceProductSource ell c B d (List.finRange d) ⟶
      c.derivedLine ell (iteratedAffineLine B d) d := by
  simpa only [List.length_finRange] using
    traceProductMap ell C negative c B d hT (List.finRange d)

/-- The supported point class is locally the positive Cartier product and also
(-1)^d times the Kummer-frame fundamental class. The source isomorphisms are
normalized by the quotient units, and target isomorphisms are the root-normalized
Tate pullbacks; none can absorb a sign. TraceCartierFinite identifies the negative
factors with the finite Kummer boundaries, and TraceCartierScalar states their
compatible integral reductions and subsequent scalar images.
Source: both formulations of complement (ii) (blueprint: def-pd-top-degree-trace-maps). -/
def PointProduct {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (C : TraceCartierFamily.{u} ell) (x : Spec (.of k) ⟶ X.left)
    [IsClosedImmersion x] (hx : x ≫ X.hom = 𝟙 _) : Prop :=
  let s := Spec (.of k)
  let A := iteratedAffineLine s d
  letI := residueInverse ell hEll X
  letI := residueInverse ell hEll (Over.mk (iteratedAffineLineProj s d))
  ∃ q : PointCoordinates X d x,
    letI := residueInverse ell hEll q.U
    ∃ (hT : IsUnit (ell : Γ(A, ⊤)))
      (α : (actualPull (c.obj.{u} ell) q.v).obj
        ((actualPush (c.obj.{u} ell) x).obj (U ell c s)) ≅
          (actualPush (c.obj.{u} ell) q.z).obj (U ell c s))
      (β : (actualPull (c.obj.{u} ell) q.t).obj
        (traceProductSource ell c s d (List.finRange d)) ≅
          (actualPush (c.obj.{u} ell) q.z).obj (U ell c s)),
      (tracePullUnit ell c q.v).inv ≫
          (actualPull (c.obj.{u} ell) q.v).map (traceSupportedUnit ell c x) ≫ α.hom =
        traceSupportedUnit ell c q.z ∧
      (tracePullUnit ell c q.t).inv ≫
          (actualPull (c.obj.{u} ell) q.t).map
            (traceProductUnit ell c s d (List.finRange d)) ≫ β.hom =
        traceSupportedUnit ell c q.z ∧
      (actualPull (c.obj.{u} ell) q.v).map (pointMap ell c hEll X d x hx) ≫
          (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.v) d).hom =
        α.hom ≫ β.inv ≫ (actualPull (c.obj.{u} ell) q.t).map
          (coordinateProduct ell c C false s d hT) ≫
            (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.t) d).hom ∧
      (actualPull (c.obj.{u} ell) q.v).map (pointMap ell c hEll X d x hx) ≫
          (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.v) d).hom =
        ((-1 : ℤ) ^ d) • (α.hom ≫ β.inv ≫ (actualPull (c.obj.{u} ell) q.t).map
          (coordinateProduct ell c C true s d hT) ≫
            (LinePullCoordinates.derived ell (CurrentTraceCup.linePull ell c q.t) d).hom)

/-- The perfectness and symmetry assertions for the specified trace--cup map.
Perfectness means both linear adjoints to the Tate-line-valued pairing are
bijective, including finite field coefficients. Degree transports preserve all
integer degrees. Alternation is asserted only in characteristic zero and odd d.
Source: complement (iii) (blueprint: def-pd-top-degree-trace-maps). -/
def FieldPairing {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] : Prop :=
  let R := CategoryTheory.MonObj.Γ (c.obj.{u} ell)
  IsField R →
    (∀ i : ℤ, ∃ b : H ell c X i →ₗ[R]
        H ell c X (2 * (d : ℤ) - i) →ₗ[R] Value ell c k d,
      (∀ x y, b x y = pairing ell c hEll X d i x y) ∧
        Function.Bijective b ∧ Function.Bijective b.flip) ∧
    (∀ (i : ℤ) (x : H ell c X i) (y : H ell c X (2 * (d : ℤ) - i)),
      pairing ell c hEll X d (2 * (d : ℤ) - i) y
          ((eqToHom (congrArg (H ell c X) (by omega : i = 2 * (d : ℤ) -
            (2 * (d : ℤ) - i)))) x) =
        sign (i * (2 * (d : ℤ) - i)) • pairing ell c hEll X d i x y ∧
      sign (i * (2 * (d : ℤ) - i)) • pairing ell c hEll X d i x y =
        sign i • pairing ell c hEll X d i x y) ∧
    (∀ (x y : H ell c X (d : ℤ)),
      pairing ell c hEll X d (d : ℤ) y
          ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) x) =
        ((-1 : ℤ) ^ d) • pairing ell c hEll X d (d : ℤ) x
          ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) y)) ∧
    (ringChar R = 0 → Odd d → ∀ x : H ell c X (d : ℤ),
      pairing ell c hEll X d (d : ℤ) x
        ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) x) = 0)

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
