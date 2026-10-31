/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SecSmoothPurity.TraceBasic
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Trace and cup product with actual condensed rational coefficients

Source: latest blueprint, sec-poincare-duality/sk-thm-poincare-duality/
def-weil-poincare-trace-cup.md (blueprint: def-weil-poincare-trace-cup).

Cohomology is represented by maps from the coefficient unit in the actual ordinary
condensed derived category. The product is the tensor product of these classes.
The trace is the exceptional counit, untwisted by the closed tensor adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

variable (ell : ℕ) [Fact ell.Prime]

/-- The prescribed continuous condensed rational coefficient ring.
Source: coefficient convention (blueprint: def-weil-poincare-trace-cup). -/
abbrev ring := (PurityTransport.Coefficient.rationals : PurityTransport.Coefficient ell).obj.{u} ell

/-- The canonical small derived category of modules over the terminal scalar ring.
Source: ordinary scalar cohomology (blueprint: def-weil-poincare-trace-cup).
This names the published Grothendieck construction explicitly, independently of
instance attributes modified by the legacy trace imports. -/
instance scalarModulesDerived : HasDerivedCategory.{u + 1}
    (ModuleCat.{u + 1} (condensedScalarRing (ring.{u} ell))) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1} (condensedScalarRing (ring.{u} ell))) _ _
      (ModuleCat.isGrothendieckAbelian_of_commRing _)

/-- The actual unbounded derived category of modules over the pulled-back ring.
Source: derived-category convention (blueprint: def-weil-poincare-trace-cup). -/
abbrev category (X : Scheme.{u}) :=
  DerivedCategory.{u + 1}
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring.{u} ell) X))

/-- The regular coefficient module in degree zero, as the derived tensor unit.
Source: K_X = p_X^* Q_ell (blueprint: def-weil-poincare-trace-cup). -/
abbrev unit (X : Scheme.{u}) : category ell X := 𝟙_ _

/-- Constant scalars act on the derived coefficient unit by multiplication.
Source: the Q_ell-module structure (blueprint: def-weil-poincare-trace-cup).
Proof: use the canonical scalar map into the regular module endomorphisms and
conjugate it through the degree-zero derived-unit isomorphism. -/
def scalar (X : Scheme.{u}) : Padic ell →+* End (unit ell X) := by
  let S := DerivedCategory.singleFunctor
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring.{u} ell) X)) 0
  let e := DerivedCategory.singleFunctorObjUnitIso
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring.{u} ell) X))
  exact (e.conjRingEquiv.toRingHom).comp ((S.mapEndRingHom _).comp
    ((Mod.regularEndRingHom (R := condensedRingObj (ring.{u} ell) X)).comp
      ((CondensedRing.condensedRingScalarSections (ring.{u} ell) X).comp
        (Profinite.continuousMapConstRingHom (Padic ell)))))

/-- Maps from the regular coefficient unit with their constant scalar action.
Source: cohomology via maps from the unit (blueprint: def-weil-poincare-trace-cup). -/
abbrev sections (X : Scheme.{u}) : category ell X ⥤ ModuleCat.{u + 1} (Padic ell) :=
  preadditiveCoyonedaObj (unit ell X) ⋙ ModuleCat.restrictScalars.{u + 1}
    ((scalar ell X).op.comp (RingEquiv.toOpposite (Padic ell)).toRingHom)

/-- H^i(X,Q_ell), represented in the actual condensed derived category.
Source: ordinary cohomology convention (blueprint: def-weil-poincare-trace-cup). -/
abbrev cohomology (X : Scheme.{u}) (i : ℤ) : ModuleCat.{u + 1} (Padic ell) :=
  (sections ell X).obj ((unit ell X) ⟦i⟧)

/-- The cup product induced by multiplication of the coefficient unit.
Source: the displayed cup product (blueprint: def-weil-poincare-trace-cup). -/
def cup {X : Scheme.{u}} {i j : ℤ}
    (x : cohomology ell X i) (y : cohomology ell X j) : cohomology ell X (i + j) := by
  change (unit ell X ⟶ (unit ell X) ⟦i⟧) at x
  change (unit ell X ⟶ (unit ell X) ⟦j⟧) at y
  exact MonoidalCategory.shiftProduct x y

/-- Pullback on classes, with the canonical unit and shift comparisons.
Source: pullback on cohomology (blueprint: def-weil-poincare-trace-cup). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℤ)
    (x : cohomology ell Y i) : cohomology ell X i := by
  change (unit ell Y ⟶ (unit ell Y) ⟦i⟧) at x
  exact
    (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) f).inv ≫
    (CondensedRing.upperStar (ring.{u} ell) f).leftDerivedFunctor.map x ≫
    ((CondensedRing.upperStar (ring.{u} ell) f).leftDerivedFunctor.commShiftIso i).hom.app _ ≫
    (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) f).hom⟦i⟧'

/-- The Hom representation of ordinary coefficient cohomology, natural in the complex.
No new cohomology theory is introduced by the maps-from-the-unit notation above.
Source: the ordinary RΓ convention (blueprint: def-weil-poincare-trace-cup).
Proof: the scalar-unit adjunction identifies global sections with maps from the regular
module. Derive this adjunction using a K-injective resolution. Evaluation on the
algebraically closed point is exact, so homology of this derived section complex
represents maps from the unit into the shifted complex. The adjunction is additive
and respects multiplication by constant scalars, giving the displayed natural iso. -/
theorem cohomology_representation (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : ℤ) :
    Nonempty (shiftFunctor (category ell X) i ⋙ sections ell X ≅
      CondensedRing.condensedRingOrdinaryCohomology (ring.{u} ell) f i ⋙
        ModuleCat.restrictScalars (Profinite.continuousMapConstRingHom (Padic ell))) := by
  sorry

/-- Constants in the terminal scalar ring used by the recorded normalized transport.
Source: the same Q_ell scalar action (blueprint: def-weil-poincare-trace-cup). -/
def terminalScalar : Padic ell →+* condensedScalarRing (ring.{u} ell) :=
  (InternalAbelianSheafModule.sectionGlobalEquiv (coherentTopology Profinite.{u})
    (ring.{u} ell) (⊤_ Profinite.{u}) terminalIsTerminal).toRingHom.comp
      (Profinite.continuousMapConstRingHom (Padic ell))

/-- The scalar cohomology functor used by the recorded normalized global transport.
Source: RΓ and constant scalar restriction (blueprint: def-weil-poincare-trace-cup). -/
abbrev transportedCohomology (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (i : ℤ) :
    category ell X ⥤ ModuleCat.{u + 1} (Padic ell) :=
  CondensedRing.CohomologyTransport.R (ring.{u} ell) a ⋙
    CondensedRing.CohomologyTransport.Γ (ring.{u} ell) (Spec (.of k)) ⋙
      DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
        (ModuleCat.{u + 1} (condensedScalarRing (ring.{u} ell))) i ⋙
        ModuleCat.restrictScalars.{u + 1} (terminalScalar.{u} ell)

/-- The uniquely normalized comparison to cohomology via the recorded RΓ transport.
Its value is characterized on every Yoneda class by the section-unit adjunction.
Source: the ordinary cohomology convention (blueprint: def-weil-poincare-trace-cup).
Proof: evaluate a representative into a K-injective complex at the coefficient unit.
The derived global-sections adjunction identifies this map with its hypercohomology
class. Exact terminal-point evaluation gives the same class in transportedCohomology.
The construction is natural in the complex and constant scalars, and uniqueness
follows because every class is represented by such a derived unit map. -/
theorem transport_representation (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (i : ℤ) :
    Nonempty (shiftFunctor (category ell X) i ⋙ sections ell X ≅
      transportedCohomology ell k a i) := by
  sorry

/-- The Hom model carries the actual pullback from the recorded RΓ isomorphism square.
Source: normalized cohomology pullback (blueprint: def-weil-poincare-trace-cup).
Proof: both maps transpose the coefficient unit by the same pullback/direct-image
adjunction. The exchange is defined as the mate of the pullback compositor. Its
unit/counit cancellations reduce it to applying derived inverse image to the class
and then the canonical coefficient-unit comparison. Naturality in shifts gives
this equality in every integer degree. -/
theorem pull_transport (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) (a' : X ⟶ Spec (.of k))
    [QuasiCompact a'] (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b]
    (f : X ⟶ Y) [IsIso f] (w : f ≫ a = a' ≫ b) (i : ℤ) :
    ∃ e : shiftFunctor (category ell Y) i ⋙ sections ell Y ≅
        transportedCohomology ell k a i,
    ∃ e' : shiftFunctor (category ell X) i ⋙ sections ell X ≅
        transportedCohomology ell k a' i,
    ∀ x : cohomology ell Y i,
      (e'.hom.app (unit ell X)) (pull ell f i x) =
        (ModuleCat.restrictScalars.{u + 1} (terminalScalar.{u} ell)).map
          ((DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
            (ModuleCat.{u + 1} (condensedScalarRing (ring.{u} ell))) i).map
            (CondensedRing.CohomologyTransport.t (ring.{u} ell) a a' b f w (unit ell Y) ≫
              (CondensedRing.CohomologyTransport.Γ (ring.{u} ell) (Spec (.of k))).map
                ((CondensedRing.CohomologyTransport.R (ring.{u} ell) a').map
                  (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) f).hom)))
          ((e.hom.app (unit ell Y)) x) := by
  sorry

/-- The coefficient multiplication gives the graded-commutative cup product.
Source: the displayed graded-commutativity identity
(blueprint: def-weil-poincare-trace-cup).
Proof: move the two shifts out of the tensor product. Interchanging them contributes
(-1)^(ij), while symmetry of the coefficient-unit multiplication removes the switch
of the two unshifted factors. The derived unitors commute with shift, so the
Eckmann-Hilton identity gives the stated formula. -/
theorem cup_comm {X : Scheme.{u}} (i j : ℤ)
    (x : cohomology ell X i) (y : cohomology ell X j) :
    cup ell y x = (i * j).negOnePow • (cup ell x y ≫
      (eqToIso (congrArg (fun n : ℤ ↦ (unit ell X) ⟦n⟧) (add_comm i j))).hom) := by
  sorry

open PurityTransport

/-- The positive Tate sheaf in degree zero.
Source: the orientation and coefficient twist (blueprint: def-weil-poincare-trace-cup). -/
abbrev positiveLine (X : Scheme.{u}) (d : ℕ) : category ell X :=
  (DerivedCategory.singleFunctor _ 0).obj ((Coefficient.rationals).line ell X d)

/-- The negative Tate line is the internal dual of the positive Tate line.
Source: the negative-twist definition (blueprint: def-weil-poincare-trace-cup). -/
abbrev negativeLine (X : Scheme.{u}) (d : ℕ) : category ell X :=
  (ihom (positiveLine ell X d)).obj (unit ell X)

/-- The derived dual presentation is the existing signed Tate line in degree zero.
Source: the signed Tate convention (blueprint: def-weil-poincare-trace-cup).
Proof: a root-trivializing cover makes the positive line free of rank one. Its
ordinary internal dual is therefore already its derived internal dual. The
degree-zero tensor and unit comparisons give the displayed isomorphism, including
d=0, and these canonical evaluation-transpose maps descend from the cover. -/
theorem negativeLine_published (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    Nonempty (CondensedRing.StrictWeil.derivedTateLine ell .rationals X (-(d : ℤ)) ≅
      negativeLine ell X d) := by
  sorry

/-- The coefficient-space Tate line, with its actual constant scalar action.
Source: Q_ell(-d) in the trace formula (blueprint: def-weil-poincare-trace-cup). -/
abbrev valueLine (X : Scheme.{u}) (d : ℕ) : ModuleCat.{u + 1} (Padic ell) :=
  (sections ell X).obj (negativeLine ell X d)

/-- Root-normalized positive Tate pullback in the actual derived category.
Source: the canonical Tate Weil structure (blueprint: def-weil-poincare-trace-cup). -/
def positiveStructure {X : Scheme.{u}} (g : Aut X)
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    (CondensedRing.StrictWeil.action (ring.{u} ell) g).obj (positiveLine ell X d) ≅
      positiveLine ell X d :=
  CondensedRing.StrictWeil.tateDatum ell .rationals g (d : ℤ)

/-- Frobenius on the internal dual line, using the inverse positive-line datum.
Source: contragredient Tate structure (blueprint: def-weil-poincare-trace-cup). -/
def negativeStructure {X : Scheme.{u}} (g : Aut X)
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    (CondensedRing.StrictWeil.action (ring.{u} ell) g).obj (negativeLine ell X d) ≅
      negativeLine ell X d :=
  CondensedRing.StrictWeil.dualDatum (ring.{u} ell) g (positiveLine ell X d)
    (positiveStructure ell g d)

/-- The actual root-induced action on the coefficient-space Tate line.
Source: geometric Frobenius on Q_ell(-d) (blueprint: def-weil-poincare-trace-cup). -/
def valueFrobenius {X : Scheme.{u}} (g : Aut X)
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ)
    (z : valueLine ell X d) : valueLine ell X d :=
  (Functor.Monoidal.εIso (CondensedRing.StrictWeil.action (ring.{u} ell) g)).hom ≫
    (CondensedRing.StrictWeil.action (ring.{u} ell) g).map z ≫ (negativeStructure ell g d).hom

/-- The coefficient prime is invertible at every residue field over the fixed closure.
Source: the standing prime convention (blueprint: def-weil-poincare-trace-cup).
Proof: the fixed closure has characteristic p. The distinct prime ell is nonzero
there; its inverse maps to an inverse through the field map into each residue field. -/
theorem residue_prime_unit (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k)) (x : X) :
    IsUnit (ell : X.residueField x) := by
  sorry

/-- Canonical root-projection, scalar-extension and tensor-power coordinates.
The normalization equations determine every map; no frame is selected.
Source: the Cartesian Tate comparisons (blueprint: def-weil-poincare-trace-cup). -/
def normalizedCoordinates (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of D.k)) (b : Y ⟶ Spec (.of D.k)) (f : X ⟶ Y) :
    LinePullCoordinates ell .rationals f :=
  letI : ∀ x : X, Invertible (ell : X.residueField x) :=
    fun x ↦ (residue_prime_unit ell D hEll a x).invertible
  letI : ∀ y : Y, Invertible (ell : Y.residueField y) :=
    fun y ↦ (residue_prime_unit ell D hEll b y).invertible
  Classical.choice (linePullCoordinates_nonempty ell .rationals f)

/-- The root-induced action on the geometric coefficient point, with invertibility proved.
Source: geometric Frobenius on Q_ell(-d) (blueprint: def-weil-poincare-trace-cup). -/
def pointValueFrobenius (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (z : valueLine ell (Spec (.of D.k)) d) :
    valueLine ell (Spec (.of D.k)) d :=
  letI : ∀ x : Spec (.of D.k), Invertible (ell : (Spec (.of D.k)).residueField x) :=
    fun x ↦ (residue_prime_unit ell D hEll (𝟙 _) x).invertible
  valueFrobenius ell (CondensedRing.StrictWeil.pointFrobenius D) d z


variable {ell} {D : WeilConjectures.FiniteFieldDatum.{u}} (s : SmoothDatum D)

/-- The regular module is constructible and has Tor interval [0,0].
Source: the coefficient unit (blueprint: def-weil-poincare-trace-cup).
Proof: on the identity stratification its model is the free rank-one scalar module.
The complex is concentrated in degree zero and its tensor functor is the identity. -/
theorem unit_mem : property ell .rationals s.Y.left
    (PurityTransport.unit ell .rationals s.Y.left) := by
  sorry

/-- The fixed closure has the prescribed positive characteristic.
Source: finite-field conventions (blueprint: def-weil-poincare-trace-cup).
Proof: a finite field of cardinality p^a with a positive has characteristic p.
An algebraic extension of a field has the same characteristic. -/
theorem closure_characteristic : ringChar D.k = D.p := by
  sorry

/-- The literal morphism of the two recorded schemes over the fixed closure.
Source: a_X as an over-field morphism (blueprint: def-weil-poincare-trace-cup). -/
abbrev nativeMap : s.X ⟶ s.Y := s.map.asOver (Spec (.of D.k))

/-- The compactification used by the recorded native constructible exceptional functor.
Source: the exceptional inverse-image convention
(blueprint: def-weil-poincare-trace-cup). -/
abbrev nativeCompactification : Compactification s.map :=
  CondensedRing.compactificationOverField (nativeMap s)

/-- The rational ring is one of the actual native exceptional coefficients.
Source: the coefficient convention (blueprint: def-weil-poincare-trace-cup).
Proof: choose the rational disjunct and the identity ring-object isomorphism. -/
theorem nativeCoefficient : CondensedRing.IsNativeExceptionalCoefficient ell (ring.{u} ell) :=
  by sorry

/-- The actual constructible exceptional inverse image of the coefficient unit.
Source: Ra_X^! Q_ell in the chosen orientation
(blueprint: def-weil-poincare-trace-cup). -/
def exceptionalUnit (hEll : ell ≠ D.p) : category ell s.X.left :=
  letI : Fact (ringChar D.k).Prime := ⟨by rw [closure_characteristic (D := D)]; exact D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨by rw [closure_characteristic (D := D)]; exact hEll.symm⟩
  ((CondensedRing.constructibleExceptionalInverseImage (ring.{u} ell) ell D.k
    (nativeMap s) (nativeCoefficient (ell := ell))).obj
      ⟨PurityTransport.unit ell .rationals s.Y.left, (unit_mem s).1⟩).obj

/-- The trace uses precisely the chosen orientation and the recorded exceptional counit.
Source: eta_X and Ra_! Ra^! Q_ell -> Q_ell
(blueprint: def-weil-poincare-trace-cup). -/
def smoothTrace (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
      (nativeCompactification s)).obj
        (Coefficient.rationals.derivedLine ell s.X.left s.dim) ⟶ unit ell s.Y.left :=
  letI : Fact (ringChar D.k).Prime := ⟨by rw [closure_characteristic (D := D)]; exact D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨by rw [closure_characteristic (D := D)]; exact hEll.symm⟩
  (CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
    (nativeCompactification s)).map η.inv ≫
      ((CondensedRing.constructibleExceptionalAdjunction (ring.{u} ell) ell D.k
        (nativeMap s) (nativeCoefficient (ell := ell))).counit.app
          ⟨PurityTransport.unit ell .rationals s.Y.left, (unit_mem s).1⟩).hom ≫
        (DerivedCategory.singleFunctorObjUnitIso
          (Mod (Sheaf (ProEt.topology s.Y.left) Ab.{u + 1})
            (condensedRingObj (ring.{u} ell) s.Y.left))).hom

/-- The compactly supported twisted top trace, before forgetting proper support.
Source: tr_X on H_c^(2d)(X,Q_ell(d))
(blueprint: def-weil-poincare-trace-cup). -/
def compactTrace (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (x : unit ell s.Y.left ⟶
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
        (nativeCompactification s)).obj (positiveLine ell s.X.left s.dim)) ⟦2 * (s.dim : ℤ)⟧) :
    unit ell s.Y.left ⟶ unit ell s.Y.left :=
  x ≫ ((CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
    (nativeCompactification s)).commShiftIso (2 * (s.dim : ℤ))).inv.app _ ≫ smoothTrace s hEll η

/-- For a proper map the specified support-forgetting comparison is invertible.
Source: the proper comparison in the trace definition
(blueprint: def-weil-poincare-trace-cup).
Proof: in a compactification of a proper morphism the open immersion is also closed.
Extension by zero equals direct image on its open-and-closed image. The ordinary
pushforward compositor then identifies the specified map with the identity. -/
theorem properComparison_isIso [IsProper s.map] (K : category ell s.X.left) :
    IsIso (traceShriekToStar ell .rationals (nativeCompactification s) K) := by
  sorry

/-- The smooth trace read on ordinary direct image for a proper structure morphism.
Source: the proper trace comparison (blueprint: def-weil-poincare-trace-cup). -/
def ordinarySmoothTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim) :
    (CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (Coefficient.rationals.derivedLine ell s.X.left s.dim) ⟶ unit ell s.Y.left :=
  letI := properComparison_isIso s
    (Coefficient.rationals.derivedLine ell s.X.left s.dim)
  inv (traceShriekToStar ell .rationals (nativeCompactification s)
    (Coefficient.rationals.derivedLine ell s.X.left s.dim)) ≫ smoothTrace s hEll η

/-- The positive-line inverse-image comparison in degree zero, with root normalization.
Source: Cartesian Tate twists (blueprint: def-weil-poincare-trace-cup). -/
def pullPositive (p : LinePullCoordinates ell .rationals s.map) :
    (CondensedRing.upperStar (ring.{u} ell) s.map).leftDerivedFunctor.obj
      (positiveLine ell s.Y.left s.dim) ≅ positiveLine ell s.X.left s.dim :=
  (shiftFunctor (category ell s.X.left) (2 * (s.dim : ℤ))).preimageIso
    (((CondensedRing.upperStar (ring.{u} ell) s.map).leftDerivedFunctor.commShiftIso
      (2 * (s.dim : ℤ))).symm.app (positiveLine ell s.Y.left s.dim) ≪≫
        LinePullCoordinates.derived ell p s.dim)

/-- The twisted ordinary trace: projection, Cartesian Tate comparison, and the counit.
Source: untwisting the smooth trace (blueprint: def-weil-poincare-trace-cup). -/
def twistedTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map) :
    ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (unit ell s.X.left)) ⟦2 * (s.dim : ℤ)⟧ ⊗ positiveLine ell s.Y.left s.dim ⟶
        unit ell s.Y.left :=
  (((curriedTensor (category ell s.Y.left)).flip.obj
    (positiveLine ell s.Y.left s.dim)).commShiftIso (2 * (s.dim : ℤ))).hom.app _ ≫
      (CondensedRing.properProjectionMorphism (ring.{u} ell) s.map
        (unit ell s.X.left) (positiveLine ell s.Y.left s.dim)) ⟦2 * (s.dim : ℤ)⟧' ≫
      ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.map
        ((unit ell s.X.left) ◁ (pullPositive s p).hom ≫ (λ_ _).hom)) ⟦2 * (s.dim : ℤ)⟧' ≫
      ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.commShiftIso
        (2 * (s.dim : ℤ))).inv.app _ ≫ ordinarySmoothTrace s hEll η

/-- The untwisted trace as a map to the actual internal dual Tate line.
Source: tr_X^(-d) (blueprint: def-weil-poincare-trace-cup). -/
def untwistedTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map)
    (x : cohomology ell s.X.left (2 * (s.dim : ℤ))) : valueLine ell s.Y.left s.dim :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology s.Y.left) Ab.{u + 1})
      (condensedRingObj (ring.{u} ell) s.Y.left))
  (CondensedRing.derivedUpperStarLowerStarAdjunction (ring.{u} ell) s.map).homEquiv _ _
      ((CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) s.map).hom ≫ x) ≫
    ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.commShiftIso
      (2 * (s.dim : ℤ))).hom.app _ ≫
      curry ((β_ (positiveLine ell s.Y.left s.dim)
        (((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
          (unit ell s.X.left)) ⟦2 * (s.dim : ℤ)⟧)).hom ≫ twistedTrace s hEll η p)

/-- The trace-cup pairing in any two complementary integer degrees.
Source: the displayed pairing (blueprint: def-weil-poincare-trace-cup). -/
def pairing [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map) (i j : ℤ)
    (hij : i + j = 2 * (s.dim : ℤ))
    (x : cohomology ell s.X.left i) (y : cohomology ell s.X.left j) :
    valueLine ell s.Y.left s.dim :=
  untwistedTrace s hEll η p (cup ell x y ≫
    (eqToIso (congrArg (fun n : ℤ ↦ (unit ell s.X.left) ⟦n⟧) hij)).hom)

end AlgebraicGeometry.ProEtale.CondensedPoincare
