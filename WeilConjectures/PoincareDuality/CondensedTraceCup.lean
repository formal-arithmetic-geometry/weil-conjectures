/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.CondensedMixedSupportCup
import WeilConjectures.PoincareDuality.CondensedTraceCupEvaluationIso
import WeilConjectures.PoincareDuality.CondensedTraceCupCoreIso
public import WeilConjectures.PoincareDuality.CondensedProperComparison
public import WeilConjectures.PoincareDuality.ConstructibleSmoothTrace
public import WeilConjectures.PoincareDuality.CondensedPoincareSetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SecSmoothPurity.TransportUnits
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting

/-! # Trace and trace--cup pairing with actual condensed coefficients

Source: latest blueprint sec-poincare-duality/sk-def-trace-cup/_section.md.
The orientation is the uniquely integration-normalized purity family. The proper
comparison uses the identity compactification. Every cup is the mixed-support cup
followed by coefficient multiplication, transported by that proper comparison.
(blueprint: sk-def-trace-cup)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCup

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Evaluation of the positive Tate line against its signed inverse; at zero it is
unit multiplication. Source: twist cancellation (blueprint: sk-def-trace-cup). -/
def evaluation (T : Scheme.{u}) : (d : ℕ) →
    c.line ell T d ⊗ StrictWeil.tateLine ell c T (-(d : ℤ)) ⟶ 𝟙_ _
  | 0 => (λ_ _).hom
  | d + 1 => (ihom.ev (c.line ell T (d + 1))).app (𝟙_ _)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The root-normalized pullback coordinates; the normalization fields determine every
map, including tensor power zero. Source: Cartesian twists
(blueprint: sk-def-trace-cup). -/
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :=
  (linePullCoordinates_nonempty ell c f).some

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Twist pullback followed by evaluation, with the cohomological shift [2d].
This is the actual cancellation arrow, before proving it invertible.
Source: the source identification of U_X (blueprint: sk-def-trace-cup). -/
def cancellation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    (c.smoothSource ell f d).obj (StrictWeil.derivedTateLine ell c Y (-(d : ℤ))) ⟶
      (unit ell c X) ⟦2 * (d : ℤ)⟧ :=
  letI : BraidedCategory (c.derived ell X) := DerivedCategory.braidedCategory' _
  let F := upperStar (c.obj ell) f
  let N := StrictWeil.tateLine ell c Y (-(d : ℤ))
  let e := (linePull ell c f).power d
  let v : c.line ell X d ⊗ F.obj N ⟶ 𝟙_ _ :=
    (e.inv ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (evaluation ell c Y d) ≫ (Functor.Monoidal.εIso F).inv
  (((tensorLeft _).commShiftIso (2 * (d : ℤ))).app _).hom ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (((((F.singleFunctorCompLeftDerivedFunctorIso).app N).hom) ⊗ₘ 𝟙 _) ≫
        (β_ _ _).hom ≫
        (singleTensor ell c X _ _ (line_flat ell c X d)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map v)

set_option synthInstance.maxHeartbeats 0 in
-- The large cancellation composite needs unrestricted instance search.
/-- Cancellation is invertible at every coefficient stage.
Source: the twist evaluation identification in the defining paragraph
(blueprint: sk-def-trace-cup).
Proof: on a compatible primitive-root cover the positive line is the coefficient
unit and its negative signed line is its internal dual. The displayed map becomes
unit multiplication, hence is invertible. Inverse image, the flat single-tensor
comparison and shift preserve these isomorphisms. Invertibility descends from the
pro-etale cover. The argument includes d=0 and finite non-field coefficient rings. -/
theorem cancellation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    IsIso (cancellation ell c f d) := by
  classical
  let F := upperStar (c.obj ell) f
  let N := StrictWeil.tateLine ell c Y (-(d : ℤ))
  let e := (linePull ell c f).power d
  let v : c.line ell Y d ⊗ N ⟶ 𝟙_ _ := evaluation ell c Y d
  have hv : IsIso v := by
    dsimp [v]
    cases d with
    | zero =>
        change IsIso ((λ_ _).hom)
        infer_instance
    | succ d =>
        exact evaluation_isIso ell c d
  have hcore := core_isIso ell c f d e v hv
  dsimp [cancellation, v, F, N, e]
  infer_instance

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The signed coefficient Tate line as an actual constructible finite-Tor complex.
Source: K_- = Lambda_s(-d) (blueprint: sk-def-trace-cup). -/
def minus (Y : Scheme.{u}) [∀ y : Y, Invertible (ell : Y.residueField y)]
    (d : ℕ) : c.ctf ell Y :=
  ⟨StrictWeil.derivedTateLine ell c Y (-(d : ℤ)),
    StrictWeil.tate_mem ell c Y (-(d : ℤ))⟩

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- U_X is inverse twist cancellation followed by the normalized smooth-purity counit.
The latter is exactly the purity-then-constructible-counit composite, by the
right-adjoint-uniqueness normalization of canonicalPurity. No ambient adjoint is supplied.
Source: the displayed three-arrow composite U_X (blueprint: sk-def-trace-cup). -/
def untwistedDerivedTrace (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (s : SmoothDatum D)
    [∀ x : s.X.left, Invertible (ell : s.X.left.residueField x)]
    [∀ y : s.Y.left, Invertible (ell : s.Y.left.residueField y)] :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).obj
      ((unit ell c s.X.left) ⟦2 * (s.dim : ℤ)⟧) ⟶
        (minus ell c s.Y.left s.dim).obj :=
  letI := cancellation_isIso ell c s.map s.dim
  (rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
    (inv (cancellation ell c s.map s.dim)) ≫
      constructibleSmoothTrace ell D hEll c s (minus ell c s.Y.left s.dim)

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricProper (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    IsProper (G.structureMorphism D.k) :=
  inferInstanceAs (IsProper (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricSeparated (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    IsSeparated (G.structureMorphism D.k) :=
  inferInstanceAs (IsSeparated (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricQuasiCompact (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    QuasiCompact (G.structureMorphism D.k) :=
  inferInstanceAs (QuasiCompact (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricFiniteType (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    LocallyOfFiniteType (G.structureMorphism D.k) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricSmoothDimension (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    SmoothOfRelativeDimension d (G.structureMorphism D.k) :=
  inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The geometric index of the actual base-changed smooth proper model, with identity
compactification. Source: X_0, X and a_X (blueprint: sk-def-trace-cup). -/
def geometry (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    SmoothDatum D :=
  { X := Over.mk (G.structureMorphism D.k)
    xFinite := geometricFiniteType D d G
    xQuasiCompact := geometricQuasiCompact D d G
    xSeparated := geometricSeparated D d G
    Y := Over.mk (𝟙 (Spec (.of D.k)))
    yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
    yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
    ySeparated := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
    map := G.structureMorphism D.k
    isOver := (Scheme.Hom.isOver_iff (Spec (.of D.k))).mpr (Category.comp_id _)
    separated := geometricSeparated D d G
    finiteType := geometricFiniteType D d G
    quasiCompact := geometricQuasiCompact D d G
    dim := d
    smooth := geometricSmoothDimension D d G
    compactification := Compactification.ofIsProper (G.structureMorphism D.k) }

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Construct the required residue inverses from ell different from the characteristic.
Source: distinct primes in the fixed setting (blueprint: sk-def-trace-cup). -/
@[instance_reducible]
def residueInverse (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (T : Over (Spec (.of D.k))) : ∀ x : T.left, Invertible (ell : T.left.residueField x) :=
  fun x ↦ (map_natCast (T.hom.residueFieldAlgebraMap x) ell) ▸
    ((primeUnit D ell hEll).map (T.hom.residueFieldAlgebraMap x)).invertible

/-- Cohomology classes represented by scalar-unit maps to the shifted coefficient complex.
Source: representatives Lambda[-i] -> RΓ, equivalently Lambda -> RΓ[i]
(blueprint: sk-def-trace-cup). -/
abbrev Classes (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :=
  (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))) ⟶ M⟦i⟧

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Tensor two class representatives, extract their shifts, then apply the given
coefficient-complex product. Source: the representative prescription
(blueprint: sk-def-trace-cup). -/
def product {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {M N P : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))}
    (mulMap : M ⊗ N ⟶ P) (i j : ℤ) (x : Classes Λ M i) (y : Classes Λ N j) :
    Classes Λ P (i + j) :=
  (λ_ _).inv ≫ (x ⊗ₘ y) ≫
    (DerivedCategory.shiftTensorShiftIso _ M N i j).hom ≫ mulMap⟦i + j⟧'

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The canonical h_r induced by the proper comparison on coefficient complexes.
Source: kappa and h_r (blueprint: sk-def-trace-cup). -/
def properClassComparison (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] (i : ℤ) :
    Classes (c.obj ell)
      ((condensedRingCompactCoefficientComplex (c.obj ell)
        (Compactification.ofIsProper (G.structureMorphism D.k))).obj
          (unit ell c (G.geometricFiber D.k))) i ≃
    Classes (c.obj ell)
      ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
        (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i :=
  (Iso.refl _).homCongr
    ((shiftFunctor _ i).mapIso
      ((Functor.isoWhiskerRight (TraceCupProper.comparison (c.obj ell)
        (G.structureMorphism D.k))
          (TraceCupPoint.fiber (c.obj ell) D.k)).app _))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Ordinary cup is h_(i+j) of the mixed-support product of h_i inverse x and y,
followed by compact-support coefficient-unit multiplication. Source: cup display
(blueprint: sk-def-trace-cup). -/
def cupRepresentatives (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ)
    (x : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i)
    (y : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) j) :=
  let a := G.structureMorphism D.k
  let C := Compactification.ofIsProper a
  let K := unit ell c (G.geometricFiber D.k)
  let m : K ⊗ K ⟶ K :=
    ((DerivedCategory.singleFunctorObjUnitIso _).hom ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
  properClassComparison ell c D d G (i + j)
    (product
      (TraceCupMixed.cup (c.bundled ell) D.k C K K ≫
        (condensedRingCompactCoefficientComplex (c.obj ell) C).map m) i j
      ((properClassComparison ell c D d G i).symm x) y)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The untwisted compact trace on representative classes, obtained by Fib_s and H^0
with the shift identification. The target is the coefficient Tate line in degree zero.
Source: tau_X display (blueprint: sk-def-trace-cup). -/
def compactTraceRepresentatives (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :=
  let s := geometry D d G
  letI := residueInverse ell D hEll s.X
  letI := residueInverse ell D hEll s.Y
  let F := TraceCupPoint.fiber (c.obj ell) D.k
  let R := rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification
  let e := (Functor.commShiftIso (R ⋙ F) (2 * (d : ℤ))).app (unit ell c s.X.left)
  fun x : Classes (c.obj ell) ((R ⋙ F).obj (unit ell c s.X.left)) (2 * (d : ℤ)) ↦
    x ≫ e.inv ≫ F.map (untwistedDerivedTrace ell c D hEll s)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Canonical identification of scalar-unit representatives with actual cohomology.
It first uses the projective scalar module and then evaluates a linear map at 1.
Source: the representative prescription (blueprint: sk-def-trace-cup). -/
def classEquiv {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :
    Classes Λ M i ≃ ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M) :=
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (((DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of (Γ Λ) (Γ Λ)) i).app M).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((ModuleCat.homLinearEquiv (R := Γ Λ) (S := ℤ)
          (M := ModuleCat.of (Γ Λ) (Γ Λ))
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv))

/-- Actual ordinary cohomology with constant coefficients in degree i.
Source: H^i(X,Lambda) (blueprint: sk-def-trace-cup). -/
abbrev H (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) (i : ℤ) :=
  (condensedRingOrdinaryCohomology (c.obj ell) (G.structureMorphism D.k) i).obj
    (unit ell c (G.geometricFiber D.k))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The cup on actual ordinary cohomology groups, through their canonical representatives.
Source: h_(i+j) H_c(m) mu_c(h_i inverse x,y) (blueprint: sk-def-trace-cup). -/
def cup (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ) (x : H ell c D d G i) (y : H ell c D d G j) : H ell c D d G (i + j) :=
  let M := (condensedRingOrdinaryCoefficientComplex (c.obj ell)
    (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))
  classEquiv (Λ := c.obj ell) M (i + j) (cupRepresentatives ell c D d G i j
    ((classEquiv (Λ := c.obj ell) M i).symm x)
    ((classEquiv (Λ := c.obj ell) M j).symm y))

/-- The coefficient Tate line, defined as exactly H^0 Fib_s(Lambda_s(-d)).
Source: the displayed definition of Lambda(-d) (blueprint: sk-def-trace-cup). -/
abbrev TateLineValue (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ (c.obj ell))) 0).obj
    ((TraceCupPoint.fiber (c.obj ell) D.k).obj
      (StrictWeil.derivedTateLine ell c (Spec (.of D.k)) (-(d : ℤ))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The compact trace on actual cohomology, through the canonical projective-single
identification of representatives. Source: tau_X display (blueprint: sk-def-trace-cup). -/
def compactTrace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : (condensedRingCompactCohomology (c.obj ell)
      (Compactification.ofIsProper (G.structureMorphism D.k)) (2 * (d : ℤ))).obj
        (unit ell c (G.geometricFiber D.k))) : TateLineValue ell c D d :=
  let M := (condensedRingCompactCoefficientComplex (c.obj ell)
    (Compactification.ofIsProper (G.structureMorphism D.k))).obj
      (unit ell c (G.geometricFiber D.k))
  let N := (TraceCupPoint.fiber (c.obj ell) D.k).obj
    (StrictWeil.derivedTateLine ell c (Spec (.of D.k)) (-(d : ℤ)))
  let t := compactTraceRepresentatives ell c D hEll d G
    ((classEquiv (Λ := c.obj ell) M (2 * (d : ℤ))).symm x)
  classEquiv (Λ := c.obj ell) N 0 (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The ordinary trace is exactly tau_X after the inverse cohomology proper comparison.
Source: tr_X^(-d) display (blueprint: sk-def-trace-cup). -/
def trace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : H ell c D d G (2 * (d : ℤ))) : TateLineValue ell c D d :=
  compactTrace ell c D hEll d G
    (((TraceCupProper.cohomology (c.obj ell) (G.structureMorphism D.k)
      (2 * (d : ℤ))).inv.app (unit ell c (G.geometricFiber D.k))) x)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The trace--cup pairing on actual homology modules for every integer i. The output
is exactly H^0 Fib_s(Lambda_s(-d)), without choosing a trivialization of its Tate line.
Source: latest blueprint sk-def-trace-cup, final display (blueprint: sk-def-trace-cup). -/
def pairing (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i : ℤ) (x : H ell c D d G i) (y : H ell c D d G (2 * (d : ℤ) - i)) :
    TateLineValue ell c D d :=
  trace ell c D hEll d G
    ((eqToHom (congrArg (H ell c D d G)
      ((add_sub_assoc i (2 * (d : ℤ)) i).symm.trans
        (add_sub_cancel_left i (2 * (d : ℤ))))))
          (cup ell c D d G i (2 * (d : ℤ) - i) x y))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The trace--cup pairing in precisely the four coefficient stages of the fixed setting.
All finite-field, coefficient, uniformizer, geometric and properness hypotheses are
explicit; the coefficient Tate line is H^0 Fib_s(Lambda_s(-d)).
Source: latest blueprint sk-def-trace-cup, entire definition (blueprint: sk-def-trace-cup). -/
def traceCupPairing (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (b : CondensedPoincare.Stage)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i : ℤ) :
    H ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d G i →
      H ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d G (2 * (d : ℤ) - i) →
        TateLineValue ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d :=
  pairing ell (CondensedPoincare.coefficient ell E π hπ n hn b) D hEll d G i

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
