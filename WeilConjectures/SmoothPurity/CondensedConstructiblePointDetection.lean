/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Geometric inverse images detect bounded constructible condensed complexes

Source: latest blueprint, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2, final sentence (blueprint: lem-pur-condensed-constructible-point-detection).

All categories here are ordinary derived categories over the actual pulled-back ring object.
The point functor keeps the full small pro-etale site of the algebraically closed field.
The finite-level clause retains the specified etale-origin representative and its maps.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing continuous-map condensed commutative ring, bundled with its existing
canonical ring structure. This only packages the published construction.
Source: current blueprint coefficient convention
(blueprint: lem-pur-condensed-constructible-point-detection). -/
noncomputable def continuousMapCoefficient (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  ⟨Profinite.continuousMapRingObj T⟩

/-- Geometric inverse-image detection for bounded constructible condensed pro-etale complexes.
Source: current blueprint, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2, final sentence (blueprint: lem-pur-condensed-constructible-point-detection).
Proof: exact module pullback and its derived factorization give the cohomology comparison.
A locally finitely presented module with zero geometric pullbacks is zero: on a weakly
contractible affine chart present it by a finite matrix of coefficient sections on the
profinite component space. Pullback at a geometric point evaluates that matrix. Vanishing
makes every evaluated matrix surjective; profinite matrix splitting gives a continuous right
inverse in the same coefficient ring, so the cokernel is zero on the chart and hence locally.
For a constructible module, use Noetherian induction on closed subsets. On a nonempty closed
subset, generic local finite presentation gives a nonempty open on which the preceding
argument applies. The complement vanishes by induction, and the open-closed exact sequence
then gives vanishing on the closed subset. Apply this to each cohomology sheaf of a bounded
constructible complex, using exactness of pullback, and use the unbounded cohomology criterion.
The allowed coefficient rings give triangulated closure of bounded constructible complexes;
apply zero detection to a cone to obtain the isomorphism criterion. Conversely functors
preserve zero objects and isomorphisms. -/
theorem geometricPoint_detection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) (hn : 1 ≤ n)
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = (let A := Padic.coefficientExtensionRing ell E n
        letI : TopologicalSpace A := ⊥
        letI : DiscreteTopology A := discreteTopology_bot A
        letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
        continuousMapCoefficient A) ∨
      Λ = ⟨Profinite.padicIntegersRingObj ell E⟩ ∨
      Λ = continuousMapCoefficient E ∨
      Λ = ⟨Profinite.padicAlgClRingObj ell⟩)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj Λ.X Y.left))}
    (hK : boundedConstructible (condensedRingObj Λ.X Y.left) K)
    (hL : boundedConstructible (condensedRingObj Λ.X Y.left) L)
    (u : K ⟶ L) :
    (IsIso u ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (b : Spec (.of Ω) ⟶ Y.left),
        IsIso ((CondensedRing.upperStar Λ.X b).leftDerivedFunctor.map u)) ∧
    (∀ (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ.X Y.left))),
      boundedConstructible (condensedRingObj Λ.X Y.left) M →
      (IsZero M ↔
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (b : Spec (.of Ω) ⟶ Y.left),
          IsZero ((CondensedRing.upperStar Λ.X b).leftDerivedFunctor.obj M))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ Y.left),
      PreservesFiniteLimits (CondensedRing.upperStar Λ.X b) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ.X b) ∧
      ∀ (r : ℤ) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ.X Y.left))),
        Nonempty ((DerivedCategory.homologyFunctor _ r).obj
          ((CondensedRing.upperStar Λ.X b).leftDerivedFunctor.obj M) ≅
          (CondensedRing.upperStar Λ.X b).obj
            ((DerivedCategory.homologyFunctor _ r).obj M))) ∧
    (∀ (C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ.X Y.left)))
      (v : L ⟶ C) (w : C ⟶ K⟦1⟧),
      Pretriangulated.Triangle.mk u v w ∈ distTriang _ →
        boundedConstructible (condensedRingObj Λ.X Y.left) C) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Elaborating the derived comparison unit in these module-sheaf categories needs more heartbeats.
/-- At finite level, full geometric derived inverse images and the ordinary geometric
stalks of a retained etale-origin representative give the same invertibility criterion.
Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 2; Stacks Tags 0991 and 099R
(blueprint: lem-pur-condensed-constructible-point-detection).
Proof: use the canonical finite coefficient derived equivalence to transport the original
arrow to fixed-scalar module sheaves. Conjugate it by the specified endpoint isomorphisms
and the retained origin isomorphisms. The representative equality identifies it with the
comparison image of f. Bounded-below comparison is fully faithful, so it reflects
invertibility. Ordinary etale geometric stalks detect each cohomology map of f, and the
unbounded cohomology criterion detects f itself. Finally the main theorem identifies
invertibility of the original arrow with invertibility of all its full point pullbacks.
This uses the stated etale origins and makes no claim about arbitrary pro-etale stalks. -/
theorem finite_geometricPoint_stalk_detection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) (hn : 1 ≤ n)
    (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    let A := Padic.coefficientExtensionRing ell E n
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    let Q := finiteCoefficientDerivedEquivalence Y.left A
    ∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj A) Y.left))),
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj A) Y.left) K →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj A) Y.left) L →
      ∀ (KF LF : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
        (eK : Q.functor.obj K ≅ KF.obj) (eL : Q.functor.obj L ≅ LF.obj)
        (wK : Scheme.FixedEtaleOriginWitness Y.left (ULift.{u + 1} A) KF)
        (wL : Scheme.FixedEtaleOriginWitness Y.left (ULift.{u + 1} A) LF)
        (u : K ⟶ L) (f : wK.complex ⟶ wL.complex),
        wK.iso.hom ≫ eK.inv ≫ Q.functor.map u ≫ eL.hom =
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
            Y.left).mapDerivedCategory).map ((DerivedCategory.Plus.ι).map f) ≫ wL.iso.hom →
        ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ Y.left),
          IsIso (((CondensedRing.upperStar (Profinite.continuousMapRingObj A)
            b).leftDerivedFunctor).map u)) ↔
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (b : Spec (.of Ω) ⟶ Y.left) (r : ℤ),
          IsIso ((Scheme.pointSmallEtale b).sheafFiber.map
            ((DerivedCategory.homologyFunctor _ r).map ((DerivedCategory.Plus.ι).map f)))) := by
  dsimp only
  intro K L hK hL KF LF eK eL wK wL u f hcomp
  let A := Padic.coefficientExtensionRing ell E n
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  let B := ULift.{u + 1} A
  let Q := finiteCoefficientDerivedEquivalence Y.left A
  let V := comparisonUpperStar (ModuleCat.{u + 1} B) Y.left
  let f₀ := DerivedCategory.Plus.ι.map f
  have hpoint := (geometricPoint_detection D ell hell E n hn
    (continuousMapCoefficient A) (Or.inl rfl) Y hK hL u).1
  have htransport : IsIso u ↔ IsIso (V.mapDerivedCategory.map f₀) := by
    constructor
    · intro hu
      let := hu
      have heq : IsIso (wK.iso.hom ≫ eK.inv ≫ Q.functor.map u ≫ eL.hom) :=
        inferInstance
      rw [hcomp] at heq
      exact IsIso.of_isIso_comp_right _ wL.iso.hom
    · intro hf
      let := hf
      have heq : IsIso (V.mapDerivedCategory.map f₀ ≫ wL.iso.hom) := inferInstance
      rw [← hcomp] at heq
      have h₁ : IsIso (eK.inv ≫ Q.functor.map u ≫ eL.hom) :=
        IsIso.of_isIso_comp_left wK.iso.hom _
      have h₂ : IsIso (Q.functor.map u ≫ eL.hom) :=
        IsIso.of_isIso_comp_left eK.inv _
      have h₃ : IsIso (Q.functor.map u) := IsIso.of_isIso_comp_right _ eL.hom
      exact isIso_of_reflects_iso u Q.functor
  have hcomparison : IsIso (V.mapDerivedCategory.map f₀) ↔ IsIso f₀ := by
    constructor
    · intro hf
      let := hf
      let adj := derivedComparisonAdjunction (ModuleCat.{u + 1} B) Y.left
      let R := (comparisonLowerStar (ModuleCat.{u + 1} B) Y.left).rightDerivedFunctor
      have hKunit : IsIso (adj.unit.app wK.complex.obj) :=
        isIso_derivedComparisonAdjunction_unit_app _ _ _ wK.complex.property
      have hLunit : IsIso (adj.unit.app wL.complex.obj) :=
        isIso_derivedComparisonAdjunction_unit_app _ _ _ wL.complex.property
      have heq : IsIso (adj.unit.app wK.complex.obj ≫
          R.map (V.mapDerivedCategory.map f₀)) := by infer_instance
      have hnat : f₀ ≫ adj.unit.app wL.complex.obj =
          adj.unit.app wK.complex.obj ≫ R.map (V.mapDerivedCategory.map f₀) :=
        adj.unit.naturality f₀
      have : IsIso (f₀ ≫ adj.unit.app wL.complex.obj) := hnat.symm ▸ heq
      exact IsIso.of_isIso_comp_right f₀ (adj.unit.app wL.complex.obj)
    · intro hf
      let := hf
      infer_instance
  dsimp only [continuousMapCoefficient] at hpoint
  refine hpoint.symm.trans (htransport.trans (hcomparison.trans ?_))
  rw [DerivedCategory.isIso_iff]
  constructor
  · intro hf Ω _ _ b r
    let := hf r
    infer_instance
  · intro hf r
    apply Scheme.isIso_of_isIso_sheafFiber_map
    intro x
    let b := Y.left.algClosurePoint x
    have hb := hf _ b r
    exact (NatIso.isIso_map_iff
      ((Scheme.pointSmallEtale b).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} B))
      ((DerivedCategory.homologyFunctor _ r).map f₀)).mpr hb

end AlgebraicGeometry.ProEtale.CondensedRing
