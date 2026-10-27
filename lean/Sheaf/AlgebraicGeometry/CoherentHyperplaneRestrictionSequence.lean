/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistMul
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A regular hyperplane restriction sequence for a coherent module

Source: Stacks Project, varieties.tex, Tags 089Z, 08A0 and 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence).

The auxiliary constructions specify the actual zero scheme, tensor pullback,
multiplication, restriction, and triangle boundary occurring in the statement.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace.HyperplaneRestriction

noncomputable section

variable {I : Type u} {S : Scheme.{u}}

/-- The zero scheme of the linear section, not an independently chosen subscheme.
Source: Stacks, Tag 089Z (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def hyperplane (s : Γ(twist I S 1, ⊤)) : Scheme.{u} :=
  (homOfGlobalSection (twist I S 1) s).zeroLocus.subscheme

/-- The closed immersion of the section's zero scheme.
Source: Stacks, Tag 089Z (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def inclusion (s : Γ(twist I S 1, ⊤)) : hyperplane s ⟶ ℙ(I; S) :=
  (homOfGlobalSection (twist I S 1) s).zeroLocus.subschemeι

/-- Twists on the hyperplane are the prescribed pullbacks of ambient twists.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def twistOn (s : Γ(twist I S 1, ⊤)) (d : ℤ) : (hyperplane s).Modules :=
  (tensorPullback (inclusion s)).obj (twist I S d)

/-- The twisted restriction is `i^* F tensor i^* O(d)`.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def moduleOn (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    (hyperplane s).Modules :=
  (tensorPullback (inclusion s)).obj F ⊗ twistOn s d

/-- The tensor comparison is fixed by its pure-section formula in Tag 01CD.
Source: Stacks, Tags 01CD, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def restrictionIso (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    (tensorPullback (inclusion s)).obj (F ⊗ twist I S d) ≅ moduleOn s F d :=
  Classical.choose (module_pullback_tensor (inclusion s)) F (twist I S d)

/-- Multiplication by the chosen linear section in every integer twist.
Source: Stacks, Tags 08A0, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def multiply (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    F ⊗ twist I S (d - 1) ⟶ F ⊗ twist I S d :=
  F ◁ twistMulHom (n := I) (by omega : 1 + (d - 1) = d) s

/-- The quotient arrow is the normalized pullback unit followed by tensor comparison.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def restriction (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    F ⊗ twist I S d ⟶ (pushforward (inclusion s)).obj (moduleOn s F d) :=
  (tensorPullbackSectionAdjunction (inclusion s)).unit.app (F ⊗ twist I S d) ≫
    (pushforward (inclusion s)).map (restrictionIso s F d).hom

/-- The induced restriction on module right-derived cohomology.
Source: Stacks, Tags 01FB, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def cohomologyRestriction (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules)
    (d : ℤ) (q : ℕ) :=
  moduleCohomologyFMap (inclusion s) (restriction s F d) q

/-- Restriction on global sections, including the canonical inverse-image-of-top cast.
Source: Stacks, Tags 0096, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def globalRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) :=
  ((tensorPullbackSectionAdjunction f).unit.app M).app ⊤ ≫
    ((tensorPullback f).obj M).presheaf.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens))

/-- The restriction of a twisted module section, expressed in `i^*F(d)`.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def moduleSectionRestriction (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    Γ(F ⊗ twist I S d, ⊤) ⟶ Γ(moduleOn s F d, ⊤) :=
  globalRestriction (inclusion s) (F ⊗ twist I S d) ≫ (restrictionIso s F d).hom.app ⊤

/-- Pull back the canonical twist multiplication through its normalized tensor comparison.
Source: Stacks, Tags 01CD, 01MT
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def pulledMultiplication {X : Scheme.{u}} (f : X ⟶ ℙ(I; S)) (d e : ℤ) :
    (tensorPullback f).obj (twist I S d) ⊗ (tensorPullback f).obj (twist I S e) ⟶
      (tensorPullback f).obj (twist I S (d + e)) :=
  (Classical.choose (module_pullback_tensor f) (twist I S d) (twist I S e)).inv ≫
    (tensorPullback f).map (twistTensorIso I S d e).hom

/-- Multiplication of a twisted restricted module by a restricted linear section.
Source: Stacks, Tags 01CD, 01MT, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def moduleMultiplication (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ) :
    moduleOn s F d ⊗ twistOn s 1 ⟶ moduleOn s F (d + 1) :=
  (α_ ((tensorPullback (inclusion s)).obj F) (twistOn s d) (twistOn s 1)).hom ≫
    (tensorPullback (inclusion s)).obj F ◁ pulledMultiplication (inclusion s) d 1

/-- The canonical triangle boundary, using standard derived-category models explicitly.
Source: Stacks, Tags 01DZ, 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def sequenceBoundary (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ)
    (hz : multiply s F d ≫ restriction s F d = 0)
    (hs : (ShortComplex.mk (multiply s F d) (restriction s F d) hz).ShortExact)
    (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology (ℙ(I; S)).toRingedSpace q).obj
          ((pushforward (inclusion s)).obj (moduleOn s F d))) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology (ℙ(I; S)).toRingedSpace (q + 1)).obj
          ((F ⊗ twist I S (d - 1)) : (ℙ(I; S)).Modules)) :=
  (forget₂ _ AddCommGrpCat.{u}).map
    (@RingedSpace.moduleCohomologyBoundary (ℙ(I; S)).toRingedSpace
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (ShortComplex.mk (C := (ℙ(I; S)).Modules)
        (multiply s F d) (restriction s F d) hz) hs q)

/-- The connecting arrow after the canonical closed-immersion cohomology comparison.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-hyperplane-restriction-sequence). -/
def boundary (s : Γ(twist I S 1, ⊤)) (F : (ℙ(I; S)).Modules) (d : ℤ)
    (hz : multiply s F d ≫ restriction s F d = 0)
    (hs : (ShortComplex.mk (multiply s F d) (restriction s F d) hz).ShortExact)
    (q : ℕ) (he : IsIso (moduleCohomologyEdgeMap (inclusion s) (moduleOn s F d) q)) :=
  inv (I := he) (moduleCohomologyEdgeMap (inclusion s) (moduleOn s F d) q) ≫
    sequenceBoundary s F d hz hs q

/-- A coherent module has a regular hyperplane with compatible twists, its short exact
restriction sequences and their canonical long exact module-cohomology sequences.

Source: Stacks Project, varieties.tex, Tags 089Z, 08A0 and 0EGK
(blueprint: lem-sfb-coherent-hyperplane-restriction-sequence).

Proof (the six DAG steps):
1. The standard polynomial charts are Noetherian, by the finite-type algebra theorem.
The structure module is quasi-coherent of finite type, hence coherent by
pqf-lem-coherent-ft-locnoeth.
2. Apply lem-sfb-coherent-regular-hyperplane-restriction to the finite family consisting
of F and O. Its single section is nonzero, is regular on both modules, and has coherent
pullback of F. Tag 089Z identifies its zero scheme with projective space of dimension n-1:
on each standard chart its defining ideal is generated by s/T_j.
3. Starting with the degree-one comparison, define all degree comparisons by powers
of its unit coefficient in local frames, using dual powers for negative degrees.
The rule c^d c^e = c^(d+e) makes them compatible with multiplication, using
lem-pc-twist-tensor and lem-weil-pbc-module-pullback-tensor.
4. The common-hyperplane theorem gives the short exact sequences. Apply the long exact
sequence of pqf-def-cohomology and the canonical closed-immersion cohomology comparison.
Its boundary is the homology boundary of the derived-sections triangle. The quotient
maps are the pullback-unit restriction maps, so the displayed maps are restriction.
5. Apply the same sequence to O in twist one. The calculation in
lem-pc-projective-space-twist-cohomology gives H^1(P,O)=0 since n is positive;
therefore restriction of linear sections is surjective.
6. The pullback unit sends a section to 1 tensor that section. The section formula of
lem-weil-pbc-module-pullback-tensor and twist multiplication yield the asserted product
identity. These comparisons use the single hyperplane fixed in step 2. -/
theorem exists_coherentHyperplaneRestrictionSequence (k : Type u) [Field k] [Infinite k]
    (n : ℕ) (hn : 1 ≤ n)
    (F : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules)
    (hF : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace F) :
    ∃ s : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤), s ≠ 0 ∧
      ∃ (e : hyperplane s ≅ ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)))
        (θ : ∀ d : ℤ, twistOn s d ≅ (tensorPullback e.hom).obj
          (twist (ULift.{u} (Fin ((n - 1) + 1))) (Spec (.of k)) d)),
        (∀ d a : ℤ,
          pulledMultiplication (inclusion s) d a ≫ (θ (d + a)).hom =
            ((θ d).hom ⊗ₘ (θ a).hom) ≫ pulledMultiplication e.hom d a) ∧
        RingedSpace.IsCoherent (hyperplane s).toRingedSpace
          ((tensorPullback (inclusion s)).obj F) ∧
        (∀ d : ℤ, ∃ hz : multiply s F d ≫ restriction s F d = 0,
          ∃ hs : (ShortComplex.mk (multiply s F d) (restriction s F d) hz).ShortExact,
            Function.Injective
              (((RingedSpace.moduleCohomology
                (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace 0).map
                  (multiply s F d)).hom) ∧
            ∀ q : ℕ, ∃ he : IsIso
                (moduleCohomologyEdgeMap (inclusion s) (moduleOn s F d) q),
              Function.Exact
                (((RingedSpace.moduleCohomology
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace q).map
                    (multiply s F d)).hom)
                (cohomologyRestriction s F d q) ∧
              Function.Exact (cohomologyRestriction s F d q) (boundary s F d hz hs q he) ∧
              Function.Exact (boundary s F d hz hs q he)
                (((RingedSpace.moduleCohomology
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace (q + 1)).map
                    (multiply s F d)).hom)) ∧
        Function.Surjective (globalRestriction (inclusion s)
          (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1)) ∧
        ∀ (d : ℤ) (u : Γ(F ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d, ⊤))
          (v : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)),
          moduleSectionRestriction s F (d + 1)
              ((F ◁ twistMulHom (n := ULift.{u} (Fin (n + 1))) (Int.add_comm 1 d) v).app ⊤ u) =
            (moduleMultiplication s F d).app ⊤ (tmulSection
              (moduleSectionRestriction s F d u)
              (globalRestriction (inclusion s)
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1) v)) := by
  sorry

end

end AlgebraicGeometry.ProjectiveSpace.HyperplaneRestriction
