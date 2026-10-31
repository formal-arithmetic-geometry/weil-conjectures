/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace
public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace

/-! # The uniform Grothendieck–Lefschetz trace formula

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-thm-tf-uniform-formula/_section.md and sk-thm-tf-uniform-formula.proof.md
(blueprint: sk-thm-tf-uniform-formula).

The operators below use the existing semilinear return maps and actual terminal scalar
sections. A model compactification is base changed to the geometric field. All coefficients
are ordinary condensed coefficients and all complexes lie in the recorded Dctf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.UniformTrace

open ModelSemilinearComparison CondensedOpenProper

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Frobenius squares of the base-changed model compactification.
Source: uniform-formula proof, operator-identification paragraph
(blueprint: sk-thm-tf-uniform-formula).
Proof: compare the two fibre-product projections of the open square. The model projection
is fixed and the closure projection is followed by geometric field Frobenius. The proper
square is the second equation of galoisMap_projections. -/
theorem compactification_squares (c₀ : Compactification X₀.hom) :
    (StrictWeil.modelFrobenius D₀ X₀).hom ≫
        (geometricCompactification D₀ X₀ c₀).i =
      (geometricCompactification D₀ X₀ c₀).i ≫
        (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom ∧
    (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom ≫
        (geometricCompactification D₀ X₀ c₀).g =
      (geometricCompactification D₀ X₀ c₀).g ≫
        (StrictWeil.pointFrobenius D₀).hom := by
  sorry

variable (Λ : ScalarSixRing.{u})

/-- The actual compact-support scalar complex functor on the model compactification.
Source: uniform-formula (1), RΓ_c (blueprint: sk-thm-tf-uniform-formula). -/
abbrev compactSections (c₀ : Compactification X₀.hom) :=
  J Λ.X (geometricCompactification D₀ X₀ c₀).i ⋙
    R Λ.X (geometricCompactification D₀ X₀ c₀).g ⋙
      CohomologyTransport.Γ Λ.X (Spec (.of D₀.k))

/-- The scalar stalk at the canonical geometric lift of an extension-valued point.
Source: uniform-formula (1), K_ybar (blueprint: sk-thm-tf-uniform-formula). -/
abbrev stalkSections (m : ℕ) (hm : 1 ≤ m) (y : D₀.extensionPoints X₀ m hm) :=
  P Λ.X (WeilConjectures.localExtensionPoint D₀ X₀ m hm y) ⋙
    CohomologyTransport.Γ Λ.X (Spec (.of D₀.k))

/-- The geometric compact Frobenius, with terminal reparametrization before exchange
and the Weil map. This is a real composite, not a chosen endomorphism.
Source: uniform-formula definition of Frob_X,K
(blueprint: sk-thm-tf-uniform-formula). -/
def globalFrobenius (c₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex Λ.X (StrictWeil.modelFrobenius D₀ X₀)) :
    End ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj) :=
  (CohomologyTransport.Γ Λ.X (Spec (.of D₀.k))).map
    (compactReturn Λ.X (geometricCompactification D₀ X₀ c₀).i
      (geometricCompactification D₀ X₀ c₀).g
      (StrictWeil.modelFrobenius D₀ X₀).hom
      (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom
      (StrictWeil.pointFrobenius D₀).hom
      (compactification_squares D₀ X₀ c₀).1
      (compactification_squares D₀ X₀ c₀).2 (ambientStructure Λ.X K).hom)

/-- An extension-valued point has precisely the semilinear return needed by its local
operator. No fixed-point or return equation is an extra hypothesis of the trace formula.
Source: uniform-formula local operator, proof operator-identification paragraph
(blueprint: sk-thm-tf-uniform-formula).
Proof: the m-th geometric field Frobenius fixes F_(q^m). The first pullback projection
of both composites is therefore the same model point, and the second is g_s^m.
The universal property of the pullback proves the equality. -/
theorem point_return (m : ℕ) (hm : 1 ≤ m) (y : D₀.extensionPoints X₀ m hm) :
    WeilConjectures.localExtensionPoint D₀ X₀ m hm y ≫
        ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) =
      ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) ≫
        WeilConjectures.localExtensionPoint D₀ X₀ m hm y := by
  sorry

/-- The local Frobenius is terminal reparametrization, the return comparison, and
pullback of the iterated Weil isomorphism, followed by actual scalar sections.
Source: uniform-formula (1), Frob_y,m (blueprint: sk-thm-tf-uniform-formula). -/
def localFrobenius
    (K : StrictWeil.Complex Λ.X (StrictWeil.modelFrobenius D₀ X₀))
    (m : ℕ) (hm : 1 ≤ m) (y : D₀.extensionPoints X₀ m hm) :
    End ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj) :=
  (CohomologyTransport.Γ Λ.X (Spec (.of D₀.k))).map
    (stalkReturn Λ.X (WeilConjectures.localExtensionPoint D₀ X₀ m hm y)
      ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
      ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m)
      (point_return D₀ X₀ m hm y)
      (iterateStructure Λ.X (End.of (StrictWeil.modelFrobenius D₀ X₀).hom)
        (ambientStructure Λ.X K) m).hom)

/-- The trace formula and perfectness, simultaneously for all admissible stages.
Source: uniform-formula (1) and its perfectness sentence
(blueprint: sk-thm-tf-uniform-formula).
Proof: for finite rings use the coefficient-morphism trace formula and the Frobenius
convention. For integral coefficients identify the actual nonfinite graph operators
with these semilinear returns and apply integral transport. For a finite extension
field choose the rational-model lemma's integral object, model isomorphism, N and
possibly noninvertible theta. Extend the integral trace identity, multiply by pi^(-Nm),
and use linearity and conjugation invariance. Descend an algebraic-closure Weil pair,
its inverse and the two inverse equations to a common finite subextension; scalar
compatibility and conjugation invariance give the formula and independence of the model.
Compact finiteness, pullback stability, and the point equivalence give perfectness;
the algebraically closed base has ell-cohomological dimension zero. Fixed-point
finiteness makes the sum over extension-valued points finite. -/
theorem formula [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D₀.p) (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (c₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex Λ.X (StrictWeil.modelFrobenius D₀ X₀)) :
    ∃ hC : DerivedCategory.IsPerfectRingComplex
        ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj),
      ∀ (m : ℕ) (hm : 1 ≤ m), Finite (D₀.extensionPoints X₀ m hm) ∧
        ∃ hS : ∀ y : D₀.extensionPoints X₀ m hm,
            DerivedCategory.IsPerfectRingComplex
              ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj),
          DerivedCategory.perfectCategoricalTrace _ hC
              (globalFrobenius D₀ X₀ Λ c₀ K ^ m) =
            ∑ᶠ y : D₀.extensionPoints X₀ m hm,
              DerivedCategory.perfectCategoricalTrace _ (hS y)
                (localFrobenius D₀ X₀ Λ K m hm y) := by
  sorry

/-- Homology of the actual scalar complex in an arbitrary integer degree.
Source: uniform-formula (2) (blueprint: sk-thm-tf-uniform-formula). -/
abbrev homology (i : ℤ) :=
  DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) i

/-- Over the listed fields, formula (1) is the finite cohomological supertrace formula.
The same finite degree set can be used for the compact complex and every stalk at a
fixed positive extension degree; negative degrees retain their integer parity.
Source: uniform-formula (2) and final sentence (blueprint: sk-thm-tf-uniform-formula).
Proof: formula gives perfectness. Over a field, bounded finite-projective scalar models
have finite-dimensional homology and finite degree support. There are finitely many
extension points, so take the union of all degree supports and the compact support.
Apply the cohomological categorical-trace formula to the compact complex and each
stalk; replacing their degree supports by this union adds only zero traces. -/
theorem cohomological_formula [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D₀.p)
    (_hΛ : Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (c₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex Λ.X (StrictWeil.modelFrobenius D₀ X₀))
    (m : ℕ) (hm : 1 ≤ m) :
    Finite (D₀.extensionPoints X₀ m hm) ∧
    (∀ i : ℤ, Module.Finite (condensedScalarRing Λ.X)
      ((homology Λ i).obj ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj))) ∧
    (∀ (y : D₀.extensionPoints X₀ m hm) (i : ℤ), Module.Finite (condensedScalarRing Λ.X)
      ((homology Λ i).obj ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj))) ∧
    ∃ s : Finset ℤ,
      (∀ i : ℤ, i ∉ s → IsZero
        ((homology Λ i).obj ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj))) ∧
      (∀ (y : D₀.extensionPoints X₀ m hm) (i : ℤ), i ∉ s → IsZero
        ((homology Λ i).obj ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj))) ∧
      (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace (condensedScalarRing Λ.X)
        ((homology Λ i).obj ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj))
        ((homology Λ i).map (globalFrobenius D₀ X₀ Λ c₀ K ^ m)).hom) =
      ∑ᶠ y : D₀.extensionPoints X₀ m hm,
        ∑ j ∈ s, (j.negOnePow : ℤ) • LinearMap.trace (condensedScalarRing Λ.X)
          ((homology Λ j).obj ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj))
          ((homology Λ j).map (localFrobenius D₀ X₀ Λ K m hm y)).hom := by
  sorry

/-- The actual coefficient homomorphism on terminal scalar rings, obtained from the
ring-object map by the canonical terminal-section/convolution-ring identification.
Source: uniform-formula coefficient-compatibility sentence
(blueprint: sk-thm-tf-uniform-formula). -/
def coefficientScalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    condensedScalarRing Λ.X →+* condensedScalarRing Λ'.X :=
  (InternalAbelianSheafModule.sectionGlobalEquiv (coherentTopology Profinite.{u})
    Λ'.X (⊤_ Profinite.{u}) terminalIsTerminal).toRingHom.comp
    ((MonObj.Γ.map a.hom.hom).comp
      (InternalAbelianSheafModule.sectionGlobalEquiv (coherentTopology Profinite.{u})
        Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom)

/-- Scalar extension of the strict pair exists and carries every global and local
trace to its coefficient image. The displayed equation specifies the extended Weil
structure using precisely the scalar-six pullback comparison; e is only a presentation
of the actual derived extension of scalars. No flatness or invertible integral lattice
is assumed. Each summand is compatible, hence so is the whole trace identity.
Source: uniform-formula coefficient-compatibility sentence and proof final paragraph
(blueprint: sk-thm-tf-uniform-formula).
Proof: listedCoefficientCtf preserves Dctf. The inverse pullback comparison followed
by scalar extension of the Weil isomorphism defines the extended strict pair and the
stated equation. The canonical compact-support and stalk-pullback comparisons of
scalar-six preserve units, counits and composition; consequently they intertwine the
semilinear return composites, including every iterate. Evaluate at the point. On a
bounded finite-projective model the resulting comparison is ordinary scalar extension
on each summand, differential and retract. The scalar-extension law of the categorical
trace therefore gives both displayed scalar equalities, including nonflat reductions.
Perfectness follows from formula on both coefficient stages. -/
theorem coefficient_compatibility [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D₀.p) {Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    (c₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex Λ.X (StrictWeil.modelFrobenius D₀ X₀)) :
    ∃ (K' : StrictWeil.Complex Λ'.X (StrictWeil.modelFrobenius D₀ X₀))
      (e : (scalarSixChange a (D₀.geometricFiber X₀).left).obj K.carrier.obj ≅ K'.carrier.obj),
      (scalarSixChange a (D₀.geometricFiber X₀).left).map (ambientStructure Λ.X K).hom ≫
          e.hom =
        (scalarSixPullHom a (StrictWeil.modelFrobenius D₀ X₀).hom).app K.carrier.obj ≫
          (scalarSixPull Λ' (StrictWeil.modelFrobenius D₀ X₀).hom).map e.hom ≫
            (ambientStructure Λ'.X K').hom ∧
      ∃ (hC : DerivedCategory.IsPerfectRingComplex
          ((compactSections D₀ X₀ Λ c₀).obj K.carrier.obj))
        (hC' : DerivedCategory.IsPerfectRingComplex
          ((compactSections D₀ X₀ Λ' c₀).obj K'.carrier.obj)),
        ∀ (m : ℕ) (hm : 1 ≤ m),
          ∃ (hS : ∀ y : D₀.extensionPoints X₀ m hm,
              DerivedCategory.IsPerfectRingComplex
                ((stalkSections D₀ X₀ Λ m hm y).obj K.carrier.obj))
            (hS' : ∀ y : D₀.extensionPoints X₀ m hm,
              DerivedCategory.IsPerfectRingComplex
                ((stalkSections D₀ X₀ Λ' m hm y).obj K'.carrier.obj)),
            coefficientScalarMap a (DerivedCategory.perfectCategoricalTrace _ hC
                (globalFrobenius D₀ X₀ Λ c₀ K ^ m)) =
              DerivedCategory.perfectCategoricalTrace _ hC'
                (globalFrobenius D₀ X₀ Λ' c₀ K' ^ m) ∧
            ∀ y : D₀.extensionPoints X₀ m hm,
              coefficientScalarMap a (DerivedCategory.perfectCategoricalTrace _ (hS y)
                  (localFrobenius D₀ X₀ Λ K m hm y)) =
                DerivedCategory.perfectCategoricalTrace _ (hS' y)
                  (localFrobenius D₀ X₀ Λ' K' m hm y) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.UniformTrace
