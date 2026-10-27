/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum

/-! # Graphs of finite embedded first-order deformations

Source: Stacks Project, quot.tex, Tag 0CZV, remark-q-defos, with F = O_X and the
trivial lift as origin (blueprint: lem-sfb-finite-embedded-dual-number-graphs).

The existing same-space model `X.dualNumbers` makes the local graph formula literal.
The theorem identifies it with the base change over k. For the two-parameter clause,
the coefficient ring is the quotient of iterated dual numbers by the mixed monomial.
Its base change is used as the ambient scheme, so flatness is over the square-zero
coefficient ring, including the relation epsilon_1 epsilon_2 = 0.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEmbeddedDualNumberGraphs

noncomputable section

/-- The coefficient ring k[epsilon_1,epsilon_2]/(epsilon_1,epsilon_2)^2, presented as
iterated dual numbers modulo their mixed monomial. Source: Stacks, Tag 0CZV,
coefficient module k epsilon_1 plus k epsilon_2
(blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
abbrev TwoCoefficients (k : Type u) [Field k] :=
  DualNumber (DualNumber k) ⧸
    Ideal.span {(TrivSqZeroExt.inr (TrivSqZeroExt.inr (1 : k)) :
      DualNumber (DualNumber k))}

/-- The canonical quotient onto the square-zero two-parameter coefficients.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def coefficientQuotient (k : Type u) [Field k] :
    DualNumber (DualNumber k) →+* TwoCoefficients k :=
  Ideal.Quotient.mk _

/-- The structure morphism of the dual-number base change, in the existing same-space model.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def structureMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : X.dualNumbers ⟶ Spec (.of (DualNumber k)) :=
  f.dualNumbers ≫ Scheme.dualNumbersToSpec (.of k)

/-- The structure morphism of the iterated dual-number model.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def iteratedStructureMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    X.dualNumbers.dualNumbers ⟶ Spec (.of (DualNumber (DualNumber k))) :=
  f.dualNumbers.dualNumbers ≫ (Scheme.dualNumbersToSpec (.of k)).dualNumbers ≫
    Scheme.dualNumbersToSpec (.of (DualNumber k))

/-- Base change to the square-zero two-parameter coefficient ring, with both parameters
and their product treated canonically. Source: Stacks, Tag 0CZV
(blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def twoAmbient {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Scheme.{u} :=
  pullback (iteratedStructureMap f) (Spec.map (CommRingCat.ofHom (coefficientQuotient k)))

/-- The closed immersion of the square-zero ambient scheme into iterated dual numbers.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def twoAmbientι {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : twoAmbient f ⟶ X.dualNumbers.dualNumbers :=
  pullback.fst (iteratedStructureMap f) (Spec.map (CommRingCat.ofHom (coefficientQuotient k)))

/-- The specified morphism to the square-zero two-parameter base.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def twoStructureMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : twoAmbient f ⟶ Spec (.of (TwoCoefficients k)) :=
  pullback.snd (iteratedStructureMap f) (Spec.map (CommRingCat.ofHom (coefficientQuotient k)))

/-- O_X-linear maps from the specified ideal to i_*O_Z, using the recorded ideal module
and the existing module pushforward. Source: Stacks, Tag 0CZV
(blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
abbrev TangentMap {X Z : Scheme.{u}} (i : Z ⟶ X) :=
  i.ker.toModules ⟶ (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)

/-- The local graph condition, on every open: the constant part comes from the ideal,
and the image of the epsilon coefficient in i_*O_Z is h of that ideal section.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def IsGraph {X Z : Scheme.{u}} (i : Z ⟶ X) (h : TangentMap i)
    (J : X.dualNumbers.IdealSheafData) : Prop :=
  ∀ (U : X.Opens) (s : Γ(X.dualNumbers, U)),
    s ∈ J.idealOfOpens U ↔ ∃ a : Γ(i.ker.toModules, U),
      i.ker.toModulesι.app U a = s.fst ∧ i.app U s.snd = h.app U a

/-- The same graph condition after restriction to an arbitrary open subscheme. Sections
are transported by the canonical open-immersion section isomorphism; h itself is restricted
by evaluating on opens contained in U. Source: Stacks, Tag 0CZV
(blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def IsOpenGraph {X Z : Scheme.{u}} (i : Z ⟶ X) (h : TangentMap i) (U : X.Opens)
    (J : U.toScheme.dualNumbers.IdealSheafData) : Prop :=
  ∀ (V : U.toScheme.Opens) (s : Γ(U.toScheme.dualNumbers, V)),
    s ∈ J.idealOfOpens V ↔ ∃ a : Γ(i.ker.toModules, U.ι ''ᵁ V),
      i.ker.toModulesι.app (U.ι ''ᵁ V) a = (U.ι.appIso V).inv s.fst ∧
      i.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv s.snd) = h.app (U.ι ''ᵁ V) a

/-- The graph condition for two maps, expressed upstairs in iterated dual numbers.
The mixed coefficient is unrestricted, so this is precisely the inverse image of the
ideal in the square-zero quotient, rather than an ideal in a different coefficient ring.
Source: Stacks, Tag 0CZV (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def IsTwoGraph {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (h₁ h₂ : TangentMap i)
    (J : (twoAmbient f).IdealSheafData) : Prop :=
  ∀ (U : X.Opens) (s : Γ(X.dualNumbers.dualNumbers, U)),
    s ∈ (J.subschemeι ≫ twoAmbientι f).ker.idealOfOpens U ↔
      ∃ a : Γ(i.ker.toModules, U),
        i.ker.toModulesι.app U a = s.fst.fst ∧
        i.app U s.fst.snd = h₁.app U a ∧ i.app U s.snd.fst = h₂.app U a

/-- The dimension of the global functions on the specified finite k-scheme, using the
k-action induced by its specified structure morphism. Source: Stacks, Tag 0CZV,
finite-support specialization (blueprint: lem-sfb-finite-embedded-dual-number-graphs). -/
def degree {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) : ℕ :=
  @Module.finrank k Γ(Z, ⊤) _ _
    (Module.compHom Γ(Z, ⊤) ((i ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))

/-- Graph classification, finite degree, and compatibility with opens and the scalar and
addition operations. Source: Stacks, quot.tex, Tag 0CZV, remark-q-defos, with F = O_X,
Q = i_*O_Z, and the trivial lift as origin
(blueprint: lem-sfb-finite-embedded-dual-number-graphs).

Proof: (1) Form the kernel of (a,b) ↦ b mod I - h(a). Quasi-coherent cokernels and
kernels (lem-weil-pbc-quasi-coherent-module-cokernel-closure,
lem-weil-pbc-quasi-coherent-module-kernel) and the affine module correspondence
(lem-weil-pbc-affine-module-correspondence) show that its image is a quasi-coherent ideal.
Multiplication by r + epsilon s preserves it since a belongs to I.
(2) On an affine open, for V = k epsilon or k epsilon_1 plus k epsilon_2, its graph
J_H in R plus R tensor V projects onto I and meets R tensor V in I tensor V.
Thus the quotient M has M/VM = R/I and VM = (R/I) tensor V. The affine tilde-section
and adjunction results (lem-weil-pbc-spec-module-tilde-sections,
lem-weil-pbc-affine-tilde-gamma-adjunction) identify these formulas with restrictions.
(3) V tensor_B M identifies with V tensor_k (M/VM); multiplication is the injection
onto VM just computed. The field-flatness and nilpotent-ideal criteria
(lem-weil-pbc-module-over-field-flat, lem-sfb-nilpotent-ideal-module-flatness) imply
B-flatness. The affine-chart criterion (lem-pc-affine-chart-relative-flat-criterion)
gives relative flatness. The same argument applies to J_H because VJ_H = I tensor V.
The quasi-coherent ideal defines its closed subscheme by
lem-weil-pbc-quasi-coherent-ideal-closed-subscheme.
(4) Conversely, flatness of M implies ker(epsilon on M) = epsilon M, by tensoring
(epsilon) into A; hence J intersects epsilon R in epsilon I. Use the affine-chart
criterion and lem-weil-pbc-quasi-coherent-module-cokernel-image to work on sections.
(5) For a in I lift a + epsilon b in J and set h(a) = b mod I. The intersection
formula proves independence; addition and multiplication prove linearity. Localizing
lifts proves compatibility on principal opens, hence gluing and inverse bijections.
The same formulas give restriction to every open subscheme.
(6) The reduction Z into Z_h is a square-zero thickening. Finiteness makes Z affine;
lem-weil-pbc-thickening-affine-scheme makes Z_h affine. Its global ring D is A-flat
by lem-weil-pbc-flat-morphism-affine-criterion, with D/epsilon D = Gamma(Z,O_Z).
(7) Lift a k-basis of this quotient to D. Reducing twice proves generation and
independence over A, including the empty basis. Apply
lem-weil-pbc-finite-free-algebra-spectrum; the unique point of Spec A has fibre Z,
so the degree is dim_k Gamma(Z,O_Z) in def-pc-finite-locally-free.
(8) Under epsilon ↦ lambda epsilon the generated ideal has graph lambda h.
It contains epsilon I by multiplication with the target epsilon even if lambda = 0.
(9) Repeat (1)--(3) with two square-zero parameters. Substitution of both parameters
by epsilon gives graph h_1 + h_2: subtract the displayed generators and use epsilon I.
No scalar or 2 is inverted. -/
theorem classification {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsHProjective f] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ f)] :
    IsPullback X.dualNumbersProj (structureMap f) f
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))) ∧
    ∃ F : TangentMap i → X.dualNumbers.IdealSheafData,
      (∀ h : TangentMap i, IsGraph i h (F h)) ∧
      Function.Injective F ∧
      (∀ J : X.dualNumbers.IdealSheafData,
        (∃ h : TangentMap i, F h = J) ↔
          Flat (J.subschemeι ≫ structureMap f) ∧ J.comap X.dualNumbersι = i.ker) ∧
      (∀ h : TangentMap i,
        ((F h).subschemeι ≫ structureMap f).IsFiniteLocallyFreeOfDegree (degree f i)) ∧
      (∀ (h : TangentMap i) (U : X.Opens) (J : U.toScheme.dualNumbers.IdealSheafData),
        IsOpenGraph i h U J ↔ J = (F h).comap U.ι.dualNumbers) ∧
      (∀ (c : k) (h : TangentMap i), ∃ hc : TangentMap i,
        (∀ (U : X.Opens) (a : Γ(i.ker.toModules, U)),
          hc.app U a = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) • h.app U a) ∧
        F hc = (F h).comap
          (X.dualNumbersScale (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))) ∧
      (∃ d : X.dualNumbers ⟶ twoAmbient f,
        d ≫ twoAmbientι f = X.dualNumbersFold ∧
        ∀ h₁ h₂ : TangentMap i, ∃ J : (twoAmbient f).IdealSheafData,
          IsTwoGraph f i h₁ h₂ J ∧ J.toModules.IsFlatOver (twoStructureMap f) ∧
          Flat (J.subschemeι ≫ twoStructureMap f) ∧ J.comap d = F (h₁ + h₂)) := by
  sorry

end

end AlgebraicGeometry.FiniteEmbeddedDualNumberGraphs
