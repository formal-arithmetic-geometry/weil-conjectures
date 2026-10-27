/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import Sheaf.TraceFormula.HenselizationQuotientAtPrime
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.HenselizationUniversalProperty

/-!
# Minimal smooth envelopes and their comparisons

Source: ILO, Exposé VIII, 2.3.11--2.3.13; the explicit local-coordinate proof in the DAG,
using Stacks Tags 00RU, 02GU, 024T, 06AA and 05WQ
(blueprint: lem-trf-smooth-embedding-etale-comparison).

The differential map is the existing canonical map on relative differentials, followed by
the stalk and residue-field extension functors. Closed-pair comparisons are Cartesian and
the ideal comparisons use the actual inverse-image ideals, rather than arbitrary ambient lifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A minimal smooth envelope is a smooth closed embedding whose canonical cotangent-fibre
map is invertible. The base structure on the closed scheme is the composite `i ≫ p`.
The stalk of the tensor pullback, tensored with the residue field of `X` at `x`, is canonically
the ambient differential fibre extended to that same residue field.
Source: minimal-envelope paragraph of the DAG; Stacks Tags 01UM and 01UV
(blueprint: lem-trf-smooth-embedding-etale-comparison). -/
def Scheme.Hom.IsMinimalSmoothEnvelope {X M S : Scheme.{u}}
    (p : M ⟶ S) (i : X ⟶ M) (x : X) : Prop :=
  IsClosedImmersion i ∧ Smooth p ∧
    IsIso ((ModuleCat.extendScalars (X.residue x).hom).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (p.relativeDifferentialsPullbackMap i)))

/-- The structural map from a local ring to a specified ordinary henselization. We retain
the localization at the maximal ideal required by the recorded henselization predicate.
Source: Stacks Tag 04GQ (blueprint: lem-trf-smooth-embedding-etale-comparison). -/
def smoothEnvelopeHenselizationMap (R : Type u) [CommRing R] [IsLocalRing R]
    (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H] : R →+* H :=
  (algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
    (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R)))

/-- A finite-type scheme over a characteristic-zero field has a minimal smooth envelope
on a neighbourhood of every point. In fact an open restriction already suffices.
Source: ILO VIII 2.3.11--2.3.13 and the local-coordinate proof, DAG Steps 1--3
(blueprint: lem-trf-smooth-embedding-etale-comparison).

Proof: present an affine neighbourhood as a quotient of a polynomial algebra, giving a
closed embedding into smooth affine space (def-weil-finite-type-morphism,
sbc-lem-affine-space-smooth). The quotient differential sequence and tensor right exactness
(lem-weil-pbc-jacobi-zariski-differential-maps, lem-weil-pbc-tensor-right-exact) identify the
kernel in the ambient differential fibre. Choose equations whose differentials form its basis,
extend by differentials of regular functions, and apply the chosen-coordinate etale criterion
(lem-pur-etale-at-point-from-differentials). The zero locus of the first coordinates is smooth
by etale base change and smooth composition. The Leibniz rule shows that its differential
fibre is the quotient by exactly that kernel. Thus its canonical map to the differential fibre
of X is an isomorphism. This uses no smoothness or reducedness of X. -/
theorem Scheme.exists_minimal_smooth_envelope
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] (x : X) :
    ∃ (U : X.Opens) (hx : x ∈ U) (M : Scheme.{u})
      (q : M ⟶ Spec (.of k)) (i : U.toScheme ⟶ M),
      i ≫ q = U.ι ≫ p ∧ q.IsMinimalSmoothEnvelope i ⟨x, hx⟩ := by
  sorry

/-- Every supplied smooth envelope contains a minimal smooth closed envelope, locally at
the specified point. The closed subscheme is the actual inverse image of the ambient open.
Source: the local-coordinate proof, DAG Steps 1--3; Stacks Tags 00RU and 02GU
(blueprint: lem-trf-smooth-embedding-etale-comparison).

Proof: on an affine ambient chart choose f_1,...,f_r in the defining ideal whose differentials
span the kernel of the surjection of differential fibres. Extend to a differential basis and
use lem-pur-etale-at-point-from-differentials. The zero locus of the f_j is the pullback of a
coordinate subspace, hence smooth by etale base change. It contains X scheme-theoretically.
The quotient differential sequence identifies its fibre with that of X, since d(sum a_j f_j)
at x is sum a_j(x) df_j. This is the canonical induced map. When r=0 use the whole ambient
open. The argument is the same as the existence construction and applies to every envelope. -/
theorem Scheme.Hom.exists_minimal_closed_smooth_envelope_inside
    (k : Type u) [Field k] [CharZero k] {X M : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q : M ⟶ Spec (.of k)) [Smooth q] (i : X ⟶ M) [IsClosedImmersion i]
    (hi : i ≫ q = p) (x : X) :
    ∃ (V : M.Opens) (U : X.Opens) (hx : x ∈ U) (hUV : U ≤ i ⁻¹ᵁ V)
      (M₀ : Scheme.{u}) (q₀ : M₀ ⟶ Spec (.of k))
      (j : M₀ ⟶ V.toScheme) (i₀ : U.toScheme ⟶ M₀),
      U = i ⁻¹ᵁ V ∧ IsClosedImmersion j ∧ j ≫ V.ι ≫ q = q₀ ∧
      i₀ ≫ j = i.resLE V U hUV ∧ i₀ ≫ q₀ = U.ι ≫ p ∧
      q₀.IsMinimalSmoothEnvelope i₀ ⟨x, hx⟩ := by
  sorry

/-- Two minimal envelopes of the same pointed germ have a common etale neighbourhood of
closed pairs, with their specified identification on X and all its specified ideals.
Writing the identified germs with the same X loses no generality: restrict and transport the
second embedding by the given germ isomorphism before applying the statement.
Source: DAG Steps 4--5 and 10; Stacks Tags 054L, 02GU, 02GO and 024T
(blueprint: lem-trf-smooth-embedding-etale-comparison).

Proof: choose etale coordinates on the second ambient scheme; restrict them to X and lift
them to the first ambient scheme by its quotient map. Minimality makes their differential
classes a basis there, so the chosen-coordinate criterion makes the lift etale locally.
The fibre product over affine space has etale projections and the specified diagonal copy of X.
For each projection, this copy is a section of a separated etale X-scheme, hence open and closed
(lem-weil-pbc-etale-section-clopen-immersion). Remove the two closed complements in the ambient
fibre product. Its inverse images of X are now exactly the same open of X, scheme-theoretically.
The marked point is its diagonal point, with unchanged residue field. For an ideal J of X,
inverse image in each ambient quotient and base change give the ideal of J in the same closed
subscheme; this proves both displayed ideal equalities, as in Step 10. -/
theorem Scheme.Hom.exists_common_etale_minimal_smooth_envelopes
    (k : Type u) [Field k] [CharZero k] {X M₁ M₂ : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q₁ : M₁ ⟶ Spec (.of k)) (q₂ : M₂ ⟶ Spec (.of k))
    (i₁ : X ⟶ M₁) (i₂ : X ⟶ M₂) (h₁ : i₁ ≫ q₁ = p) (h₂ : i₂ ≫ q₂ = p)
    (x : X) (hm₁ : q₁.IsMinimalSmoothEnvelope i₁ x)
    (hm₂ : q₂.IsMinimalSmoothEnvelope i₂ x) :
    ∃ (U : X.Opens) (_ : x ∈ U) (P : Scheme.{u})
      (a₁ : P ⟶ M₁) (a₂ : P ⟶ M₂) (j : U.toScheme ⟶ P),
      Etale a₁ ∧ Etale a₂ ∧ IsClosedImmersion j ∧ a₁ ≫ q₁ = a₂ ≫ q₂ ∧
      IsPullback j U.ι a₁ i₁ ∧ IsPullback j U.ι a₂ i₂ ∧
      ∀ J : X.IdealSheafData,
        (J.map i₁).comap a₁ = (J.comap U.ι).map j ∧
        (J.map i₂).comap a₂ = (J.comap U.ι).map j := by
  sorry

/-- The ambient henselian germs of two minimal envelopes are isomorphic over k and induce
the specified quotient identification on the henselian germ of X. The structural maps are
those of the given henselizations; the local quotient maps are characterized by the displayed
commutative squares. No algebraization of an arbitrary prescribed henselian isomorphism is claimed.
Source: DAG Step 6; Stacks Tags 08HQ, 08HR, 04GQ, 05WQ and 0A02
(blueprint: lem-trf-smooth-embedding-etale-comparison).

Proof: construct the common pointed etale neighbourhood from Steps 4--5. Its marked residue
field is exactly kappa(x). The pointed etale lifting theorem
(lem-weil-pbc-map-into-henselian-colimit) extends each ambient local map to its henselization.
Localize and use the ordinary henselization universal property to extend in the other direction.
Uniqueness of pointed etale lifts and of henselization extensions makes these maps inverse.
The quotient theorem lem-trf-henselization-quotient-at-prime and the Cartesian closed pairs
identify both quotients with the specified henselization of the germ of X, proving surjectivity
and the quotient square. All maps are over k. Existence of ordinary henselizations follows
from pair henselization at the maximal ideal and its universal property, as expanded in Step 6.
Conversely the common neighbourhood already constructed gives the existence formulation;
the claim is not that an independently specified henselian isomorphism algebraizes. -/
theorem Scheme.Hom.minimal_smooth_envelopes_henselian_comparison
    (k : Type u) [Field k] [CharZero k] {X M₁ M₂ : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q₁ : M₁ ⟶ Spec (.of k)) (q₂ : M₂ ⟶ Spec (.of k))
    (i₁ : X ⟶ M₁) (i₂ : X ⟶ M₂) (h₁ : i₁ ≫ q₁ = p) (h₂ : i₂ ≫ q₂ = p)
    (x : X) (hm₁ : q₁.IsMinimalSmoothEnvelope i₁ x)
    (hm₂ : q₂.IsMinimalSmoothEnvelope i₂ x)
    (H₁ H₂ Hₓ : Type u) [CommRing H₁] [CommRing H₂] [CommRing Hₓ]
    [HenselianLocalRing H₁] [HenselianLocalRing H₂] [HenselianLocalRing Hₓ]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (M₁.presheaf.stalk (i₁ x)))) H₁]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (M₂.presheaf.stalk (i₂ x)))) H₂]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) Hₓ]
    (hh₁ : Algebra.IsHenselizationAtPrime' (M₁.presheaf.stalk (i₁ x))
      (IsLocalRing.maximalIdeal (M₁.presheaf.stalk (i₁ x))) H₁)
    (hh₂ : Algebra.IsHenselizationAtPrime' (M₂.presheaf.stalk (i₂ x))
      (IsLocalRing.maximalIdeal (M₂.presheaf.stalk (i₂ x))) H₂)
    (hhₓ : Algebra.IsHenselizationAtPrime' (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) Hₓ) :
    ∃ (b₁ : H₁ →+* Hₓ) (b₂ : H₂ →+* Hₓ) (e : H₁ ≃+* H₂),
      IsLocalHom b₁ ∧ IsLocalHom b₂ ∧ Function.Surjective b₁ ∧ Function.Surjective b₂ ∧
      b₁.comp (smoothEnvelopeHenselizationMap (M₁.presheaf.stalk (i₁ x)) H₁) =
        (smoothEnvelopeHenselizationMap (X.presheaf.stalk x) Hₓ).comp (i₁.stalkMap x).hom ∧
      b₂.comp (smoothEnvelopeHenselizationMap (M₂.presheaf.stalk (i₂ x)) H₂) =
        (smoothEnvelopeHenselizationMap (X.presheaf.stalk x) Hₓ).comp (i₂.stalkMap x).hom ∧
      b₂.comp e.toRingHom = b₁ ∧
      e.toRingHom.comp ((smoothEnvelopeHenselizationMap (M₁.presheaf.stalk (i₁ x)) H₁).comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫ q₁.appTop ≫
          M₁.presheaf.germ ⊤ (i₁ x) trivial).hom)) =
      (smoothEnvelopeHenselizationMap (M₂.presheaf.stalk (i₂ x)) H₂).comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫ q₂.appTop ≫
          M₂.presheaf.germ ⊤ (i₂ x) trivial).hom) := by
  sorry

/-- A smooth closed pair has an etale tubular chart centred on an open neighbourhood T of
the chosen point of N. The chart retracts to T, has exactly T as its zero fibre and as its
inverse image of N, and its actual transverse coordinates generate the section ideal and
form a regular sequence. The quotient equivalence is the section augmentation.
The zero-fibre and ideal identities explicitly encode adjoining/eliminating the transverse
parameters and preservation of specified ideals, without choosing arbitrary lifts.
Source: DAG Steps 7--10; Stacks Tags 06AA, 02GU, 024T and 067U
(blueprint: lem-trf-smooth-embedding-etale-comparison).

Proof: choose etale coordinates t_j on N and lift to g_j on an affine ambient chart. The
smooth conormal sequence (lem-pur-conormal-sequence-smooth-immersion) supplies ideal elements
f_j whose differentials complement those of g_j. The chosen-coordinate criterion makes
(g,f) etale after restriction. Base change along the etale coordinate map of N gives
P=M times_{A^d} N with an etale map to M and a projection to N. Remove the closed complement
of the graph section in the inverse image of N, as in Steps 4--5. The graph is now the whole
inverse image. The map (projection,f) to A^r_N is the base change of (g,f), hence etale.
Its projection is smooth of relative dimension r by lem-sbc-smooth-relative-dimension-permanence.
Apply lem-sc-smooth-section-affine-coordinates to obtain centred affine coordinates, with
section ideal, regular sequence and augmentation quotient. Compose the ambient etale maps
and restrict to the resulting open T of N. Cartesian pasting preserves the closed pair.
For each ideal on N, the quotient-ideal calculation of Step 10 gives the first ideal identity.
Pullback along the zero-section square gives the second; quotienting the transverse regular
parameters eliminates them, and pulling the ideal back along the retraction adjoins them.
When r=0 the sequence is empty and affine zero-space is T; the same construction applies. -/
theorem Scheme.Hom.exists_etale_smooth_closed_pair_retraction
    (k : Type u) [Field k] [CharZero k] {N M : Scheme.{u}}
    (q : M ⟶ Spec (.of k)) (p : N ⟶ Spec (.of k)) [Smooth q] [Smooth p]
    (i : N ⟶ M) [IsClosedImmersion i] (hi : i ≫ q = p) (y : N) :
    ∃ (T : N.Opens) (_ : y ∈ T) (_ : IsAffineOpen T) (P : Scheme.{u})
      (_ : IsAffine P) (a : P ⟶ M) (b : P ⟶ T.toScheme) (s : T.toScheme ⟶ P)
      (r : ℕ) (e : P ⟶ AffineSpace (ULift.{u} (Fin r)) T.toScheme)
      (f : Fin r → Γ(P, ⊤)),
      Etale a ∧ IsClosedImmersion s ∧ b ≫ T.ι ≫ p = a ≫ q ∧ s ≫ b = 𝟙 T.toScheme ∧
      IsPullback s T.ι a i ∧ Etale e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin r)) T.toScheme ↘ T.toScheme) = b ∧
      IsPullback s (𝟙 T.toScheme) e
        (AffineSpace.homOfVector (𝟙 T.toScheme) (fun _ : ULift.{u} (Fin r) ↦ 0)) ∧
      (∀ j : Fin r, f j = e.appTop (AffineSpace.coord T.toScheme (ULift.up j))) ∧
      RingTheory.Sequence.IsRegular Γ(P, ⊤) (List.ofFn f) ∧
      (∀ W : P.affineOpens, s.ker.ideal W = Ideal.span (Set.range (fun j : Fin r ↦
        P.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op (f j)))) ∧
      (∃ hP : IsAffineOpen (⊤ : P.Opens),
        ∃ Q : Γ(P, ⊤) ⧸ s.ker.ideal ⟨⊤, hP⟩ ≃+* Γ(T.toScheme, ⊤),
          ∀ z : Γ(P, ⊤), Q (Ideal.Quotient.mk _ z) = s.appTop z) ∧
      ∀ J : N.IdealSheafData,
        (J.map i).comap a = (J.comap T.ι).map s ∧
        ((J.comap T.ι).map
          (AffineSpace.homOfVector (𝟙 T.toScheme)
            (fun _ : ULift.{u} (Fin r) ↦ 0))).comap e = (J.comap T.ι).map s := by
  sorry

end AlgebraicGeometry
