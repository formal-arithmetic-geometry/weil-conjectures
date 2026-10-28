/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.SixFunctorsBasics.BrownHypothesesDefinitions
import Sheaf.SixFunctorsBasics.BrownHypothesesCriteria
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic

/-!
# Hypotheses of Brown representability

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses/_section.md.
The original arbitrary-field compactness assertion remains disputed. The bundle lives
in `BrownHypothesesDefinitions`; proved criteria and conditional obstructions live in
`BrownHypothesesCriteria`. The integral specialization below retains the finite or
separably closed base-field hypothesis of the upstream Ext bound.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

open scoped CategoryTheory.Obj in
private theorem ordinary_constructible_of_constant_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let φ := condensedPullbackHom Λ (S.immersion a)
  have h := (hS a).isLocallyFinitelyPresented _
  unfold CondensedRing.upperStar at h
  exact lfp_of_comap (inv φ)
    (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))

open scoped CategoryTheory.Obj in
/-- Integral Brown hypotheses over a finite or separably closed base field.
The field restriction is explicit; positive characteristic alone does not imply it.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraph 2,
and sk-lem-int-ext, uniform Ext-bound clause, with the field restriction of
`hasUniformConstructibleExtBound_padicIntegersRingObj` retained.
(blueprint: lem-sfb-brown-integral-finite-or-separably-closed).

Proof: finite type over a field makes X compact, and separatedness makes it
quasi-separated. A finite constant presentation on each stratum is a local finite
presentation after transport across the canonical coefficient isomorphism. Thus the
upstream Ext bound applies to the actual constant-model constructible sheaves.
For its single-degree bound n ≤ N use the shifted-Hom bound q > -N; the canonical
isomorphism N[0][q] ≅ N[-q] identifies the groups. The integral Brown equivalence
then supplies compactness, the ambient structures, thickness, smallness and generation.
The empty scheme and zero sheaves require no separate assumption. -/
theorem brownHypotheses_padicIntegers_of_finite_or_separablyClosed
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hk : Finite k ∨ IsSepClosed k) :
    BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X := by
  let _ : Fact (ringChar k ≠ ℓ) := ⟨(ringChar.eq k p) ▸ hpℓ⟩
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  have hb := CondensedRing.hasUniformConstructibleExtBound_padicIntegersRingObj
    ℓ E (X ↘ Spec (.of k)) hk
  apply (brownHypothesesFor_padicIntegers_iff_ext_bounded ℓ E k p hp hpℓ X).mpr
  intro C
  obtain ⟨d, hd⟩ := hb C.obj
    (ordinary_constructible_of_constant_model _ X C.obj C.property)
  refine ⟨-d, fun N q hq ↦ ?_⟩
  have hN := ordinary_constructible_of_constant_model _ X N.obj N.property
  let e := ((DerivedCategory.singleFunctors _).shiftIso q (-q) 0 (by omega)).app N.obj
  refine ⟨fun f g ↦ ?_⟩
  apply (cancel_mono e.hom).mp
  exact (hd N.obj hN (-q) (by omega) (f ≫ e.hom)).trans
    (hd N.obj hN (-q) (by omega) (g ≫ e.hom)).symm

-- STATEMENT-DISPUTED: The arbitrary-field compactness assertion lacks a finiteness
-- hypothesis on the base field. The finite/rational compactness dependencies require
-- FiniteFieldDatum; the integral one requires an Ext bound. Finite type over an arbitrary
-- positive-characteristic field does not supply finite ℓ-cohomological dimension.
-- Concrete mathematical obstruction: take ell = 2, p = 3, X = Spec k for
-- k = algebraicClosure(F_3)(t_1,t_2,...) and Lambda the constant finite ring F_2.
-- The constant rank-one object is constructible of Tor amplitude [0,0]. Kummer cup
-- symbols in t_1,...,t_n are nonzero in H^n(k,F_2), detected by iterated residues.
-- Exact countable products make the coproduct of its positive shifts also their
-- product. The resulting map with every projection nonzero violates compactness.
-- This is a natural-language counterexample, not a claimed Lean field-cohomology proof.
-- Generation itself is proved without this finiteness assumption by the helpers above.
-- The supplied compactness theorem specifically uses D.k, the algebraic closure of a
-- finite field. Its algebraic-closure coefficient is finite-subextension-valued.
-- The supported geometric finite-field Brown bundle is proved in BrownHypothesesFiniteField;
-- its proof does not assert the original arbitrary-field claim.

/-- Brown representability hypotheses for a separated finite-type scheme in positive
characteristic different from the coefficient prime, for exactly the admissible rings.
`IsLocalizingAdmissibleCoefficient` specifies the six concrete coefficient objects up to
ring-object isomorphism, including the discrete finite rings killed by a power of `ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md and sk-lem-brown-hypotheses.proof.md
(blueprint: sk-lem-brown-hypotheses).

Proof: First unpack sk-def-sfb-dc-setting: the datum is a prime ℓ, a field of
characteristic p > 0 distinct from ℓ, and a separated finite-type k-scheme X.
Unpack sk-def-localizing-closure: Λ is one of the six specified condensed rings;
the ambient category is the unbounded derived category of modules over Λ_X;
S is the bounded constructible finite-Tor property and L is its replete localizing
intersection, with coproducts in the fixed universe and no completeness restriction.
Second apply det-brown-hypotheses-ambient to this datum to obtain local smallness,
triangulation, arbitrary sums and split idempotents of L. Apply
 det-brown-hypotheses-small to obtain thickness and essential smallness of S.
Choosing one representative per isomorphism class gives a small skeleton.
Third let G be any such skeleton and apply det-brown-hypotheses-generation:
each representative is compact in L, and vanishing of Hom(C[n], K) for all
representatives C and all integers n forces K to be zero. Compactness is exactly
def-pc-compact-object. To identify the second conclusion with def-pc-generators,
use Hom(coproduct C, K[-n]) = product Hom(C[n], K). If every morphism from the
coproduct into every shift of K is zero, the component Hom groups vanish,
so K is zero; contrapositively every nonzero K receives a nonzero map from the
coproduct into some shift. This is IsTriangulatedGeneratingFamily. All these
arguments apply to every small skeleton, with the inherited shift and any chosen
coproduct universal properties. -/
-- The final compactness input required by this unrestricted statement is unavailable
-- over an arbitrary positive-characteristic field; this remains the original named
-- obligation rather than importing the retired false witness.
theorem brownHypotheses
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  sorry

end CategoryTheory
