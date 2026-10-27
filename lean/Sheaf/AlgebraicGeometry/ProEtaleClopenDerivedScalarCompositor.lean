/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData
import Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarUnits
import Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarModels
import Sheaf.AlgebraicGeometry.ProEtaleClopenScalarComparisonDescent
import Sheaf.AlgebraicGeometry.ProEtaleClopenScalarComparisonCoherence

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

/-- Clopen restriction commutes with arbitrary derived coefficient extension, normalized
on every flat-term K-flat model, with its compositor and identity laws.
Source: Stacks 06YY, 0D6D, 05V4; the node's five-step clopen scalar calculation
(blueprint: lem-pur-clopen-derived-scalar-compositor).

Proof:
1. Apply lem-pur-clopen-total-tensor-kflat-detection to the coefficient ring in degree
zero. The sectionwise map sends s tensor p to restricted s tensor restricted p, is
linear over the component target ring, and commutes with differentials and homotopies.
2. Apply lem-weil-pbc-ringed-topos-kflat-pullback to the identity topos and the coefficient
map. Extension has flat terms and is K-flat over the NEW coefficient ring without any
flatness hypothesis on the map. Restriction preserves these properties by the tensor node.
3. Use lem-weil-pbc-site-derived-tensor-descent to identify the localization of flat-term
K-flat homotopy models with the entire derived category. The computation counits of
lem-pur-derived-change-of-rings and the localization factors of
lem-pur-clopen-unbounded-derived-localization give the displayed representative equation.
Localization universal property (2) descends the chain comparison and its inverse.
Part (3) gives uniqueness and hence independence of every choice of resolution.
4. On one common flat-term K-flat representative the successive compositor of
lem-sfb-successive-derived-quotient-normalization sends z tensor (s tensor p) to
psi(s)z tensor p. Both restriction paths therefore have exactly that local formula.
The sheafified pure tensors generate, so the chain maps agree. Localization uniqueness
extends their equality to every derived object and morphism.
5. Multiplication s tensor p maps to sp gives the unit laws, first on models and then
by the same uniqueness. Substitute the actual quotient transitions and completion
projections identified by lem-pur-clopen-ringed-module-gluing to obtain their laws.
Empty components, an empty partition, and zero coefficient sheaves are included by
the zero-category conclusions of lem-pur-clopen-unbounded-derived-localization. -/
theorem clopen_derived_scalar_compositor
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)) :
    ∃ (p : Presentations.{t, u} X) (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X) @p) (U : Units.{t, u} (Z := X) @p)
      (q : ∀ i, Presentations.{t, u} (Y i)) (m : ∀ i, Normalization.{t + 1, t, max u (t + 1), max (u
        + 1) (t + 2)} (C := (Y i).ProEt) (J := topology (Y i)) (hD := derived.{t, u} (Y i)) (fun {R
        S} a ↦ q i (R := R) (S := S) a))
      (V : ∀ i, Units.{t, u} (Z := Y i) (fun {R S} a ↦ q i (R := R) (S := S) a)) (d : ∀ i,
        Comparison.{t, u} (j i) @p (fun {R S} a ↦ q i (R := R) (S := S) a)),
      ∀ i, (d i).sections ∧ (d i).degree ∧ (d i).representative ∧
        (d i).computed ∧ (d i).extended ∧ (d i).unique ∧
        Coherence.{t, u} (j i) n (m i) U (V i) (d i) := by
  classical
  obtain ⟨p, ⟨n⟩⟩ := successive_derived_quotient_normalization
    (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X)
  have hy (i : I) := successive_derived_quotient_normalization
    (C := (Y i).ProEt) (J := topology (Y i)) (hD := derived.{t, u} (Y i))
  choose q m using hy
  let m' i := Classical.choice (m i)
  obtain ⟨U⟩ := clopen_scalar_unit_normalization n
  let V i := Classical.choice (clopen_scalar_unit_normalization (m' i))
  obtain ⟨d, hd⟩ := clopen_scalar_comparison_descent X I Y j hdisjoint hcover p n q m'
  have hmodels := clopen_scalar_model_properties X I Y j hdisjoint hcover p n q m' d
  have hnorm i : (d i).sections ∧ (d i).degree ∧ (d i).representative ∧
      (d i).computed ∧ (d i).extended ∧ (d i).unique :=
    ⟨(hd i).1, (hd i).2.1, (hd i).2.2.1,
      (hmodels i).1, (hmodels i).2, (hd i).2.2.2⟩
  have hcoh := clopen_scalar_comparison_coherence X I Y j hdisjoint hcover
    p n q m' U V d hnorm
  refine ⟨p, n, U, q, m', V, d, fun i ↦ ?_⟩
  exact ⟨(hnorm i).1, (hnorm i).2.1, (hnorm i).2.2.1,
    (hnorm i).2.2.2.1, (hnorm i).2.2.2.2.1, (hnorm i).2.2.2.2.2, hcoh i⟩

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
