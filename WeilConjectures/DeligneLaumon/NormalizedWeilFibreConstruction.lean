/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData

/-! # Construction of the normalized Weil action on actual condensed fibres
Source: Weil II (1.1.10)--(1.1.12), generic-fibre proof steps 2--4 and 7--8.
(blueprint: lem-dl-a1-normalized-weil-fibre-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]

variable (ell : ℕ) [Fact ell.Prime]


/-- Construct only the forward normalized tensor fibre functor; no fullness or
essential surjectivity, abelianness, or subobject classification is asserted.

Source: Weil II (1.1.10)--(1.1.12), proof steps 2--4 and 7--8.
(blueprint: lem-dl-a1-normalized-weil-fibre-construction).

Proof: use the normal constant field L = F_(q^d) and its cyclic component decomposition.
On the selected component restrict the sheaf and compose its d successive Frobenius
structure maps to obtain the return isomorphism a. Apply the normal lisse correspondence
in S to obtain its geometric representation rho on the actual fibre. Choose a degree d
lift s in the arithmetic exact sequence over L. The finite-cover-normalized path gives
L_s from the fibre of the return pullback to the original fibre, and naturality gives
L_s rho_f(g) = rho(s^-1 g s)L_s. Set T = a_t L_s^-1. Hence
T rho(h) T^-1 = rho(s h s^-1). Every Weil element is uniquely h s^n, so define its action
by rho(h) T^n; the conjugation equation proves multiplicativity for every integer n.
Take scalar restriction and extension along the coefficient equivalence to the specified
ULift coefficient field. The correspondence supplies the finite geometric coefficient
model. Sheaf morphisms intertwine these actions by path naturality. Identify the resulting
fibre with actual point sections, retaining the specified scalar law. The normalized
finite-cover path for any positive original degree gives the same return action: two paths
with the same arithmetic image agree on all finite covers, and therefore on integral
reductions and their rational scalar extensions. Pullback, point sections and path transport
commute with tensors. These give the tensor constraints and their coherence by evaluation
on pure tensors. Local finite freeness proves the tensor and unit lisse clauses; the unit
has constant one-dimensional fibre with trivial action. -/
theorem normalized_weil_fibre_construction
    (hEll : ell ≠ D.p) [IsSeparated U₀.hom]
    (hNormal : ∀ z : U₀.left, IsDomain (U₀.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk z))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z)
    (A : Geometry D U₀ t G) (S : RealCondensedFibre.System.{u} ell) :
    Nonempty (NormalizedFunctor D U₀ t G ell A S) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
