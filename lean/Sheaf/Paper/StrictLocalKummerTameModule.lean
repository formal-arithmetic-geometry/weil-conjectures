/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Strict-local compatible-root tameness

Source: the strict-local tame condition in paragraph (3) of the direct-image proof,
blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability.
(blueprint: def-sfb-strict-local-kummer-tame-module).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Positive root orders prime to the residue characteristic.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
abbrev TameRootOrder (p : ℕ) := {n : ℕ // 0 < n ∧ n.Coprime p}

/-- Equations for all roots, with compatibility under divisibility. These impose both
x_(i,n)^n = t_i and x_(i,m)^(m/n) = x_(i,n) whenever n divides m.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
def tameRootRelations (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    Set (MvPolynomial (Fin r × TameRootOrder p) R) :=
  {a | (∃ (i : Fin r) (n : TameRootOrder p),
      a = MvPolynomial.X (i, n) ^ n.val - MvPolynomial.C (t i)) ∨
    ∃ (i : Fin r) (n m : TameRootOrder p), n.val ∣ m.val ∧
      a = MvPolynomial.X (i, m) ^ (m.val / n.val) - MvPolynomial.X (i, n)}

/-- The actual algebra adjoining compatible roots of the parameters of every order prime to p.
Its spectrum over the boundary complement is the inverse-limit Kummer cover. In rank zero
there are no variables or relations, giving the original ring canonically.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
abbrev tameRootAlgebra (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :=
  MvPolynomial (Fin r × TameRootOrder p) R ⧸ Ideal.span (tameRootRelations p t)

/-- The Kummer scheme over the strict localization, restricted to W. Pullback restricts
away from the boundary after adjoining the roots; consequently all roots of boundary
parameters are units on this scheme.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
abbrev strictLocalTameRootProjection (p : ℕ) {Y W : Scheme.{u}} (w : W ⟶ Y)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    {r : ℕ} (t : Fin r → Scheme.strictHenselizationRing s) :
    pullback w (Spec.map (CommRingCat.ofHom
      (algebraMap (Scheme.strictHenselizationRing s) (tameRootAlgebra p t))) ≫
        Scheme.strictHenselizationStructuralMap s) ⟶ W :=
  pullback.fst _ _

/-- A tuple is the boundary part of a regular system of parameters of the strict local
ring: it extends to a full regular system, and its product has precisely the pulled-back
boundary as its zero set. For a reduced SNC boundary this says exactly that these
parameters cut out its distinct local components.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
def IsStrictLocalBoundaryParameters {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    {r : ℕ} (t : Fin r → Scheme.strictHenselizationRing s) : Prop :=
  (∃ (_hlocal : IsLocalRing (Scheme.strictHenselizationRing s))
      (_hnoeth : IsNoetherianRing (Scheme.strictHenselizationRing s))
      (rest : List (Scheme.strictHenselizationRing s)),
    IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ rest)) ∧
  (Scheme.strictHenselizationStructuralMap s) ⁻¹' (D.support : Set Y) =
    PrimeSpectrum.zeroLocus {∏ i, t i}

/-- Tame means that at every geometric point, on the compatible prime-to-p root cover
for every regular boundary parameter tuple, the pulled-back module is finite constant.
The coefficient ring is pulled back from the condensed point using the existing module
pullback. All parameter choices are quantified, so this condition has no chosen parameters.
For r = 0 the root cover is canonically the strict-local boundary complement itself.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
def IsStrictLocalKummerTameModule (p : ℕ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y W : Scheme.{u}} (D : Y.IdealSheafData)
    (w : W ⟶ Y)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) : Prop :=
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (s : Spec (.of κ) ⟶ Y)
    (r : ℕ) (t : Fin r → Scheme.strictHenselizationRing s),
    IsStrictLocalBoundaryParameters D s t →
      Mod.IsFree (condensedRingObj Λ _)
        ((CondensedRing.upperStar Λ (strictLocalTameRootProjection p w s t)).obj L)

end AlgebraicGeometry.ProEtale
