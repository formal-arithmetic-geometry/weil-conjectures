/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # Geometry and canonical maps for the Kummer line computation

Source: blueprint sk-prop-a1-kummer, Degrees 0 and 1
(blueprint: def-pur-kummer-line-geometry).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.KummerLine

/-- The two affine schemes in the computation.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def curve (k : Type u) [Field k] : Bool → Scheme.{u}
  | false => Spec (CommRingCat.of (Polynomial k))
  | true => Spec (CommRingCat.of (LaurentPolynomial k))

/-- The structure morphisms of the two lines over k.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def structureMap (k : Type u) [Field k] : (b : Bool) → curve k b ⟶ Spec (CommRingCat.of k)
  | false => Spec.map (CommRingCat.ofHom Polynomial.C)
  | true => Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The canonical open inclusion, induced by k[t] → k[t,t⁻¹].
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def inclusion (k : Type u) [Field k] : curve k true ⟶ curve k false :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

/-- Pullback of a scalar to global functions on either line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def scalar (k : Type u) [Field k] (b : Bool) : k →+* Γ(curve k b, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k b).appTop).hom

/-- The global unit t on the punctured line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def coordinateUnit (k : Type u) [Field k] : Γ(curve k true, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := k) 1).unit

/-- The Kummer generator is the actual connecting homomorphism applied to t.
Source: blueprint sk-prop-a1-kummer, Degrees 0 and 1
(blueprint: thm-pur-kummer-affine-line). -/
def generator (k : Type u) [Field k] (m : ℕ) (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1 :=
  (curve k true).kummerδ₀ m hm (Additive.ofMul (coordinateUnit k))

/-- Restriction on root-sheaf cohomology, using the canonical pullback comparison.
Source: Stacks, Tag 03PK (blueprint: thm-pur-kummer-affine-line). -/
def rootRestriction (k : Type u) [Field k] (m q : ℕ) :
    Sheaf.H ((curve k false).rootsOfUnitySheaf m) q →+
      Sheaf.H ((curve k true).rootsOfUnitySheaf m) q :=
  (Sheaf.H.map (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m (inclusion k)) q).comp
    (Etale.cohomologyMap (inclusion k) ((curve k false).rootsOfUnitySheaf m) q)

end AlgebraicGeometry.KummerLine
