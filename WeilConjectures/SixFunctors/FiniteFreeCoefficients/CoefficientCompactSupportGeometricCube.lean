/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange

/-! # The scalar compact-support cube under geometric reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The scalar compact-support comparison commutes with isomorphism base change.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-coefficient-compact-support-geometric-cube).
Proof: choose the compactification of f and pull it back along e. Factor compact
support into open extension and proper direct image. On the open part scalar
extension is tensoring on the open and zero off it, so its balancing comparison
commutes with reindexing. For the proper part, transpose the direct-image square
under geometric pullback/direct image; the counit identity gives scalar extension
of the pulled-back counit. Paste these squares, using naturality of proper exchange
at the open scalar map. This proves the cube for the pulled-back compactification.
Compare this compactification with the one chosen for the base-changed map through
a common refinement. Proper/open scalar composition and refinement naturality
identify the two compact-support coefficient maps. The refinement isomorphism in
the definition of rightDerivedLowerShriekBaseChangeMap then gives exactly this
identity. Geometric reindexing and the refinement maps are equivalences, so the
argument works on unbounded complexes and requires no Noetherian hypothesis,
flatness of phi or invertibility of the scalar comparison. -/
theorem coefficient_compact_support_geometric_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [QuasiCompact f] (S' : Scheme.{u}) (e : S' ≅ S)
    (N : Cat A X) :
      (Sites.pull B e.hom).map
          (ExceptionalCoefficients.compactSupportMap φ
            (HasCompactification.compactification f) N) ≫
        (rightDerivedLowerShriekBaseChangeMap B
          (IsPullback.of_hasPullback f e.hom)).app ((scalarExtension φ X).obj N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B)
          (pullback.snd f e.hom)).map
          ((Sites.scalarPull φ (pullback.fst f e.hom)).hom.app N) =
      (Sites.scalarPull φ e.hom).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≫
        (scalarExtension φ S').map
          ((rightDerivedLowerShriekBaseChangeMap A
            (IsPullback.of_hasPullback f e.hom)).app N) ≫
        ExceptionalCoefficients.compactSupportMap φ
          (HasCompactification.compactification (pullback.snd f e.hom))
          ((Sites.pull A (pullback.fst f e.hom)).obj N) := by
  simpa only [Sites.pull, Sites.scalarPull, compactScalarChosenMap, compactScalarMap] using
    sectionScalar_exchange_left φ (IsPullback.of_hasPullback f e.hom) N

end WeilConjectures.FiniteFreeCoefficients
