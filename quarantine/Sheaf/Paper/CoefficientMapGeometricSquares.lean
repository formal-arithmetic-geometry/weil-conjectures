/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtensionData
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.ExceptionalCoefficientMaps
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.SixFunctors.CoefMonoidalSquareHomTransport
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.DualityPairing
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # Geometric squares for arbitrary finite coefficient maps

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Scheme-isomorphism transport of canonical coefficient maps is independent of
flatness of the coefficient homomorphism.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph
(blueprint: lem-sf-coefficient-map-geometric-squares).

Proof: a scheme isomorphism reindexes the small sites with inverse given by its
inverse scheme map. Constant rings and their module actions are unchanged.
The ordinary scalar and tensor exchange maps on sections are balancing maps,
so the coefficient/geometric square commutes on pure tensors. Applying these
exact reindexing equivalences termwise and localizing gives the same equality
for derived tensorators, including arbitrary coefficient maps. For direct image,
transpose the proposed square under inverse image/direct image: naturality of
its counit and the preceding scalar square identify both transposes. For a closed
immersion, transpose once more under its own direct-image/right-adjoint adjunction;
the inverse image-comparison terms cancel, leaving the extended closed counit.
For compact supports, perform the same calculation after factoring into the fixed
open immersion and proper morphism. Open extension is the given module on the
open and zero outside it, so reindexing identifies its coefficient comparison.
The mate calculation gives ExceptionalGeometry; evaluating at the regular unit
gives the dualizing square. For internal Hom, transpose with tensor--Hom: both
paths are scalar extension of pulled-back evaluation. The normalization hypothesis
identifies any tensorator in the statement with this representative-normalized
one, including after replacing X by the isomorphic scheme. On the pro-etale site,
the scalar/site and geometric/site balancing squares commute. Take their right
mates to identify rnuScalar and rnuPull, retaining the site counit. Substitution
in the definitions of proClosedMap, proClosedPull, proOmegaMap and proOmegaPull
then transports the etale squares. The same evaluation transpose proves the
pro-etale Hom square. The finite-Tor constructible domain supplies bounded
etale origin wherever full faithfulness is needed. None of these equalities
asserts that a coefficient quotient is flat. -/
theorem coefficient_map_geometric_squares
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T X Z S : Scheme.{u}} (f : T ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} [QuasiCompact aX] (c : Compactification aX)
    (μ : Sites.TensorComparison true φ X) (hμ : Sites.NormalizedTensor true φ X μ) :
    Sites.DirectGeometry φ f ∧ Sites.HomGeometry φ X ∧
    Sites.ClosedGeometry φ i ∧ Sites.ExceptionalGeometry φ c (𝟙_ _) ∧
    Sites.ProDirectGeometry φ f ∧ Sites.ProClosedGeometry φ i ∧
    Sites.ProHomGeometry φ X μ ∧ Sites.ProOmegaGeometry φ c := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
