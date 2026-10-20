/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison
import Sheaf.CategoryTheory.DerivedMorphismPresheaf
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Localized derived extension of coefficients and comparison

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 0D6D, 07A4 and 0G7E.
(blueprint: lem-weil-pbc-derived-scalar-extension-local-systems)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- Derived coefficient extension is compatible with localization and comparison inverse image.
The local and global extension functors are fixed by adjunction to restriction of scalars,
and each comparison is the mate normalized by the displayed unit equation. No boundedness,
finite coefficient or Tor-dimension assumption is made.

Source: Stacks Project, Cohomology on Sites, Tags 06YY (construction of derived pullback),
0D6D (composition), 07A4 (tensor compatibility) and 0G7E (K-flat pullback).
(blueprint: lem-weil-pbc-derived-scalar-extension-local-systems)

Proof: Form the sheafified extension-of-scalars functor on the original site and each slice.
Resolve complexes functorially by K-flat complexes with flat terms and apply extension to
these resolutions. Extension preserves quasi-isomorphisms between these representatives;
its ordinary adjunction to the exact restriction-of-scalars functor descends to the derived
adjunction. Restriction to a slice and comparison inverse image preserve K-flat flat-term
resolutions, so the ordinary tensor balancing comparisons compute their derived comparisons.
On a presheaf pure tensor, each comparison sends the tensor to the identical restricted or
pulled-back pure tensor. Its inverse is the opposite balancing map, proving invertibility.
Fix the slice comparison canonically as follows. Write r for slice restriction, L for
coefficient extension, R for coefficient restriction, eta for its adjunction unit, and
alpha for the canonical square commuting r with R. The comparison
r ⋙ L.local ⟶ L.global ⋙ r is the adjunction transpose of r(eta) followed by the inverse
restriction-of-scalars comparison.
The hom-equivalence inverse law gives its displayed slice unit equation, and naturality
follows from unit naturality and naturality of that restriction comparison. Comparing this
mate with the invertible flat-resolution balancing map proves it is an isomorphism.
Use the same mate construction for comparison inverse image. The ordinary units are
m ↦ 1 ⊗ m. The derived unit, composed with restriction of the left-derived counit, is the
localized ordinary unit followed by the exact restriction functor's localization comparison.
This identifies the three mates with the balancing maps and gives all three unit identities.
The same pure-tensor calculation for successive restrictions proves coherence
of the local comparisons; hence their conjugated maps form the two DerivedLocalFunctor
structures. Finally the comparison square on local maps is natural in both inputs: both
routes apply the local scalar-extension functor to the same pulled-back chain map and
conjugate by those balancing identifications. Descending to derived morphisms gives the
last identity. All constructions apply to the zero ring and to empty schemes as well. -/
theorem derivedScalarExtension_localSystems
    (B' : Type (u + 1)) [CommRing B'] (φ : B →+* B') :
    ∃ T : DerivedLocalFunctor X.smallEtaleTopology B B',
    ∃ S : DerivedLocalFunctor (ProEt.topology X) B B',
    ∃ c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B',
      ∃ aT : T.globalFunctor ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ,
      ∃ aS : S.globalFunctor ⊣ Sheaf.derivedRestrictScalars (ProEt.topology X) φ,
      ∃ aTL : ∀ V : X.Etale, T.localFunctor V ⊣
        Sheaf.derivedRestrictScalars (X.smallEtaleTopology.over V) φ,
      ∃ aSL : ∀ U : X.ProEt, S.localFunctor U ⊣
        Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ,
      (∀ (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (V : X.Etale),
        (aTL V).unit.app ((derivedSliceRestriction X.smallEtaleTopology B V).obj A) ≫
            (Sheaf.derivedRestrictScalars (X.smallEtaleTopology.over V) φ).map
              ((T.restrictionIso V).hom.app A) ≫
            (sliceRestrictScalarsIso X.smallEtaleTopology B φ V).hom.app
              (T.globalFunctor.obj A) =
          (derivedSliceRestriction X.smallEtaleTopology B V).map (aT.unit.app A)) ∧
      (∀ (A : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
        (U : X.ProEt),
        (aSL U).unit.app ((derivedSliceRestriction (ProEt.topology X) B U).obj A) ≫
            (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
              ((S.restrictionIso U).hom.app A) ≫
            (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.app
              (S.globalFunctor.obj A) =
          (derivedSliceRestriction (ProEt.topology X) B U).map (aS.unit.app A)) ∧
      (∀ A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        aS.unit.app ((derivedComparison X B).obj A) ≫
            (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).map (c.hom.app A) =
          (derivedComparison X B).map (aT.unit.app A) ≫
            (comparisonRestrictScalarsIso X B φ).hom.app (T.globalFunctor.obj A)) ∧
      (∀ (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (V : X.Etale)
        (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
          (derivedSliceRestriction X.smallEtaleTopology B V).obj D),
        derivedComparisonLocalHom X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) V
            ((T.homPresheafMap A D).app (op V) f) =
          (S.homPresheafMap ((derivedComparison X B).obj A)
              ((derivedComparison X B).obj D) ≫
            derivedLocalHomPresheafMap (c.inv.app A) (c.hom.app D)).app
              (op ((toProEt X).obj V)) (derivedComparisonLocalHom X B A D V f)) := by sorry

end AlgebraicGeometry.Scheme
