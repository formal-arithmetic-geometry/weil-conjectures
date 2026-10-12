/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleSupport
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Support of a constructible etale module sheaf

Source: Stacks Project, Etale Cohomology, Tags 09YS(3), 04FS and 04FN
(blueprint: lem-weil-pbc-constructible-module-support-constructible).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The zero-stalk condition is independent of the geometric point over a point of `X`;
a single zero stalk excludes that point from the support. The support is constructible.
Stalks and support are taken for the underlying abelian sheaf.

Source: Stacks Project, Etale Cohomology, Tags 09YS(3), 04FS and 04FN
(blueprint: lem-weil-pbc-constructible-module-support-constructible).

Proof:
1. For two geometric points over `x`, embed an algebraic closure of the residue field
   into both algebraically closed fields. Both stalks are isomorphic to the stalk at
   that common geometric point by 04FN
   (`lem-weil-pbc-algebraic-extension-embeds-algebraically-closed` and
   `lem-weil-pbc-geometric-point-morphism-stalk-bijection`). Thus their zero conditions
   agree, and one zero stalk implies that `x` is outside the support.
2. Choose the finite locally closed stratification and trivializing etale covers from
   `def-weil-pbc-etale-constructible-sheaf`. Each immersion identifies its domain with
   the corresponding constructible stratum (`def-constructible-stratification`).
3. Identify the pullback stalk at a geometric point of a stratum with the original stalk
   (`lem-weil-pbc-inverse-image-stalk-germ`). Step 1 identifies nonvanishing with membership
   in the support at the underlying point.
4. On a stratum, a geometric point lifts to each covering member whose image contains
   its underlying point (`lem-weil-pbc-etale-cover-geometric-point-lift`). Its stalk is
   the constant finite module there (`lem-weil-pbc-finite-locally-constant-module-values`).
   The support and its complement are the unions of images of covering members with
   respectively nonzero and zero values. Etale maps are open
   (`lem-weil-pbc-etale-morphism-open-map`), so both subsets are open in the stratum.
5. The underlying qcqs scheme is spectral (`lem-weil-pbc-qcqs-scheme-spectral`). A clopen
   part of a constructible subset is constructible: write it and its complement using
   quasi-compact open basis members and extract finite subcovers using compactness in
   the constructible topology (`lem-weil-pbc-spectral-constructible-finite-intersection`).
   This expresses the part as the intersection of the stratum with finitely many such
   opens (`def-weil-constructible-subset`).
6. The support is the finite union of its intersections with the strata, hence is
   constructible (`def-weil-constructible-subset`). -/
theorem constructibleEtaleModuleSupport {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G) :
    let F := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
    (∀ (x : X) (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X),
      s default = x → s' default = x →
        (IsZero (((pointSmallEtale s).sheafFiber).obj F) ↔
          IsZero (((pointSmallEtale s').sheafFiber).obj F))) ∧
    (∀ (x : X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s default = x → IsZero (((pointSmallEtale s).sheafFiber).obj F) →
        x ∉ etaleSheafSupport F) ∧
    Topology.IsConstructible (etaleSheafSupport F) := by
  sorry

end AlgebraicGeometry.Scheme
