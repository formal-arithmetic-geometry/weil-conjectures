/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.CategoryTheory.PushoutShortExactSequence

/-!
# Finite-stage descent of extensions with constructible quotient

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, proof of Lemma 7.4.4,
printed p.306 (PDF p.312), global extension-class assertion
(blueprint: lem-per-constructible-extension-finite-stage).

Module-valued etale sheaves represent modules over the constant ring sheaf via
`Scheme.etaleConstantModuleFunctor_isEquivalence`. The directed subobjects are represented
by a diagram equipped with monic inclusion maps to its specified colimit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- An extension with constructible quotient and kernel a directed union of subobjects is
obtained by pushing out an extension by one stage; the middle comparison is monic.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, proof of Lemma 7.4.4,
printed p.306 (PDF p.312)
(blueprint: lem-per-constructible-extension-finite-stage).

Proof plan:
1. Write H, F, G for the terms of S. The module-sheaf category is Grothendieck abelian by
lem-weil-pbc-module-sheaves-grothendieck-abelian. Apply
lem-per-noetherian-constructible-flat-lifting to S.g and the identity of G, obtaining an
epic finite affine etale rank-one sum E -> G and a lift E -> F. Its kernel K maps to H.
2. By lem-weil-pbc-constructible-module-subobject-noetherian, K is constructible. Apply the
same lifting lemma to its identity to get an epic finite affine rank-one sum Q -> K.
3. The adjunction lem-pur-site-restriction-module-adjunction-exact identifies maps from
j_V! R_V to M with sections M(V), by evaluation at 1. The construction is the sum-extension
of def-weil-pbc-etale-sum-extension, naturally in M. Thus Q -> H gives finitely many sections.
4. By lem-weil-pbc-etale-qcqs-sections-filtered-colimit, each section over an affine V comes
from one stage. Directedness puts these finitely many stages below one a. For an empty sum
choose any a using nonemptiness. Naturality gives Q -> H_a lifting Q -> H.
5. This map kills the kernel of Q -> K because H_a -> H is monic. Since Q -> K is the
cokernel of its kernel, it descends to K -> H_a. Epic cancellation identifies its composite
to H with the original K -> H.
6. Push out K -> E along K -> H_a. By lem-weil-pbc-pushout-short-exact-sequence this gives
0 -> H_a -> F_a -> G -> 0 and a comparison to S. A map killed by F_a -> F factors through
H_a by exactness; monicity of H_a -> H -> F kills that factor, proving the comparison monic.
7. Push out instead along K -> H. The same lemma and lem-weil-pbc-short-five-lemma identify
this second pushout with F, since both endpoint comparisons are identities.
8. A compatible pair of maps from F_a and H restricts to compatible maps from E and H.
The second pushout gives a unique map from F. Its restriction to F_a is the required map
by the first pushout. This proves the asserted IsPushout universal property. -/
theorem exists_constructible_extension_finite_stage
    (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R] [Algebra (ZMod ℓ) R]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hS : S.ShortExact) [Scheme.IsConstructibleSheaf S.X₃]
    (I : Type (u + 1)) [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (ι : D ⟶ (Functor.const I).obj S.X₁) [∀ a : I, Mono (ι.app a)]
    (hι : IsColimit (Cocone.mk S.X₁ ι)) :
    ∃ (a : I) (Fₐ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (iₐ : D.obj a ⟶ Fₐ) (pₐ : Fₐ ⟶ S.X₃) (hz : iₐ ≫ pₐ = 0),
      (ShortComplex.mk iₐ pₐ hz).ShortExact ∧
        ∃ φ : ShortComplex.mk iₐ pₐ hz ⟶ S,
          φ.τ₁ = ι.app a ∧ φ.τ₃ = 𝟙 S.X₃ ∧ Mono φ.τ₂ ∧
            IsPushout iₐ (ι.app a) φ.τ₂ S.f := by
  sorry

end AlgebraicGeometry.Etale
