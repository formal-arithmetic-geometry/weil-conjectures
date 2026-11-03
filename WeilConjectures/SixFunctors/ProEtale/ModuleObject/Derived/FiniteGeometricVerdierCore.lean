/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteGeometricVerdierBase
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteGeometricVerdierNormalization

/-!
# Normalized finite-coefficient geometric dualizing core

Source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, opening locality/restriction step
(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Normalized dualizing objects and geometric exchange for arbitrary finite coefficients.
Source: latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`det-prop-sf-biduality-general.proof.md`, opening geometric restriction argument.

Proof: identify the finite discrete condensed coefficient modules with ordinary constant-A
modules, and their constructible finite-Tor categories with the etale categories. Exact
pullback preserves bounded flat constructible representatives and their Tor intervals; its
canonical tensorator preserves the Koszul symmetry. The field-extension projection is an
fpqc cover, so exact faithful inverse image detects vanishing cohomology of cones and hence
isomorphisms. Compact-support exchange is the open-extension comparison followed by the
proper direct-image mate, with compactification coherence identifying the chosen models.

Choose the directed tower of finite separable subextensions of a separable closure in kbar.
Finite etale sum functors are left adjoint to pullback and agree with compact support.
Support composition and the exceptional adjunction identify Hom(P, g_i^*W) with
Hom(Ra_i!P, A), so Yoneda produces the finite-stage dualizing isomorphism. The
etale-horizontal support mate identifies its adjunction counit with the specified exchange,
which proves the displayed normalization. Exchange pasting makes these maps compatible.
Constructible finite-Tor descent and Hom continuity pass the representing bijections and
normalization to the separable closure. The original-stage identity of W corresponds to its
counit, fixing the normalization uniquely. Any remaining purely inseparable extension is a
universal homeomorphism; topological invariance preserves constructibility and, by
monoidality, finite Tor amplitude. Transport the representing bijections across this
equivalence and paste exchange to obtain the asserted normalized isomorphism over kbar.
The finite-or-algebraically-closed field assumption supplies the exceptional adjoints and
constructible support stability throughout; the algebraically closed tower is trivial.
No internal-Hom invertibility or biduality is used in this core. If A is zero or X is empty,
the same representing bijections yield the unique zero-category comparisons.
(blueprint: new-lem-sfb-finite-geometric-verdier-core) -/
theorem finite_geometric_verdier_core_exists
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) :
    Nonempty (FiniteFieldDualizingPullbackCore
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A)
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ⊓
        DerivedCategory.finiteTorAmplitude _)
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (leftDerivedUpperStarUnitIso (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A)) X)
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A))
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) )
      (detSfCompactSupport (cartesianFinitePointRing A) c)
      (detSfCompactSupport (cartesianFinitePointRing A)
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfCompactSupportBaseChangeComposite (cartesianFinitePointRing A) a
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c
        (compactSupportOpenBaseChangeIso (cartesianFinitePointRing A) a
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c))) := by
  obtain ⟨W, Wbar, counit, counitBar, hW, hWbar, rep, repBar,
      symmetry, preserves, conservative, exchange⟩ :=
    finite_geometric_verdier_base_exists p ell hple k hk A hA kbar X a c
  obtain ⟨w, hw⟩ := finite_geometric_dualizing_normalization
    p ell hple k hk A hA kbar X a c W Wbar counit counitBar hW hWbar rep repBar
  exact ⟨{
    W := W
    Wbar := Wbar
    W_ctf := hW
    Wbar_ctf := hWbar
    counit := counit
    counitBar := counitBar
    represents := rep
    representsBar := repBar
    symmetry := symmetry
    preserves_ctf := preserves
    conservative := conservative
    exchange_iso := exchange
    dualizingIso := w
    counit_normalization := hw }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
