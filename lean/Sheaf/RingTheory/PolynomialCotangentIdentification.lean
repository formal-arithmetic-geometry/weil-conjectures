/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Polynomial cotangent complexes and localization

Source: Stacks Project, Cotangent Complex, Tags 08QH and 08SF
(blueprint: lem-trf-smooth-cotangent-identification).

The augmentation is specified on every tensor generator, rather than replaced
by an unspecified isomorphism. The localization clause uses the canonical
Kähler equivalence to identify its target with the localized differential module.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Simplicial

namespace Algebra.CotangentResolution

/-- The augmentation from the standard differential complex to universal
Kähler differentials in degree zero. Its degree-zero value on `b ⊗ dx` is
`b d(ε(x))`; the other components have zero target. These values uniquely
specify the chain map, since differential tensors generate degree zero.
Source: Stacks Project, Cotangent Complex, Tags 08PN and 08QH
(blueprint: lem-trf-smooth-cotangent-identification). -/
structure DifferentialAugmentation
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) where
  map : differentialComplex (C.differentials (C.standard f)) ⟶
    (HomologicalComplex.single (ModuleCat.{u} f.right) (ComplexShape.up ℤ) 0).obj
      (CommRingCat.KaehlerDifferential f.hom)
  generator : ∀ (b : f.right) (x : (C.standard f).algebra.obj (op ⦋0⦌)),
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (CommRingCat.KaehlerDifferential f.hom)).hom
        (map.f 0 (complexGenerator (C.differentials (C.standard f)) 0 b x)) =
      b • CommRingCat.KaehlerDifferential.d
        ((C.standard f).augmentation.app (op ⦋0⦌) x)

/-- The canonical identification between differentials of the bundled algebra
map and the usual algebra-instance notation. This transports only along the
existing equality `toAlgebra_algebraMap`.
Source: Stacks Project, Algebra, universal differentials, Tag 00RM
(blueprint: lem-trf-smooth-cotangent-identification). -/
def kahlerAlgebraMapIso (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A B)) ≅
      ModuleCat.of B (KaehlerDifferential A B) :=
  eqToIso (congrArg (fun α : Algebra A B ↦
    letI := α
    ModuleCat.of B (KaehlerDifferential A B)) (toAlgebra_algebraMap (R := A) (S := B)))

/-- For a polynomial algebra with any set of variables, the canonical
augmentation identifies its standard cotangent complex with its universal
Kähler differentials in degree zero. After every localization the same
augmentation, composed with the inverse canonical Kähler localization
isomorphism, identifies the cotangent complex with the localized polynomial
differential module in degree zero.
Source: Stacks Project, Cotangent Complex, Tags 08QH and 08SF
(blueprint: lem-trf-smooth-cotangent-identification).

Proof: (1) Use the constant simplicial polynomial algebra augmented by its
identity. Its alternating differential from degree `-n` is zero for odd `n`
and the identity for positive even `n`. Thus its augmentation is a polynomial
resolution, even for an empty or infinite variable set.
(2) Apply lem-trf-cotangent-resolution-coherence to compare this resolution
with the standard one. For its constant differential module, the degree-zero
inclusion and augmentation are inverse up to the contraction whose component
in degree `-n` is the identity for odd positive `n` and zero otherwise.
Naturality of comparison identifies this isomorphism with the specified
augmentation, since both send `b ⊗ dx` to `b d(ε(x))`.
(3) lem-weil-pbc-polynomial-ring-kahler-basis-any-variables identifies the
module with the direct sum on `dx_e`, with the usual finite-support partial
derivative formula; base change gives the localized basis.
(4) Apply the ring-localization clause of lem-trf-affine-cotangent-comparison
with the bottom multiplicative subset `{1}`. By
lem-weil-pbc-localization-module-exact, localization preserves the preceding
augmentation quasi-isomorphism: localized kernels and images compute its
cohomology. The tensor/fraction maps are `m ⊗ (p/t) ↦ pm/t` and
`m/t ↦ m ⊗ (1/t)`. By lem-weil-pbc-kahler-differentials-localization, the
canonical Kähler equivalence sends `c ⊗ dp` to `c d(p/1)`. Its compatibility
with augmentation follows on each generator, where both maps send
`dq ⊗ (p/t)` to `(p/t) d(ε(q)/1)`. This gives the displayed localized map
and isomorphism for every multiplicative subset, including those containing
zero. -/
theorem polynomial_augmentation_isIso
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (A : Type u) [CommRing A] (E : Type u) :
    (∃ a : DifferentialAugmentation C
      (Arrow.mk (CommRingCat.ofHom (algebraMap A (MvPolynomial E A)))),
      IsIso (DerivedCategory.Q.map a.map)) ∧
    ∀ T : Submonoid (MvPolynomial E A),
      ∃ a : DifferentialAugmentation C
        (Arrow.mk (CommRingCat.ofHom (algebraMap A (Localization T)))),
        IsIso (DerivedCategory.Q.map
          (a.map ≫
            (HomologicalComplex.single (ModuleCat.{u} (Localization T))
              (ComplexShape.up ℤ) 0).map
              ((kahlerAlgebraMapIso A (Localization T)).hom ≫
                ModuleCat.ofHom
                  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
                    A (MvPolynomial E A) (Localization T)).symm.toLinearMap))) := by
  sorry

end Algebra.CotangentResolution
