/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen

/-!
# Unramifiedness from ordinary fibre decompositions

Source: Stacks Project, Morphisms, Lemma Tag 02G8 (lemma-unramified-etale-fibres),
part (2), lines 7828--7839 (blueprint: lem-trf-unramified-ordinary-fibre-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism whose ordinary fibres are arbitrary coproducts of
finite separable field spectra is unramified.

Source: Stacks Project, Morphisms, Lemma Tag 02G8 (lemma-unramified-etale-fibres),
part (2), lines 7828--7839 (blueprint: lem-trf-unramified-ordinary-fibre-criterion).

Proof:
1. On an affine chart of the target and an affine member of a locally finite type
   cover of its inverse image, each fibre chart is an open subscheme of a fibre of
   `h`; the fibre decomposition criterion (Tag 02G7) and restriction stability of
   unramified morphisms make every such chart unramified.
2. The affine unramified criterion gives vanishing fibre differentials. Differential
   base change, finite generation of relative differentials, and Nakayama's lemma
   then force the relative differentials of every affine chart to vanish.
3. The affine-cover characterization of an unramified morphism glues these charts,
   yielding `LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)`. -/
theorem unramified_of_ordinary_fibre_coproduct_finite_separable
    {Z B : Scheme.{u}} (h : Z ⟶ B) [LocallyOfFiniteType h] :
    (∀ s : B, ∃ (I : Type u) (L : I → Type u)
      (hfield : ∀ i, Field (L i))
      (halg : ∀ i, Algebra (B.residueField s) (L i)),
      (∀ i, @Module.Finite (B.residueField s) (L i)
        inferInstance
        (hfield i).toCommRing.toRing.toAddCommGroup.toAddCommMonoid
        (halg i).toModule) ∧
      (∀ i, @Algebra.IsSeparable (B.residueField s) (L i)
        inferInstance (hfield i).toCommRing.toRing (halg i)) ∧
      ∃ e : h.fiber s ≅ ∐ (fun i : I ↦ Spec (CommRingCat.of (L i))),
        e.hom ≫ Sigma.desc (fun i : I ↦
          (Spec.homEquiv (R := B.residueField s)
            (S := CommRingCat.of (L i))).symm
            (CommRingCat.ofHom
              (@algebraMap (B.residueField s) (L i) inferInstance
                (hfield i).toCommRing.toSemiring (halg i)))) =
          h.fiberToSpecResidueField s) →
      LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h) := by
  sorry

end AlgebraicGeometry
