/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Reduced local closure and strict-local components

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Proposition 2.1.3,
printed pages 209--210; Stacks Project, Tags 01J3, 01J6, 04HX and 05WS
(blueprint: lem-per-etale-immediate-component-criterion).

The abbreviations specialize the existing reduced closed subscheme and stalk-spectrum
constructions. The theorem supplies the point of the closed subscheme and the geometric
point of its local spectrum, rather than assuming these factorizations.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The reduced closure of a point, using the existing vanishing-ideal construction.
Source: Stacks Project, Tag 01J3; ILO XIV 2.1.3
(blueprint: lem-per-etale-immediate-component-criterion). -/
noncomputable abbrev reducedPointClosure (X : Scheme.{u}) (y : X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subscheme

/-- The canonical closed immersion of the reduced closure of a point.
Source: Stacks Project, Tag 01J3; ILO XIV 2.1.3
(blueprint: lem-per-etale-immediate-component-criterion). -/
noncomputable abbrev reducedPointClosureι (X : Scheme.{u}) (y : X) :
    reducedPointClosure X y ⟶ X :=
  (IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι

/-- The local spectrum of the reduced point closure at its point `w`.
Source: Stacks Project, Tag 01J6; ILO XIV 2.1.3
(blueprint: lem-per-etale-immediate-component-criterion). -/
noncomputable abbrev reducedLocalClosure (X : Scheme.{u}) (y : X)
    (w : reducedPointClosure X y) : Scheme.{u} :=
  Spec ((reducedPointClosure X y).presheaf.stalk w)

/-- The canonical map from the reduced local closure to the ambient scheme.
Source: Stacks Project, Tag 01J6; ILO XIV 2.1.3
(blueprint: lem-per-etale-immediate-component-criterion). -/
noncomputable abbrev reducedLocalClosureMap (X : Scheme.{u}) (y : X)
    (w : reducedPointClosure X y) : reducedLocalClosure X y w ⟶ X :=
  (reducedPointClosure X y).fromSpecStalk w ≫ reducedPointClosureι X y

/-- Reduced local closure, its strict-local comparison, and the component criterion.
Source: ILO, Travaux de Gabber, Expose XIV, Proposition 2.1.3, pp. 209--210
(blueprint: lem-per-etale-immediate-component-criterion).

Proof, following the six steps of the node:
1. On an affine neighbourhood of `x`, write the primes of `y,x` as p ⊆ m. The
   reduced-induced-closed-subscheme theorem identifies the reduced closure with Spec(R/p),
   and affine-open-stalk-localization identifies A with (R/p)_(m/p), a nonzero domain.
   Its zero prime maps to `y`, and its closed point maps to `x`, by the canonical
   Spec-local-ring morphism. This gives the point `w` and the generic point of Z.
2. The geometric point factors through the reduced closure and then its local spectrum.
   Apply affine-strict-local-ring-comparison to W and Spec A with the same separable
   residue closure and algebraic strict-henselization presentation. Localization of A
   at its maximal ideal is A. Structural-map and residue compatibility, followed by
   uniqueness in strict-henselization-functoriality, identify the resulting isomorphism
   with the canonical strictHenselizationMap.
3. Closed-immersion-strict-localization-cartesian gives the comparison with the fibre
   product. Its projection to the ambient strict localization is a closed embedding,
   whose image is the inverse image of W. Hence every ambient point over `y` lies in
   that image, the fibres correspond bijectively, and the restricted projection is a
   homeomorphism of point closures.
4. Strict-henselization-structural-flat and flat-going-down show that every minimal
   prime of the strict local ring contracts to zero in the domain A. Scheme sobriety
   identifies these primes with the generic points of irreducible components. Thus
   each component has its generic point over `y`.
5. Conversely, choose a component containing a point over `y`, using
   irreducible-components-cover, and its generic point using scheme-sober. Both points
   lie over `y`; strict-localization-discrete-fibres and the subspace topology of the
   scheme fibre imply that a generalization between them is equality. Thus each point
   over `y` is the generic point of a component of the reduced local strict localization.
6. The homeomorphisms in step 3 preserve chains of irreducible closed subsets, hence
   topological Krull dimension. Steps 4 and 5 give both directions of the final
   one-dimensional-component equivalence. No ambient-component assertion is used. -/
theorem strictLocalClosure_component_criterion
    (X : Scheme.{u}) [IsNoetherian X] (x y : X) (hxy : x ∈ closure {y})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barX : Spec (.of Ω) ⟶ X) (hbarX : barX (IsLocalRing.closedPoint Ω) = x) :
    ∃ w : reducedPointClosure X y,
      reducedPointClosureι X y w = x ∧
      (∃ η : reducedLocalClosure X y w,
        IsGenericPoint η Set.univ ∧ reducedLocalClosureMap X y w η = y) ∧
      reducedLocalClosureMap X y w
        (IsLocalRing.closedPoint ((reducedPointClosure X y).presheaf.stalk w)) = x ∧
      ∃ (barZ : Spec (.of Ω) ⟶ reducedLocalClosure X y w)
        (hbarZ : barZ ≫ reducedLocalClosureMap X y w = barX)
        (e : strictHenselizationScheme barZ ≅
          pullback (strictHenselizationStructuralMap barX) (reducedPointClosureι X y)),
        e.hom ≫ pullback.fst _ _ =
          strictHenselizationMap (reducedLocalClosureMap X y w) barZ ≫
            eqToHom (congrArg strictHenselizationScheme hbarZ) ∧
        e.hom ≫ pullback.snd _ _ =
          strictHenselizationStructuralMap barZ ≫ (reducedPointClosure X y).fromSpecStalk w ∧
        Set.BijOn (e.hom ≫ pullback.fst _ _)
          {t | (strictHenselizationStructuralMap barZ ≫ reducedLocalClosureMap X y w) t = y}
          {t | strictHenselizationStructuralMap barX t = y} ∧
        (∀ t : strictHenselizationScheme barZ,
          (strictHenselizationStructuralMap barZ ≫ reducedLocalClosureMap X y w) t = y →
          (∃ E : closure ({t} : Set (strictHenselizationScheme barZ)) ≃ₜ
              closure ({(e.hom ≫ pullback.fst _ _) t} :
                Set (strictHenselizationScheme barX)),
            ∀ z, (E z).val = (e.hom ≫ pullback.fst _ _) z.val) ∧
          topologicalKrullDim (closure ({t} : Set (strictHenselizationScheme barZ))) =
            topologicalKrullDim (closure ({(e.hom ≫ pullback.fst _ _) t} :
              Set (strictHenselizationScheme barX)))) ∧
        (∀ t : strictHenselizationScheme barZ,
          (strictHenselizationStructuralMap barZ ≫ reducedLocalClosureMap X y w) t = y →
          ∃ C ∈ irreducibleComponents (strictHenselizationScheme barZ), IsGenericPoint t C) ∧
        (∀ C ∈ irreducibleComponents (strictHenselizationScheme barZ),
          ∃ t : strictHenselizationScheme barZ,
            IsGenericPoint t C ∧
              (strictHenselizationStructuralMap barZ ≫ reducedLocalClosureMap X y w) t = y) ∧
        ((∃ t : strictHenselizationScheme barX,
            strictHenselizationStructuralMap barX t = y ∧
              topologicalKrullDim (closure ({t} : Set (strictHenselizationScheme barX))) = 1) ↔
          ∃ C ∈ irreducibleComponents (strictHenselizationScheme barZ),
            topologicalKrullDim C = 1) := by
  sorry

end AlgebraicGeometry.Scheme
