/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation
import Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing

/-! # Blowup immersion from a compatible Rees presentation

Source: Stacks Project, Divisors, Tag 02NS; Constructions, Tags 01MY, 01NQ and 07ZK
(blueprint: lem-sfb-rees-presentation-blowup-immersion).

The recorded relative-Proj interface presents quasi-coherent graded algebras on the
basis of affine opens. A graded algebra isomorphism to `I.reesData` is exactly the
family of base-linear graded Rees isomorphisms commuting with coefficient restriction.
In particular it fixes degree-zero scalars, and identifies degree zero with the base.
The local equations below use the ordinary glued blowup's canonical chart embeddings.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.GradedAlgebraData

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A compatible affine Rees presentation determines the unique chart-compatible
isomorphism from the ordinary blowup, and the given symmetric quotient determines its
closed immersion into the canonical projective bundle of the ideal.
Source: Stacks Project, Divisors, Tag 02NS; Constructions, Tags 01MY, 01NQ and 07ZK
(blueprint: lem-sfb-rees-presentation-blowup-immersion).

Proof: (1) The coefficient isomorphisms alpha of
lem-sfb-sheaf-rees-symmetric-presentation identify the sheaf Rees algebra with the
polynomial Rees algebras. By lem-sfb-blowup-rees-symmetric-presentation the ordinary
blowup is its relative Proj, compatibly with every affine chart.
(2) Compose theta with the inverse coefficient identifications to obtain a base-linear
graded sheaf algebra isomorphism gamma. Restriction compatibility follows by cancelling
alpha in the two coefficient-restriction identities. Apply
 def-sfb-relative-proj-iso-of-graded-iso and compose with the comparison in (1).
On a homogeneous chart its comorphism sends a/f^m to theta(a)/theta(f)^m, since
alpha gamma = theta. The map fixes scalars and therefore lies over X.
(3) For any two affine opens, refine their intersection by affine opens using
lem-weil-pbc-affine-opens-basis. The restriction formulas identify both local maps
with theta on every refinement. By lem-weil-pbc-scheme-morphism-gluing the local
maps agree on the whole overlap. The same uniqueness on the inverse-image affine
cover gives uniqueness of e; its inverse is determined by its forward morphism.
(4) Lift each homogeneous summand under phi and sum the finitely many lifts. This
proves surjectivity on whole affine section rings. Clause (3) of
prop-nagata-relative-proj-functoriality gives the closed immersion q = Proj(phi).
(5) Set j = e.hom followed by q. The canonical symmetric grading is generated in
degree one. The chart assertion of lem-sfb-graded-proj-quotient-twist-comparison
identifies q on fractions, and composing with (2) gives the Proj morphism of
 theta phi, with the corresponding inverse-image standard charts. Both maps fix
base scalars, so the projective-bundle projection composed with j is the blowup map,
first on each affine and then globally by scheme-morphism gluing. The target is
P_X(I) by def-trf-projective-bundle-morphism; its finite-type requirement is hI.
(6) Composing a closed immersion with a source isomorphism is a closed immersion:
the underlying map is a homeomorphism onto a closed subset, and its sheaf map is
the composite of a surjection with an isomorphism (def-weil-closed-immersion).
No integrality, Noetherian, or nonzero-ideal assumption enters any step. -/
theorem rees_presentation_blowup_immersion {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.toModules.IsQuasiCoherentFiniteType) (C : X.GradedAlgebraData)
    (θ : C ≅ I.reesData)
    (φ : @SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hI.1 ⟶ C)
    (hφ : ∀ (U : X.affineOpens) (n : ℕ),
      Function.Surjective ((φ.app U).gradedAddHom n)) :
    ∃ (hθirr : IrrelevantLE θ.hom) (hφirr : IrrelevantLE φ),
      ∃ e : I.blowup ≅ C.relProj,
        e.hom ≫ C.relProjHom = I.blowupMap ∧
        (∀ U : X.affineOpens,
          I.blowupι U ≫ e.hom =
            Proj.map (θ.hom.app U) (hθirr U) ≫ C.relProjι U) ∧
        (∀ e' : I.blowup ≅ C.relProj,
          e'.hom ≫ C.relProjHom = I.blowupMap →
          (∀ U : X.affineOpens,
            I.blowupι U ≫ e'.hom =
              Proj.map (θ.hom.app U) (hθirr U) ≫ C.relProjι U) → e' = e) ∧
        (∀ U V : X.affineOpens,
          pullback.fst (I.blowupι U) (I.blowupι V) ≫
            Proj.map (θ.hom.app U) (hθirr U) ≫ C.relProjι U =
          pullback.snd (I.blowupι U) (I.blowupι V) ≫
            Proj.map (θ.hom.app V) (hθirr V) ≫ C.relProjι V) ∧
        (∀ (U V : X.affineOpens) (h : U ≤ V),
          I.blowupFunctor.map (homOfLE h) ≫ I.blowupι V ≫ e.hom =
            Proj.map (θ.hom.app U) (hθirr U) ≫ C.relProjι U) ∧
        IsClosedImmersion (e.hom ≫ relProjMap φ hφirr) ∧
        (∀ U : X.affineOpens,
          I.blowupι U ≫ e.hom ≫ relProjMap φ hφirr =
            Proj.map ((θ.hom.app U).comp (φ.app U))
              (HomogeneousIdeal.irrelevant_le_map_comp (hφirr U) (hθirr U)) ≫
                (@SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hI.1).relProjι U) ∧
        (e.hom ≫ relProjMap φ hφirr) ≫
          (@SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hI.1).relProjHom =
            I.blowupMap := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
