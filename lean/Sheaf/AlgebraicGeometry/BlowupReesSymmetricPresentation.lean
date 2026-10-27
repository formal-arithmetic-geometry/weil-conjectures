/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.Blowup.Affine.ReesPieceLocalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
import Mathlib.AlgebraicGeometry.Gluing

/-! # The symmetric quotient and Rees presentation of the ordinary blowup

Source: Stacks Project, Divisors, Tags 02NS and 0804; Constructions, Tags 01NO,
01NP and 01NQ (blueprint: lem-sfb-blowup-rees-symmetric-presentation).

We use the dependency's affine-basis description of quasi-coherent graded algebra
sheaves. Thus a `GradedAlgebraData.Hom` is a morphism of graded algebra sheaves,
including its restriction compatibility. The actual symmetric sheaf is identified
with this affine presentation by its canonical `sectionMap`. The Rees presentation
uses the polynomial model; `decomposeAlgEquiv` and `reesGradingEquivPow` identify it
with the direct sum of the ideal powers, by taking coefficients.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped DirectSum

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The canonical symmetric-to-Rees quotient and the ordinary blowup's relative-Proj
presentation, with affine coefficient and refinement formulas.
Source: Stacks Project, Divisors, Tags 02NS and 0804; Constructions, Tags 01LH,
01NO, 01NP and 01NQ (blueprint: lem-sfb-blowup-rees-symmetric-presentation).

Proof: (1) Apply lem-sfb-sheaf-rees-symmetric-presentation to the ideal. On each
 affine open it identifies the symmetric sheaf with the symmetric algebra of the
 ideal sections, and identifies the power-sheaf sections with the ideal powers.
 The Rees polynomial is sent to its finite tuple of coefficients; its inverse sums
 the monomials. Convolution is polynomial multiplication, giving the graded algebra
 identification with the direct sum. The degree-one extension is graded and fixes
 degree zero. Products of generators map to the corresponding Rees monomials.
 Every homogeneous Rees coefficient is a finite sum of products of ideal elements;
 summing the corresponding symmetric monomials proves affine surjectivity. This
 gives sheaf surjectivity since affines form a basis, and uniqueness of the symmetric
 extension gives canonicity and compatibility with restriction.
 (2) By def-nagata-global-blowup-local-model and def-nagata-affine-blowup the ordinary
 blowup's affine pieces are the Proj of these Rees rings. The affine charts of
 lemma-nagata-relative-proj-exists are the same Proj schemes with the same degree-zero
 structure morphisms. The coefficient identification induces their identity comparison
 on homogeneous primes and equal-degree fractions (def-nagata-affine-proj).
 (3) Check the transitions using lem-nagata-proj-affine-restriction: restriction sends
 each coefficient to its restriction, exactly def-nagata-rees-localization-map. The
 Proj maps are def-nagata-affine-blowup-restriction-map and act on fractions by
 a/f^k mapping to (a/1)/(f/1)^k. Cover intersections by opens principal in both
 affines (lem-sc-affine-inter-principal-both). Their overlap comparisons agree with
 def-nagata-global-blowup-overlap-basic-map. Scheme-morphism gluing gives equality
 on whole overlaps, hence compatibility with def-nagata-global-blowup-glue-data.
 (4) Glue the local comparisons and their inverses by lem-weil-pbc-scheme-morphism-gluing.
 Their composites and structural maps agree on the affine cover, so the comparison
 is an isomorphism over the base. For any further affine, enlarge the cover and use
 prop-nagata-global-blowup-cover-independent and lemma-nagata-relative-proj-exists.
 This gives the same comparison on every affine and its compatibility with all
 affine refinements. The existing relProjReesIso is precisely this canonical comparison.
 No intersection of affine opens is assumed affine. -/
theorem blowup_rees_symmetric_presentation {T : Scheme.{u}} (I : T.IdealSheafData) :
    ∃ hqc : I.toModules.IsQuasicoherent,
      ∃ q : (@SymmetricAlgebraSheaf.gradedAlgebraData T I.toModules hqc ⟶ I.reesData),
        (∀ U : T.affineOpens, Function.Surjective (q.app U)) ∧
        (∀ (U : T.affineOpens) (n : ℕ) (x : Fin n → Γ(I.toModules, U.1)),
          (reesAlgebra (I.ideal U)).subtype
            (q.app U (∏ i, SymmetricAlgebra.ι (T.presheaf.obj (op U.1))
              (I.toModules.val.obj (op U.1)) (x i))) =
            Polynomial.monomial n (∏ i, @id (T.presheaf.obj (op U.1))
              (I.toModulesι.app U.1 (x i)))) ∧
        (∀ U : T.affineOpens,
          Function.Bijective (SymmetricAlgebraSheaf.sectionMap I.toModules (op U.1))) ∧
        (∀ (U : T.affineOpens) (n : ℕ),
          Set.range (fun x : Γ((I ^ n).toModules, U.1) ↦
            @id (T.presheaf.obj (op U.1)) ((I ^ n).toModulesι.app U.1 x)) =
              (↑((I.ideal U) ^ n) : Set (T.presheaf.obj (op U.1)))) ∧
        (∀ (U : T.affineOpens) (F : reesAlgebra (I.ideal U)) (n : ℕ),
          (reesGradingEquivPow (I.ideal U) n
            ((DirectSum.decomposeAlgEquiv (reesGrading (I.ideal U)) F) n) :
              T.presheaf.obj (op U.1)) =
              (F : Polynomial (T.presheaf.obj (op U.1))).coeff n) ∧
        I.relProjReesIso.inv ≫ I.reesData.relProjHom = I.blowupMap ∧
        (∀ U : T.affineOpens,
          I.blowupι U ≫ I.relProjReesIso.inv = I.reesData.relProjι U) ∧
        (∀ (U V : T.affineOpens) (h : U ≤ V),
          I.blowupFunctor.map (homOfLE h) ≫ I.blowupι V ≫ I.relProjReesIso.inv =
            I.reesData.relProjFunctor.map (homOfLE h) ≫ I.reesData.relProjι V) ∧
        (∀ (U V : T.affineOpens) (h : U ≤ V) (F : reesAlgebra (I.ideal V)),
          (reesAlgebra (I.ideal U)).subtype (I.reesData.res h F) =
            (F : Polynomial (T.presheaf.obj (op V.1))).map
              (T.presheaf.map (homOfLE (X := T.Opens) h).op).hom) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
