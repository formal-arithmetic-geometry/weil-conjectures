/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Blowup.Affine.ReesPieceLocalization
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded

/-! # Affine presentations and the symmetric-to-Rees surjection

Source: Stacks Project, Divisors, Tag 02NS (lemma-blowing-up-projective),
its symmetric-to-Rees map; Schemes, Tags 01HV, 01IA and 01ID; Modules, Tags
01CG and 01CL (blueprint: lem-sfb-sheaf-rees-symmetric-presentation).

We use the recorded Rees dependency's affine-basis model of a quasi-coherent
algebra sheaf, `IdealSheafData.reesData`. Its affine sections are definitionally
`reesAlgebra (I.ideal U)`, so the affine algebra identification theta is the
identity in this model. Its homogeneous inclusions are the Rees monomials.
The linear equivalences below identify those inclusions with actual sections
of the ideal-power sheaves. The coefficient formula for `decomposeAlgEquiv`
identifies the polynomial model with the direct sum, including finite support.
The symmetric sheaf's affine comparison is its canonical `sectionMap`.

A morphism in `GradedAlgebraData` includes grading, scalar compatibility and
naturality. Uniqueness below is also asserted among compatible algebra maps
without any grading assumption, as required by the symmetric universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped DirectSum

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Affine Rees presentations, coefficientwise restriction, and the unique graded
symmetric-to-Rees surjection for an arbitrary quasi-coherent ideal sheaf.
Source: Stacks Project, Divisors, Tag 02NS (lemma-blowing-up-projective), displayed
surjection; Schemes, Tags 01HV, 01IA and 01ID; Modules, Tags 01CG and 01CL
(blueprint: lem-sfb-sheaf-rees-symmetric-presentation).

Proof: (1) On an affine U, ideal-power sections are the powers of I(U)
(def-sbc-ideal-sheaf-powers). Open restriction preserves module coproducts
(lem-weil-pbc-module-restriction-open-immersion-colimits). The tilde functor also
preserves coproducts and its affine unit is an isomorphism
(lem-weil-pbc-affine-tilde-gamma-adjunction). Thus sections of the sheaf Rees
coproduct are the direct sum of the ideal powers, with finite degree support.
(2) Send a finite tuple to the sum of its monomials. Coefficient extraction is
its inverse in reesAlgebra (def-nagata-rees-algebra). Multiplication and the unit
agree with those of def-nagata-sheaf-rees-algebra, giving the graded algebra
identification and the degree-zero identity.
(3) Summand inclusions commute with sheaf restriction. Hence restriction sends
each coefficient through structure-sheaf restriction. On a principal open this
is a/1, by lem-weil-pbc-spec-module-tilde-sections. No intersection of arbitrary
affines is assumed affine.
(4) Apply lem-weil-pbc-quasi-coherent-symmetric-algebra to the degree-one Rees
inclusion. Its universal property gives the unique algebra-sheaf extension;
its affine comparison identifies the source with the symmetric algebra of
ideal sections. Products of n generators map to their product times t^n.
(5) The monomials span symmetric degree n
(lem-weil-pbc-symmetric-algebra-graded), with the grading of
def-trf-canonical-symmetric-graded-algebra, so the map preserves degree.
Every element of I(U)^n is a finite sum of scalar multiples of products of n
ideal elements: use I^0=R and induct on I^(n+1)=I^n I. The corresponding sum of
symmetric monomials is a preimage in degree n. No finite generation is used.
(6) Symmetric restriction sends each generator to its restricted section and
scalars by ring restriction. Multiplicativity gives the same restricted Rees
monomial in either order, and the spanning result extends this to all sections.
This proves compatibility and the asserted uniqueness. Zero and unit ideals,
degree zero and the empty affine are included. -/
theorem sheaf_rees_symmetric_presentation {X : Scheme.{u}} (I : X.IdealSheafData) :
    ∃ hqc : I.toModules.IsQuasicoherent,
      ∃ q : (@SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hqc ⟶ I.reesData),
        (∀ (U : X.affineOpens) (n : ℕ), Function.Surjective ((q.app U).gradedAddHom n)) ∧
        (∀ (U : X.affineOpens) (n : ℕ) (x : Fin n → Γ(I.toModules, U.1)),
          (reesAlgebra (I.ideal U)).subtype
            (q.app U (∏ i, SymmetricAlgebra.ι (X.presheaf.obj (op U.1))
              (I.toModules.val.obj (op U.1)) (x i))) =
            Polynomial.monomial n
              (∏ i, @id (X.presheaf.obj (op U.1)) (I.toModulesι.app U.1 (x i)))) ∧
        (∀ (U : X.affineOpens) (r : (X.presheaf.obj (op U.1))),
          (reesAlgebra (I.ideal U)).subtype
            (q.app U (algebraMap (X.presheaf.obj (op U.1))
              (SymmetricAlgebraSheaf.sections I.toModules (op U.1)) r)) = Polynomial.C r) ∧
        (∀ U : X.affineOpens,
          Function.Bijective (SymmetricAlgebraSheaf.sectionMap I.toModules (op U.1))) ∧
        (∀ (U : X.affineOpens) (n : ℕ),
          ∃ e : Γ((I ^ n).toModules, U.1) ≃ₗ[(X.presheaf.obj (op U.1))] reesGrading (I.ideal U) n,
            ∀ x : Γ((I ^ n).toModules, U.1),
              (reesAlgebra (I.ideal U)).subtype (e x) =
                Polynomial.monomial n
                  (@id (X.presheaf.obj (op U.1)) ((I ^ n).toModulesι.app U.1 x))) ∧
        (∀ (U : X.affineOpens) (F : reesAlgebra (I.ideal U)) (n : ℕ),
          (reesGradingEquivPow (I.ideal U) n
            ((DirectSum.decomposeAlgEquiv (reesGrading (I.ideal U)) F) n) :
              X.presheaf.obj (op U.1)) =
              (F : Polynomial (X.presheaf.obj (op U.1))).coeff n) ∧
        (∀ (U V : X.affineOpens) (h : U ≤ V) (F : reesAlgebra (I.ideal V)),
          (reesAlgebra (I.ideal U)).subtype (I.reesData.res h F) =
            (F : Polynomial (X.presheaf.obj (op V.1))).map
              (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom) ∧
        (∀ (U V : X.affineOpens) (h : U ≤ V)
            (a : SymmetricAlgebraSheaf.sections I.toModules (op V.1)),
          (reesAlgebra (I.ideal U)).subtype
            (q.app U (SymmetricAlgebraSheaf.restriction I.toModules
              (homOfLE (X := X.Opens) h).op a)) =
            ((reesAlgebra (I.ideal V)).subtype (q.app V a)).map
              (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom) ∧
        (∀ (f : ∀ U : X.affineOpens,
            SymmetricAlgebraSheaf.sections I.toModules (op U.1) →ₐ[(X.presheaf.obj (op U.1))]
              reesAlgebra (I.ideal U)),
          (∀ (U V : X.affineOpens) (h : U ≤ V)
              (a : SymmetricAlgebraSheaf.sections I.toModules (op V.1)),
            f U (SymmetricAlgebraSheaf.restriction I.toModules
              (homOfLE (X := X.Opens) h).op a) = I.reesData.res h (f V a)) →
          (∀ (U : X.affineOpens) (x : Γ(I.toModules, U.1)),
            (reesAlgebra (I.ideal U)).subtype
              (f U (SymmetricAlgebra.ι (X.presheaf.obj (op U.1))
                (I.toModules.val.obj (op U.1)) x)) =
                Polynomial.monomial 1 (@id (X.presheaf.obj (op U.1)) (I.toModulesι.app U.1 x))) →
          ∀ (U : X.affineOpens) (a : SymmetricAlgebraSheaf.sections I.toModules (op U.1)),
            f U a = q.app U a) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
