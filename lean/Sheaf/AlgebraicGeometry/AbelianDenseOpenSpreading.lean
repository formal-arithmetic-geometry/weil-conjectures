/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.GenericGeometricallyConnectedSpread
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import WeilConjectures.AlgebraicGeometry.EventuallyProper

/-!
# Spreading an abelian variety over a dense open

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §1.4, paragraph before
Theorem 3 and its proof, printed pp. 19--20.
(blueprint: lem-sfb-abelian-dense-open-spreading)

Group schemes are group objects in the category of schemes over the base. The generic
fibre uses the existing group-object base-change functor, so its isomorphism with the
abelian variety preserves all group operations. The smooth proper commutative group
scheme with connected fibres in the conclusion is the abelian scheme of the source.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

set_option autoImplicit false

/-- An abelian variety over the fraction field of a Dedekind domain extends to an abelian
scheme over an open neighbourhood of the generic point.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §1.4, pp. 19--20, before and in
Theorem 3 (blueprint: lem-sfb-abelian-dense-open-spreading).

Proof: (1) Index the principal localizations of D by finite subsets of its nonzero
 elements. Their colimit is E by lem-weil-pbc-localization-colimit-principal-localizations,
 and their spectra have limit Spec E by lem-weil-pbc-limit-affine-transition. Each
 principal open contains the generic point. (2) Properness and smoothness make A finitely
 presented, so clause (1) of thm-pd-spreading-out descends its underlying scheme to a
 stage. (3) Products of this model remain finitely presented and qcqs by
 lem-weil-pbc-qcqs-morphism-permanence and
 lem-weil-pbc-finite-presentation-base-change-composition. Clause (2) of
 thm-pd-spreading-out descends multiplication, inverse and unit to a common later stage.
 (4) Clause (3) descends the six identities: associativity, the two unit identities,
 the two inverse identities, and commutativity (lem-sc-av-commutative). Taking a common
 later stage gives the commutative group model and a generic group isomorphism.
 (5) The generic fibre is geometrically integral by
 lem-sc-abelian-variety-characterization. By
 lem-sbc-generic-geometrically-connected-spread, shrink to a principal open with
 geometrically connected fibres. (6) On the cofinal tail,
 lem-weil-pbc-descend-smooth-qcqs gives eventual smoothness and
 lem-weil-pbc-eventually-proper gives properness at a later stage. These restrictions
 preserve the group structure and connected fibres. (7) That stage is the required
 nonempty open U, model B, and generic group isomorphism.

Mathlib's IsDedekindDomain permits dimension zero; the explicit dimension equality
retains the node's convention that a Dedekind domain has Krull dimension exactly one. -/
theorem exists_abelianScheme_denseOpen
    (D : Type u) [CommRing D] [IsDedekindDomain D] (_hD : ringKrullDim D = 1)
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (A : Over (Spec (CommRingCat.of E))) [GrpObj A] [IsAbelianVariety A] :
    ∃ U : (Spec (CommRingCat.of D)).Opens,
      (U : Set (Spec (CommRingCat.of D))).Nonempty ∧
      genericPoint (Spec (CommRingCat.of D)) ∈ U ∧
      ∃ (j : Spec (CommRingCat.of E) ⟶ U.toScheme),
        j ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap D E)) ∧
        ∃ B : Grp (Over U.toScheme),
          Smooth B.X.hom ∧ IsProper B.X.hom ∧ IsCommMonObj B.X ∧
          (∀ s : U.toScheme, ConnectedSpace (B.X.hom.fiber s)) ∧
          Nonempty (((Over.pullback j).mapGrp.obj B) ≅ Grp.mk A) := by
  sorry

end AlgebraicGeometry
