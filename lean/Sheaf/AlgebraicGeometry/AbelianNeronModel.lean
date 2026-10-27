module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic

/-! # Finite-type Néron models of abelian varieties

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, 1.3 Corollary 2 and 1.4 Theorem 3,
printed pages 16 and 19; 1.2 Proposition 6 for the group structure.
(blueprint: lem-sfb-abelian-neron-model)

The generic-fibre identification is an isomorphism of group objects. The mapping property
uses morphisms of schemes over the base, with no group structure on the smooth test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An abelian variety over the fraction field of a dimension-one Dedekind domain has a
smooth separated commutative finite-type Néron model, with the full mapping property.
No excellence, completeness or perfection hypothesis is imposed.

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, 1.3 Corollary 2 and 1.4 Theorem 3,
printed pages 16 and 19; 1.2 Proposition 6, printed page 14, for group structures.
(blueprint: lem-sfb-abelian-neron-model)

Proof plan from the accepted DAG split:
1. At every closed point, lem-sc-dedekind-localization-dvr gives a DVR. Its strict
   henselization (def-weil-pbc-strict-henselization-limit) is a DVR by
   lem-sc-strict-henselization-dvr. Embed the abelian variety in projective space using
   lem-sc-abelian-variety-projective. Assign each fraction-field point to a coordinate
   of minimal valuation. Every coordinate ratio in that chart has nonnegative valuation,
   so lem-sfb-bounded-group-local-neron-criterion supplies its local finite-type model.
2. Use lem-sfb-abelian-dense-open-spreading to spread to an abelian scheme on a nonempty
   open. The lemma lem-sfb-abelian-scheme-neron-property gives its mapping property;
   def-weil-proper-morphism gives separatedness and finite type.
3. The complement consists of closed points and is finite by
   lem-sc-noetherian-closed-points-finite. Glue the local models and the open model by
   lem-sfb-neron-finite-complement-patching. This includes an empty complement and the
   mapping property for all smooth test schemes, even those not quasi-compact.
4. Extend multiplication, inverse and unit by the mapping property, using the smooth
   test schemes G × G, G and S. Smoothness of products follows from
   lem-weil-pbc-smooth-ring-map-base-change-composition and def-sbc-smooth-morphisms.
   Uniqueness proves every group diagram. Commutativity follows in the same way from
   lem-sc-av-commutative. The generic identification is therefore a group isomorphism. -/
theorem exists_abelian_neron_model
    (D : Type u) [CommRing D] [IsDedekindDomain D] (hD : ringKrullDim D = 1)
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (A : Over (Spec (.of E))) [GrpObj A] [IsAbelianVariety A] :
    ∃ G : Grp (Over (Spec (.of D))),
      IsCommMonObj G.X ∧ Smooth G.X.hom ∧ IsSeparated G.X.hom ∧
      LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
      ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.obj G ≅
          Grp.mk A,
        ∀ (X : Over (Spec (.of D))), Smooth X.hom →
          Function.Bijective (fun f : X ⟶ G.X ↦
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map f ≫
              (Grp.forget (Over (Spec (.of E)))).map e.hom) := by
  sorry

end AlgebraicGeometry
