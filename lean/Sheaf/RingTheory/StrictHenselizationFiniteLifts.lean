/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits

import Sheaf.RingTheory.HenselianFiniteEtaleFieldLift
import Mathlib.RingTheory.Ideal.GoingUp
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective
import WeilConjectures.RingTheory.FiniteLocalHenselian
import Sheaf.RingTheory.FilteredColimitHenselianPair
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.EtaleResidueTriplesStrictHenselization
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import Mathlib.FieldTheory.SeparableClosure
import WeilConjectures.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Strict henselization from finite local lifts

Source: Stacks Project, Algebra, Remark 0BSL; geometric comparison: Tag 04HX;
finite Galois cofinality: Tags 09DT and 0EXM
(blueprint: lem-wf-strict-henselization-finite-lifts).

The auxiliary structure bundles the finite lifts, their specified residue identifications,
and the unique compatible arrows. It chooses no algebra from an existence theorem.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Algebra

/-- The finite residue subextensions indexing Remark 0BSL. Separability follows from
`IsSepClosure`; the trivial subextension is included.
Source: Stacks Project, Tag 0BSL (blueprint: lem-wf-strict-henselization-finite-lifts). -/
abbrev finiteResidueLiftIndex (H K : Type u) [CommRing H] [IsLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField H) K] :=
  {e : IntermediateField (IsLocalRing.ResidueField H) K //
    FiniteDimensional (IsLocalRing.ResidueField H) e}

/-- The geometric point through the specified residue closure, allowing imperfect residues.
Source: Stacks Project, Tag 04HX (blueprint: lem-wf-strict-henselization-finite-lifts). -/
noncomputable def finiteResidueLiftPoint (A K Ω : Type u) [CommRing A] [Field K] [Field Ω]
    [Algebra A K] [Algebra K Ω] : Spec (.of Ω) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom ((algebraMap K Ω).comp (algebraMap A K)))

/-- The affine pointed chart represented by an object of the small index category.
Source: Stacks Project, Tag 04HX (blueprint: lem-wf-strict-henselization-finite-lifts). -/
noncomputable def finiteResidueLiftChart {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (j : (SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))ᵒᵖ) :
    Scheme.AffinePointedEtaleNeighborhood s :=
  (Scheme.strictHenselizationAffineInclusion s).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop)

/-- The canonical coprojection from a small affine pointed chart to the recorded ring.
The existing representative-comparison isomorphism fixes the comparison of colimit choices.
Source: Stacks Project, Tag 04HX (blueprint: lem-wf-strict-henselization-finite-lifts). -/
noncomputable def finiteResidueLiftChartMap {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (j : (SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))ᵒᵖ) :
    (Scheme.smallStrictHenselizationDiagram s).obj j ⟶ Scheme.strictHenselizationRing s :=
  colimit.ι (Scheme.smallStrictHenselizationDiagram s) j ≫
    (Scheme.strictHenselizationRepresentativeIso s CategoryTheory.Equivalence.refl
      (Scheme.smallStrictHenselizationDiagram s) (Iso.refl _)).hom

/-- The system of finite local etale lifts with specified residue identifications.
A surjective residue map with kernel `m_H B_e` specifies exactly an isomorphism
`B_e / m_H B_e ≃ e`. The scalar equation makes it an identification over the residue
field of `H`. Unique compatible isomorphisms and arrows are included as explicit fields.
Source: Stacks Project, Tag 0BSL and Tag 04GK
(blueprint: lem-wf-strict-henselization-finite-lifts). -/
structure StrictHenselizationFiniteLiftSystem (H K : Type u) [CommRing H]
    [HenselianLocalRing H] [Field K] [Algebra (IsLocalRing.ResidueField H) K] where
  /-- The actual diagram of algebras and transition maps. -/
  diagram : finiteResidueLiftIndex H K ⥤ CommAlgCat.{u} H
  /-- Each lift is local. -/
  localRing : ∀ e, IsLocalRing (diagram.obj e)
  /-- Each lift is finite as a module. -/
  finite : ∀ e, Module.Finite H (diagram.obj e)
  /-- Each lift is etale. -/
  etale : ∀ e, Algebra.Etale H (diagram.obj e)
  /-- The specified quotient map to the indexed field. -/
  residue : ∀ e, diagram.obj e →+* e.val
  /-- The residue map is onto. -/
  residue_surjective : ∀ e, Function.Surjective (residue e)
  /-- Its kernel is the extended maximal ideal of the base. -/
  residue_ker : ∀ e, RingHom.ker (residue e) =
    (IsLocalRing.maximalIdeal H).map (algebraMap H (diagram.obj e))
  /-- It induces the specified residue-field extension. -/
  residue_scalar : ∀ e h, residue e (algebraMap H (diagram.obj e) h) =
    algebraMap (IsLocalRing.ResidueField H) e.val (IsLocalRing.residue H h)
  /-- Every transition is local. -/
  map_local : ∀ {e f} (t : e ⟶ f), IsLocalHom (diagram.map t).hom.toRingHom
  /-- Every transition induces the given inclusion inside the fixed closure. -/
  map_residue : ∀ {e f} (t : e ⟶ f) b,
    (residue f ((diagram.map t).hom b) : K) = (residue e b : K)
  /-- The transition is the unique local lift of that residue inclusion. -/
  map_unique : ∀ {e f} (t : e ⟶ f) (g : diagram.obj e →ₐ[H] diagram.obj f),
    IsLocalHom g.toRingHom →
    (∀ b, (residue f (g b) : K) = (residue e b : K)) → g = (diagram.map t).hom
  /-- Any other lift with its residue identification has a unique compatible isomorphism. -/
  lift_unique : ∀ e (T : Type u) [CommRing T] [IsLocalRing T] [Algebra H T],
    Module.Finite H T → Algebra.Etale H T → ∀ q : T →+* e.val,
    Function.Surjective q →
    RingHom.ker q = (IsLocalRing.maximalIdeal H).map (algebraMap H T) →
    (∀ h, q (algebraMap H T h) =
      algebraMap (IsLocalRing.ResidueField H) e.val (IsLocalRing.residue H h)) →
    ∃! i : diagram.obj e ≃ₐ[H] T, ∀ b, q (i b) = residue e b

/-- Strict henselization is the local filtered colimit of the finite local residue lifts.
The presentations over `A` and `H` specify the canonical residue-compatible algebra
comparisons, rather than an arbitrary ring isomorphism. The geometric comparison is
uniquely characterized by its structural map and its maps from every pointed chart.

Source: Stacks Project, Remark 0BSL, Tag 04HX, and Tags 09DT/0EXM
(blueprint: lem-wf-strict-henselization-finite-lifts).

Proof:
1. Lift every finite separable residue extension using
`lem-weil-pbc-henselian-finite-etale-field-lift`. The finite-algebra radical lemma
`lem-weil-pbc-finite-algebra-local-radical` shows that its field quotient is its unique
maximal quotient, so the lift is local.
2. Full faithfulness `lem-weil-pbc-henselian-finite-etale-map-bijective` lifts inclusions
uniquely. Their residue injections make the lifts local. Uniqueness gives the functor
laws and unique residue-compatible isomorphisms. Finite subfields form a directed poset.
3. Take the algebra colimit (`lem-weil-pbc-commutative-algebras-colimits-exist`). The
pointings give its residue map. By `lem-weil-pbc-filtered-colimit-algebras-elementwise`
every element comes from a stage. The residue map is onto since every element of the
closure lies in a finite subfield; its kernel is the union of the stage maximal ideals.
Every element outside that kernel is a unit already at its stage, proving locality.
4. Each stage is henselian by `lem-weil-pbc-finite-local-henselian`; apply
`lem-weil-pbc-filtered-colimit-henselian-pair` to their maximal ideals. The colimit is
strictly henselian since its residue field is the chosen separable closure.
5. The colimit is ind-etale over `H`; `lem-trf-henselization-prime-ind-etale` and
`lem-weil-pbc-ind-etale-stability` make it ind-etale over `A`.
6. Compare with the etale triple colimit using `lem-weil-pbc-strict-henselization-triples`
and `lem-sc-etale-triples-colimit-is-strict-henselization`. Apply
`lem-weil-pbc-map-into-henselian-colimit` in both directions with residue identity;
uniqueness makes the composites identities. Repeat over `H`. The henselization universal
property identifies the two `H` structures.
7. Embed the closure in an algebraically closed field. Its relative separable closure
of the base residue field is the original closure, including for imperfect fields.
Etale residue fields are finite separable, so their pointings land in that closure.
Use `lem-weil-pbc-etale-chart-residue-triples-equivalence` to identify ring diagrams and
structural/residue maps; their colimits agree by the universal property.
8. The normal closure of each finite residue subextension is finite Galois inside the
separable closure (`lem-weil-pbc-separable-closure-exists-galois` and
`lem-weil-pbc-finite-set-in-finite-galois-subextension`). A common Galois overfield shows
that extending a cocone along these inclusions is independent of choices. Restriction
and extension of cocones are inverse, so the restricted cocone is still a colimit. -/
theorem strictHenselization_finite_lifts
    (A H K : Type u) [CommRing A] [IsLocalRing A] [CommRing H]
    [HenselianLocalRing H] [Algebra A H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H)
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K]
    [Algebra H K] [IsScalarTower H (IsLocalRing.ResidueField H) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [IsScalarTower A H K] :
    ∃ D : StrictHenselizationFiniteLiftSystem H K,
      IsFiltered (finiteResidueLiftIndex H K) ∧
      ∃ c : Cocone D.diagram, Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((forget₂ (CommAlgCat H) CommRingCat).mapCocone c)) ∧
        ∃ (_ : IsLocalRing c.pt) (_ : Algebra A c.pt) (_ : IsScalarTower A H c.pt)
          (q : c.pt →+* K),
          Function.Surjective q ∧ RingHom.ker q = IsLocalRing.maximalIdeal c.pt ∧
          (∀ e b, q ((c.ι.app e).hom b) = (D.residue e b : K)) ∧
          (∃ P : StrictHenselizationPresentationIn.{u, u} A K c.pt, P.residueMap = q) ∧
          (∃ P : StrictHenselizationPresentationIn.{u, u} H K c.pt, P.residueMap = q) ∧
          IsFiltered (ObjectProperty.FullSubcategory
            (fun e : finiteResidueLiftIndex H K ↦
              Normal (IsLocalRing.ResidueField H) e.val)) ∧
          Nonempty (IsColimit (c.whisker (ObjectProperty.ι
            (fun e : finiteResidueLiftIndex H K ↦
              Normal (IsLocalRing.ResidueField H) e.val)))) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω],
            ∃! i : c.pt ≃+* Scheme.strictHenselizationRing (finiteResidueLiftPoint A K Ω),
              ∀ j : (SmallModel.{u}
                  (Scheme.strictHenselizationNeighbourhoods (finiteResidueLiftPoint A K Ω)))ᵒᵖ,
                i.toRingHom.comp (algebraMap A c.pt) =
                  ((Scheme.ΓSpecIso (.of A)).inv ≫
                    (finiteResidueLiftChart (finiteResidueLiftPoint A K Ω) j).obj.fst.hom.appTop ≫
                    finiteResidueLiftChartMap (finiteResidueLiftPoint A K Ω) j).hom ∧
                ((algebraMap K Ω).comp (q.comp i.symm.toRingHom)).comp
                    (finiteResidueLiftChartMap (finiteResidueLiftPoint A K Ω) j).hom =
                  ((finiteResidueLiftChart (finiteResidueLiftPoint A K Ω) j).obj.snd.left.appTop ≫
                    (Scheme.ΓSpecIso (.of Ω)).hom).hom := by
  sorry

end Algebra
