/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Normal schemes are geometrically unibranch

Source: Stacks Project, Properties, Tag 0BQ3, `lemma-normal-geometrically-unibranch`,
with More on Algebra, Tags 06DI and 06DM for the strict-henselization criterion
(blueprint: lem-dl-a1-normal-geometrically-unibranch).
-/

@[expose] public section

universe u v

open CategoryTheory

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false in
-- Changing the base to ULift puts all rings in the common algebra universe.
private def liftBase (A : Type u) [CommRing A] :
    CommAlgCat.{max u v} A ≌ CommAlgCat.{max u v} (ULift.{v} A) := by
  let F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} (ULift.{v} A) :=
    { obj := fun B ↦
        letI : Algebra (ULift.{v} A) B := ULift.algebra' A B
        CommAlgCat.of (ULift.{v} A) B
      map := fun {B C} f ↦ by
        letI : Algebra (ULift.{v} A) B := ULift.algebra' A B
        letI : Algebra (ULift.{v} A) C := ULift.algebra' A C
        exact CommAlgCat.ofHom
          { f.hom.toRingHom with commutes' := fun a ↦ f.hom.commutes a.down } }
  let G : CommAlgCat.{max u v} (ULift.{v} A) ⥤ CommAlgCat.{max u v} A :=
    { obj := fun B ↦
        letI : Algebra A B :=
          ((algebraMap (ULift.{v} A) B).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        CommAlgCat.of A B
      map := fun {B C} f ↦ by
        letI : Algebra A B :=
          ((algebraMap (ULift.{v} A) B).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        letI : Algebra A C :=
          ((algebraMap (ULift.{v} A) C).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.ofHom
          { f.hom.toRingHom with commutes' := fun a ↦ f.hom.commutes (ULift.up a) } }
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun B ↦ by
        apply CommAlgCat.isoMk
        exact @AlgEquiv.ofRingEquiv A B (G.obj (F.obj B)) _ _ _ B.algebra
          (G.obj (F.obj B)).algebra (RingEquiv.refl B) (fun _ ↦ rfl)) (by intros; ext; rfl)
      counitIso := NatIso.ofComponents (fun B ↦ by
        apply CommAlgCat.isoMk
        exact @AlgEquiv.ofRingEquiv (ULift.{v} A) (F.obj (G.obj B)) B _ _ _
          (F.obj (G.obj B)).algebra B.algebra (RingEquiv.refl B) (fun _ ↦ rfl))
        (by intros; ext; rfl) }

private lemma liftBase_etale (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    Algebra.Etale (ULift.{v} A) ((liftBase.{u, v} A).functor.obj B) ↔
      Algebra.Etale A B := by
  let : Algebra (ULift.{v} A) B := ULift.algebra' A B
  have : IsScalarTower A (ULift.{v} A) B := by
    constructor
    intro a b c
    change (a * b.down) • c = a • b.down • c
    exact mul_smul a b.down c
  have : Algebra.Etale A (ULift.{v} A) := Algebra.Etale.of_equiv ULift.algEquiv.symm
  constructor
  · intro h
    change Algebra.Etale (ULift.{v} A) B at h
    have := h
    exact Algebra.Etale.comp A (ULift.{v} A) B
  · intro h
    have := h
    exact Algebra.Etale.of_restrictScalars A (ULift.{v} A) B

private noncomputable def pointedLift (A : Type u) (K : Type (max u v))
    [CommRing A] [Field K] [Algebra A K] :
    let K' := (liftBase.{u, v} A).functor.obj (CommAlgCat.of A K)
    ObjectProperty.FullSubcategory (fun S : Over (CommAlgCat.of A K) ↦
      Algebra.Etale A S.left) ≌
    ObjectProperty.FullSubcategory (fun S : Over K' ↦ Algebra.Etale (ULift.{v} A) S.left) := by
  let E := Over.postEquiv (liftBase.{u, v} A) (X := CommAlgCat.of A K)
  let K' := (liftBase.{u, v} A).functor.obj (CommAlgCat.of A K)
  let Q : ObjectProperty (Over K') :=
    fun S ↦ Algebra.Etale (ULift.{v} A) S.left
  let : Q.IsClosedUnderIsomorphisms := ⟨fun {S T} i h ↦ by
    have : Algebra.Etale (ULift.{v} A) S.left := h
    change Algebra.Etale (ULift.{v} A) T.left
    let i' : S.left ≅ T.left := (Over.forget K').mapIso i
    exact Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso i')⟩
  exact E.congrFullSubcategory (Q := Q) (by
    ext S
    exact liftBase_etale A S.left)

-- Transport both the specified colimit and its residue separable-closure structure.
private theorem strictPresentation_domain
    (A : Type u) (K H : Type (max u v)) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} A K H) : IsDomain H := by
  classical
  let R := ULift.{v} A
  let e : R ≃+* A := ULift.ringEquiv
  let : IsLocalRing R := e.symm.isLocalRing
  let : IsDomain R := MulEquiv.isDomain _ e.toMulEquiv
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  let E₀ := liftBase.{u, v} A
  let : Algebra R K := ULift.algebra' A K
  have : IsLocalHom e.toRingHom :=
    ⟨fun x hx ↦ hx.map e.symm.toMonoidHom⟩
  let eκ := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra (IsLocalRing.ResidueField R) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp eκ.toRingHom).toAlgebra
  have : IsSepClosure (IsLocalRing.ResidueField R) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv eκ.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  have : IsScalarTower R (IsLocalRing.ResidueField R) K := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap A K r.down =
      algebraMap (IsLocalRing.ResidueField A) K
        (IsLocalRing.ResidueField.map e.toRingHom (IsLocalRing.residue R r))
    rw [IsLocalRing.ResidueField.map_residue]
    exact IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K r.down
  let E := pointedLift.{u, v} A K
  let D := Algebra.strictHenselizationPointedDiagramIn.{u, v} A K
  let D' := Algebra.strictHenselizationPointedDiagram R K
  let d : E.functor ⋙ D' ≅ D ⋙ E₀.functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let c := E₀.functor.mapCocone P.cocone
  let hc : IsColimit c := isColimitOfPreserves E₀.functor P.isColimit
  let cE := (Cocone.precompose d.hom).obj c
  let hcE : IsColimit cE := (IsColimit.precomposeHomEquiv d c).symm hc
  let c' := (Cocone.precompose (E.invFunIdAssoc D').inv).obj (cE.whisker E.inverse)
  let hc' : IsColimit c' :=
    (IsColimit.precomposeHomEquiv (E.invFunIdAssoc D').symm _).symm
      (hcE.whiskerEquivalence E.symm)
  let H' := E₀.functor.obj (CommAlgCat.of A H)
  let : Algebra R H := ULift.algebra' A H
  have hH : Algebra.IsStrictHenselization R K H :=
    ⟨c', ⟨hc'⟩, ⟨E₀.functor.mapIso P.identification⟩⟩
  obtain ⟨hloc, _⟩ := Algebra.strictHenselization_local_maximalIdeal R K H hH
  have := hloc
  obtain ⟨hsmall, hfilt⟩ := Algebra.pointedEtale_small_filtered R K
  let := hsmall
  let := hfilt
  let I := ObjectProperty.FullSubcategory
    (fun T : Over (CommAlgCat.of R K) ↦ Algebra.Etale R T.left)
  let S := CategoryTheory.equivSmallModel.{max u v} I
  let : IsFiltered (SmallModel.{max u v} I) := IsFiltered.of_equivalence S
  let B := S.inverse ⋙ D'
  let cb := c'.whisker S.inverse
  let hcb := hc'.whiskerEquivalence S.symm
  let : HasColimit B := ⟨⟨cb, hcb⟩⟩
  let i := (colimit.isColimit B).coconePointUniqueUpToIso hcb ≪≫
    E₀.functor.mapIso P.identification
  change IsLocalRing H at hloc
  let : IsLocalRing H := hloc
  let ei : ↥(colimit B) ≃+* H := (CommAlgCat.algEquivOfIso i).toRingEquiv
  let : IsLocalRing ↥(colimit B) := ei.symm.isLocalRing
  have hR (p : Ideal R) [p.IsPrime] :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
      p.primeCompl_le_nonZeroDivisors⟩
  have hB (j : SmallModel.{max u v} I) : Algebra.Etale R (B.obj j) :=
    (S.inverse.obj j).property
  obtain ⟨⟨hd, _⟩, _⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit R hR B hB
  let : IsDomain ↥(colimit B) := hd
  exact MulEquiv.isDomain _ ei.symm.toMulEquiv

namespace AlgebraicGeometry

/-- Every strict henselization of a local ring of a normal scheme has irreducible spectrum.
This is geometric unibranchness at every point, with no Noetherian hypothesis.

Source: Stacks Project, Properties, Tag 0BQ3, `lemma-normal-geometrically-unibranch`;
More on Algebra, Tags 06DI and 06DM
(blueprint: lem-dl-a1-normal-geometrically-unibranch).

Proof (the three steps of the DAG node):
1. Fix `x` and put `A = O_{X,x}`. The hypothesis says that `A` is a normal domain
   (`def-weil-pbc-normal-ring`). For every prime `q` of `A`, its complement excludes zero.
   The localization theorem for normal domains (`lem-weil-pbc-localization-normal-domain`)
   therefore makes `A_q` a normal domain. Thus `A` is also a normal ring in the sense of
   `def-weil-pbc-normal-ring` (Stacks Tag 00GV).
2. By `def-sc-ring-strict-henselization`, the specified strict henselization `H` is the
   colimit of the pointed etale `A`-algebras over the chosen separable residue closure `K`.
   The index category is essentially small and filtered by
   `lem-sc-pointed-etale-small-filtered`. Restrict to a small equivalent category,
   preserving the colimit. The ring `H` is local by
   `lem-sc-ring-strict-henselization-local-maximal-ideal`. Clause (a) of
   `lem-weil-pbc-etale-colimit-normal-local-domain` now makes `H` a normal domain,
   in particular a domain. These facts apply in any common algebra universe containing
   `A`: lift `A` to that universe, transport the pointed-etale diagram along the
   equivalence of base-algebra categories, and transport its universal cocone.
   This is the filtered-etale-colimit argument of Stacks Tag 06DI, also used in the
   case `A = A'` of Tag 06DM, (1) implies (2).
3. The zero ideal of the domain `H` is prime and is contained in every prime ideal.
   Its point therefore has closure all of `Spec H`. This spectrum is nonempty,
   and the closure of a point is irreducible. Thus `Spec H` is irreducible.
   Since `x` and the strict henselization were arbitrary, the claim holds at every
   point. For the empty scheme the assertion is vacuous.
-/
theorem normal_geometrically_unibranch (X : Scheme.{u})
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (x : X) (K H : Type (max u v)) [Field K]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [Algebra (X.presheaf.stalk x) K]
    [IsScalarTower (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
    [CommRing H] [Algebra (X.presheaf.stalk x) H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} (X.presheaf.stalk x) K H) :
    IrreducibleSpace (PrimeSpectrum H) := by
  let : IsDomain (X.presheaf.stalk x) := (hnormal x).1
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (hnormal x).2
  let : IsDomain H := strictPresentation_domain (X.presheaf.stalk x) K H P
  infer_instance

end AlgebraicGeometry
