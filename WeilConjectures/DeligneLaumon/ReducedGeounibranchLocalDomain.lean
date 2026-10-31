/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.RingTheory.PointedEtaleEssentiallySmall

/-! # Reduced geometrically unibranch local rings are domains

Source: Stacks Project, `more-algebra.tex`, Tag 06DM, proof, paragraph beginning
“Assume (2)” (blueprint: lem-dl-a1-reduced-geounibranch-local-domain).

The theorem states that a reduced local ring whose strict henselization has
irreducible spectrum is an integral domain.  The strict henselization condition is
expressed using the project's pointed-etale colimit presentations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Transport the base ring while retaining the algebra universe. This is the same
-- equivalence used privately in `WeilConjectures.AlgebraicGeometry.NormalEtaleComponentsClopen`.
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

private theorem presentation_algebraMap_injective
    (A : Type u) (K H : Type (max u v)) [CommRing A] [IsLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} A K H) :
    Function.Injective (algebraMap A H) := by
  classical
  let R := ULift.{v} A
  let e : R ≃+* A := ULift.ringEquiv
  let : IsLocalRing R := e.symm.isLocalRing
  let E₀ := liftBase.{u, v} A
  let : Algebra R K := ULift.algebra' A K
  have : IsLocalHom e.toRingHom :=
    ⟨fun x hx ↦ hx.map e.symm.toMonoidHom⟩
  let eκ := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra (IsLocalRing.ResidueField R) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp eκ.toRingHom).toAlgebra
  have hsep : IsSepClosure (IsLocalRing.ResidueField R) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv eκ.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  let := hsep
  have htower : IsScalarTower R (IsLocalRing.ResidueField R) K := by
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
  have hc : IsColimit c := isColimitOfPreserves E₀.functor P.isColimit
  let cE := (Cocone.precompose d.hom).obj c
  have hcE : IsColimit cE := (IsColimit.precomposeHomEquiv d c).symm hc
  let c' := (Cocone.precompose (E.invFunIdAssoc D').inv).obj (cE.whisker E.inverse)
  have hc' : IsColimit c' :=
    (IsColimit.precomposeHomEquiv (E.invFunIdAssoc D').symm _).symm
      (hcE.whiskerEquivalence E.symm)
  let : Algebra R H := ULift.algebra' A H
  have hH : Algebra.IsStrictHenselization R K H :=
    ⟨c', ⟨hc'⟩, ⟨E₀.functor.mapIso P.identification⟩⟩
  obtain ⟨p, hp, a, hs, ι, ⟨hcι⟩, hι⟩ := hH.triples_presentation R K H
  let := a
  let := hs
  have hff := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
    (CommRingCat.of R) p hp K (CategoryTheory.Limits.Cocone.mk (CommRingCat.of H) ι)
    hcι (CommRingCat.ofHom (algebraMap R H)) hι
  have hinjR : Function.Injective (algebraMap R H) := hff.injective
  intro x y hxy
  have hlift : (ULift.up x : R) = ULift.up y := hinjR hxy
  exact congrArg ULift.down hlift

private theorem presentation_exists
    (A : Type u) (K : Type (max u v)) [CommRing A] [IsLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K] :
    ∃ H : CommAlgCat.{max u v} A,
      Nonempty (Algebra.StrictHenselizationPresentationIn.{u, v} A K H) := by
  classical
  let R := ULift.{v} A
  let e : R ≃+* A := ULift.ringEquiv
  let : IsLocalRing R := e.symm.isLocalRing
  let E₀ := liftBase.{u, v} A
  let : Algebra R K := ULift.algebra' A K
  have : IsLocalHom e.toRingHom :=
    ⟨fun x hx ↦ hx.map e.symm.toMonoidHom⟩
  let eκ := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra (IsLocalRing.ResidueField R) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp eκ.toRingHom).toAlgebra
  have hsep : IsSepClosure (IsLocalRing.ResidueField R) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv eκ.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  let := hsep
  have htower : IsScalarTower R (IsLocalRing.ResidueField R) K := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap A K r.down =
      algebraMap (IsLocalRing.ResidueField A) K
        (IsLocalRing.ResidueField.map e.toRingHom (IsLocalRing.residue R r))
    rw [IsLocalRing.ResidueField.map_residue]
    exact IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K r.down
  let E := pointedLift.{u, v} A K
  have : EssentiallySmall.{max u v} (ObjectProperty.FullSubcategory
      (fun S : Over ((liftBase.{u, v} A).functor.obj (CommAlgCat.of A K)) ↦
        Algebra.Etale R S.left)) := by
    change EssentiallySmall.{max u v} (ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of R K) ↦ Algebra.Etale R S.left))
    exact Algebra.pointedEtale_essentiallySmall R K
  let I := ObjectProperty.FullSubcategory
    (fun S : Over (CommAlgCat.of A K) ↦ Algebra.Etale A S.left)
  have : EssentiallySmall.{max u v} I := essentiallySmall_of_fully_faithful E.functor
  have : HasColimitsOfSize.{max u v, max u v} (CommAlgCat.{max u v} A) :=
    Adjunction.has_colimits_of_equivalence E₀.functor
  have : HasColimitsOfShape I (CommAlgCat.{max u v} A) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  let D := Algebra.strictHenselizationPointedDiagramIn.{u, v} A K
  exact ⟨colimit D, ⟨{
    cocone := colimit.cocone D
    isColimit := colimit.isColimit D
    identification := Iso.refl _ }⟩⟩

/-- A reduced local ring with geometrically unibranch strict henselizations is a domain.

Source: Stacks Project, `more-algebra.tex`, Tag 06DM, proof, paragraph beginning
“Assume (2)” (blueprint: lem-dl-a1-reduced-geounibranch-local-domain).

Proof:
1. Construct a residue separable closure in the common universe. Essential
   smallness of pointed-etale algebras gives their colimit, hence a presentation.
   The hypothesis makes its spectrum irreducible.
2. Transport the base to `ULift B`, so the base and algebras lie in one universe.
   Compare with the residue-triple colimit using
   `Algebra.IsStrictHenselization.triples_presentation`, and apply
   `strictHenselization_faithfullyFlat`. Its injectivity transfers back to `B`.
3. Irreducibility makes the colimit's nilradical prime. Its inverse image is zero:
   injectivity reflects nilpotence, and `B` is reduced. Thus zero is prime in `B`,
   which is precisely the domain criterion.
-/
theorem reduced_geounibranch_local_domain
    (B : Type u) [CommRing B] [IsLocalRing B] [IsReduced B]
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField B) K]
      [IsSepClosure (IsLocalRing.ResidueField B) K]
      [Algebra B K]
      [IsScalarTower B (IsLocalRing.ResidueField B) K]
      [CommRing H] [Algebra B H],
      Algebra.StrictHenselizationPresentationIn.{u, v} B K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    IsDomain B := by
  classical
  let Ω := AlgebraicClosure (ULift.{v} (IsLocalRing.ResidueField B))
  let : Algebra (IsLocalRing.ResidueField B) Ω :=
    ((algebraMap (ULift.{v} (IsLocalRing.ResidueField B)) Ω).comp
      ULift.ringEquiv.symm.toRingHom).toAlgebra
  let K := separableClosure (IsLocalRing.ResidueField B) Ω
  let : Algebra B K :=
    ((algebraMap (IsLocalRing.ResidueField B) K).comp (IsLocalRing.residue B)).toAlgebra
  have : IsScalarTower B (IsLocalRing.ResidueField B) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨H, ⟨P⟩⟩ := presentation_exists B K
  have hirr := hgeom K H P
  have hinj : Function.Injective (algebraMap B H) :=
    presentation_algebraMap_injective B K H P
  have : (nilradical H).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  have heq : Ideal.comap (algebraMap B H) (nilradical H) = (⊥ : Ideal B) := by
    ext b
    simp only [Ideal.mem_comap, mem_nilradical, Ideal.mem_bot,
      IsNilpotent.map_iff hinj, isNilpotent_iff_eq_zero]
  have : (⊥ : Ideal B).IsPrime := heq ▸ Ideal.IsPrime.comap (algebraMap B H)
  exact IsDomain.of_bot_isPrime B

end AlgebraicGeometry
