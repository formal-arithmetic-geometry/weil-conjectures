/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.AlgebraicGeometry.GeometricTriplesComparisonMaps
import Sheaf.AlgebraicGeometry.GeometricTriplesDiagramComparison
import Sheaf.AlgebraicGeometry.GeometricTriplesAlgebraRecognition

/-! # Geometric neighbourhoods and residue-triple colimits

Source: Stacks Project, Tags 04HX, 08HR and 08HT
(blueprint: lem-wf-geometric-triples-colimit-comparison).

The auxiliary definitions only spell out the canonical maps in the comparison.
Quantification over small representative equivalences expresses independence of representatives.
-/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Recognition of any henselian local ind-etale algebra with the specified residue closure,
and the unique geometric/residue-triple comparison.
Source: Stacks Project, Tags 04HX, 08HR, 08HT, 09GT and 09GS
(blueprint: lem-wf-geometric-triples-colimit-comparison).

Proof:
1. A separable element over k is separable over K by tower_top. The intermediate
   separable closure of the separably closed K is bottom, so the element lies in K.
   Conversely separability of K/k maps through the scalar tower.
2. geometric_triples_diagram_comparison supplies residue containment, representing
   triples, the maps b and g, their coprojection equations, and uniqueness of g.
3. Set rho = b followed by inverse g. geometric_triples_algebra_recognition gives
   e : C ~= c.pt preserving rho and q, with uniqueness of inverse maps.
4. Compose e with g to obtain i. Its base and evaluation equations follow from
   those for e and g. For any competing i', use colimit.hom_ext on the geometric
   coprojections and cancel the injection K -> Omega to identify q i' inverse g
   with qA. The inverse composite also preserves A, so algebraic recognition
   uniqueness gives i' inverse g = e inverse. Surjectivity of g implies i' = i.
   Cancellation with inverse g also gives q i inverse g = qA.
5. Choose Mathlib's AlgebraicClosure K. Every representative category is covered
   by step 2, so all the preceding conclusions hold for each one.
-/
theorem geometric_triples_colimit_comparison
    (A : CommRingCat.{u}) [IsLocalRing A]
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra (IsLocalRing.ResidueField A) Ω]
    [IsScalarTower (IsLocalRing.ResidueField A) K Ω]
    (C : Type v) [CommRing C] [HenselianLocalRing C] [Algebra A C]
    [IsLocalHom (algebraMap A C)]
    (hC : RingHom.IndEtaleAcrossUniverses (algebraMap A C))
    (q : C →+* K) (hq : Function.Surjective q)
    (hker : RingHom.ker q = IsLocalRing.maximalIdeal C)
    (hqa : q.comp (algebraMap A C) = (geometricTriplesBaseResidue A K).hom) :
    (∀ z : Ω, z ∈ separableClosure (IsLocalRing.ResidueField A) Ω ↔
      z ∈ Set.range (algebraMap K Ω)) ∧
    (∀ (n : strictHenselizationNeighbourhoods (geometricTriplesPoint A K Ω))
      (z : ((AffineEtale.Spec (Spec A)).obj n.1).left.residueField
        (SpecToEquivOfField Ω _ n.2.left).1),
      (SpecToEquivOfField Ω _ n.2.left).2 z ∈ Set.range (algebraMap K Ω)) ∧
    (∀ (J : Type u) [SmallCategory J]
      (r : J ⥤ strictHenselizationNeighbourhoods (geometricTriplesPoint A K Ω))
      [r.IsEquivalence]
      (c : Cocone (etaleResidueTriplesRingDiagram A (geometricTriplesResiduePoint A K).1 K
        (geometricTriplesResiduePoint A K).2)) (_hc : IsColimit c)
      (qA : c.pt ⟶ .of K)
      (_hqA : ∀ t, c.ι.app t ≫ qA = geometricTriplesTripleResidue t),
      (∀ j : J, ∃ (t : EtaleResidueTriple A (geometricTriplesResiduePoint A K).1 K
        (geometricTriplesResiduePoint A K).2)
        (hB : t.B = (strictHenselizationCoordinateRings
          (geometricTriplesPoint A K Ω)).obj (op (r.obj j))),
        GeometricTriplesRepresents (r.obj j) t hB) ∧
      ∃ b : A ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
          (geometricTriplesPoint A K Ω)),
        (∀ j : J, geometricTriplesChart (r.obj j) ≫
          colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
            (geometricTriplesPoint A K Ω)) (op j) = b) ∧
        ∃ i : C ≃+* ↥(colimit (r.op ⋙ strictHenselizationCoordinateRings
            (geometricTriplesPoint A K Ω)) : CommRingCat.{u}),
          (i.toRingHom.comp (algebraMap A C) = b.hom ∧
            ∀ j : J, (algebraMap K Ω).comp (q.comp (i.symm.toRingHom.comp
              (colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
                (geometricTriplesPoint A K Ω)) (op j)).hom)) =
                  (geometricTriplesEvaluation (r.obj j)).hom) ∧
          (∀ i' : C ≃+* ↥(colimit (r.op ⋙ strictHenselizationCoordinateRings
              (geometricTriplesPoint A K Ω)) : CommRingCat.{u}),
            (i'.toRingHom.comp (algebraMap A C) = b.hom ∧
              ∀ j : J, (algebraMap K Ω).comp (q.comp (i'.symm.toRingHom.comp
                (colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
                  (geometricTriplesPoint A K Ω)) (op j)).hom)) =
                    (geometricTriplesEvaluation (r.obj j)).hom) →
            i' = i) ∧
          ∃ g : c.pt ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
              (geometricTriplesPoint A K Ω)),
            GeometricTriplesCoprojections r c g ∧ IsIso g ∧
            (∀ t, t.α ≫ c.ι.app t ≫ g = b) ∧
            q.comp (i.symm.toRingHom.comp g.hom) = qA.hom ∧
            ∀ g' : c.pt ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
                (geometricTriplesPoint A K Ω)),
              GeometricTriplesCoprojections r c g' → g' = g) ∧
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L), IsAlgClosure K L) := by
  classical
  have hsep (z : Ω) :
      z ∈ separableClosure (IsLocalRing.ResidueField A) Ω ↔
        z ∈ Set.range (algebraMap K Ω) := by
    have : IsSepClosed K := IsSepClosure.sep_closed (IsLocalRing.ResidueField A)
    constructor
    · intro hz
      have hz' : z ∈ separableClosure K Ω :=
        mem_separableClosure_iff.mpr ((mem_separableClosure_iff.mp hz).tower_top K)
      have hb := IntermediateField.eq_bot_of_isSepClosed_of_isSeparable
        (separableClosure K Ω)
      exact IntermediateField.mem_bot.mp (hb ▸ hz')
    · rintro ⟨y, rfl⟩
      apply mem_separableClosure_iff.mpr
      exact (Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField A) y).map
        (IsScalarTower.toAlgHom (IsLocalRing.ResidueField A) K Ω)
        (RingHom.injective _)
  obtain ⟨hres, hdiag⟩ := geometric_triples_diagram_comparison A K Ω hsep
  refine ⟨hsep, hres, ?_, ?_⟩
  · intro J _ r _ c hc qA hqA
    obtain ⟨ht, b, hb, g, hg, hgi, hgb, hgev, hgu⟩ := hdiag J r c hc qA hqA
    have : IsIso g := hgi
    let ρ : A ⟶ c.pt := b ≫ inv g
    have hρ (t) : t.α ≫ c.ι.app t = ρ := by
      dsimp [ρ]
      rw [← hgb t]
      simp
    obtain ⟨e, heA, heq, heu⟩ :=
      geometric_triples_algebra_recognition A K C hC q hq hker hqa c hc qA hqA ρ hρ
    let G := (asIso g).commRingCatIsoToRingEquiv
    let i := e.trans G
    have hρg (a : A) : g.hom (ρ.hom a) = b.hom a := by
      have h := congrArg (fun f : A ⟶ _ ↦ f.hom a)
        (show ρ ≫ g = b by simp [ρ])
      exact h
    have hiA : i.toRingHom.comp (algebraMap A C) = b.hom := by
      ext a
      change G (e (algebraMap A C a)) = b.hom a
      rw [show e (algebraMap A C a) = ρ.hom a from DFunLike.congr_fun heA a]
      exact hρg a
    have hiq (y) : q (i.symm y) = qA.hom ((inv g).hom y) := by
      change q (e.symm (G.symm y)) = _
      exact DFunLike.congr_fun heq (G.symm y)
    have hiEv (j : J) : (algebraMap K Ω).comp (q.comp (i.symm.toRingHom.comp
        (colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
          (geometricTriplesPoint A K Ω)) (op j)).hom)) =
            (geometricTriplesEvaluation (r.obj j)).hom := by
      ext x
      exact (congrArg (algebraMap K Ω) (hiq _)).trans (DFunLike.congr_fun (hgev j) x)
    refine ⟨ht, b, hb, i, ⟨hiA, hiEv⟩, ?_, g, hg, hgi, hgb, ?_, hgu⟩
    · intro i' hi'
      let f : c.pt →+* C := i'.symm.toRingHom.comp g.hom
      have hfA : f.comp ρ.hom = algebraMap A C := by
        ext a
        apply i'.injective
        change i' (i'.symm (g.hom (ρ.hom a))) = i' (algebraMap A C a)
        rw [i'.apply_symm_apply, hρg]
        exact (DFunLike.congr_fun hi'.1 a).symm
      have hpt : CommRingCat.ofHom ((algebraMap K Ω).comp
          (q.comp i'.symm.toRingHom)) = inv g ≫ qA ≫
            CommRingCat.ofHom (algebraMap K Ω) := by
        apply colimit.hom_ext
        intro j
        apply CommRingCat.hom_ext
        obtain ⟨j⟩ := j
        exact (hi'.2 j).trans (hgev j).symm
      have hfq : q.comp f = qA.hom := by
        ext x
        apply (algebraMap K Ω).injective
        have h := congrArg (fun a ↦ a.hom (g.hom x)) hpt
        simpa only [f, CommRingCat.hom_ofHom, CommRingCat.hom_comp,
          RingHom.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id_apply] using h
      have hf := heu f hfA hfq
      have hsymm (y) : i'.symm y = i.symm y := by
        obtain ⟨x, rfl⟩ := G.surjective y
        change i'.symm (G x) = e.symm (G.symm (G x))
        rw [G.symm_apply_apply]
        exact DFunLike.congr_fun hf x
      ext x
      apply i'.symm.injective
      rw [i'.symm_apply_apply, hsymm, i.symm_apply_apply]
    · ext x
      change q (e.symm (G.symm (G x))) = qA.hom x
      rw [G.symm_apply_apply]
      exact DFunLike.congr_fun heq x
  · exact ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
