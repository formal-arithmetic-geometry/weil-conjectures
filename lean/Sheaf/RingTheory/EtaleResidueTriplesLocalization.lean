/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Localization properties of the pointed etale colimit

Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), second and third
paragraphs of its proof, applied to triples as in Tag 04GP (lemma-strict-henselization).
(blueprint: lem-weil-pbc-etale-triples-colimit-localization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), second and third
paragraphs of its proof, applied to triples as in Tag 04GP (lemma-strict-henselization).

Proof: Every colimit element x is represented by f at a triple (S,q,φ). If ψ(x) ≠ 0,
then f is outside q. The principal localization S_f remains etale over R and its map
to K extends because the image of f is a unit. Thus it is a later triple, and the image
of 1/f makes x a unit in the colimit. Conversely a unit cannot map to zero in a field.
The structural map R → K kills p, giving pC ⊆ ker ψ. If ψ(x)=0, its representative
f lies in q. Etaleness implies pS_q=qS_q. Clear denominators to find u outside q with
uf in pS. The later triple S_u represents x by an element of pS_u, so x lies in pC.
These two inclusions prove the equality of ideals. The zero ring cannot be the colimit,
since the compatible map to K is unital.
(blueprint: lem-weil-pbc-etale-triples-colimit-localization). -/
theorem etaleResidueTriples_colimit_localization
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ρ : R ⟶ c.pt)
    (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    (∀ x : c.pt, ψ x ≠ 0 → IsUnit x) ∧
      RingHom.ker ψ = p.asIdeal.map ρ.hom := by
  sorry

end AlgebraicGeometry.Scheme
