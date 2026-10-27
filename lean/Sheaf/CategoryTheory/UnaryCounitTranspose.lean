module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Unary counit substitution and comparison transpose

Source: blueprint `sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
coefficient comparisons preserving units and counits; the explicit categorical extraction
(blueprint: lem-pur-unary-counit-transpose).

The adjunctions retain the specified units and counits, and `Adjunction.homEquiv` is their
actual unit-defined transpose. Composition `≫` is written in diagrammatic order.
-/

@[expose] public section

universe vCs vDs vCt vDt uCs uDs uCt uDt

namespace CategoryTheory.Adjunction.UnaryCounitTranspose

variable {Cs : Type uCs} [Category.{vCs} Cs] {Ds : Type uDs} [Category.{vDs} Ds]
  {Ct : Type uCt} [Category.{vCt} Ct] {Dt : Type uDt} [Category.{vDt} Dt]
  {Rs : Cs ⥤ Ds} {Ls : Ds ⥤ Cs} {Rt : Ct ⥤ Dt} {Lt : Dt ⥤ Ct}
  {A : Ds ⥤ Dt} {Abar : Cs ⥤ Ct}

/-- The specified arrow `r_I = e_t R_t(d_I⁻¹)`.
Source: blueprint coefficient-comparison construction, unary counit substitution
(blueprint: lem-pur-unary-counit-transpose). -/
def restriction (adjT : Rt ⊣ Lt) (d : Rs ⋙ A ⋙ Lt ≅ Abar) (I : Cs) :
    Rt.obj (Abar.obj I) ⟶ A.obj (Rs.obj I) :=
  Rt.map (d.inv.app I) ≫ adjT.counit.app (A.obj (Rs.obj I))

/-- The comparison `a_A(M) = d_{L_s M} (L_t A(e_s,M))⁻¹`, where the counit is invertible.
Source: blueprint coefficient-comparison construction, inverse comparison
(blueprint: lem-pur-unary-counit-transpose). -/
noncomputable def comparison (adjS : Rs ⊣ Ls) (d : Rs ⋙ A ⋙ Lt ≅ Abar)
    (M : Ds) [IsIso (adjS.counit.app M)] : Lt.obj (A.obj M) ⟶ Abar.obj (Ls.obj M) :=
  inv (Lt.map (A.map (adjS.counit.app M))) ≫ d.hom.app (Ls.obj M)

/-- All unary counit-substitution, comparison-transpose and actual-unit identities.
Source: blueprint `sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
coefficient comparisons preserving units and counits; explicit categorical extraction
(blueprint: lem-pur-unary-counit-transpose).

Proof, following the node's nine elementary calculations using def-nagata-category:
1. Expand `b` by the unit formula for homEquiv. Counit naturality at q, followed by
   the Rs triangle identity, gives q = Rs(b) followed by the counit at M.
2. Apply unit naturality to d_I inverse, then the Lt triangle identity, to transpose r_I.
3. Expand q_A = r_I followed by A(q). Functoriality and step 2 give its transpose
   as d_I inverse followed by Lt A(q).
4. Substitute step 1, and move Rs(b) past d inverse by naturality of d at b.
   This gives the second factorization of the transpose.
5. If b and the counit at M are invertible, every factor in step 4 is invertible.
   Reverse the factors and cancel adjacent inverse pairs to obtain the asserted inverse.
6. Apply Lt A to counit naturality at an arbitrary f. Multiply by the inverses of
   the two mapped counits to obtain the inverse-factor identity; f need not be invertible.
7. Naturality of d at Ls(f), together with step 6, gives naturality of comparison.
8. The identity coefficient transposes to the actual unit by functoriality. The Ls
   triangle identity and invertibility of the counit give the unit on Ls(M).
9. Apply step 8 at Rs(K). Unit naturality at h gives the last displayed identity.
   Solving it for the unit at K writes that unit as a composite of isomorphisms.
All calculations take place in the given categories; no evaluation or faithfulness is used.
-/
theorem identities (adjS : Rs ⊣ Ls) (adjT : Rt ⊣ Lt) (d : Rs ⋙ A ⋙ Lt ≅ Abar) :
    (∀ (I : Cs) (M : Ds) (q : Rs.obj I ⟶ M),
      q = Rs.map (adjS.homEquiv I M q) ≫ adjS.counit.app M ∧
      adjT.unit.app (Abar.obj I) ≫ Lt.map (restriction adjT d I) = d.inv.app I ∧
      adjT.homEquiv (Abar.obj I) (A.obj M) (restriction adjT d I ≫ A.map q) =
        d.inv.app I ≫ Lt.map (A.map q) ∧
      adjT.homEquiv (Abar.obj I) (A.obj M) (restriction adjT d I ≫ A.map q) =
        Abar.map (adjS.homEquiv I M q) ≫ d.inv.app (Ls.obj M) ≫
          Lt.map (A.map (adjS.counit.app M)) ∧
      (∀ [IsIso (adjS.homEquiv I M q)] [IsIso (adjS.counit.app M)],
        ∃ (_ : IsIso
          (adjT.homEquiv (Abar.obj I) (A.obj M) (restriction adjT d I ≫ A.map q))),
          inv (adjT.homEquiv (Abar.obj I) (A.obj M)
            (restriction adjT d I ≫ A.map q)) =
              comparison adjS d M ≫ Abar.map (inv (adjS.homEquiv I M q)))) ∧
    (∀ (M M' : Ds) (f : M ⟶ M')
      [IsIso (adjS.counit.app M)] [IsIso (adjS.counit.app M')],
      Lt.map (A.map f) ≫ inv (Lt.map (A.map (adjS.counit.app M'))) =
        inv (Lt.map (A.map (adjS.counit.app M))) ≫
          Lt.map (A.map (Rs.map (Ls.map f))) ∧
      Lt.map (A.map f) ≫ comparison adjS d M' =
        comparison adjS d M ≫ Abar.map (Ls.map f)) ∧
    (∀ I : Cs, adjS.homEquiv I (Rs.obj I) (𝟙 (Rs.obj I)) = adjS.unit.app I) ∧
    (∀ (M : Ds) [IsIso (adjS.counit.app M)],
      adjS.unit.app (Ls.obj M) = inv (Ls.map (adjS.counit.app M))) ∧
    (∀ (K : Cs) (h : Ls.obj (Rs.obj K) ≅ K) [IsIso (adjS.counit.app (Rs.obj K))],
      IsIso (adjS.unit.app K) ∧
      h.hom ≫ adjS.unit.app K = adjS.unit.app (Ls.obj (Rs.obj K)) ≫ Ls.map (Rs.map h.hom)) := by
  have hunit (M : Ds) [IsIso (adjS.counit.app M)] :
      adjS.unit.app (Ls.obj M) = inv (Ls.map (adjS.counit.app M)) :=
    (comp_hom_eq_id _).1 (adjS.right_triangle_components M)
  refine ⟨?_, ?_, adjS.homEquiv_id, hunit, ?_⟩
  · intro I M q
    have hq : q = Rs.map (adjS.homEquiv I M q) ≫ adjS.counit.app M := by
      exact ((adjS.homEquiv I M).symm_apply_apply q).symm
    have hr : adjT.unit.app (Abar.obj I) ≫ Lt.map (restriction adjT d I) =
        d.inv.app I := by
      exact (adjT.unit_comp_map_eq_iff _ _).2 rfl
    have ht : adjT.homEquiv (Abar.obj I) (A.obj M)
        (restriction adjT d I ≫ A.map q) = d.inv.app I ≫ Lt.map (A.map q) := by
      rw [adjT.homEquiv_naturality_right, adjT.homEquiv_unit, hr]
    have hf : adjT.homEquiv (Abar.obj I) (A.obj M)
        (restriction adjT d I ≫ A.map q) =
          Abar.map (adjS.homEquiv I M q) ≫ d.inv.app (Ls.obj M) ≫
            Lt.map (A.map (adjS.counit.app M)) := by
      rw [ht]
      conv_lhs => rw [hq, A.map_comp, Lt.map_comp]
      rw [← Category.assoc]
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun f ↦ f ≫ Lt.map (A.map (adjS.counit.app M)))
          (d.inv.naturality (adjS.homEquiv I M q)).symm
    refine ⟨hq, hr, ht, hf, ?_⟩
    intro hb he
    have hi : IsIso (adjT.homEquiv (Abar.obj I) (A.obj M)
        (restriction adjT d I ≫ A.map q)) := by
      rw [hf]
      infer_instance
    refine ⟨hi, ?_⟩
    simp only [hf, IsIso.inv_comp, NatIso.inv_inv_app, ← Abar.map_inv, comparison,
      Category.assoc]
  · intro M M' f he he'
    have hn : Lt.map (A.map (Rs.map (Ls.map f))) ≫
        Lt.map (A.map (adjS.counit.app M')) =
          Lt.map (A.map (adjS.counit.app M)) ≫ Lt.map (A.map f) := by
      simpa only [Functor.comp_map, Functor.id_map, Functor.map_comp] using
        congrArg (fun g ↦ Lt.map (A.map g)) (adjS.counit.naturality f)
    have hinv : Lt.map (A.map f) ≫ inv (Lt.map (A.map (adjS.counit.app M'))) =
        inv (Lt.map (A.map (adjS.counit.app M))) ≫
          Lt.map (A.map (Rs.map (Ls.map f))) := by
      apply (IsIso.eq_inv_comp _).2
      rw [← Category.assoc, ← hn]
      simp
    refine ⟨hinv, ?_⟩
    dsimp only [comparison]
    rw [← Category.assoc, hinv, Category.assoc, Category.assoc]
    exact congrArg (fun g ↦ inv (Lt.map (A.map (adjS.counit.app M))) ≫ g)
      (d.hom.naturality (Ls.map f))
  · intro K h he
    have hn : h.hom ≫ adjS.unit.app K =
        adjS.unit.app (Ls.obj (Rs.obj K)) ≫ Ls.map (Rs.map h.hom) :=
      (adjS.unit_naturality h.hom).symm
    have hv : IsIso (adjS.unit.app (Ls.obj (Rs.obj K))) := by
      rw [hunit]
      infer_instance
    have hu : IsIso (adjS.unit.app K) := IsIso.of_isIso_fac_left hn
    exact ⟨hu, hn⟩

end CategoryTheory.Adjunction.UnaryCounitTranspose
