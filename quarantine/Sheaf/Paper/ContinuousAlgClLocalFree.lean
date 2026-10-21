/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.NoetherianSpace
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre

/-!
# Local finite freeness over the full continuous algebraic closure

Source: the local finite-presentation step in rational coefficient constructibility.
(blueprint: det-sf-comp-continuous-algcl-local-free).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
private theorem exists_finiteFree_cover_of_field_lfp
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P) := by
  classical
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj E) X
  obtain ⟨C, hC⟩ := hP
  choose n m f e using hC
  let A (i : C.I₀) := continuousFieldPresentationMatrix E (C.X i)
    (condensedFieldPullbackRealization E (C.f i)) (f i)
  let corank (i : C.I₀) (v : C.X i) : ℕ := n i - ((A i).map (fun a ↦ a v)).rank
  have hcompat (i j : C.I₀) (v : C.X i) (w : C.X j) (h : C.f i v = C.f j w) :
      corank i v = corank j w :=
    condensedField_presentation_corank_eq E X P C n m f (fun i ↦ (e i).some) i j v w h
  have hspec (i : C.I₀) {v w : C.X i} (h : v ⤳ w) : corank i v = corank i w := by
    have hA : (A i).map (fun a ↦ a v) = (A i).map (fun a ↦ a w) := by
      ext j k
      exact (h.map ((A i) j k).continuous).eq
    simp only [corank, hA]
  obtain ⟨d, hd, hdc⟩ := exists_locallyConstant_descent_of_specializes C.X C.f
    (fun i ↦ by
      have : WeaklyEtale (C.f i) :=
        Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
      infer_instance)
    (fun x ↦ by
      have hsurj := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
        (Scheme.propQCPrecoverage_le_precoverage _ C.mem₀)).1
      exact hsurj x)
    corank hcompat (fun i _ _ h ↦ hspec i h)
  have hr (i : C.I₀) : IsLocallyConstant (fun v : C.X i ↦
      ((A i).map (fun a ↦ a v)).rank) := by
    have hc : IsLocallyConstant (corank i) := by
      have he : corank i = d ∘ (C.f i) := funext fun v ↦ (hdc i v).symm
      rw [he]
      exact hd.comp_continuous (C.f i).continuous
    have he : (fun v : C.X i ↦ ((A i).map (fun a ↦ a v)).rank) =
        (fun r ↦ n i - r) ∘ corank i := by
      funext v
      exact (Nat.sub_sub_self (Matrix.rank_le_height _)).symm
    rw [he]
    exact hc.comp _
  have hlocal (i : C.I₀) : ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i),
      ∀ j : D.I₀, Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (D.f j)).obj
          ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R))
        (((upperStar AddCommGrpCat.{u + 1} (D.f j)).mapMod _).obj
          (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj P)) := by
    obtain ⟨D, hD⟩ := exists_finiteFree_cover_cokernel_of_locallyConstant_rank E (C.X i)
      _ (condensedFieldPullbackRealization E (C.f i)) (f i) (hr i)
    refine ⟨D, fun j ↦ free_of_iso (hD j) ?_⟩
    exact ((upperStar AddCommGrpCat.{u + 1} (D.f j)).mapMod _).mapIso (e i).some.symm
  choose D hD using hlocal
  refine ⟨C.bind D, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (free_pullback_comp_iff ((D i).f j) (C.f i) P).mpr (hD i j)


/-- Locally finitely presented full continuous algebraic-closure modules on a
topologically Noetherian scheme are locally finite free.

Source: the local finite-presentation step of rational coefficient constructibility,
Hemo--Richarz--Scholbach Example 3.1, and the proved rank-descent and Gaussian
elimination lemmas in CondensedFieldLfpLocalTriviality.
(blueprint: det-sf-comp-continuous-algcl-local-free).

Proof: use a finite presentation on a pro-etale cover. Specialization preserves
continuous field-valued entries, because the field is totally disconnected.
Consequently the corank is constant under specialization and compatible between
cover charts. The rank descent theorem makes it locally constant downstairs.
On this refinement Gaussian elimination with an invertible maximal minor gives
a finite free cokernel. Bind these refinements into a pro-etale cover and use
the given presentation isomorphisms. The argument applies to every totally
disconnected normed field, without finite-dimensionality. Apply it to a universe
lift of PadicAlgCl and transport along the continuous coefficient isomorphism.
Rank zero and the empty scheme use the same construction. -/
theorem continuousAlgCl_lf (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))
    (hM : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
        (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)).obj M) := by
  let E' := ULift.{u} (PadicAlgCl ℓ)
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro S a b
        apply ULift.ext
        change (a.down * b.down : C(S.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso (PadicAlgCl ℓ))
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (liftCoefficientIso (PadicAlgCl ℓ)).hom
  have : IsMonHom φ := inferInstance
  have : TotallyDisconnectedSpace (PadicAlgCl ℓ) := inferInstance
  have : TotallyDisconnectedSpace E' :=
    Homeomorph.ulift.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  have h := exists_finiteFree_cover_of_field_lfp E' X
    ((Mod.comap (inv φ)).obj M) (lfp_comap (inv φ) hM)
  exact locally_free_of_iso (locally_free_comap φ h)
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app M)


end AlgebraicGeometry.ProEtale
