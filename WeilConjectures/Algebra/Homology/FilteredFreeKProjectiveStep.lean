/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Split extensions by shifted free complexes

## References

* Stacks Project, Differential Graded Algebra, Tags 09KJ and 09KM
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A single free module is bounded above and projective in every degree. -/
private theorem single_projective {A : Type u} [CommRing A] (d : ℤ) :
    IsKProjective ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) d).obj
      (ModuleCat.of A (ULift.{v} A))) := by
  have (n : ℤ) : Projective
      (((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) d).obj
        (ModuleCat.of A (ULift.{v} A))).X n) := by
    by_cases h : n = d
    · subst n
      rw [HomologicalComplex.single_obj_X_self]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).projective
  exact isKProjective_of_projective _ d

/-- Assemble component homotopies using the degreewise coproduct universal property. -/
private theorem coproduct_projective {C : Type*} [Category* C] [Abelian C]
    {I : Type*} (F : I → CochainComplex C ℤ) [HasCoproduct F]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (HomologicalComplex.eval C (.up ℤ) n)]
    [∀ i, (F i).IsKProjective] : (∐ F).IsKProjective := by
  classical
  constructor
  intro N g hN
  let h (i : I) := IsKProjective.homotopyZero (Sigma.ι F i ≫ g) hN
  let c (n : ℤ) := Cofan.mk ((∐ F).X n) (fun i ↦ (Sigma.ι F i).f n)
  let hc (n : ℤ) : IsColimit (c n) :=
    (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval C (.up ℤ) n) F
      (Cofan.mk (∐ F) (Sigma.ι F))).1
        (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n)
          (coproductIsCoproduct F))
  let H (n m : ℤ) : (∐ F).X n ⟶ N.X m :=
    (hc n).desc (Cofan.mk _ (fun i ↦ (h i).hom n m))
  have fac (i : I) (n m : ℤ) : (Sigma.ι F i).f n ≫ H n m = (h i).hom n m :=
    (hc n).fac _ ⟨i⟩
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    intro i
    change (Sigma.ι F i.as).f n ≫ H n m = _
    rw [fac, (h i.as).zero n m hnm, comp_zero]
  · intro n
    apply (hc n).hom_ext
    intro i
    change (Sigma.ι F i.as).f n ≫ g.f n =
      (Sigma.ι F i.as).f n ≫ (dNext n H + prevD n H + (0 : (∐ F) ⟶ N).f n)
    simp only [Preadditive.comp_add, HomologicalComplex.zero_f, add_zero,
      dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι F i.as).comm_assoc, fac,
      ← Category.assoc ((Sigma.ι F i.as).f n) (H n _) _, fac]
    simpa [h, dNext, prevD] using (h i.as).comm n

/-- A degreewise split extension of a K-projective complex by shifted free complexes
is K-projective.
-/
theorem isKProjective_of_filtered_free_step {A : Type u} [CommRing A]
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ L) (hprev : K.IsKProjective)
    (hsplit : ∀ k : ℤ, ∃ r : L.X k ⟶ K.X k,
      f.f k ≫ r = 𝟙 (K.X k))
    (hquot : ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel f ≅ ∐ (fun i : I ↦
        (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
          (ModuleCat.of A (ULift.{v} A))))) :
    L.IsKProjective := by
  classical
  obtain ⟨I, degree, ⟨e⟩⟩ := hquot
  let F (i : I) := (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ)
    (degree i)).obj (ModuleCat.of A (ULift.{v} A))
  have (i : I) : IsKProjective (F i) := single_projective (degree i)
  have : IsKProjective (∐ F) := coproduct_projective F
  have : (cokernel f).IsKProjective := isKProjective_of_iso e.symm
  let S := ShortComplex.cokernelSequence f
  let σ (n : ℤ) : (S.map (HomologicalComplex.eval _ _ n)).Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction _
      ((ShortComplex.cokernelSequence_exact f).map (HomologicalComplex.eval _ _ n))
      (hsplit n).choose (hsplit n).choose_spec (by
        change Epi ((HomologicalComplex.eval _ _ n).map (cokernel.π f))
        infer_instance)
  let T := trianglehOfDegreewiseSplit S σ
  have hT : T ∈ distTriang _ :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S, σ, ⟨Iso.refl _⟩⟩
  rw [isKProjective_iff_leftOrthogonal]
  exact (HomotopyCategory.subcategoryAcyclic (ModuleCat.{max u v} A)).leftOrthogonal
    |>.ext_of_isTriangulatedClosed₂ T hT
      (IsKProjective.leftOrthogonal K) (IsKProjective.leftOrthogonal (cokernel f))

end CochainComplex
