/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Finite free cohomology and projective split models

Source: Stacks Project, proetale.tex, Tag 09C3, generator lifting in the proof of
lemma-local-structure-constructible-complex; derived.tex, Tag 064B
(blueprint: lem-sf-projective-cohomology-split-model).

The zero-differential model and its summand inclusions are explicit constructions.
The cohomology map and its generator-section map use the canonical single-complex
and localization comparisons, so the asserted bijection has a specified forward map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

namespace WeilConjectures

variable {U : Scheme.{u}}
    (C : Sheaf (Scheme.ProEt.topology U) CommRingCat.{max (u + 1) v})

/-- The coefficient ring sheaf, forgetting only commutativity.
Source: Stacks 09C3, module sheaves over the coefficient sheaf
(blueprint: lem-sf-projective-cohomology-split-model). -/
abbrev sfSplitRings : Sheaf (Scheme.ProEt.topology U) RingCat.{max (u + 1) v} :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj C

/-- The prescribed zero-differential complex: finite free terms in `[a,b]`, zero elsewhere.
Source: Stacks 09C3, simultaneous generator lifting in the proof
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfSplitComplex (a b : ℤ) (r : ℤ → ℕ) :
    CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ where
  X q := if a ≤ q ∧ q ≤ b then
    SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q))) else 0
  d _ _ := 0

/-- The actual inclusion of the degree-`q` summand in the zero-differential model.
Source: Stacks 09C3, identification of the lifted top cell
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfSplitCell (a b : ℤ) (r : ℤ → ℕ) (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
    (CochainComplex.singleFunctor
      (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q)))) ⟶
      sfSplitComplex C a b r :=
  HomologicalComplex.mkHomFromSingle
    (eqToHom (by dsimp [sfSplitComplex]; rw [if_pos hq]))
    (fun _ _ ↦ by simp [sfSplitComplex])

variable [HasDerivedCategory.{w} (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))]

/-- The cohomology map of an arrow from a finite free sheaf placed in degree `q`.
The single complex in degree `q` is the model for `C^r[-q]`.
Source: Stacks 064B and the generator calculation in Stacks 09C3
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfFreeCohomologyMap (q : ℤ) (r : ℕ)
    {A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))}
    (f : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) :
    SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)) ⟶
      (DerivedCategory.homologyFunctor _ q).obj A :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) q
      (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))).inv ≫
    (DerivedCategory.homologyFunctorFactors _ q).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ q).map f

/-- Send a derived arrow to the images of the standard generators in `H^q(A)(U)`.
Source: Stacks 09C3, lifting the sections `rho(e_s)`, and Stacks 064B
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfShiftedFreeGeneratorMap (q : ℤ) (r : ℕ)
    (A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
    (f : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) :
    Fin r → ((DerivedCategory.homologyFunctor _ q).obj A).val.obj
      (op (Scheme.ProEt.mk (𝟙 U))) :=
  fun i ↦ (((DerivedCategory.homologyFunctor _ q).obj A).freeHomEquiv
    (sfFreeCohomologyMap C q r f) (ULift.up i)).val (op (Scheme.ProEt.mk (𝟙 U)))

/-- Prescribed finite free cohomology gives a chain quasi-isomorphism from its split model;
any derived arrow inducing the top prescribed isomorphism is its top-cell inclusion.
Source: Stacks 09C3, generator lifting, expanded degreewise; Stacks 064B
(blueprint: lem-sf-projective-cohomology-split-model).

Proof:
1. The exact forgetful functor to abelian sheaves preserves epimorphisms
   (lem-weil-pbc-module-sheaves-colimits-forgetful). The local-surjectivity criteria for
   abelian sheaves and set sheaves identify their underlying maps as epimorphisms of
   set sheaves. The evaluation hypothesis therefore makes module quotients surjective
   on sections at U; kernels are sectionwise.
2. A map from a finite free module sheaf is determined by its generator sections at
   the terminal object U. Lift those sections through any epimorphism. This proves
   projectivity, including rank zero.
3. Lift each theta through the quotient from cycles to cohomology of Z, using the
   fixed representative isomorphism e. Compose with the cycle inclusions. The resulting
   components form v since the model differential is zero. Their cohomology maps are
   exactly theta. Outside the interval both cohomologies vanish, so v is a quasi-isomorphism.
4. Bounded-above projective complexes are K-projective by
   lem-sc-bounded-above-projective-kprojective; their derived arrows are homotopy classes
   by lem-coef-kprojective-derived-hom-bijection, with no target boundedness requirement.
5. For a single finite free term, chain maps are tuples of cycles and homotopies are
   tuples of boundaries. Step 1 makes the quotient on sections exactly H^q(A)(U).
   Hence the generator map is bijective and natural for every derived arrow.
6. The top cell followed by v induces theta_b. By step 5 any other arrow with that
   cohomology map is equal to it, giving the stated summand identification. -/
theorem sf_projective_cohomology_split_model
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U)))))
    (N : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (hN : ∀ q : ℤ, ¬ (a ≤ q ∧ q ≤ b) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj N))
    (theta : ∀ (q : ℤ) (_hq : a ≤ q ∧ q ≤ b),
      SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q))) ≅
        (DerivedCategory.homologyFunctor _ q).obj N)
    (Z : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (e : DerivedCategory.Q.obj Z ≅ N) :
    ∃ v : sfSplitComplex C a b r ⟶ Z,
      QuasiIso v ∧
      (∀ (q : ℤ) (hq : a ≤ q ∧ q ≤ b),
        sfFreeCohomologyMap C q (r q)
          (DerivedCategory.Q.map (sfSplitCell C a b r q hq ≫ v) ≫ e.hom) =
          (theta q hq).hom) ∧
      (∀ f : DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor
            (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) b).obj
            (SheafOfModules.free (R := sfSplitRings.{u, v} C)
              (ULift.{max (u + 1) v} (Fin (r b))))) ⟶ N,
        sfFreeCohomologyMap C b (r b) f = (theta b ⟨hab, le_refl b⟩).hom →
        f = DerivedCategory.Q.map (sfSplitCell C a b r b ⟨hab, le_refl b⟩ ≫ v) ≫ e.hom) := by
  sorry

/-- The specified generator-section map is bijective, naturally in the derived target.
Source: Stacks 064B; Stacks 09C3, lifting `rho(e_s)`
(blueprint: lem-sf-projective-cohomology-split-model).

Proof: Steps 1--2 of sf_projective_cohomology_split_model make each finite free term
projective and evaluation exact. By steps 4--5, chain maps from its single complex
are tuples of cycles, and their homotopies are precisely tuples of boundaries.
Exact evaluation identifies the quotient with sections of cohomology. This proves
bijectivity. Functoriality of derived cohomology and evaluation on the standard
free generators proves the naturality equation for all derived arrows. -/
theorem sf_shifted_free_generator_bijective_natural
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U))))) :
    (∀ (q : ℤ) (r : ℕ)
      (A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))),
      Function.Bijective (sfShiftedFreeGeneratorMap C q r A)) ∧
    (∀ (q : ℤ) (r : ℕ)
      (A B : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
      (alpha : A ⟶ B)
      (f : DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
          (SheafOfModules.free (R := sfSplitRings.{u, v} C)
            (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) (i : Fin r),
      sfShiftedFreeGeneratorMap C q r B (f ≫ alpha) i =
        ((DerivedCategory.homologyFunctor _ q).map alpha).val.app
          (op (Scheme.ProEt.mk (𝟙 U))) (sfShiftedFreeGeneratorMap C q r A f i)) := by
  sorry

/-- Bounded-above projective module complexes represent all derived maps, with equality
exactly chain homotopy (`f-g = dh+hd` in Mathlib's Homotopy convention).
Source: Stacks 064B, lemma-morphisms-from-projective-complex
(blueprint: lem-sf-projective-cohomology-split-model).

Proof: Apply lem-sc-bounded-above-projective-kprojective to P and its bound d.
Then lem-coef-kprojective-derived-hom-bijection identifies homotopy-category maps
out of P with derived maps. The quotient functor from complexes is full, and
its fibers are precisely Nonempty (Homotopy f g). Transport along the canonical
quotient/localization comparison gives the two assertions for Q itself. No enough
projectives hypothesis and no boundedness on L are required. -/
theorem sf_bounded_above_projective_chain_representatives
    (P : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (d : ℤ) [P.IsStrictlyLE d] [∀ n : ℤ, Projective (P.X n)]
    (L : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ) :
    (∀ phi : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L,
      ∃ f : P ⟶ L, DerivedCategory.Q.map f = phi) ∧
    (∀ f g : P ⟶ L, DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔
      Nonempty (Homotopy f g)) := by
  sorry

end WeilConjectures
