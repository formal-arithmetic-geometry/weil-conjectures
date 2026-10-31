/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BertiniLocalFirstJets
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.SourceFibreDifferentialSectionsAux

/-! # Differential sections over a fixed source point

Source: Stacks Project, Morphisms, lemma-base-change-differentials (Tag 01V0),
lemma-smooth-omega-finite-locally-free (Tag 02G1), and Sheaves, Tag 0098.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The cotangent fibre becomes the sections of the pulled-back differential sheaf
when the source projection factors through a fixed residue-field point. This statement
contains no line bundle, section family, universal equation, or singular locus.

Source: Stacks Project, Morphisms, lemma-base-change-differentials (Tag 01V0),
lemma-smooth-omega-finite-locally-free (Tag 02G1), and Sheaves, Tag 0098.
(blueprint: lem-zl-source-fibre-differential-sections).

Proof: Write q and p for the source and base projections of B times_k Y. Base change
for differentials gives q^* Omega_f isomorphic to Omega_p, carrying 1 tensor da to
 d(q^*a). Pull this isomorphism back along g and use the normalized composition
comparison. The equality hg identifies the resulting module with h^* of the
pullback along Spec kappa_U(z) -> U -> Y. Open restriction identifies the latter
pullback with the module on Spec kappa_U(z) associated to the actual cotangent
fibre of U -> Spec k. The stalk-pullback comparison carries each differential
germ to 1 tensor that germ, so this identification sends the local differential
to the second entry of bertiniLocalFirstJet. Smoothness makes the differential
sheaf finite locally free. Thus its fibre admits a finite basis; pullback of
the corresponding finite free module and evaluation on T identify its sections
with Gamma(T,O_T) tensor that fibre, by the identity on a finite power of the
section ring. Compose these isomorphisms to obtain D. The equality hα identifies
the scalar action with the specified algebra structure. All comparisons preserve
the normalized unit sections, so the formula for 1 tensor da follows from the
base-change formula. A-linearity gives the formula for b tensor da. An isomorphism
is injective. If T is empty both modules are zero; rank zero also gives zero modules.
No affineness of T, reducedness, or vanishing criterion is required. -/
theorem exists_source_fibre_differential_sections
    {k : Type u} [Field k] {Y B T : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] (c : B ⟶ Spec (.of k))
    (U : Y.Opens) (z : U)
    (h : T ⟶ Spec ((U : Scheme).residueField z)) (g : T ⟶ pullback c f)
    (hg : g ≫ pullback.snd c f = h ≫ (U : Scheme).fromSpecResidueField z ≫ U.ι)
    (α : (U : Scheme).residueField z →+* Γ(T, ⊤))
    (hα : α = ((Scheme.ΓSpecIso ((U : Scheme).residueField z)).inv ≫ h.appTop).hom) :
    let K := (U : Scheme).residueField z
    let A := Γ(T, ⊤)
    letI : Algebra K A := α.toAlgebra
    ∃ D : (A ⊗[K] bertiniCotangentFibre f U z) →ₗ[A]
        Γ((Scheme.Modules.tensorPullback g).obj (pullback.fst c f).relativeDifferentials, ⊤),
      Function.Injective D ∧
      ∀ (W : Y.Opens) (hz : U.ι z ∈ W)
        (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W))
        (a : Γ(Y, W)) (b : A),
        D (b ⊗ₜ[K] (bertiniLocalFirstJet f U z W hz a).2) =
          b • ((Scheme.Modules.tensorPullback g).obj
            (pullback.fst c f).relativeDifferentials).presheaf.map (homOfLE hV).op
              (Scheme.Modules.tensorPullbackSection g (pullback.fst c f).relativeDifferentials
                ((pullback.snd c f) ⁻¹ᵁ W)
                ((pullback.fst c f).relativeDifferentialsDerivation.d
                  (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
                  ((pullback.snd c f).app W a))) := by
  dsimp
  obtain ⟨D, hD⟩ := exists_source_fibre_differential_formula f c U z h g hg α hα
  refine ⟨D, ?_, hD⟩
  exact source_fibre_differential_injective_of_formula f c U z h g hg α hα D hD

end AlgebraicGeometry
