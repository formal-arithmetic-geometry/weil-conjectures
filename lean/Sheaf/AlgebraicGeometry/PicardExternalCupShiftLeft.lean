/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Left dimension shifting for external cup

Source: Stacks Project, Varieties, Tag 0BED, proof of lemma-kunneth.
(blueprint: lem-sc-picard-external-cup-shift-left).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- One successor step in the left coefficient's cohomological bound.
The hypothesis covers every quasi-coherent coefficient with bound d and every
normalized realization, in every degree. The conclusion only raises that bound once.
Source: Stacks Project, Varieties, Tag 0BED, short exact coefficient sequences and
induction after `equation-kunneth-on-cech` (blueprint: lem-sc-picard-external-cup-shift-left).

Proof: Give X its specified k-structure. Embed F into an acyclic quasi-coherent
module E using the acyclic embedding theorem and form its cokernel Q. Quasi-coherence
is closed under cokernels. The long exact module cohomology sequence gives
H^p(Q) = H^(p+1)(F) for p>0. Therefore Q has bound d: if d<p then p>0 and
d+1<p+1. E also has bound d since it is acyclic and d is nonnegative.
Choose finite affine covers and the product cover. Affine diagonal ensures affine
finite intersections. Sections on these intersections are exact on quasi-coherent
coefficients; the affine pullback and tensor formulas identify product sections
with tensors of factor sections. Tensor over k is exact. Consequently the Cech
external-cup comparison is a map of short exact sequences of complexes for
0 -> F -> E -> Q -> 0. Naturality of affine Cech comparisons and the signed cup
formula identify the induced maps with external cup and make the long exact
homology ladders commute, including the connecting maps. Apply the inductive
hypothesis to normalized cochain realizations for E and Q, whose existence is
picardExternalCupCochain_exists. The five lemma makes the Cech comparison for F
invertible in all degrees, including the beginning of the long exact sequence.
Transport along the resolution comparisons. Tensor Kunneth's cycle formula and
surjectivity of homology projections show that tensor-cycle classes span source
homology. The normalization hc identifies the given c with the transported Cech
comparison on those classes, hence everywhere by linearity. Its homology map is
therefore invertible. This is one dimension-shifting step, without invoking the
comparison for arbitrary cohomological bounds. It applies when d=0, when Q can
have nonzero H^0, and also when E or Q or the other coefficient is zero. -/
theorem picardExternalCupCochain_isIso_shiftLeft
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] (d : ℕ)
    (ih : ∀ (F' : X.Modules) [F'.IsQuasicoherent],
      (∀ p : ℕ, d < p →
        IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F')) →
      ∀ (c' : picardExternalTotal f g F' G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F' G)),
        IsPicardExternalCupCochain f g F' G c' → ∀ n : ℕ,
          IsIso (HomologicalComplex.homologyMap c' (n : ℤ)))
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ p : ℕ, d + 1 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F))
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  have : IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k))) := by
    change IsAffineHom (pullback.diagonal f)
    infer_instance
  obtain ⟨E, hE, i, hi, hacyclic⟩ := exists_quasicoherent_acyclic_embedding k X F
  have : E.IsQuasicoherent := hE
  have : Mono i := hi
  let Q := cokernel i
  have : Q.IsQuasicoherent := isQuasicoherent_cokernel i
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    .mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (Opposite.op ⊤)))
  let : EnoughInjectives (SheafOfModules.{w} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  obtain ⟨_, _, hexact⟩ := hS.exists_rightDerived_full_long_exact Γ
  have hQ : ∀ p : ℕ, d < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj Q) := by
    intro p hp
    obtain ⟨_, _, _, h₁, _⟩ := hexact p
    exact h₁.isZero_of_both_isZero (hacyclic p (by omega)) (hF (p + 1) (by omega))
  have hEbound : ∀ p : ℕ, d < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj E) := by
    intro p hp
    exact hacyclic p (by omega)
  obtain ⟨cE, hcE⟩ := picardExternalCupCochain_exists f g E G
  obtain ⟨cQ, hcQ⟩ := picardExternalCupCochain_exists f g Q G
  obtain ⟨R₁, R₂, φ, e₁, e₂, hR₁, hR₂, houterE, houterQ, hcomm⟩ :=
    picardExternalCupCochain_left_homology_ladder k X Y f g S hS G
      cE hcE cQ hcQ c hc n
  obtain ⟨h₀, h₃⟩ := houterE (ih E hEbound cE hcE)
  obtain ⟨h₁, h₄⟩ := houterQ (ih Q hQ cQ hcQ)
  have : IsIso (ComposableArrows.app' φ 0) := h₀
  have : IsIso (ComposableArrows.app' φ 4) := h₄
  have : IsIso (ComposableArrows.app' φ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ φ
      inferInstance h₁ h₃ inferInstance
  have hmap : HomologicalComplex.homologyMap c (n : ℤ) =
      e₁.inv ≫ ComposableArrows.app' φ 2 ≫ e₂.hom := by
    rw [hcomm, ← Category.assoc, e₁.inv_hom_id, Category.id_comp]
  rw [hmap]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
