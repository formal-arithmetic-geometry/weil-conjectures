/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F1 and C3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Right dimension shifting for external cup

Source: Stacks Project, Varieties, Tag 0BED, proof of lemma-kunneth.
(blueprint: lem-sc-picard-external-cup-shift-right).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Exactness at the cokernel cohomology kills it when its two neighbors are zero.
Source: Stacks Project, Derived Categories, Tag 015B, specialized to global sections. -/
private theorem moduleCohomology_cokernel_isZero
    (Y : Scheme.{w}) (G E : Y.Modules) (i : G ⟶ E) [Mono i]
    (p : ℕ) (hE : IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj E))
    (hG : IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace (p + 1)).obj G)) :
    IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj (cokernel i)) := by
  let : EnoughInjectives (SheafOfModules.{w} (moduleRings Y.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  let T := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  have : PreservesFiniteLimits T := by
    dsimp [T, RingedSpace.globalSectionsFunctor]
    infer_instance
  have hS : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance
      epi_g := by dsimp [ShortComplex.cokernelSequence]; infer_instance }
  obtain ⟨δ, _, hδ⟩ := hS.exists_rightDerived_full_long_exact T
  obtain ⟨_, w₁, w₂, hr, _⟩ := hδ p
  exact hr.isZero_X₂ (hE.eq_of_src _ _) (hG.eq_of_tgt _ _)

/-- One successor step in the right coefficient's cohomological bound.
The hypothesis covers every quasi-coherent coefficient with bound d and every
normalized realization, in every degree. The conclusion only raises that bound once.
Source: Stacks Project, Varieties, Tag 0BED, short exact coefficient sequences and
induction after `equation-kunneth-on-cech` (blueprint: lem-sc-picard-external-cup-shift-right).

Proof: Give Y its specified k-structure. Embed G into an acyclic quasi-coherent
module E using the acyclic embedding theorem and form its cokernel Q. Quasi-coherence
is closed under cokernels. The long exact module cohomology sequence gives
H^p(Q) = H^(p+1)(G) for p>0. Therefore Q has bound d: if d<p then p>0 and
d+1<p+1. E also has bound d since it is acyclic and d is nonnegative.
Choose finite affine covers and the product cover. Affine diagonal ensures affine
finite intersections. Sections on these intersections are exact on quasi-coherent
coefficients; the affine pullback and tensor formulas identify product sections
with tensors of factor sections. Tensor over k is exact. Consequently the Cech
external-cup comparison is a map of short exact sequences of complexes for
0 -> G -> E -> Q -> 0. Naturality of affine Cech comparisons and the signed cup
formula identify the induced maps with external cup and make the long exact
homology ladders commute, including the connecting maps. Apply the inductive
hypothesis to normalized cochain realizations for E and Q, whose existence is
picardExternalCupCochain_exists. The five lemma makes the Cech comparison for G
invertible in all degrees, including the beginning of the long exact sequence.
Transport along the resolution comparisons. Tensor Kunneth's cycle formula and
surjectivity of homology projections show that tensor-cycle classes span source
homology. The normalization hc identifies the given c with the transported Cech
comparison on those classes, hence everywhere by linearity. Its homology map is
therefore invertible. This is one dimension-shifting step, without invoking the
comparison for arbitrary cohomological bounds. It applies when d=0, when Q can
have nonzero H^0, and also when E or Q or the other coefficient is zero. -/
theorem picardExternalCupCochain_isIso_shiftRight
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)
    (ih : ∀ (G' : Y.Modules) [G'.IsQuasicoherent],
      (∀ p : ℕ, d < p →
        IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G')) →
      ∀ (c' : picardExternalTotal f g F G' ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G')),
        IsPicardExternalCupCochain f g F G' c' → ∀ n : ℕ,
          IsIso (HomologicalComplex.homologyMap c' (n : ℤ)))
    (G : Y.Modules) [G.IsQuasicoherent]
    (hG : ∀ p : ℕ, d + 1 < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G))
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) := by
  let : Y.Over (Spec (CommRingCat.of k)) := ⟨g⟩
  have : IsAffineHom (pullback.diagonal (Y ↘ Spec (CommRingCat.of k))) := by
    change IsAffineHom (pullback.diagonal g)
    infer_instance
  obtain ⟨E, hE, i, hi, hEacyclic⟩ := exists_quasicoherent_acyclic_embedding k Y G
  have : E.IsQuasicoherent := hE
  have : Mono i := hi
  have : (cokernel i).IsQuasicoherent := (quasiCoherent_cokernel_image i).2.2.2.2.2.2.1
  have hEbound : ∀ p : ℕ, d < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj E) := by
    intro p hp
    exact hEacyclic p (by omega)
  have hQbound : ∀ p : ℕ, d < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj (cokernel i)) := by
    intro p hp
    exact moduleCohomology_cokernel_isZero Y G E i p (hEbound p hp)
      (hG (p + 1) (by omega))
  obtain ⟨cE, hcE⟩ := picardExternalCupCochain_exists f g F E
  obtain ⟨cQ, hcQ⟩ := picardExternalCupCochain_exists f g F (cokernel i)
  have hS : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance
      epi_g := by dsimp [ShortComplex.cokernelSequence]; infer_instance }
  have : (ShortComplex.cokernelSequence i).X₁.IsQuasicoherent := by
    change G.IsQuasicoherent
    infer_instance
  have : (ShortComplex.cokernelSequence i).X₂.IsQuasicoherent := by
    change E.IsQuasicoherent
    infer_instance
  have : (ShortComplex.cokernelSequence i).X₃.IsQuasicoherent := by
    change (cokernel i).IsQuasicoherent
    infer_instance
  exact picardExternalCupCochain_isIso_of_right_shortExact k X Y f g F
    (ShortComplex.cokernelSequence i) hS c hc cE hcE cQ hcQ
    (ih E hEbound cE hcE) (ih (cokernel i) hQbound cQ hcQ) n

end AlgebraicGeometry.Scheme.Modules
