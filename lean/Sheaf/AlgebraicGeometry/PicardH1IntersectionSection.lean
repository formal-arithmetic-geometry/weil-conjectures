/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Lifting a fibre generator over the intersection of Picard loci

Source: Stacks Project, More on Morphisms, Tag 0BF2, through the equality d = 0.
(blueprint: lem-sc-picard-h1-intersection-section)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The cohomological part of the multiple Picard-locus argument produces a section on
an intersection near the marked point, nonvanishing on its entire marked fibre.
No local triviality or equality with the source Picard locus is asserted here.

Source: Stacks Project, More on Morphisms, Tag 0BF2, first paragraph through d = 0.
(blueprint: lem-sc-picard-h1-intersection-section)

Proof: Form the finite scheme-theoretic intersection W of the immersions ji, using
successive fibre products (for n = 0 use S). The universal property is factorization
through every ji. Since s belongs to every Zi and an immersion induces an isomorphism
on residue fields at its image, the fibre product has a point w over s with the same
residue field. Pull back the families and L to W; all hypotheses are stable under base
change, including joint H1 injectivity at w. By hZi the pulled-back Li come from finite
locally free modules on W. The universal structure pushforward, together with invertibility
of Li, makes these modules line bundles; trivialize them on a common affine neighbourhood
of w. The condition hs and hZ makes L on the marked fibre trivial as well.
Apply perfect_derivedDirectImage_baseChange to L and to the target structure modules;
the direct images are perfect and their fibres are the corresponding fibre cohomology.
Apply exists_finiteFreeResidueModel, shrinking the common affine neighbourhood finitely
many times. The fixed models start in degree zero with rank one and their differentials
vanish at w. Represent each derived pullback map by a chain map between these fixed
models, using bounded finite free source terms and affine acyclicity. The degree-zero
residue maps are isomorphisms, and the joint degree-one residue map is injective by hH.
A maximal nonzero minor gives injectivity of the joint degree-one map after shrinking
(the rank-zero case needs no minor). Each target degree-zero differential is zero:
the target line bundle is trivial and its universal structure pushforward is O_W.
The chain-map equations therefore imply that the source degree-zero differential is
zero. Its generator defines a global section lifting a fibre generator of L, so it
is nonvanishing at every point over w. Every shrinking was an open neighbourhood in
the intersection; since its immersion is a topological embedding, extend this open
to an ambient open U of S and replace W by its inverse image. Then W still represents
the intersection over U and the section restricts to W as asserted. -/
theorem picard_h1_intersection_section {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (Z : Scheme.{v}) (j : Z ⟶ S) [IsImmersion j]
    (Zi : Fin n → Scheme.{v}) (ji : ∀ i, Zi i ⟶ S) [∀ i, IsImmersion (ji i)]
    (hZ : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      (∃ h : T ⟶ Z, h ≫ j = g) ↔
        ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj L ≅
            (Modules.tensorPullback (pullback.snd f g)).obj N))
    (hZi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      (∃ h : T ⟶ Zi i, h ≫ ji i = g) ↔
        ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst (fi i) g)).obj
            ((Modules.tensorPullback (ui i)).obj L) ≅
            (Modules.tensorPullback (pullback.snd (fi i) g)).obj N))
    (s : S) (hs : s ∈ Set.range j) (hsi : ∀ i, s ∈ Set.range (ji i))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ (U : S.Opens), s ∈ U ∧ ∃ (W : Scheme.{v}) (k : W ⟶ S),
      IsImmersion k ∧ ∃ (w : W), k w = s ∧
        (∀ {T : Scheme.{v}} (g : T ⟶ S), Set.range g ⊆ U →
          ((∃ h : T ⟶ W, h ≫ k = g) ↔ ∀ i, ∃ h : T ⟶ Zi i, h ≫ ji i = g)) ∧
        ∃ σ : Γ((Modules.tensorPullback (pullback.fst f k)).obj L, ⊤),
          ∀ x : (pullback f k : Scheme.{v}), (pullback.snd f k) x = w →
            x ∈ Modules.nonvanishingLocus
              ((Modules.tensorPullback (pullback.fst f k)).obj L) σ := by
  sorry

end AlgebraicGeometry.Scheme
