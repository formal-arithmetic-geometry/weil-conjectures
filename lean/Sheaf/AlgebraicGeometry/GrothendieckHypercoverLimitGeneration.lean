/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.GrothendieckHypercoverCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Finite cochain descent generates limit hypercover cohomology -/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Stage hypercover cohomology objects jointly generate the limit object.
This statement concerns alternating cochain complexes and their colimits only;
it makes no reference to injective resolutions or derived sections.
Source: blueprint lemma-weil-pbc-finite-hypercover-descent and the finite-cochain
argument of lemma-weil-pbc-etale-cohomology-continuity, steps 2–4.
(blueprint: lem-weil-pbc-grothendieck-hypercover-limit-generation).

Proof: pull a finite split hypercover at a stage to the limit. Base change preserves
its splitting, finite coproduct decomposition and matching covers. The inverse-image
unit gives a map of its section complexes and hence a map from stage hypercover
cohomology to limit hypercover cohomology, compatible with refinements. For a fixed
q, the cohomology of a hypercover section complex depends only on degrees through
q + 1. Descend that finite truncation to a stage using finite hypercover descent;
extend its truncation there by successively choosing finite covers of matching
objects. Sections of an inverse-image sheaf on a descended qcqs etale object are
the filtered colimit of the stage section objects. This is the coherent-site
inverse-image formula: choose finite covers, express the sheaf condition by finite
equalizers, and commute those equalizers with filtered colimits using AB5. The
formula applies to the finitely many terms and differentials of the truncation.
AB5 again identifies their cohomology with the filtered colimit of the cohomologies.
Consequently the canonical stage-to-limit maps are jointly epic on every summand
of the hypercover colimit. The colimit injections are jointly epic, so these maps
are jointly epic on the whole limit object. The displayed family contains those
canonical maps, proving the claimed cancellation. This works also at q = 0;
cofilteredness supplies a stage, and the empty scheme has zero section objects. -/
theorem hypercoverCohomology_limit_hom_ext
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]
    (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (B : A)
    (f g : hypercoverCohomology A ((Etale.upperStar A c.pt.hom).obj F) q ⟶ B)
    (h : ∀ (i : I)
      (a : hypercoverCohomology A ((Etale.upperStar A (D.obj i).hom).obj F) q ⟶
        hypercoverCohomology A ((Etale.upperStar A c.pt.hom).obj F) q),
      a ≫ f = a ≫ g) : f = g := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover
