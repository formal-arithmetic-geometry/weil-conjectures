/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.GeometricTowerData
public import WeilConjectures.CategoryTheory.RepresentingCounit.RepresentingCounits

/-! # Smooth representing pairs with their finite evaluated counits
Source: blueprint sk-prop-sp-tower-geometric, Classes and integration, Charts and gluing,
and the final evaluation paragraph.
(blueprint: lem-sp-condensed-geometric-representatives)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A representing pair and its objectwise finite counit identifications. No functor
on these objects, unit formula, or quotient-reduction equation is assumed here.
Source: blueprint sk-prop-sp-tower-geometric, Charts and gluing, finite evaluation.
(blueprint: lem-sp-condensed-geometric-representatives) -/
structure GeometricRepresentative {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (B : GeometricSupport l E DX DY c)
    (C : CtfTowers l E Y) where
  pair : RepresentingCounit (B.support l E) C
  levels : ∀ n, (ctfEvaluation l E X n).obj pair.object ≅
    (B.finite.right n).obj ((ctfEvaluation l E Y n).obj C)
  counit : ∀ n,
    (B.supportLevels n).inv.app pair.object ≫
      (ctfEvaluation l E Y n).map pair.counit =
    (B.finite.support l E n).map (levels n).hom ≫
      (B.finite.adjunction n).counit.app ((ctfEvaluation l E Y n).obj C)

/-- Every smooth compact-support Hom functor has a uniformly constructible representing
pair, and the evaluated pair is identified with the finite pair by its counit.
Source: blueprint sk-prop-sp-tower-geometric, Classes and integration, Charts and gluing,
and the final evaluation paragraph; det-sp-tower-gluing(1) and the objectwise part of (3).
Proof: the exact Kummer sequence in towers of abelian sheaves supplies the Chern and
supported diagonal classes. Extend their scalars to the actual ell-power coefficient
diagram. The unit and Chern class give the projective-line splitting; exact evaluations
identify it with the finite splitting and jointly detect its invertibility. Twist its
inverse and project to the second summand to define the projective-line trace. The
projection and diagonal formulas give the projective-line unit and counit; their triangle
identities reduce to the diagonal integrals. These are equalities between tower sheaves
in degree zero and hence follow from the finite integrals. Restrict to affine space by
extension by zero, iterate, and compose with the etale fibre-sum adjunction on each chart.
For two opens, uniquely identify the overlap representing pairs with their counits, form
the open-cover cone, and lift the compatible counits by its exact Hom sequence. Comparing
the Hom sequences by the five lemma proves representability. Induct on a finite chart
cover. Chart restrictions bound the cohomology and Tor amplitudes by common finite
intervals, so the pair lies in the uniform constructible category. Evaluation preserves
the local constructions and the finite gluing argument, giving a finite representing
pair; uniqueness with its counit gives each displayed level isomorphism. This only
constructs objectwise pairs and comparisons; functoriality, units, and actual quotient
reductions are proved separately by transposition.
(blueprint: lem-sp-condensed-geometric-representatives) -/
theorem geometric_representatives_exist
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (B : GeometricSupport l E (model l E X) (model l E Y)
      (fieldCompactification k X Y f)) :
    ∀ C : CtfTowers l E Y, Nonempty (GeometricRepresentative l E B C) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
