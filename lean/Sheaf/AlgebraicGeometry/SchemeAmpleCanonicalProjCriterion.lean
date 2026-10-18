/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.TraceFormula.SpaceLineModuleProjMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Sheaf.AlgebraicGeometry.AmpleProjLocalChart
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-!
# Relative ampleness and the canonical section-algebra Proj map

Source: Stacks Project, Morphisms, Tags 01VH, 01VI and 01VJ, equivalence (1) and (5);
Constructions, Tag 01O9 (blueprint: lem-trf-scheme-ample-canonical-proj-criterion).

The section algebra is presented by its actual homogeneous sections on affine base opens.
The presentation fixes its products, scalars, unit and restriction maps. Evaluation is the
section-normalized tensor pullback. The canonical map is specified by the same trivializing
chart formula as `GradedLineMap.IsCanonicalMap` in the recorded algebraic-space construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical graded section algebra, in the existing quasi-coherent affine-basis
presentation used by relative Proj. Its degree-n sections are exactly sections of L^n
on the inverse-image open, not a chosen unrelated algebra. These identifications determine
it up to the unique graded algebra isomorphism preserving sections.
Source: Stacks, Morphisms, Tag 01VJ(5)
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion). -/
structure RelativeSectionAlgebra {X T : Scheme.{u}} (f : X ⟶ T) (L : X.Modules) where
  data : T.GradedAlgebraData
  sectionEquiv (V : T.affineOpens) (n : ℕ) :
    data.grading V n ≃+ Γ(L.tensorPow n, f ⁻¹ᵁ V.1)
  smul (V : T.affineOpens) (n : ℕ) (r : Γ(T, V.1)) (a : data.grading V n) :
    sectionEquiv V n (r • a) = f.app V.1 r • sectionEquiv V n a
  one (V : T.affineOpens) :
    sectionEquiv V 0 ⟨1, SetLike.one_mem_graded (data.grading V)⟩ =
      unitSectionsEquiv (f ⁻¹ᵁ V.1) 1
  mul (V : T.affineOpens) (m n : ℕ) (a : data.grading V m) (b : data.grading V n) :
    sectionEquiv V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V.1)
        (tmulSection (sectionEquiv V m a) (sectionEquiv V n b))
  restriction {V W : T.affineOpens} (h : V ≤ W) (n : ℕ) (a : data.grading W n) :
    sectionEquiv V n ⟨data.res h a, (data.res h).map_mem a.property⟩ =
      (L.tensorPow n).val.map (homOfLE (f.preimage_mono h)).op (sectionEquiv W n a)

/-- Evaluation of a homogeneous section on a trivializing scheme chart. The section map
is literally `1 ⊗ s`, followed by the existing tensor-power pullback comparison.
Source: Stacks, Morphisms, Tag 01VJ(5), adjunction map; Constructions, Tag 01O9
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion). -/
noncomputable def RelativeSectionAlgebra.evaluate {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) {W : Scheme.{u}} (j : W ⟶ X)
    (V : T.affineOpens) (h : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (f ⁻¹ᵁ V.1))
    (n : ℕ) (a : A.data.grading V n) :
    Γ(((tensorPullback j).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso j L n).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow n)).val.map (homOfLE h).op
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow n)).app (f ⁻¹ᵁ V.1)
        (A.sectionEquiv V n a)))

/-- The assertion U(evaluation) = X: a positive-degree homogeneous section generates the
rank-one stalk at every point. Sections may be taken on any affine base neighbourhood.
Source: Stacks, Constructions, Tag 01O9, generation locus; Morphisms, Tag 01VJ(5)
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion). -/
def RelativeSectionAlgebra.GeneratesEverywhere {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) : Prop :=
  ∀ x : X, ∃ (V : T.affineOpens) (hx : x ∈ f ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
    ∃ a : A.data.grading V n,
      (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (f ⁻¹ᵁ V.1) x hx)
          (A.sectionEquiv V n a) ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))

/-- The scheme specialization of the canonical chart formula in the recorded
`GradedLineMap.IsCanonicalMap`, for the evaluation map of the section algebra.
All trivializing open scheme charts are tested. The ring map is fixed on every
homogeneous section, including degree zero; the irrelevant-ideal condition is precisely
the hypothesis for the existing `Proj.fromOfGlobalSections` construction.
Source: Stacks, Constructions, Tag 01O9(2),(3); Morphisms, Tag 01VJ(5)
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion). -/
def RelativeSectionAlgebra.IsCanonicalMap {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) (r : X ⟶ A.data.relProj) : Prop :=
  r ≫ A.data.relProjHom = f ∧
    ∀ (W : Scheme.{u}) (j : W ⟶ X), IsOpenImmersion j →
      ∀ (V : T.affineOpens) (h : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (f ⁻¹ᵁ V.1))
        (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
        (α : A.data.obj V →+* Γ(W, ⊤)),
        (∀ (n : ℕ) (a : A.data.grading V n), α a =
          (unitSectionsEquiv ⊤).symm
            ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (A.evaluate j V h n a))) →
        ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.data.grading V)).toIdeal = ⊤,
          j ≫ r = Proj.fromOfGlobalSections (A.data.grading V) α hα ≫ A.data.relProjι V

/-- The canonical graded comparison from the sum of direct-image tensor powers to the
direct image of their sum. Its restriction to each summand is the direct image of that
summand's inclusion; thus no choice of an abstract isomorphism is involved.
Source: Stacks, Morphisms, Tag 01VJ(5); Schemes, Tag 01LC
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion). -/
noncomputable def relativeSectionAlgebraCoproductComparison {X T : Scheme.{u}}
    (f : X ⟶ T) (L : X.Modules) :
    (∐ fun n : ℕ ↦ (pushforward f).obj (L.tensorPow n)) ⟶
      (pushforward f).obj (∐ fun n : ℕ ↦ L.tensorPow n) :=
  Sigma.desc (fun n ↦ (pushforward f).map (Sigma.ι (fun n : ℕ ↦ L.tensorPow n) n))

/-- For a quasi-compact morphism, relative ampleness is equivalent to quasi-separatedness
and an everywhere-defined open canonical immersion into the Proj of its section algebra.
Either condition implies separatedness. The canonical direct-sum comparison also identifies
the algebra with the direct image of the tensor algebra whenever f is quasi-separated.

Source: Stacks, Morphisms, Tags 01VH, 01VI and 01VJ, equivalence (1) and (5)
(blueprint: lem-trf-scheme-ample-canonical-proj-criterion).

Proof, following the node's nine steps:
1. For affine V in T, ampleness on W = f inverse-image V makes W absolutely separated
(lem-weil-pbc-ample-scheme-separated). Cancel the map V to Spec Z to obtain separation
of W over V (lem-weil-pbc-separated-cancellation).
2. These separated restrictions glue on the affine base cover: the diagonals are closed
immersions locally. Thus f is separated and its diagonal is quasi-compact, giving
quasi-separatedness (def-weil-closed-immersion, def-weil-proper-morphism,
def-weil-quasi-separated-morphism).
3. Every tensor power of L is quasi-coherent. Apply pqf-lem-pushforward-qcoh and
lem-weil-pbc-quasi-coherent-module-coproduct-closure to form the graded section algebra.
On every affine base open, its homogeneous pieces are the sections specified above.
Use lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-qcqs-over-affine on W, then
lem-weil-pbc-qcqs-cohomology-direct-sum in degree zero, to identify the sum of pushforwards
with the pushforward of the sum by the displayed canonical comparison.
4. Form relative Proj using lemma-nagata-relative-proj-exists. Evaluation is the
adjunction map. Apply the scheme specialization of lem-trf-space-line-module-proj-map:
on each trivializing chart it is exactly the existing homogeneous-section Proj map.
5. The affine nonvanishing section cover supplied by ampleness generates the stalks,
so U(evaluation) = X (def-weil-pbc-ample-invertible-module).
6. Apply lem-sc-ample-proj-local-chart over each affine base open. The canonical map is
an isomorphism on affine nonvanishing charts. The local inverses agree and glue, so the
map to relative Proj is an open immersion.
7. Conversely restrict the open immersion to an affine base open. Its image in the
ordinary Proj is quasi-compact by quasi-compactness of f. Apply
lem-trf-proj-canonical-map-twist-comparison to obtain a common positive twist d and
identify the pullbacks of O(dk) with L^(dk) for all k > 0.
8. Apply lem-trf-proj-qc-open-twist-ample to that quasi-compact open. A common positive
multiple de identifies an ample invertible Proj twist with L^(de). Its affine
nonvanishing cover also proves ampleness of L itself, without assuming O(1) invertible.
9. This gives ampleness over every affine base open, hence relative ampleness by 01VH.
Steps 1 and 2 give the final separatedness assertion under either equivalent condition.
The construction permits the empty scheme and uses all positive tensor degrees. -/
theorem isAmple_iff_canonical_section_proj_openImmersion {X T : Scheme.{u}}
    (f : X ⟶ T) [QuasiCompact f] (L : X.Modules) [L.IsInvertible] :
    (∀ _hqs : QuasiSeparated f, IsIso (relativeSectionAlgebraCoproductComparison f L)) ∧
    ((∀ V : T.Opens, IsAffineOpen V →
        ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
          @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h) ↔
      ∃ (_hqs : QuasiSeparated f) (A : RelativeSectionAlgebra f L),
        A.GeneratesEverywhere ∧
          ∃ r : X ⟶ A.data.relProj, A.IsCanonicalMap r ∧ IsOpenImmersion r) ∧
    ((∀ V : T.Opens, IsAffineOpen V →
        ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
          @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h) →
      IsSeparated f) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
