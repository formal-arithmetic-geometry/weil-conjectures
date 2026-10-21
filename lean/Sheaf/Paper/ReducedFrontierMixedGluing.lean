/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.ExtensionByZeroPunctual
public import Sheaf.Paper.SfCommonStageDirectImage
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.ConstructiblePullbackTExact
import Sheaf.Paper.MixedWeightsStability
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual
import Sheaf.Paper.ZlImmersionWeilLocalBehavior
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections

/-! # Mixed Weil filtrations along a reduced closed frontier

Source: main-20261015, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, final three paragraphs
(blueprint: lem-zl-reduced-frontier-mixed-gluing).

The structures below only package the hypotheses and clauses of this lemma. Closed
image is tied to the recorded derived direct image and its actual adjunction unit.
Open image and every restriction are the existing canonical Weil-heart functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The given reduced frontier, with all maps over the fixed finite field. The
first term is the reduction, identified over X, and the last has empty underlying
space. Finite component sets may be empty. Finite type and separatedness of these
subschemes are inherited from X; bundling them records these inherited structures.
Source: source paragraphs 6--9 (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlReducedFrontier (D : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) where
  length : ℕ
  closed : Fin (length + 1) → Over (Spec (.of D.k₀))
  [closed_ft : ∀ a, LocallyOfFiniteType (closed a).hom]
  [closed_qc : ∀ a, QuasiCompact (closed a).hom]
  [closed_sep : ∀ a, IsSeparated (closed a).hom]
  reduced : ∀ a, IsReduced (closed a).left
  ambient : ∀ a, closed a ⟶ X
  [ambient_closed : ∀ a, IsClosedImmersion (ambient a).left]
  reduction : (closed 0).left ≅ X.left.nilradical.subscheme
  reduction_over : reduction.hom ≫ X.left.nilradical.subschemeι = (ambient 0).left
  finish : IsEmpty (closed (Fin.last length)).left
  inclusion : ∀ a : Fin length, closed a.succ ⟶ closed a.castSucc
  [inclusion_closed : ∀ a, IsClosedImmersion (inclusion a).left]
  ambient_next : ∀ a : Fin length, inclusion a ≫ ambient a.castSucc = ambient a.succ
  difference : Fin length → Over (Spec (.of D.k₀))
  [difference_ft : ∀ a, LocallyOfFiniteType (difference a).hom]
  [difference_qc : ∀ a, QuasiCompact (difference a).hom]
  [difference_sep : ∀ a, IsSeparated (difference a).hom]
  openInclusion : ∀ a : Fin length, difference a ⟶ closed a.castSucc
  [open_inclusion : ∀ a, IsOpenImmersion (openInclusion a).left]
  complement : ∀ a, Set.range (openInclusion a).left = (Set.range (inclusion a).left)ᶜ
  count : Fin length → ℕ
  piece : ∀ a : Fin length, Fin (count a) → Over (Spec (.of D.k₀))
  [piece_ft : ∀ a b, LocallyOfFiniteType (piece a b).hom]
  [piece_qc : ∀ a b, QuasiCompact (piece a b).hom]
  [piece_sep : ∀ a b, IsSeparated (piece a b).hom]
  pieceInclusion : ∀ (a : Fin length) (b : Fin (count a)), piece a b ⟶ difference a
  [piece_open : ∀ a b, IsOpenImmersion (pieceInclusion a b).left]
  [piece_closed : ∀ a b, IsClosedImmersion (pieceInclusion a b).left]
  cover : ∀ a, ⋃ b, Set.range (pieceInclusion a b).left = Set.univ
  disjoint : ∀ a b c, b ≠ c →
    Disjoint (Set.range (pieceInclusion a b).left) (Set.range (pieceInclusion a c).left)

attribute [instance] ZlReducedFrontier.closed_ft ZlReducedFrontier.closed_qc
  ZlReducedFrontier.closed_sep ZlReducedFrontier.ambient_closed
  ZlReducedFrontier.inclusion_closed ZlReducedFrontier.difference_ft
  ZlReducedFrontier.difference_qc ZlReducedFrontier.difference_sep
  ZlReducedFrontier.open_inclusion ZlReducedFrontier.piece_ft ZlReducedFrontier.piece_qc
  ZlReducedFrontier.piece_sep ZlReducedFrontier.piece_open ZlReducedFrontier.piece_closed

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Exact preservation of an individual finite filtration, with precisely its
assigned pure quotient weights, as well as preservation of a mixed upper bound.
No strictness is imposed on the inclusions, and length zero is permitted.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlFrontierFiltrationPreservation
    {Y X : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (iota : Ω ≃+* ℂ)
    (T : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω) : Prop where
  additive : T.Additive
  finiteLimits : PreservesFiniteLimits T
  finiteColimits : PreservesFiniteColimits T
  filtration : ∀ (m : ℕ) (G : Fin (m + 1) → sfCommonStageWeilSheaf D l hl Y Ω)
    (φ : ∀ s : Fin m, G s.castSucc ⟶ G s.succ) (weights : Fin m → ℝ),
    IsZero (G 0) → (∀ s, Mono (φ s)) →
    (∀ s, SfIsPunctuallyPureOfWeight D l hl Ω Y iota (cokernel (φ s)) (weights s)) →
      IsZero (T.obj (G 0)) ∧ (∀ s, Mono (T.map (φ s))) ∧
      ∀ s, SfIsPunctuallyPureOfWeight D l hl Ω X iota
        (cokernel (T.map (φ s))) (weights s)
  mixed : ∀ (G : sfCommonStageWeilSheaf D l hl Y Ω) (w : ℝ),
    SfIsMixedOfWeightsAtMost D l hl Ω Y iota G w →
      SfIsMixedOfWeightsAtMost D l hl Ω X iota (T.obj G) w

variable {Y X : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Closed direct image in the constructible Weil heart, specified by its recorded
derived carrier and adjunction unit. This is a presentation of the actual direct
image, not an arbitrary functor or an arbitrary isomorphism of objects.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlFrontierClosedImage (iota : Ω ≃+* ℂ) (i : Y ⟶ X)
    [IsClosedImmersion i.left] where
  functor : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω
  carrier : functor ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ sfModelWeilDerivedPush D l hl Ω i
  adjunction : zlWeilPull D l hl Ω i ⊣ functor
  unit_normalization : ∀ F : sfCommonStageWeilSheaf D l hl X Ω,
    HEq ((ObjectProperty.ι _).map (adjunction.unit.app F))
      ((sfModelWeilDerivedAdjunction D l hl Ω i).unit.app F.obj)
  preservation : ZlFrontierFiltrationPreservation D l hl Ω iota functor

/-- The canonical open adjunction already used to define zlOpenWeilShriek.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
def zlFrontierOpenAdjunction (j : Y ⟶ X) [IsOpenImmersion j.left] :
    zlOpenWeilShriek D l hl Ω j ⊣ zlWeilPull D l hl Ω j :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (zlWeilPull D l hl Ω j)
    (zlOpenWeilPull_isRightAdjoint D l hl Ω j)

/-- The localization sequence uses the actual open counit and closed unit.
The last restriction is i*F; inverse-image composition identifies this with the
restriction to the next member of the frontier.
Source: displayed sequence in source final paragraph
(blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
def ZlFrontierLocalization (iota : Ω ≃+* ℂ) {Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : Y ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]
    (P : ZlFrontierClosedImage D l hl Ω iota i)
    (F : sfCommonStageWeilSheaf D l hl X Ω) : Prop :=
  ∃ h : (zlFrontierOpenAdjunction D l hl Ω j).counit.app F ≫
      P.adjunction.unit.app F = 0,
    (ShortComplex.mk ((zlFrontierOpenAdjunction D l hl Ω j).counit.app F)
      (P.adjunction.unit.app F) h).ShortExact

/-- Gluing along the given finite reduced frontier, including extension of each
component filtration, the canonical short exact sequences and the reduction unit.
No reality hypothesis occurs. Every bound shared by the component filtrations is
retained by the resulting finite filtration.

Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraphs 6--9
(blueprint: lem-zl-reduced-frontier-mixed-gluing).

Proof, following the seven DAG steps:
1. All closed and open subschemes are separated finite type, hence Noetherian.
   Apply lem-zl-immersion-weil-local-behavior to restrictions and
   lem-zl-finite-adic-direct-image to closed images, using
   lem-weil-pbc-closed-immersion-finite. Exact Frobenius pullback induces invertible
   Weil structures on kernels and cokernels in the constructible heart
   (lem-a1-constructible-pullback-t-exact, def-weil-constructible-heart).
2. By lem-zl-extension-by-zero-punctual and lem-zl-finite-pushforward-punctual,
   the two exact image functors preserve each pure quotient with its assigned
   weight. Apply them term by term to the given finite filtrations.
3. Apply prop-sf-open-closed-triangle-all-stages to each complementary pair.
   All three vertices lie in the heart; lem-weil-heart-short-exact-triangles
   gives the displayed short exact sequence with the actual counit and unit.
   These arrows are Weil-equivariant since the inclusions are over k₀.
4. In a short exact sequence 0 → A → B → C → 0, concatenate the subobjects
   of a filtration of A with inverse images of a filtration of C under B → C.
   The successive quotients are the original pure quotients, with the original
   weights (lem-a1-mixed-direct-summand, clause 2); no splitting is needed.
5. Induct on the finite number of clopen components, extending their filtrations
   by zero and splicing. An empty component set gives the zero sheaf on the empty
   open. The composition comparisons of prop-weil-operations identify all restrictions.
6. Induct backwards from the empty last closed term. At each step extend the open
   filtration and push forward the next closed filtration, then splice by step 4.
   There are finitely many steps and every common upper bound is preserved.
7. The reduction is a surjective closed immersion by
   lem-weil-pbc-reduction-universal-homeomorphism. Its open complement is empty,
   so the same localization sequence makes the actual reduction unit a Weil
   isomorphism. Transport the filtration through this unit. A length-zero chain
   forces the reduction, and hence F, to be zero; the empty filtration suffices.
   A finite list of real weights has a real upper bound, using 0 for the empty list.
-/
theorem zlReducedFrontierMixedGluing (iota : Ω ≃+* ℂ)
    (C : ZlReducedFrontier D X) (F : sfCommonStageWeilSheaf D l hl X Ω)
    (mixed : ∀ (a : Fin C.length) (b : Fin (C.count a)),
      ∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω (C.piece a b) iota
        ((zlWeilPull D l hl Ω
          (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w) :
    ∃ (images : ∀ a : Fin C.length,
        ZlFrontierClosedImage D l hl Ω iota (C.inclusion a))
      (reduction : ZlFrontierClosedImage D l hl Ω iota (C.ambient 0)),
      (∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω X iota F w) ∧
      (∀ w : ℝ, (∀ (a : Fin C.length) (b : Fin (C.count a)),
        SfIsMixedOfWeightsAtMost D l hl Ω (C.piece a b) iota
          ((zlWeilPull D l hl Ω
            (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w) →
        SfIsMixedOfWeightsAtMost D l hl Ω X iota F w) ∧
      (∀ (a : Fin C.length) (b : Fin (C.count a)),
        ZlFrontierFiltrationPreservation D l hl Ω iota
          (zlOpenWeilShriek D l hl Ω (C.pieceInclusion a b))) ∧
      (∀ a : Fin C.length,
        ZlFrontierFiltrationPreservation D l hl Ω iota
          (zlOpenWeilShriek D l hl Ω (C.openInclusion a)) ∧
        ZlFrontierLocalization D l hl Ω iota (C.openInclusion a) (C.inclusion a)
          (images a) ((zlWeilPull D l hl Ω (C.ambient a.castSucc)).obj F)) ∧
      IsIso (reduction.adjunction.unit.app F) := by
  sorry

end WeilConjectures
