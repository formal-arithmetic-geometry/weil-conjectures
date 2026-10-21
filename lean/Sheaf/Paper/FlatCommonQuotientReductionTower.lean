/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.CommonQuotientTowerPresentation
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Flat common-quotient reduction, with strict towers and quotient cones

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-cohomology.tex, Tags 06YS, 06YT, 06YY; sites-modules.tex, Tag 03EK.
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower).

The quotient ideals are the kernel ideal sheaves in the common-quotient presentation.
Both derived scalar extensions are the existing universal cochain models. The ordinary
comparisons, transitions and cones are characterized by their actual sheafified tensor
sections. Scalar extension in the existing library writes the scalar first: `s ⊗ p`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v r wR wB wS wA wT
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules.CommonQuotientReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The recorded module category, with no change of encoding or coefficient universe.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev Modules (A : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J A)

/-- Actual restriction of scalars, used also termwise on complexes.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev restriction {A T : Sheaf J CommRingCat.{r}} (a : A ⟶ T) :
    Modules T ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- A pure scalar-extension section in the prescribed ordinary presentation of a
cochain derived-change-of-rings model. This is precisely the sheafification-unit
image of the balanced tensor, transported along the model's object equality.
Source: Stacks 03EK (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
def scalarSection {A T : Sheaf J CommRingCat.{r}} {a : A ⟶ T}
    [HasDerivedCategory.{wA} (Modules A)] [HasDerivedCategory.{wT} (Modules T)]
    (F : DerivedChangeOfRingsCochainModel a) (M : Modules A)
    (U : Cᵒᵖ) (s : T.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x))

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Modules (D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

/-- The actual `S_n`-linear complex obtained by reduction over `R`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((a n).E.mapHomologicalComplex (.up ℤ)).obj
    (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The actual `S_n`-linear complex obtained by reduction over `B`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((b n).E.mapHomologicalComplex (.up ℤ)).obj P

/-- The levels of the first strict tower, restricted to `R`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (leftComplex D a n P)

/-- The levels of the second strict tower, also restricted to `R` through `q_n`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (rightComplex D b n P)

/-- The full normalized comparison specification. All maps below are fixed by pure
sections or by localization/counit compatibility; in particular the strict cones
are the quotient cones, not arbitrary morphisms with the same vertices.

Source: Stacks 099L, 03EK and 06YY
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
structure Comparison where
  /-- Restriction on derived categories. -/
  res : DerivedCategory (Modules B) ⥤ DerivedCategory (Modules R)
  /-- Its prescribed localization of termwise restriction. -/
  resFactors : DerivedCategory.Q ⋙ res ≅
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Ordinary, `S_n`-linear, natural comparisons on cochain complexes. -/
  ordinary : ∀ n : ℕ,
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙
      (a n).E.mapHomologicalComplex (.up ℤ) ≅ (b n).E.mapHomologicalComplex (.up ℤ)
  /-- The ordinary comparison sends `s ⊗ p` to the same pure section. -/
  ordinary_sections : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ) (i : ℤ)
    (U : Cᵒᵖ) (s : (D.S.obj (op n)).obj.obj U) (p : (P.X i).val.obj U),
    (((ordinary n).hom.app P).f i).val.app U
      (scalarSection (a n) ((restriction φ).obj (P.X i)) U s p) =
        scalarSection (b n) (P.X i) U s p
  /-- The induced natural derived comparisons. -/
  derived : ∀ n : ℕ, res ⋙ (a n).T ≅ (b n).T
  /-- Their canonical representative normalization, using the existing derived counits. -/
  computes : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
      (derived n).hom.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P =
        (a n).T.map (resFactors.hom.app P) ≫
          (a n).ε.app (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((ordinary n).hom.app P)
  /-- One flat-term K-flat representative works simultaneously at every level. -/
  representatives : ∀ M : DerivedCategory (Modules B),
    ∃ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ M)
  /-- The strict tower comparisons, their transition formulas and their quotient cones. -/
  strict : ∀ P : CochainComplex (Modules B) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    ∃ (tL : ∀ n : ℕ, leftLevel D a (n + 1) P ⟶ leftLevel D a n P)
      (tR : ∀ n : ℕ, rightLevel D b (n + 1) P ⟶ rightLevel D b n P)
      (e : Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL ≅
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR)
      (ηL : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL)
      (ηR : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR),
      (∀ n : ℕ, e.hom.app (op n) =
        ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).map
          ((ordinary n).hom.app P)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tL n).f i).val.app U
          (scalarSection (a (n + 1)) ((restriction φ).obj (P.X i)) U s p) =
            scalarSection (a n) ((restriction φ).obj (P.X i)) U
              ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tR n).f i).val.app U (scalarSection (b (n + 1)) (P.X i) U s p) =
          scalarSection (b n) (P.X i) U
            ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        (((ηL.app (op n)).f i).val.app U p =
          scalarSection (a n) ((restriction φ).obj (P.X i)) U 1 p) ∧
        (((ηR.app (op n)).f i).val.app U p = scalarSection (b n) (P.X i) U 1 p)) ∧
      (ηL ≫ e.hom = ηR) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((ηL.app (op n)).f i)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        ((ηL.app (op n)).f i).val.app U p = 0 ↔
          D.locallyInIdealProduct n ((restriction φ).obj (P.X i)) U p)

/-- Flat common-quotient reduction gives the canonical derived comparison together
with its ordinary representative, strict quotient-transition and cone normalizations.

Source: Stacks 099L (section-derived-completion-noetherian), 03EK, 06YS, 06YT and 06YY
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower).

Proof:
1. Resolve a representative of M over B by a K-flat complex P with flat terms (06YS).
Flat scalar restriction makes Res P K-flat over R with flat terms; restriction leaves
underlying abelian sheaves unchanged, so it preserves the resolution quasi-isomorphism.
Thus a single P computes every reduction, with no compatible choices of resolutions.
2. The sheafified balanced maps p tensor r-bar to [rp], and [p] to p tensor 1,
identify Res P tensor_R S_n with P/I_n P. They are mutually inverse by balancing;
sections of the quotient coefficient ring are lifted locally, never globally (03EK).
3. Repeat over B. The submodule (I_n B)P equals I_n P: a generator (φ(j)b)p equals
φ(j)(bp), and the reverse inclusion takes b=1. Both tensors are therefore the same
quotient. The comparison and its inverse preserve every pure section s tensor p.
4. Apply this calculation in every degree. Both differential composites send s tensor p
to s tensor d(p); both naturality composites send it to s tensor h(p). Pure sections
locally generate the sheaf tensor, so these are actual equalities of sheaf morphisms.
5. The adjacent quotient-transition squares send s tensor p to t_n(s) tensor p.
Restrict to R and assemble them with Functor.ofOpSequence. Their components are
isomorphisms, hence give a strict tower isomorphism. Quotient cones send p to 1 tensor p;
the same calculation proves their transition compatibility and equality under the
comparison. The quotient maps are epimorphisms, with kernel locally I_n P, expressing
both identifications with the actual sheaf quotient, including its quotient projection.
6. The derived-change-of-rings counits compute both sides on this same P (06YT, 06YY).
The ordinary comparison is natural on complexes and inverts quasi-isomorphisms on the
flat-term K-flat resolving class. Descend it and its inverse by the universal resolving-
class construction (06XN). This gives the natural derived isomorphism and the displayed
counit normalization, proving independence of the resolution. Restriction itself is
localized from its exact termwise functor. -/
theorem nonempty_comparison
    (hflat : IsFlatOnSite (R := R)
      ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J B)))) :
    Nonempty (Comparison D a b) := by
  sorry

end SheafOfModules.CommonQuotientReduction
