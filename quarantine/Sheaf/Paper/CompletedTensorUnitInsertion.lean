/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.CategoryTheory.Monoidal.Functor
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Completion-unit insertions and coherent completed inverse image

Source: Stacks Project, algebraization.tex, Tags 099A and 099G; proetale.tex,
Tags 099M and 099N; sites-cohomology.tex, Tags 07A4 and 0FPT
(blueprint: lem-pur-completed-tensor-unit-insertion).

The helpers only spell out the constraints in proof steps 5 and 7--9. The theorem
uses the published constant-coefficient derived categories, quotient-tower completion,
and completion units. Ordinary tensor and its signed constraints are the published
native derived tensor structure. Its inverse-image tensor comparison is specified
on flat-term K-flat representatives, rather than replaced by an arbitrary isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u vB uB vE uE

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.ConstantCompletion

section Constraints

variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [SymmetricCategory B]

/-- The left insertion of the actual reflector unit, after tensor and completion.
Source: Stacks 099G, proof steps 1--2
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def tensorInsertLeft (T : B ⥤ B) (η : 𝟭 B ⟶ T) (V W : B) :=
  T.map (η.app V ⊗ₘ 𝟙 W)

/-- The right insertion of the actual reflector unit, after tensor and completion.
Source: Stacks 099G, proof step 2
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def tensorInsertRight (T : B ⥤ B) (η : 𝟭 B ⟶ T) (V W : B) :=
  T.map (𝟙 V ⊗ₘ η.app W)

/-- The completed tensor constraints, with their exact insertion normalization.
A monoidal structure supplies naturality, the pentagon and triangle; a symmetric
structure supplies involutivity and both hexagons. The equations below fix their
underlying arrows, including both unitors, on the full complete subcategory.
Source: Stacks 099G, proof steps 5--6
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedConstraintModel (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hLeft : ∀ V W : B, IsIso (tensorInsertLeft T η V W))
    (hRight : ∀ V W : B, IsIso (tensorInsertRight T η V W))
    (hη : ∀ V : P.FullSubcategory, IsIso (η.app V.obj))
    (m : MonoidalCategory P.FullSubcategory)
    (s : @SymmetricCategory P.FullSubcategory _ m) : Prop :=
  letI := hLeft
  letI := hRight
  letI (V : P.FullSubcategory) := hη V
  letI := m
  letI := s
  (∀ V W : P.FullSubcategory, (V ⊗ W).obj = T.obj (V.obj ⊗ W.obj)) ∧
  (∀ (V W V' W' : P.FullSubcategory) (f : V ⟶ V') (g : W ⟶ W'),
    HEq (f ⊗ₘ g).hom (T.map (f.hom ⊗ₘ g.hom))) ∧
  (𝟙_ P.FullSubcategory).obj = T.obj (𝟙_ B) ∧
  (∀ V W Z : P.FullSubcategory,
    HEq (α_ V W Z).hom.hom
      (inv (tensorInsertLeft T η (V.obj ⊗ W.obj) Z.obj) ≫
        T.map (α_ V.obj W.obj Z.obj).hom ≫
          tensorInsertRight T η V.obj (W.obj ⊗ Z.obj))) ∧
  (∀ V W : P.FullSubcategory,
    HEq (β_ V W).hom.hom (T.map (β_ V.obj W.obj).hom)) ∧
  (∀ V : P.FullSubcategory,
    HEq (λ_ V).hom.hom
      (inv (tensorInsertLeft T η (𝟙_ B) V.obj) ≫
        T.map (λ_ V.obj).hom ≫ inv (η.app V.obj))) ∧
  (∀ V : P.FullSubcategory,
    HEq (ρ_ V).hom.hom
      (inv (tensorInsertRight T η V.obj (𝟙_ B)) ≫
        T.map (ρ_ V.obj).hom ≫ inv (η.app V.obj)))

variable {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [SymmetricCategory E]

/-- The completed inverse image, using fullness and the reflector's complete output.
Source: Stacks 099N, proof step 3
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def completeInverse (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T' : E ⥤ E) (hT' : ∀ V : E, P' (T'.obj V)) :
    P.FullSubcategory ⥤ P'.FullSubcategory :=
  ObjectProperty.lift P' (P.ι ⋙ L ⋙ T') (fun V ↦ hT' (L.obj V.obj))

/-- Associativity, symmetry and both tensor-unit equations for the completed comparison.
The oplax monoidal laws assert the actual associativity and unitor equations. Its
cotensorator and unit are exactly the separately normalized completed isomorphisms;
the last equation is compatibility with the specified completed symmetry.
Source: Stacks 099G and 07A4, proof steps 8--9
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedPullbackCoherence (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E) (hT' : ∀ V : E, P' (T'.obj V))
    (μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T')
    (ec : (L ⋙ T').obj (T.obj (𝟙_ B)) ≅ T'.obj (𝟙_ E))
    (m : MonoidalCategory P.FullSubcategory)
    (m' : MonoidalCategory P'.FullSubcategory)
    (s : @SymmetricCategory P.FullSubcategory _ m)
    (s' : @SymmetricCategory P'.FullSubcategory _ m') : Prop :=
  letI := m
  letI := m'
  letI := s
  letI := s'
  ∃ o : (completeInverse P P' L T' hT').OplaxMonoidal,
    (∀ V W : P.FullSubcategory,
      HEq (o.δ V W).hom
        (μc.hom.app (V.obj, W.obj))) ∧
    HEq (o.η).hom ec.hom ∧
    (∀ V W : P.FullSubcategory,
      o.δ V W ≫
          (β_ ((completeInverse P P' L T' hT').obj V)
            ((completeInverse P P' L T' hT').obj W)).hom =
        (completeInverse P P' L T' hT').map (β_ V W).hom ≫
          o.δ W V)

/-- All three insertions and the unique normalized coherent completed comparison.
The completed constraints are specified by `CompletedConstraintModel`, so coherence
refers to completion of the ordinary constraints, including completion of the unit.
Source: Stacks 099G, 099M, 099N and 07A4, proof steps 1--9
(blueprint: lem-pur-completed-tensor-unit-insertion). -/
def CompletedTensorAssertions (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E)
    (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (μ : tensor B ⋙ L ≅ (L.prod L) ⋙ tensor E) : Prop :=
  ∃ (_hT : ∀ V : B, P (T.obj V)) (hT' : ∀ V : E, P' (T'.obj V))
    (hη : ∀ V : P.FullSubcategory, IsIso (η.app V.obj))
    (hη' : ∀ V : P'.FullSubcategory, IsIso (η'.app V.obj))
    (hLeft : ∀ V W : B, IsIso (tensorInsertLeft T η V W))
    (hRight : ∀ V W : B, IsIso (tensorInsertRight T η V W))
    (hLeft' : ∀ V W : E, IsIso (tensorInsertLeft T' η' V W))
    (hRight' : ∀ V W : E, IsIso (tensorInsertRight T' η' V W)),
    (∀ V : B, IsIso (T'.map (L.map (η.app V)))) ∧
    ∃ (e : L.obj (𝟙_ B) ≅ 𝟙_ E)
      (μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T')
      (ec : (L ⋙ T').obj (T.obj (𝟙_ B)) ≅ T'.obj (𝟙_ E)),
      (∀ V : B, μ.hom.app (𝟙_ B, V) ≫ (e.hom ⊗ₘ 𝟙 (L.obj V)) ≫
        (λ_ (L.obj V)).hom = L.map (λ_ V).hom) ∧
      (∀ V : B, μ.hom.app (V, 𝟙_ B) ≫ (𝟙 (L.obj V) ⊗ₘ e.hom) ≫
        (ρ_ (L.obj V)).hom = L.map (ρ_ V).hom) ∧
      (∀ V W : B,
        T'.map (L.map (η.app (V ⊗ W))) ≫ μc.hom.app (V, W) =
          T'.map (μ.hom.app (V, W) ≫ (η'.app (L.obj V) ⊗ₘ η'.app (L.obj W)))) ∧
      (∀ ν : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T',
        (∀ V W : B,
          T'.map (L.map (η.app (V ⊗ W))) ≫ ν.hom.app (V, W) =
            T'.map (μ.hom.app (V, W) ≫ (η'.app (L.obj V) ⊗ₘ η'.app (L.obj W)))) →
          ν = μc) ∧
      T'.map (L.map (η.app (𝟙_ B))) ≫ ec.hom = T'.map e.hom ∧
      ∃ (m : MonoidalCategory P.FullSubcategory)
        (m' : MonoidalCategory P'.FullSubcategory)
        (s : @SymmetricCategory P.FullSubcategory _ m)
        (s' : @SymmetricCategory P'.FullSubcategory _ m'),
        CompletedConstraintModel P T η hLeft hRight hη m s ∧
        CompletedConstraintModel P' T' η' hLeft' hRight' hη' m' s' ∧
        CompletedPullbackCoherence P P' L T T' hT' μc ec m m' s s'

end Constraints

section ConstantSites

variable {C E : Type u} [SmallCategory C] [SmallCategory E]
  (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
  (A : Type u) [CommRing A]

/-- The published ordinary derived monoidal structure at the standard localization.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedMonoidal : MonoidalCategory (D (constant JC A)) :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  RingedDerivedNative.monoidal.{u, u, u} JC (constant JC A)

/-- Its published Koszul symmetry, with precisely that monoidal structure.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedSymmetric :
    @SymmetricCategory (D (constant JC A)) _ (constantDerivedMonoidal JC A) :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  RingedDerivedNative.symmetric.{u, u, u} JC (constant JC A)

/-- The ordinary tensor bifunctor, transparently from the published monoidal structure.
Source: Stacks 0FPT (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev constantDerivedTensor : D (constant JC A) × D (constant JC A) ⥤ D (constant JC A) :=
  @tensor (D (constant JC A)) _ (constantDerivedMonoidal JC A)

variable {JC JD A}
  {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}

/-- The existing pure-tensor-normalized ordinary pullback comparison data, specialized
only to the actual inverse image of the constant ring and its canonical ring map.
Source: Stacks 03EL and 07A4 (blueprint: lem-pur-completed-tensor-unit-insertion). -/
abbrev ConstantTensorData (F : InverseImageData L) (A : Type u) [CommRing A] :=
  SheafOfModules.CanonicalRingedTensorComparison (constant JC A) (constant JD A)
    (F.rings.obj (constant JC A)) L (F.algebra (constant JC A)) (constantMap F A)
    (pull F (constantMap F A)) (fun _ ↦ rfl)

/-- The Tag 07A4 normalization of ordinary derived inverse-image tensor comparison.
The equation is written without inverting a derived comparison at a non-K-flat object.
It uses the canonical cochain comparison, oriented from the tensor of the pullbacks
into the pullback of the tensor. Both source factors range over all flat-term K-flat
complexes; the images are again K-flat. This fixes the whole natural comparison by
fully faithful restriction to representatives.
Source: Stacks 07A4 (blueprint: lem-pur-completed-tensor-unit-insertion). -/
def ConstantTensorNormalization (F : InverseImageData L)
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A]
    (k : ConstantTensorData F A)
    (μ : constantDerivedTensor JC A ⋙ (derivedPull F V adj (constantMap F A)).functor ≅
      (((derivedPull F V adj (constantMap F A)).functor).prod
        ((derivedPull F V adj (constantMap F A)).functor)) ⋙ constantDerivedTensor JD A) :
    Prop :=
  letI := HasDerivedCategory.standard (Mod (constant JC A))
  letI := HasDerivedCategory.standard (Mod (constant JD A))
  ∀ (P Q : Cx (constant JC A))
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := constant JC A) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (R := constant JC A) Q),
    (∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlat (Q.X n)) →
    ∃ (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := constant JD A)
        (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj P))
      (_hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := constant JD A)
        (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj Q)),
      (derivedPull F V adj (constantMap F A)).functor.map
          (RingedDerivedNative.tensorIso.{u, u, u} JC (constant JC A) P Q (Or.inl hP)).hom ≫
        μ.hom.app ((CategoryTheory.ConstantCompletion.Q (constant JC A)).obj P,
          (CategoryTheory.ConstantCompletion.Q (constant JC A)).obj Q) ≫
        (constantDerivedTensor JD A).map
          (Prod.mkHom ((derivedPull F V adj (constantMap F A)).comparison.app P)
            ((derivedPull F V adj (constantMap F A)).comparison.app Q)) ≫
        (RingedDerivedNative.tensorIso.{u, u, u} JD (constant JD A)
          (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj P)
          (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj Q)
          (Or.inl hP')).inv ≫
        (CategoryTheory.ConstantCompletion.Q (constant JD A)).map
          (k.total (constant JC A) (constant JD A) (F.rings.obj (constant JC A))
            L (F.algebra (constant JC A)) (constantMap F A) (pull F (constantMap F A))
            (fun _ ↦ rfl) P Q) =
        (derivedPull F V adj (constantMap F A)).comparison.app
          ((WeilConjectures.coefficientTotalTensor.{u, u, u} JC (constant JC A)).obj (P, Q))

end ConstantSites

/-- Completion units become tensor and pullback isomorphisms, and determine the
unique coherent completed tensor comparison. There is no perfectness assumption on
any positive quotient A/I^(n+1), and both derived inputs are unbounded and arbitrary.

Source: Stacks Project, algebraization.tex, Tags 099A and 099G; proetale.tex,
Tags 099M and 099N; sites-cohomology.tex, Tags 07A4 and 0FPT
(blueprint: lem-pur-completed-tensor-unit-insertion).

Proof (the node's nine steps):
1. For complete Z, RHom(W,Z) is complete by lem-sf-ringed-rhom-derived-complete.
   The tensor-Hom bijections of lem-sf-ringed-derived-closed-symmetric-monoidal
   and reflection from lem-sp-completed-pullback-adjunction identify precomposition
   by C(eta_V tensor 1) with the bijection Hom(CV,RHom(W,Z)) -> Hom(V,RHom(W,Z)).
   Testing Z at source and target gives a two-sided inverse.
2. The same argument applies to every arrow inverted by C, even after tensoring
   with an arbitrary object. Symmetry gives the other tensor insertion. Naturality
   follows from eta and tensor; both units can therefore be inserted together.
3. Put F=C_X L. Direct image preserves completeness by
   lem-sp-completed-pullback-adjunction. The ordinary and completed adjunctions
   identify Hom(F C_Y V,Z) -> Hom(FV,Z) with the reflection bijection into RZ.
   Hence F(eta_V) is invertible, and F inverts all C_Y equivalences.
4. Normalize ordinary mu by the localized cochain tensor comparison of Tag 07A4.
   lem-pur-cochain-pullback-tensor-coherence gives its reassociation, signed symmetry
   and both action-unit equations. Fully faithful descent on flat-term K-flat
   representatives (lem-weil-pbc-site-derived-tensor-descent) gives the equations on
   all derived inputs, as in lem-weil-pbc-pullback-tensor-canonical-shift-unit.
5. On the full complete subcategory define tensor by C(V tensor W) and unit by C1.
   Define the associator as inverse left insertion, C of the ordinary associator,
   then right insertion. Symmetry is C of the ordinary symmetry. Each unitor is
   inverse unit insertion, C of the ordinary unitor, then inverse eta of the
   complete input. These are exactly CompletedConstraintModel's formulas.
6. Insert eta at every internal vertex of a parenthesized tensor expression. All
   such insertions are invertible by step 2. After precomposition by these maps,
   the completed pentagon, triangle, involution and hexagons become C of the
   ordinary equations. Cancel the insertion isomorphisms.
7. Set a_V=F(eta_V) and b=C_X(mu followed by eta_LV tensor eta_LW).
   Both are invertible, so mu_c=b a_(V tensor W)^(-1) is a natural isomorphism.
   Its normalization is mu_c a=b; this equation forces uniqueness.
8. For associativity precompose with the two insertion isomorphisms from the
   ordinary threefold tensor. Substitute mu_c a=b and the completed associator
   formula. Naturality of eta cancels the insertions and leaves ordinary
   associativity of mu from step 4. Cancel the source isomorphism.
9. The same substitution for symmetry leaves the ordinary signed symmetry square.
   Define e_c=C_X(e) a_1^(-1). For each unit equation precompose with F of the
   ordinary unit insertion followed by a. Substitution of the completed unitor
   formula and mu_c a=b cancels eta, leaving the ordinary left or right unit
   equation of step 4. No limit is pulled through inverse image, and no quotient
   is required to be perfect. -/
theorem completedTensorUnitInsertion
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (F : InverseImageData L) (k : ConstantTensorData F A)
      (μ : constantDerivedTensor JC A ⋙ (derivedPull F V adj (constantMap F A)).functor ≅
        (((derivedPull F V adj (constantMap F A)).functor).prod
          ((derivedPull F V adj (constantMap F A)).functor)) ⋙ constantDerivedTensor JD A),
      ConstantTensorNormalization F V adj A k μ ∧
      @CompletedTensorAssertions (D (constant JC A)) _
        (constantDerivedMonoidal JC A) (constantDerivedSymmetric JC A)
        (D (constant JD A)) _
        (constantDerivedMonoidal JD A) (constantDerivedSymmetric JD A)
        (IsComplete (quotient JC A I 0)) (IsComplete (quotient JD A I 0))
        (derivedPull F V adj (constantMap F A)).functor
        (completion JC A I false) (completion JD A I false)
        (completionUnit JC A I false) (completionUnit JD A I false) μ := by
  sorry

end CategoryTheory.ConstantCompletion
