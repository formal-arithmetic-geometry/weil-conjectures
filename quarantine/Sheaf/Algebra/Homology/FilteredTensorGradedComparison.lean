/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Convolution tensor and its canonical graded comparison

Source: Stacks Project, More on Algebra, `section-kunneth-spectral-sequence`,
paragraphs preceding Tag 0H7W,
and Tag 0H7Y (blueprint: lem-kun-filtered-tensor-graded-comparison).

The coproduct indexed by `i : ℤ` uses the pair `(i, a - i)` on the diagonal `i + j = a`.
All complexes are unbounded integer cochain complexes. The upstream monoidal tensor on
complexes is `CochainComplex.mapBifunctor` for the module tensor, with the Koszul sign.
The derived tensor is the upstream K-flat derived monoidal tensor; its comparison is the
lax monoidal map of the localization. This is the ordinary tensor of Tag 06Y6, as in
`lem-pc-derived-tensor-second-factor-functor` with identical coefficient rings.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The hypotheses on one filtered complex: finite filtration, flat terms in the underlying,
step and graded complexes, and K-flatness of those same complexes.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W, finite specialization
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
def HasKunnethFiltration (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) : Prop :=
  P.filtration.IsFinite ∧
  (∀ n : ℤ, ObjectProperty.flat (P.obj.X n)) ∧
  (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P.obj ∧
  (∀ i n : ℤ, ObjectProperty.flat
    ((P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
  (∀ i n : ℤ, ObjectProperty.flat ((P.filtration.gradedPiece i).X n)) ∧
  (∀ i : ℤ, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
    (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ)) ∧
  (∀ i : ℤ, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
    (P.filtration.gradedPiece i))

/-- The full category of filtered complexes satisfying the hypotheses of the comparison.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
abbrev KunnethFilteredComplex (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory (HasKunnethFiltration (R := R))

/-- The diagonal family of tensors of filtration steps.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethTensorSteps
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⊗
    (Q.filtration.step (a - i) : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The diagonal family of tensors of graded complexes.
Source: Stacks, `section-kunneth-spectral-sequence`, graded comparison before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethTensorGraded
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  P.filtration.gradedPiece i ⊗ Q.filtration.gradedPiece (a - i)

/-- The sum of the tensor inclusions, whose image is the convolution step.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolutionArrow
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a : ℤ) :
    (∐ kunnethTensorSteps P Q a) ⟶ P.obj ⊗ Q.obj :=
  Sigma.desc (fun i ↦ (P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow)

/-- Successive convolution steps are nested.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison).

Proof: the summand indexed by `(i,j)` on diagonal `a+1` factors through the summand
`(i-1,j)` on diagonal `a`, using the decreasing inclusion of the first filtration.
The coproduct universal property then gives containment of images. This is Step 2
of the node, and does not use flatness, K-flatness or finiteness. -/
theorem kunnethConvolution_decreasing
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a : ℤ) :
    imageSubobject (kunnethConvolutionArrow P Q (a + 1)) ≤
      imageSubobject (kunnethConvolutionArrow P Q a) := by
  sorry

/-- The actual convolution filtration: the image of the sum of tensor inclusions.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolution
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) :
    DecreasingFiltration (P.obj ⊗ Q.obj) where
  F a := imageSubobject (kunnethConvolutionArrow P Q a)
  F_succ_le a := kunnethConvolution_decreasing P Q a

/-- The tensor complex equipped with its convolution filtration.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolutionObject
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) :
    FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ⟨P.obj ⊗ Q.obj, kunnethConvolution P Q⟩

/-- The ordinary graded projection, the cokernel of the next-step inclusion.
Source: Stacks, Homology, Tag 012K
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable abbrev kunnethGradedProjection
    (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      P.filtration.gradedPiece i :=
  P.filtration.complexQuotientπ i (i + 1) (Int.le_add_one le_rfl)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The diagonal family of ordinary K-flat derived tensors in `D(R)`.
Source: Stacks, Section `section-kunneth-spectral-sequence` and Tag 06Y6
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethDerivedGraded
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (P.filtration.gradedPiece i) ⊗
    DerivedCategory.Q.obj (Q.filtration.gradedPiece (a - i))

/-- The canonical convolution/graded comparison, natural in both filtered complexes.
Source: Stacks, More on Algebra, `section-kunneth-spectral-sequence`
before Tag 0H7W and Tag 0H7Y
(blueprint: lem-kun-filtered-tensor-graded-comparison).

The maps `l` are fixed by the tensor inclusion equation; the equation for `e` says exactly
that tensors of residue classes map to the residue class of tensors of representatives.
The equations for `c` and `cgr` fix the derived tensor comparisons. The localized
complex sum, with the displayed coprojections, is a coproduct of derived tensors. Thus
`(DerivedCategory.Q.mapIso (e P Q a)).symm` is the displayed derived graded comparison.
Naturality and identity/composition
laws are simultaneous in both variables. The last clause is preservation of quasi-isomorphisms
on every graded complex.

Proof (the seven DAG steps):
1. Tensor commutes with direct sums and is right exact. Flat modules are closed under tensor,
   direct sums and extensions. Apply `lem-weil-pbc-flat-quotient-tensor-injective` and induct
   on the finite graded layers to show that the quotients by filtration steps are flat.
2. The convolution formula is decreasing by `kunnethConvolution_decreasing`. Lower bounds
   A,B give the full tensor at A+B, and upper zero bounds C,D give zero at C+D-1.
3. Project the tensor to the tensor products of quotients by the next filtration steps.
   On the diagonal step tensors, all off-diagonal components vanish. Flat quotient tensor
   injectivity identifies the diagonal images with tensors of graded pieces. Their kernels
   are sums of tensors in which one factor is in its next filtration step.
4. The resulting surjection from the convolution step to the diagonal sum has kernel the
   next convolution step. Descend to the quotient. Its inverse has exactly the displayed
   representative equation for `e`.
5. Tensor/direct-sum closure proves flatness of underlying and graded terms. Finite extension
   induction gives flatness of step terms. Associativity gives K-flatness of the tensor and
   graded complexes. Tensor the step/graded short exact sequences with an acyclic complex;
   flat graded terms preserve exactness, and `lem-weil-pbc-complex-ses-homology-long-exact`
   gives K-flatness of the steps by finite descending induction.
6. Tensoring filtered maps preserves convolution steps. On representatives the naturality
   square sends x tensor y to u(x) tensor v(y). Apply the fixed-second-factor functor of
   `lem-pc-derived-tensor-second-factor-functor` with A=R and identity K-flat resolutions.
   It identifies ordinary and derived tensors by the localization's monoidal comparison.
   Localizing `e` gives the derived comparison. Its target is the coproduct of derived
   tensors: the localized complex sum has the universal property with the specified legs.
7. Under `e`, the graded tensor map is the sum of tensors of the two graded maps. Factor
   each as u tensor identity followed by identity tensor v. K-flatness and clauses (1),(3)
   of `lem-pc-derived-tensor-second-factor-functor` make both quasi-isomorphisms. Cohomology
   commutes with the finite nonzero diagonal sum, proving the final assertion. All maps
   respect identities and composition by their representative characterizations. -/
theorem filteredTensor_graded_comparison :
    ∃ (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
          kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
      (l : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
          kunnethTensorSteps P.obj Q.obj a i ⟶
            ((kunnethConvolution P.obj Q.obj).step a :
              CochainComplex (ModuleCat.{u} R) ℤ))
      (e : ∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
          (∐ kunnethTensorGraded P.obj Q.obj a) ≅
            (kunnethConvolution P.obj Q.obj).gradedPiece a)
      (c : ∀ P Q : KunnethFilteredComplex R,
          DerivedCategory.Q.obj P.obj.obj ⊗ DerivedCategory.Q.obj Q.obj.obj ≅
            DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj))
      (cgr : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
          kunnethDerivedGraded P.obj Q.obj a i ≅
            DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i)),
      (∀ P Q : KunnethFilteredComplex R,
        HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj)) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        l P Q a i ≫ ((kunnethConvolution P.obj Q.obj).step a).arrow =
          (P.obj.filtration.step i).arrow ⊗ₘ (Q.obj.filtration.step (a - i)).arrow) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (kunnethGradedProjection P.obj i ⊗ₘ kunnethGradedProjection Q.obj (a - i)) ≫
            Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i ≫ (e P Q a).hom =
          l P Q a i ≫ kunnethGradedProjection (kunnethConvolutionObject P.obj Q.obj) a) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
        (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        CategoryTheory.Limits.Sigma.map
            (f := kunnethTensorGraded P.obj Q.obj a)
            (g := kunnethTensorGraded P'.obj Q'.obj a)
            (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
            FilteredObject.gradedMapSteps g.hom (a - i)) ≫ (e P' Q' a).hom =
          (e P Q a).hom ≫ FilteredObject.gradedMapSteps (m P P' Q Q' f g) a) ∧
      (∀ P Q : KunnethFilteredComplex R,
        m P P Q Q (𝟙 P) (𝟙 Q) = 𝟙 _) ∧
      (∀ (P P' P'' Q Q' Q'' : KunnethFilteredComplex R)
          (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q''),
        m P P'' Q Q'' (f ≫ f') (g ≫ g') =
          m P P' Q Q' f g ≫ m P' P'' Q' Q'' f' g') ∧
      (∀ P Q : KunnethFilteredComplex R,
        (c P Q).hom = Functor.LaxMonoidal.μ DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (cgr P Q a i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
          (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        Nonempty (IsColimit (Cofan.mk
          (DerivedCategory.Q.obj (∐ kunnethTensorGraded P.obj Q.obj a))
          (fun i ↦ (cgr P Q a i).hom ≫ DerivedCategory.Q.map
            (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i))))) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        DerivedCategory.Q.map (FilteredObject.gradedMapSteps (m P P' Q Q' f g) a) ≫
            (DerivedCategory.Q.mapIso (e P' Q' a)).inv =
          (DerivedCategory.Q.mapIso (e P Q a)).inv ≫ DerivedCategory.Q.map
            (CategoryTheory.Limits.Sigma.map
            (f := kunnethTensorGraded P.obj Q.obj a)
            (g := kunnethTensorGraded P'.obj Q'.obj a)
            (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
              FilteredObject.gradedMapSteps g.hom (a - i)))) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
        (∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom i)) →
        (∀ j : ℤ, QuasiIso (FilteredObject.gradedMapSteps g.hom j)) →
          ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps (m P P' Q Q' f g) a)) := by
  sorry

end CochainComplex
