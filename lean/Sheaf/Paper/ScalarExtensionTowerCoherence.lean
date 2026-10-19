/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CoefficientExtensionReductionModel
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.ScalarExtensionTensorUnit
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Scalar extension on strict quotient models

Source: main-20261015 blueprint, def-weil-derived-pullback-tensor-hom, integral operations;
Stacks Tags 03EL and 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).

## Main definitions

* `Comparisons`: the pure-tensor-normalized comparisons on whole quotient systems.
* `TensorModel`: the representative-normalized completed tensor realization.

## Main statements

* `square`, `unit`, `composition`: strict tower coherence before localization.
* `quotientModels`: the actual quotient representatives and their association formula.
* `scalarExtensionTowerCoherence`: their identification with the canonical integral maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

/-- The sequence site has the small pro-etale site's original size.
Source: Stacks 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) sequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} W

/-- The original small pro-etale site, with object size u+1 and Hom size u.
Source: blueprint size convention (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance (priority := 3000) siteSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable (l : ℕ) [Fact l.Prime]

/-- Signed direct-sum total tensor on the actual quotient sequence site.
Source: blueprint integral operations; Stacks 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev tensor (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)

/-- Cochain quotient systems, with every transition retained in their module structure.
Source: blueprint integral operations; Stacks 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev Complex (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Additivity of the actual ordinary sequence-site scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-scalar-extension-tower-coherence). -/
instance scalarAdditive (W : Scheme.{u}) :
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.Additive :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).additive

/-- Termwise scalar extension through the actual quotient-ring inclusions.
Source: blueprint integral operations; Stacks 06YY
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev scalar (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.mapHomologicalComplex (.up ℤ)

/-- Termwise constant-coefficient pro-etale pullback of entire quotient systems.
Source: blueprint integral operations; Stacks 03D2
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)

/-- The specified scalar-association isomorphism, lifted termwise.
Source: blueprint integral operations, proof step 3; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def kappa {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ⋙ scalar l E L ι X ≅ scalar l E L ι Y ⋙ pull l L f :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarPullback.{u, u} l E L ι f) (.up ℤ)

/-- The scalar action unitor on the same strict quotient complexes.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarUnit (W : Scheme.{u}) : scalar l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit.{u, u} l E W) (.up ℤ)

/-- Successive extension is identified by multiplication of the coefficient factors.
Source: blueprint integral operations, proof step 7
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarComp (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : Scheme.{u}) :
    scalar l E L ι W ⋙ scalar l L F j W ≅ scalar l E F (j.comp ι) W :=
  NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarComposition.{u, u} l E L ι F j W) (.up ℤ)

/-- Tensor generator in the (p,q) summand of the signed direct-sum total.
Source: Stacks 03EK, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
abbrev generator (W : Scheme.{u}) (P Q : Complex l E W) (p q : ℤ)
    (U : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :=
  coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl U x y

/-- The adjunction-unit generator read as a section on the base-change object.
Source: Stacks 03D2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).obj M).val.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)) :=
  integralComparisonSequenceGenerator.{u, u} l E f M n U x

/-- Pure-tensor-normalized tensor comparisons on strict quotient systems.
All components, including their inverses, are chain maps of actual sequence-site modules.
Source: blueprint integral operations, proof steps 3--6; Stacks 03EL and 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure Comparisons where
  /-- Scalar tensor comparison for all coefficient extensions. -/
  sigma : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W
  /-- The comparison sends b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). -/
  sigma_formula : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    (P Q : Complex l A W) (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l B W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    (((sigma A B i W).hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection.{u, u} l A B i W
        (((tensor l A W).obj (P, Q)).X (p + q)) U b
        (generator l A W P Q p q U x y)) =
      generator l B W ((scalar l A B i W).obj P) ((scalar l A B i W).obj Q) p q U
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (P.X p) U b x)
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (Q.X q) U 1 y)
  /-- Finite tensor-pullback comparisons on whole quotient diagrams. -/
  c : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X
  /-- The inverse-image unit formula, extended to arbitrary target coefficients. -/
  c_formula : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l A Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l A X).obj.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))),
    (((c A f).hom.app (P, Q)).f (p + q)).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l A f
        (((tensor l A Y).obj (P, Q)).X (p + q)) n U
        (generator l A Y P Q p q (op (n, U)) x y)) =
      generator l A X ((pull l A f).obj P) ((pull l A f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l A f (P.X p) n U x)
        (pullSection l A f (Q.X q) n U y)

/-- Existence and uniqueness of the two specified chain comparisons.
Source: blueprint integral operations, proof steps 3--4; Stacks 03EL and 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: apply the ordinary sheaf tensor comparison to the geometric inverse image
and to identity inverse image with the actual coefficient map. Its insertion and
multiplication formulas are inverse by balancing. Totalize over all p+q=n. The
comparison preserves bidegrees, so commutes with both differential terms, including
(-1)^p. These formulas commute with horizontal quotient maps and vertical restrictions,
hence are maps on the sequence site. Pure tensors locally generate the sheaf tensor
and its direct-sum total; this proves uniqueness as well as naturality. -/
theorem comparisons_existsUnique : Nonempty (Unique (Comparisons l)) := by
  sorry

/-- Canonical comparisons fixed by their pure-tensor characterization.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def comparisons : Comparisons l := (Classical.choice (comparisons_existsUnique l)).default

/-- The left route around the scalar-extension square, as an actual strict chain iso.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def leftRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerLeft (tensor l E Y) (kappa l E L ι f) ≪≫
    Functor.isoWhiskerRight ((comparisons l).sigma E L ι Y) (pull l L f) ≪≫
    Functor.isoWhiskerLeft ((scalar l E L ι Y).prod (scalar l E L ι Y))
      ((comparisons l).c L f)

/-- The right route, using the same scalar-association maps on both tensor factors.
Source: node proof steps 3--6 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def rightRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerRight ((comparisons l).c E f) (scalar l E L ι X) ≪≫
    Functor.isoWhiskerLeft ((pull l E f).prod (pull l E f)) ((comparisons l).sigma E L ι X) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (kappa l E L ι f) (kappa l E L ι f)) (tensor l L X)

/-- Equality before localization, hence for both directions and all quotient transitions.
Source: blueprint integral operations; Stacks 03EL, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: expand the specified scalar association and the two tensor comparisons on
b tensor (x tensor y). Both composites give (b tensor x) tensor (1 tensor y).
The coefficient square commutes on constant sections, hence after sheafification.
Balancing extends the equality to arbitrary scalars in either factor. Homogeneous
tensors generate each summand and the direct sum total, proving equality of chain
maps. Their inverses are equal because the two maps are isomorphisms. Every map
is a sequence-site module map, so this equality and its inverse retain every
horizontal quotient transition, as well as vertical restrictions. -/
theorem square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftRoute l E L ι f = rightRoute l E L ι f := by
  sorry

private theorem pull_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules.{u, u} l E Y)
    (N : coefficientSequenceModules.{u, u} l E X)
    {a b : (integralComparisonSequencePullback.{u, u} l E f).obj M ⟶ N}
    (h : ∀ (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))),
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x) =
        b.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
          (pullSection l E f M n U x)) : a = b := by
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h V.unop.1 V.unop.2 x

private theorem scalar_unit_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).hom.app M).val.app V
      (integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V s x) =
        s • x := by
  exact (integralComparisonSequenceScalarUnit_existsUnique.{u, u} l E W).exists.choose_spec
    M V s x

private theorem scalar_unit_inv_section (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V x =
      integralComparisonSequenceTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W M V 1 x := by
  have h := scalar_unit_section l E W M V 1 x
  have hh := congrArg
    (fun z ↦ ((integralComparisonSequenceScalarUnit.{u, u} l E W).inv.app M).val.app V z) h
  simpa only [one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.hom_inv_id_app, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh.symm

private theorem pull_section_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : coefficientSequenceModules.{u, u} l E Y} (a : M ⟶ N)
    (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequencePullback.{u, u} l E f).map a).val.app
        (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x) =
      pullSection l E f N n U (a.val.app (op (n, U)) x) := by
  have h := (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).unit.naturality a
  exact (congrArg (fun k ↦ (k.val.app (op (n, U))) x) h).symm

private theorem scalar_pull_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonSequenceScalarPullback.{u, u} l E E (AlgHom.id ℚ_[l] E) f ≪≫
        Functor.isoWhiskerRight (integralComparisonSequenceScalarUnit.{u, u} l E Y)
          (integralComparisonSequencePullback.{u, u} l E f) =
      Functor.isoWhiskerLeft (integralComparisonSequencePullback.{u, u} l E f)
        (integralComparisonSequenceScalarUnit.{u, u} l E X) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi ((integralComparisonSequenceScalarUnit.{u, u} l E X).inv.app
    ((integralComparisonSequencePullback.{u, u} l E f).obj M))).1
  apply pull_hom_ext l E f M
  intro n U x
  dsimp
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_unit_inv_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) (pullSection l E f M n U x)]
  have hk := (integralComparisonSequenceScalarPullback_existsUnique.{u, u}
    l E E (AlgHom.id ℚ_[l] E) f).exists.choose_spec M n U x
  change ((integralComparisonSequencePullback.{u, u} l E f).map
      ((integralComparisonSequenceScalarUnit.{u, u} l E Y).hom.app M)).val.app _
      (((integralComparisonSequenceScalarPullback.{u, u} l E E
        (AlgHom.id ℚ_[l] E) f).hom.app M).val.app _ _) = _
  erw [hk, pull_section_naturality, scalar_unit_section, one_smul]
  symm
  simpa only [Functor.id_obj, one_smul] using scalar_unit_section l E X
    ((integralComparisonSequencePullback.{u, u} l E f).obj M)
    (op (n, (Scheme.proEtaleBaseChange f).obj U)) 1 (pullSection l E f M n U x)

/-- Identity extension is the identity under the actual scalar action unitors.
Source: node proof step 7; Stacks 03EL
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: at identity coefficients the scalar-association map multiplies the inserted
coefficient, exactly the action unitor. On x tensor y the tensor comparison inserts
one in the second factor. Applying the two action unitors gives x tensor y again.
These formulas commute with every quotient and restriction, giving the displayed
identities as strict-system equations. -/
theorem unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (kappa l E E (AlgHom.id ℚ_[l] E) f ≪≫
      Functor.isoWhiskerRight (scalarUnit l E Y) (pull l E f) =
        Functor.isoWhiskerLeft (pull l E f) (scalarUnit l E X)) ∧
    ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y ≪≫
      Functor.isoWhiskerRight (NatIso.prod (scalarUnit l E Y) (scalarUnit l E Y)) (tensor l E Y) =
      Functor.isoWhiskerLeft (tensor l E Y) (scalarUnit l E Y)) := by
  constructor
  · have h := congrArg (fun a ↦ NatIso.mapHomologicalComplex a (.up ℤ))
      (scalar_pull_unit l E f)
    exact h
  · exact scalarExtensionTensorUnit l E Y
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y)
      (fun P Q p q V x y ↦
        (comparisons l).sigma_formula E E (AlgHom.id ℚ_[l] E) Y P Q p q V 1 x y)

/-- Direct and successive scalar comparisons agree before passing to derived limits.
Source: node proof step 7; Stacks 03EL, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: the coefficient map for E to F is the composite of those for E to L and
L to F. The scalar associator sends d tensor (b tensor x) to d*j(b) tensor x.
The two pullback routes therefore multiply exactly these coefficients. For tensor,
both routes send d tensor (b tensor (x tensor y)) to
(d*j(b) tensor x) tensor (1 tensor y). Balancing, sheafification and direct sums
extend these equations. Reductions preserve multiplication and one, so these are
identities of strict systems, including their inverses. -/
theorem composition (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.isoWhiskerRight (kappa l E L ι f) (scalar l L F j X) ≪≫
      Functor.isoWhiskerLeft (scalar l E L ι Y) (kappa l L F j f) ≪≫
      Functor.isoWhiskerRight (scalarComp l E L ι F j Y) (pull l F f) =
      Functor.isoWhiskerLeft (pull l E f) (scalarComp l E L ι F j X) ≪≫
        kappa l E F (j.comp ι) f) ∧
    (Functor.isoWhiskerRight ((comparisons l).sigma E L ι Y) (scalar l L F j Y) ≪≫
      Functor.isoWhiskerLeft ((scalar l E L ι Y).prod (scalar l E L ι Y))
        ((comparisons l).sigma L F j Y) ≪≫
      Functor.isoWhiskerRight (NatIso.prod (scalarComp l E L ι F j Y)
        (scalarComp l E L ι F j Y)) (tensor l F Y) =
      Functor.isoWhiskerLeft (tensor l E Y) (scalarComp l E L ι F j Y) ≪≫
        (comparisons l).sigma E F (j.comp ι) Y) := by
  sorry


/-- A generator read in the legacy restricted finite-tensor tower's exact section type.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def integralTensorGenerator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q).X r).val.obj U) :
    ((((integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P, Q)).obj
      (op n)).X (p + r)).val.obj U :=
  integralOperationsTotalTensorSection.{u, u} l E W n P Q p r U x y

/-- Representative normalization of the completed tensor realization, including its
local tensor formula and its specified Roos comparison.
Source: Stacks 06YS, 07A4, 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv) ≫
        (integralComparisonRoosBridge.{u, u} l E W ρ ((tensor l E W).obj (C, D))).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
        (integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q)

/-- A normalized presentation of the named completed tensor by whole quotient systems.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4 and 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure TensorModel (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) where
  /-- The named completed tensor, realized by the specified system closed tensor. -/
  realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
    S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W
  /-- Normalization at every simultaneous good quotient presentation. -/
  normalization : IsTensorModelNormalized l E W S ρ realization

/-- The actual reduction of a completed pullback, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullbackReduction (W : Bool → Scheme.{u}) (M : CompletedOperations.Models.{u, u} l E W)
    (f : W true ⟶ W false) (K : DerivedCategory (scalarReductionSource.{u, u} l E (W false))) :
    (M.calculus true).reduction.obj ((integralDerivedPullback.{u, u} l E f).obj K) ⟶
      (integralComparisonDerivedSequencePullback.{u, u} l E f).obj
        ((M.calculus false).reduction.obj K) :=
  (M.calculus true).reduction.map ((M.pullback f).realization.hom.app K) ≫
    (M.calculus true).adjunction.counit.app _

/-- The actual coherent scalar-reduction comparison, obtained from its normalized
realization and the coherent counit, with no arbitrary quotient identification.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarReduction (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L W)
    (M : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    SL.reduction.obj ((integralScalarExtension.{u} l E L ι W).obj K) ⟶
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).obj (SE.reduction.obj K) :=
  SL.reduction.map (M.realization.hom.app K) ≫ SL.adjunction.counit.app _

/-- The completed tensor's actual quotient comparison, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def tensorReduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) (M : TensorModel l E W S ρ)
    (K N : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    S.reduction.obj ((integralCompletedTensor.{u, u} l E W).obj (K, N)) ⟶
      S.systemClosed.tensor.obj (S.reduction.obj K, S.reduction.obj N) :=
  S.reduction.map (M.realization.hom.app (K, N)) ≫ S.adjunction.counit.app _

/-- The flat-term K-flat class used for scalar/tensor descent on the sequence site.
Source: Stacks 06YS, 0G7E (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def Good (W : Scheme.{u}) (P : Complex l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) P ∧
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) (P.X n)

/-- Cochain normalization of the system derived scalar/tensor comparison.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def DerivedSigmaModel (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor) :
    Prop :=
  ∀ (P Q : Complex l E W) (hP : Good l E W P) (hQ : Good l E W Q),
    ∃ (hsP : Good l L W ((scalar l E L ι W).obj P))
      (hsQ : Good l L W ((scalar l E L ι W).obj Q)),
    (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
        ((SE.systemTensorModel.iso _ _ _ P Q hP.1 hQ.1).hom) ≫
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      SL.systemClosed.tensor.map (Prod.mkHom
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app P)
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app Q)) =
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app
        ((tensor l E W).obj (P, Q)) ≫
      DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (P, Q)) ≫
      (SL.systemTensorModel.iso _ _ _ _ _ hsP.1 hsQ.1).hom

/-- The derived comparison is determined by the same strict sigma on good representatives.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: flat-term K-flat change of rings works without flatness of the ring map.
It preserves Good and computes scalar derived extension by its universal counit.
Localize sigma on the two resolving subcategories, inserting the normalized tensor
models and scalar counits. Simultaneous K-flat resolutions give naturality on roofs
and independence of resolutions. The localization universal property gives uniqueness
with this cochain model equation. -/
theorem derivedSigma_existsUnique (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :
    ∃! α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor,
      DerivedSigmaModel l E L ι W SE SL α := by
  sorry

/-- The representative-normalized derived tensor scalar comparison on coherent systems.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def derivedSigma (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :=
  (derivedSigma_existsUnique l E L ι W SE SL).exists.choose

/-- The normalized realization models exist for the named completed tensor and scalar functors.
Source: node proof step 8; Stacks 06YS, 07A4, 0941
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: form the strict quotients of one good representative. For tensor take their
signed total tensor; for scalar use the actual quotient inclusions. K-flat change
of rings and closure under total tensor identify these ordinary complexes with
the derived systems. The coefficient-extension reduction model supplies its
normalized coherent counit. Completed-operation substitution identifies the tensor
limit; scalar extension is its defining strict Roos limit. The K-injective-normalized
Roos bridge identifies these with total derived limit. The generator formulas fix
all tower identifications. Universal localization gives the displayed realizations
and their normalization on every simultaneous presentation. -/
theorem realizationModels (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W) :
    ∀ a : Bool, Nonempty (TensorModel l E (W a) (ME.calculus a) (ME.roos a)) ∧
      Nonempty (IntegralComparisonScalarModel.{u, u} l E L ι (W a)
        (ME.calculus a) (ML.roos a)) := by
  sorry

/-- The coherent quotient representatives of the canonical completed comparisons.
Together with square, unit, composition and the normalized cochain definitions, this
identifies the actual strict quotient maps and their derived limits, including ramification.
The displayed equations are in the derived category of whole quotient systems;
applying total derived limit gives exactly the two stated integral comparisons.
Source: main-20261015 blueprint, def-weil-derived-pullback-tensor-hom, integral clause;
Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence).
Proof:
1. Use flat-term K-flat representatives P,Q and K-flat change of rings to form
   P_m,Q_m and their scalar extensions. Total tensor and finite pullback preserve
   this representative class; no flatness of A_m to B_m is used.
2. The balanced association (x tensor a) tensor b maps to x tensor iota(a)*b.
   Its inverse inserts one. The coefficient-extension reduction model identifies
   these simultaneously with P tensor B_m,Q tensor B_m, including every transition,
   and makes their coherent systems normalized.
3. Scalar association defines kappa. Tensor balancing gives its inverse; the
   constant coefficient square commutes on constant sections and on sheafification.
4. The signed total tensor comparison defines sigma and c. They preserve each
   bidegree, so preserve the factor (-1)^p in the second differential summand.
5. Both routes on b tensor (x tensor y) give (b tensor x) tensor (1 tensor y).
   Tensor generators, sheafification and direct sums prove the strict square.
6. Reduction preserves multiplication and one. Thus every map and inverse respects
   every quotient transition, and these are equations of strict systems.
7. For identity coefficients multiplication is the action unitor. For E to L to F,
   the direct coefficient map is the composite. Both successive and direct formulas
   multiply d*j(b), so the unit and transitivity equations hold strictly.
8. Apply coefficient-extension reduction and completed-operation tower substitution
   to these normalized systems. Their defining realizations and the canonical
   coherent counits are precisely pullbackReduction, scalarReduction and
   tensorReduction below. The cochain-normalized derivedSigma and the recorded
   derived kappa are the localizations of the same strict chain maps. Their coherent
   counit squares give the two equations, with the specified completed comparisons.
9. Apply total derived limit. Functoriality preserves the square, inverse, units
   and successive-extension equations. The normalized realizations identify the
   limit maps with the canonical scalarPullbackCompleted and scalarTensorCompleted;
   no interchange with arbitrary inverse limits or uniqueness of arbitrary isos is used.
-/
theorem scalarExtensionTowerCoherence (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (TE : TensorModel l E (W false) (ME.calculus false) (ME.roos false))
    (TL : TensorModel l L (W false) (ML.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M N : sfIntegralConstructibleCategory l E (W false)) :
    ∃ (hF : IsSfDerivedComplete l E (W true) ((integralDerivedPullback.{u, u} l E f).obj M.obj))
      (hT : IsSfDerivedComplete l E (W false)
        ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj))),
    ((ML.calculus true).reduction.map
        (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
      pullbackReduction l L W ML f ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
      (integralComparisonDerivedSequencePullback.{u, u} l L f).map
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj) =
      scalarReduction l E L ι (W true) (ME.calculus true) (ML.calculus true)
          (ML.roos true) SX ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f M.obj) ≫
        (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
          ((ME.calculus false).reduction.obj M.obj)) ∧
    ((ML.calculus false).reduction.map
        (scalarTensorCompleted l E L ι (W false) M.obj N.obj M.property.1 N.property.1 hT).hom ≫
      tensorReduction l L (W false) (ML.calculus false) (ML.roos false) TL
        ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj)
        ((integralScalarExtension.{u} l E L ι (W false)).obj N.obj) ≫
      (ML.calculus false).systemClosed.tensor.map (Prod.mkHom
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY M.obj)
        (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY N.obj)) =
      scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
          (ML.roos false) SY ((integralCompletedTensor.{u, u} l E (W false)).obj (M.obj, N.obj)) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W false)).map
          (tensorReduction l E (W false) (ME.calculus false) (ME.roos false) TE M.obj N.obj) ≫
        (derivedSigma l E L ι (W false) (ME.calculus false) (ML.calculus false)).hom.app
          ((ME.calculus false).reduction.obj M.obj, (ME.calculus false).reduction.obj N.obj)) := by
  sorry

/-- The actual local section of a strict quotient model specified by its evaluation iso.
Source: node proof step 2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def modelSection (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : (P.obj.X i).val.obj U) :
    ((d.direct.obj P).X i).val.obj (op (n, U.unop)) :=
  integralComparisonSequenceSection.{u, u} l L W ((d.direct.obj P).X i) n U
    ((((d.directEvaluation n).inv.app P).f i).val.app U
      (integralScalarTensorSection.{u, u} l E L ι W n (P.obj.X i) U b x))

/-- Scalar extension of the actual E quotient complex is the actual B quotient complex,
with the balanced association formula and all quotient transitions retained.
Source: node proof steps 1--2, 5--6; Stacks 03EL, 0G7E
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: the coefficient-extension reduction model supplies d and d0. Their finite
values are P tensor B_m and P tensor A_m with the actual quotient transitions.
Associate (x tensor a) tensor b to x tensor iota(a)*b; the inverse inserts one.
Balancing proves inverse identities and naturality. These formulas are chain maps
and commute with every quotient transition because coefficient reduction is a ring
map. They therefore glue to the displayed unique strict-system iso. K-flat change
of rings and closure under total tensor justify every derived interpretation.
Apply square to these E quotient representatives. The resulting iso equality is
exactly the stated scalar-extension square, on the actual models, in both directions.
No flatness of A_m to B_m is required, including in ramified extensions. -/
theorem quotientModels {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (A : CoefficientExtensionSystems.{u, u} l E L ι Y)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) Y)
    (M N : sfIntegralConstructibleCategory l E Y)
    (P Q : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (_eP : DerivedCategory.Q.obj P.obj ≅ M.obj) (_eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj) :
    ∃ (d : CoefficientExtensionReductionData.{u, u} l E L ι Y SE SL A)
      (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) Y SE SE A0),
    (∀ K : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory,
      ∃! δ : (scalar l E L ι Y).obj (d0.direct.obj K) ≅ d.direct.obj K,
        ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ)
          (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj (op (n, U.unop)))
          (a : (coefficientSequenceCommRingSheaf l E Y).obj.obj (op (n, U.unop)))
          (x : (K.obj.X i).val.obj U),
          (δ.hom.f i).val.app (op (n, U.unop))
            (integralComparisonSequenceTensorSection l E L ι Y ((d0.direct.obj K).X i)
              (op (n, U.unop)) b
              (modelSection l E E (AlgHom.id ℚ_[l] E) Y SE SE A0 d0 K n i U a x)) =
          modelSection l E L ι Y SE SL A d K n i U
            (((integralComparisonSequenceScalarMap.{u, u} l E L ι Y).hom.app
              (op (n, U.unop))) a * b) x) ∧
    (leftRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) =
      (rightRoute l E L ι f).app (d0.direct.obj P, d0.direct.obj Q) := by
  sorry

end WeilConjectures.ScalarExtensionTower
