/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module
public import Sheaf.Paper.AdicLisseModule
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
/-! # Data for completed constant realization

Source: Stacks Tags 093J--093M and 06YU.
(blueprint: def-weil-pbc-completed-constant-realization-data).

The constructions and interfaces are moved verbatim from
`CompletedConstantFiniteComplexRealization` so that the module and complex calculations
can be stated independently without an import cycle.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
/-- Abelian sheafification at the specified coefficient size, transported through the
small site model. Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
instance completedConstantAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
/-- The locally bijective description at exactly the same coefficient size.
Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
instance completedConstantAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1}
    _
/-- The standard localization, used uniformly for the representative calculations.
Source: Stacks Tag 05RU
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantDerived (D : Type v) [Category.{w} D] [Abelian D] :=
  @DerivedCategory D _ _ (HasDerivedCategory.standard D)
/-- The localization functor for `completedConstantDerived`.
Source: Stacks Tag 05RU
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantQ (D : Type v) [Category.{w} D] [Abelian D] :
    CochainComplex D ℤ ⥤ completedConstantDerived D :=
  @DerivedCategory.Q D _ _ (HasDerivedCategory.standard D)
/-- Termwise application of an additive functor, with its actual differentials.
Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantMapComplex {D : Type v} {E : Type w} [Category.{vD} D] [Category.{vE} E]
    [Preadditive D] [Preadditive E] (F : D ⥤ E) (hF : F.Additive) :
    CochainComplex D ℤ ⥤ CochainComplex E ℤ :=
  letI := hF
  F.mapHomologicalComplex (ComplexShape.up ℤ)
/-- Module sheaves on the original small site; its object and Hom universes are unequal.
Source: Stacks Tags 09A5 and 03D1
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantModules (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((adicLisseForget X).obj R)
/-- Ordinary scalar extension, selected with its specified objects and morphisms from
`derivedChangeOfRingsIndependentCoefficients`. Those specifications determine the functor.
Source: Stacks Tags 03EK and 06YY
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantExtension (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    completedConstantModules X R ⥤ completedConstantModules X S :=
  letI := HasDerivedCategory.standard (completedConstantModules X R)
  letI := HasDerivedCategory.standard (completedConstantModules X S)
  (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u} φ).choose
/-- The scalar extension witness is additive, as specified by the existing derived
change-of-rings theorem. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
instance completedConstantExtension_additive (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (completedConstantExtension X φ).Additive :=
  letI := HasDerivedCategory.standard (completedConstantModules X R)
  letI := HasDerivedCategory.standard (completedConstantModules X S)
  Exists.choose (Exists.choose_spec (Exists.choose_spec (Exists.choose_spec
    (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u} φ))))
/-- Bounded complexes of finite modules. A bound does not require a nonzero term.
Source: Tag 09BV, bounded local models in the blueprint proof (c)
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantFiniteComplex {A : Type (u + 1)} [CommRing A] :
    ObjectProperty (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  fun Q ↦ (∀ i : ℤ, Module.Finite A (Q.X i)) ∧
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (Q.X i)
/-- The finite module subcategory, so exactness refers to its finite limits and colimits.
Source: Stacks Tag 00MB
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantFiniteModules (A : Type (u + 1)) [CommRing A] :
    ObjectProperty (ModuleCat.{u + 1} A) :=
  fun N ↦ Module.Finite A N
/-- The category of finite-free resolutions used in the source proof: the target is
bounded finite, and the source is bounded above with finite free terms. Morphisms are
commutative squares, including maps between resolutions of the same complex.
Source: Tag 00LP and proof step 4
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantResolutions (C : Type (u + 1)) [CommRing C] :
    ObjectProperty (Arrow (CochainComplex (ModuleCat.{u + 1} C) ℤ)) :=
  fun f ↦ completedConstantFiniteComplex f.right ∧ QuasiIso f.hom ∧
    (∀ i : ℤ, Module.Finite C (f.left.X i) ∧ Module.Free C (f.left.X i)) ∧
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (f.left.X i)
/-- The quotient module over a ring mapping to the completed coefficient sheaf.
Source: Stacks Tag 06YU, restriction along the quotient projection
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantQuotient (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕᵒᵖ) :=
  (SheafOfModules.restrictScalars.{u + 1}
    ((adicLisseForget X).map (β ≫ limit.π (adicLisseRingSystem X I) n))).obj
      (SheafOfModules.unit ((adicLisseForget X).obj ((adicLisseRingSystem X I).obj n)))
/-- A quotient diagram with the actual quotient maps, characterized on every section.
`level` and `transition` fix all objects and arrows; this is no arbitrary diagram.
Source: Stacks Tags 093M and 06YU, proof steps 5--8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantQuotientTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) where
  diagram : ℕᵒᵖ ⥤ completedConstantModules X R
  level : ∀ n : ℕᵒᵖ, diagram.obj n = completedConstantQuotient X I R β n
  transition : ∀ (m n : ℕᵒᵖ) (g : m ⟶ n) (U : X.ProEtᵒᵖ)
      (x : ((adicLisseRingSystem X I).obj m).obj.obj U),
    ((eqToHom (level m).symm ≫ diagram.map g ≫ eqToHom (level n)).val.app U) x =
      ((adicLisseRingSystem X I).map g).hom.app U x
/-- The total tensor bifunctor, using the existing monoidal structure and total differential.
Source: Stacks Tags 06YN and 06YU
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CochainComplex (completedConstantModules X R) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ ⥤
        CochainComplex (completedConstantModules X R) ℤ :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.symmetricCategory R
  letI : HasCoproducts.{0} (completedConstantModules X R) := inferInstance
  (MonoidalCategory.curriedTensor _).map₂CochainComplex
/-- Underived tensor with the entire quotient tower, followed by localization.
Its target is a diagram category, so all quotient transitions are retained.
Source: Stacks Tag 06YU, proof steps 5 and 8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantTensorTower (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P : ℕᵒᵖ ⥤ completedConstantModules X R) :
    CochainComplex (completedConstantModules X R) ℤ ⥤
      (ℕᵒᵖ ⥤ completedConstantDerived (completedConstantModules X R)) :=
  ((P ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
    (completedConstantTensor X R).flip) ⋙
      (Functor.whiskeringRight _ _ _).obj (completedConstantQ _)).flip
/-- The everywhere defined derived tensor tower, fixed by its universal counit and
computed on every K-flat complex. This bundles the existing left-derived property,
without introducing another definition of derived tensor.
Source: Stacks Tags 06YY and 06YU; lem-pur-derived-change-of-rings
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantDerivedTower (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P : ℕᵒᵖ ⥤ completedConstantModules X R) where
  functor : completedConstantDerived (completedConstantModules X R) ⥤
    (ℕᵒᵖ ⥤ completedConstantDerived (completedConstantModules X R))
  counit : completedConstantQ _ ⋙ functor ⟶ completedConstantTensorTower X R P
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (completedConstantModules X R) (ComplexShape.up ℤ))
  computes : ∀ F : CochainComplex (completedConstantModules X R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) F →
      IsIso (counit.app F)
/-- Completed realization by extension of the constant completion ring to completed
sheaf scalars. The theorem identifies this actual tensor construction with the limit.
Source: Stacks Tag 093M and proof step 2
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantRealization (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :=
  adicLisseConstantModules X (AdicCompletion I A) ⋙ completedConstantExtension X φ
/-- The constant-module sheafification generator, the image of an actual module element.
Source: Stacks Tag 093J, constant sheafification
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantGenerator (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (U : X.ProEtᵒᵖ) (x : N) :
    ((adicLisseConstantModules X B).obj N).val.obj U :=
  (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of N))).app U x
/-- A finite reduction on complexes: tensor the module complex with `P_(n+1)`,
make it constant, and restrict its scalars along the specified projection.
Source: Stacks Tag 06YU, proof step 5
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantReductionLevel (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (h : (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ :=
  letI := h
  letI := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (AdicCompletion.evalₐ I (n + 1)).toRingHom ⋙
    adicLisseConstantModules X (A ⧸ I ^ (n + 1)) ⋙
    SheafOfModules.restrictScalars.{u + 1} ((adicLisseForget X).map
      (β ≫ limit.π (adicLisseRingSystem X I) (op n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)
/-- Constant reductions, with all quotient transitions fixed on tensor generators.
Applied to a bounded-above finite-free resolution F, this represents precisely
`underline(Q tensor^L_C P_n)`, with its specified R-action. The generator condition
prevents replacing quotient transitions by arbitrary maps.
Source: Stacks Tag 06YU, proof steps 5 and 8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantReductionTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) where
  functor : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (completedConstantModules X R) ℤ)
  level : ∀ (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ) (n : ℕ),
    (functor.obj F).obj (op n) = (completedConstantReductionLevel X I R β n (h n)).obj F
  map_level : ∀ (F G : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ)
      (f : F ⟶ G) (n : ℕ),
    eqToHom (level F n).symm ≫ (functor.map f).app (op n) ≫ eqToHom (level G n) =
      (completedConstantReductionLevel X I R β n (h n)).map f
  transition : ∀ (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ)
      (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (p : A ⧸ I ^ (n + 2)) (x : F.X i),
    (((eqToHom (level F (n + 1)).symm ≫ (functor.obj F).map
        (homOfLE (Nat.le_succ n)).op ≫ eqToHom (level F n)).f i).val.app U)
      (completedConstantGenerator X _
       
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (AdicCompletion.evalₐ I (n + 2)).toRingHom).obj
          (F.X i))
        U (p ⊗ₜ[(AdicCompletion I A), (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) =
      completedConstantGenerator X _
       
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (AdicCompletion.evalₐ I (n + 1)).toRingHom).obj
          (F.X i))
        U ((Ideal.Quotient.factorPowSucc I (n + 1) p) ⊗ₜ[(AdicCompletion I A),
          (AdicCompletion.evalₐ I (n + 1)).toRingHom] x)
/-- Restrict a completion-module to A. On this module I^n N = (IC)^n N, so its
quotient and completed constant sheaf are exactly those in the node's statement.
Source: Stacks Tag 00MA, proof step 1
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantUnderlyingModule {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} (AdicCompletion I A)) :=
  (ModuleCat.restrictScalars.{u + 1} (algebraMap A (AdicCompletion I A))).obj N
/-- The A-linear map on the actual quotients induced by an A-linear map.
Source: Stacks Tag 093J and the componentwise limit construction
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantQuotientMap {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (n : ℕ) :
    ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) ⟶
      ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)) :=
  ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ (n + 1))).restrictScalars A)
/-- The constant A-action on the completed coefficient ring.
Source: Stacks Tag 093M and the limit projections
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantBaseMap (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :=
  ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))) ≫ φ
/-- The module-level assertions and the specified realization isomorphisms.
The limit is formed from the dependency's actual quotient-module system. Its
linearity condition fixes the completed-scalar action on every finite projection;
naturality fixes the maps of the realization functor. Restriction to A changes
no quotient: I^n N = (IC)^n N for a C-module.
Source: Stacks Tags 093J--093M, 09BT, and 09BV, proof steps 1--3
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantModuleRealization (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) where
  scalar : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I
  scalar_projection : ∀ n : ℕ,
    scalar ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)
  additive : (completedConstantRealization X I scalar).Additive
  exact_finite :
    PreservesFiniteLimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
      completedConstantRealization X I scalar) ∧
    PreservesFiniteColimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
      completedConstantRealization X I scalar)
  lisse : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A)),
    Module.Finite (AdicCompletion I A) N →
      IsAdicLisseModule X I ((completedConstantRealization X I scalar).obj N)
  realization : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
    (_hN : Module.Finite (AdicCompletion I A) N),
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (completedConstantBaseMap X I scalar))).obj
          ((completedConstantRealization X I scalar).obj N) ≅
        adicLisseCompletedModule X I (completedConstantUnderlyingModule I N)
  linearity : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hN : Module.Finite (AdicCompletion I A) N) (n : ℕ) (U : X.ProEtᵒᵖ)
      (r : ((adicLisseCompletedRing X I).obj.obj U))
      (a : (adicLisseConstantRing X A).obj.obj U)
      (x : ((completedConstantRealization X I scalar).obj N).val.obj U),
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a =
        (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r →
    (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
      (op n)).val.app U ((realization N hN).hom.val.app U (r • x)) =
      a • (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
        (op n)).val.app U ((realization N hN).hom.val.app U x)
  naturality : ∀ (M N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hM : Module.Finite (AdicCompletion I A) M)
      (hN : Module.Finite (AdicCompletion I A) N) (f : M ⟶ N) (n : ℕ)
      (U : X.ProEtᵒᵖ) (x : ((completedConstantRealization X I scalar).obj M).val.obj U),
    (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
        (op n)).val.app U ((realization N hN).hom.val.app U
          (((completedConstantRealization X I scalar).map f).val.app U x)) =
      (((adicLisseConstantModules X A).map (completedConstantQuotientMap I
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)).val.app U)
          ((limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I M))
            (op n)).val.app U ((realization M hM).hom.val.app U x))
/-- The two sides of a reduction comparison, including naturality in the bounded
complex and its finite-free resolution, and in every quotient transition. The right
side uses the constant reduction of the resolution, so it retains all higher Tor.
The derived counit on K-flat complexes fixes the left side, including comparison
between arbitrary K-flat resolutions. All categories here retain their R-action.
Source: Stacks Tag 06YU and proof steps 4--8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def CompletedConstantReductionComparisons (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) : Prop :=
  (∀ Q : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ,
    completedConstantFiniteComplex Q →
      ∃ (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ) (f : F ⟶ Q),
        completedConstantResolutions (AdicCompletion I A) (Arrow.mk f)) ∧
  ∃ (P : CompletedConstantQuotientTower X I R β)
    (L : CompletedConstantDerivedTower X R P.diagram)
    (T : CompletedConstantReductionTower X I R β h),
    Nonempty
      (((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.rightFunc ⋙
          completedConstantMapComplex c hc ⋙ completedConstantQ _ ⋙ L.functor) ≅
        ((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc ⋙
          T.functor ⋙ (Functor.whiskeringRight _ _ _).obj (completedConstantQ _)))
end AlgebraicGeometry.Scheme
