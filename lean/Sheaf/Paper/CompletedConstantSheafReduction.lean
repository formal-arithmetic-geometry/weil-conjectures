/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Sites.Abelian
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.RingTheory.LimitFlatModules
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Completed constant sheaves and finite reduction

Source: Stacks Project, Modules on Sites, Tags 093J--093M;
Cohomology on Sites, Tags 06YN and 06YU
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.CompletedConstantReduction

open AdicCoefficients

/-- The base map is uniquely fixed by all quotient projections. Source: Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: apply the limit universal property to the quotient maps. Their compatibility follows
on representatives from the quotient factor formula, and constant sheafification preserves it.
The limit universal property also gives uniqueness. -/
theorem base_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ∃! φ : adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem T I) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  let c : Cone (adicLisseRingSystem T I) :=
    { pt := adicLisseConstantRing T A
      π := NatTrans.ofOpSequence
        (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) (by
            intro n
            simp only [Functor.const_obj_map, adicLisseRingSystem,
              Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            congr 1) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro φ hφ
    apply limit.hom_ext
    intro n
    exact (hφ n.unop).trans (limit.lift_π c n).symm

/-- The canonical constant-to-completed coefficient homomorphism. Source: Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def base (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I :=
  (base_exists T I).choose

/-- The completed coefficient sheaf as a module over the constant coefficient sheaf.
Source: Stacks Tag 093M (blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def completedModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map (base T I))).obj
    (SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I)))

/-- The quotient sheaf, retaining its action by the completed ring through its projection.
Source: Stacks Tags 093M and 06YU
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def residue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseCompletedRing T I)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map
    (limit.π (adicLisseRingSystem T I) (op n)))).obj
      (SheafOfModules.unit ((adicLisseForget T).obj
        (adicLisseConstantRing T (A ⧸ I ^ (n + 1)))))

/-- The reduction map is uniquely determined on local tensor generators by projection
and multiplication. Source: Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: multiplication after the nth projection is balanced over the constant base ring.
It commutes with restriction, and therefore descends through module sheafification.
Constant module sections and local pure tensors generate the source, proving uniqueness. -/
theorem reduction_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! r : (completedAdicChange T (base T I)).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
          residue T I n,
      ∀ (U : T.ProEtᵒᵖ) (b : (adicLisseCompletedRing T I).obj.obj U)
        (x : A ⧸ I ^ (n + 1)),
        r.val.app U (tensorSection T (base T I) _ U b
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
            @id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
              ((limit.π (adicLisseRingSystem T I) (op n)).hom.app U b) *
              @id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
                ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x) := by
  sorry

/-- The ordinary canonical reduction map, fixed by its formula in `reduction_exists`.
Source: Stacks Tag 093M (blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def reduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) := (reduction_exists T I n).choose

/-- The actual canonical reduction on a complex mapping to the constant quotient.
Source: Stacks Tags 06YY and 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def reductionComplex (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
    (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))) :=
  ((completedAdicChange T (base T I)).mapHomologicalComplex (.up ℤ)).map f ≫
    ((completedAdicChange T (base T I)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map (reduction T I n)

/-- A direct summand of a finite sum of copies of the completed coefficient ring.
The zero-fold sum is included. Source: Stacks Tag 093J, split finite-projective argument
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def IsFiniteRetract (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseCompletedRing T I))) : Prop :=
  ∃ r : ℕ,
    ∃ i : M ⟶ ∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I))),
    ∃ s : (∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I)))) ⟶ M,
      i ≫ s = 𝟙 M

/-- Constant module sheafification is additive. Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: the constant presheaf functor and associated-module-sheafification functor are additive,
and so is their composite defining `adicLisseConstantModules`. -/
theorem constant_additive (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (adicLisseConstantModules T A).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.toSheaf _).map_injective
  change (presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).map
    ((Functor.const T.ProEtᵒᵖ).map
      ((forget₂ (ModuleCat A) AddCommGrpCat).map (f + g))) = _
  rw [Functor.map_add, Functor.map_add, Functor.map_add]
  rfl

/-- The termwise constant module sheaf of a complex. Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def constantComplex (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    CochainComplex (ModuleCat.{u + 1} A) ℤ ⥤
      CochainComplex
        (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ :=
  letI := constant_additive T A
  (adicLisseConstantModules T A).mapHomologicalComplex (.up ℤ)

/-- The augmentation of the constant sheaf resolution, with the standard degree-zero
comparison. Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def constantAugmentation (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1)))) :=
  letI := constant_additive T A
  (constantComplex T A).map f ≫
    ((adicLisseConstantModules T A).mapCochainComplexSingleFunctor 0).hom.app _

/-- Flatness, the canonical derived reduction, and its bounded finite-projective model.
Source: Stacks Tags 093J--093M and 06YU
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: (1) Constant quotient sections are flat over their Noetherian quotient rings and have
surjective transitions (`lem-weil-pbc-constant-module-section-properties`). Apply
`lem-weil-pbc-limit-flat-modules` sectionwise, then
`lem-pc-sites-modules-sheafification-flat`, obtaining flatness over the constant ring sheaf.
(2) The tensor-limit comparison for the finite module A/I^(n+1) is eventually constant;
its projection-and-multiplication formula is precisely `reduction`, hence it is invertible.
(3) Exact scalar extension preserves quasi-isomorphisms, so on every K-flat resolution
its canonical reduction is a quasi-isomorphism and represents the required derived iso.
(4) Finite projectives split off finite free modules. Constant sheafification and scalar
extension preserve the splitting. Their exactness preserves the augmented resolution,
and termwise application retains the given two bounds. -/
theorem completed_constant_sheaf_reduction (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlatOnSite (completedModule T I) ∧
    (∀ n : ℕ, IsIso (reduction T I n)) ∧
    (∀ (n : ℕ) (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
      (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))),
      CochainComplex.IsAcyclicTensorKFlat (R := adicLisseConstantRing T A) P → QuasiIso f →
        QuasiIso (reductionComplex T I n P f)) ∧
    (∀ (n : ℕ) (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
      (f : F ⟶ (CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of A (A ⧸ I ^ (n + 1)))) (a b : ℤ),
      QuasiIso f →
      (∀ i : ℤ, Module.Finite A (F.X i) ∧ Module.Projective A (F.X i)) →
      (∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)) →
      QuasiIso (reductionComplex T I n ((constantComplex T A).obj F)
        (constantAugmentation T I n F f)) ∧
      (∀ i : ℤ, IsFiniteRetract T I
        ((completedAdicChange T (base T I)).obj (((constantComplex T A).obj F).X i))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero
        ((completedAdicChange T (base T I)).obj (((constantComplex T A).obj F).X i)))) := by
  sorry

/-- Constants-to-functions comparisons commute with every quotient transition.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: both presheaf composites send a constant value to the constant function of its quotient
image. Sheafification preserves this equality, and composites give every tower transition. -/
theorem systemComparison_naturality (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1)))
    (m n : ℕᵒᵖ) (f : m ⟶ n) :
    (adicLisseRingSystem T I).map f ≫
      @constantComparison _ _ _ (hf n.unop) =
    @constantComparison _ _ _ (hf m.unop) ≫ (ringSystem T I hf).map f := by
  let := hf
  let c : adicLisseRingSystem T I ⟶ ringSystem T I hf :=
    NatTrans.ofOpSequence (fun n ↦ constantComparison T (A ⧸ I ^ (n + 1))) (by
      intro k
      simp only [adicLisseRingSystem, ringSystem, Functor.ofOpSequence_map_homOfLE_succ,
        constantComparison, constantSheaf, Functor.comp_map, coefficientMap,
        ← Functor.map_comp]
      congr 1)
  exact c.naturality f

/-- The canonical comparison of quotient ring diagrams, retaining the quotient maps.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def systemComparison (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    adicLisseRingSystem T I ⟶ ringSystem T I hf where
  app n := @constantComparison T (A ⧸ I ^ (n.unop + 1)) _ (hf n.unop)
  naturality m n f := systemComparison_naturality T I hf m n f

/-- The canonical comparison of inverse-limit coefficient rings.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def completedComparison (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    adicLisseCompletedRing T I ⟶ completedRing T I hf :=
  lim.map (systemComparison T I hf)

/-- The quotient function sheaf as a module over completed function coefficients.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteResidue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :=
  AdicCoefficients.residue T I hf n

/-- The finite-coefficient reduction is fixed by projection and the image of each constant
quotient value. Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: the specified formula is balanced over the constant A action. Its restrictions commute
with the formula, so it sheafifies. Constant module generators and local tensor generators
prove uniqueness. This is the transport of the ordinary reduction along the ring comparisons. -/
theorem finiteReduction_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :
    ∃! r : (completedAdicChange T (base T I ≫ completedComparison T I hf)).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
          finiteResidue T I hf n,
      ∀ (U : T.ProEtᵒᵖ) (b : (completedRing T I hf).obj.obj U)
        (x : A ⧸ I ^ (n + 1)),
        r.val.app U (tensorSection T (base T I ≫ completedComparison T I hf) _ U b
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
            (limit.π (ringSystem T I hf) (op n)).hom.app U b *
              ((systemComparison T I hf).app (op n)).hom.app U
                (@id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
                  ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x)) := by
  sorry

/-- The finite-coefficient reduction map, specified uniquely on tensor generators.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :=
  (finiteReduction_exists T I hf n).choose

/-- The canonical derived finite reduction on a chosen K-flat representative of the quotient.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteReductionComplex (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ)
    (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
    (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))) :=
  ((completedAdicChange T
    (base T I ≫ completedComparison T I hf)).mapHomologicalComplex (.up ℤ)).map f ≫
    ((completedAdicChange T
      (base T I ≫ completedComparison T I hf)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map (finiteReduction T I hf n)

/-- Finite function coefficients are precisely constant finite quotient sheaves, naturally
in the quotient system, and the canonical reduction agrees after this identification.
Source: blueprint finite-coefficient interpretation; Stacks Tags 093J--093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: a continuous function to a finite discrete ring has finitely many clopen fibres in the
underlying scheme. These form a pro-etale cover. Gluing the constant values on that cover
proves the universal property of the constant sheafification. The empty object is handled by
its empty covering. Postcomposition with ring maps respects those gluings, so the quotient
comparisons are compatible. Limits preserve these natural isomorphisms. On local tensor
generators the transported reduction is exactly the formula defining finiteReduction.
The ordinary reduction and every K-flat representative are thus isomorphic by the first
four clauses of completed_constant_sheaf_reduction. -/
theorem finite_coefficient_identification (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    (∀ n : ℕ, IsIso ((systemComparison T I hf).app (op n))) ∧
    IsIso (completedComparison T I hf) ∧
    (∀ n : ℕ, IsIso (finiteReduction T I hf n)) ∧
    (∀ (n : ℕ) (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
      (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))),
      CochainComplex.IsAcyclicTensorKFlat (R := adicLisseConstantRing T A) P → QuasiIso f →
        QuasiIso (finiteReductionComplex T I hf n P f)) := by
  sorry

end AlgebraicGeometry.Scheme.CompletedConstantReduction
