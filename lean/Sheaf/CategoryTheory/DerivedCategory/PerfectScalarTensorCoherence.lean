/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange

/-! # Perfect scalar extension and its tensor and tower coherence

Source: Stacks Project, More on Algebra, Tags 06Y6 and 0GWN; the explicit balanced
comparisons and their coherence are the agent-formulated conjunction in the DAG
(blueprint: lem-sf-perfect-scalar-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor

namespace DerivedCategory
namespace PerfectScalar

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The existing derived category, with its chosen localization size.
Source: Stacks 06Y6 (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
abbrev D (R : CommRingCat.{u}) := DerivedCategory (ModuleCat.{u} R)

/-- Termwise ordinary scalar extension; its monoidal maps are the balanced maps.
Source: Stacks 06Y6 and 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
noncomputable abbrev E {R S : CommRingCat.{u}} (f : R ⟶ S) :=
  (ModuleCat.extendScalars f.hom).mapHomologicalComplex (.up ℤ)

/-- The regular coefficient module in degree zero.
Source: Stacks 06Y6 (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
noncomputable abbrev coefficient (S : CommRingCat.{u}) :=
  (HomologicalComplex.single (ModuleCat.{u} S) (.up ℤ) 0).obj (ModuleCat.of S S)

/-- Scalar extension is the fixed-second-factor derived tensor evaluated at S[0].
The universal left-derived property determines this functor up to its canonical isomorphism.
Source: Stacks 06Y6 (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
noncomputable def B {R S : CommRingCat.{u}} (f : R ⟶ S) : D R ⥤ D S :=
  (Classical.choose (exists_derivedTensor_second_factor_functor f.hom).2).obj
    (coefficient S)

/-- The canonical K-flat computation map into termwise scalar extension. The first map
is the counit of the recorded universal derived tensor. The second removes the degree-zero
coefficient factor using the ordinary left unitor. No comparison is chosen arbitrarily.
Source: Stacks 06Y6 (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
noncomputable def modelMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (B f).obj (Q.obj P) ⟶ Q.obj ((E f).obj P) :=
  (Classical.choose (Classical.choose_spec
    (exists_derivedTensor_second_factor_functor f.hom).2) (coefficient S)).app P ≫
  Q.map (CochainComplex.mapBifunctorSingle₂Iso (ModuleCat.mixedTensor f.hom).flip
      (ModuleCat.of S S) P ≪≫
    (NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars f.hom) (leftUnitorNatIso (ModuleCat S)) ≪≫
        Functor.rightUnitor _) (.up ℤ)).app P).hom

/-- The signed symmetry of the existing K-flat derived tensor, without choosing a braiding.
Source: Stacks 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
noncomputable def symmetry (R : CommRingCat.{u}) (P Q : D R) : P ⊗ Q ≅ Q ⊗ P :=
  DerivedMonoidal.braiding' (Qh (C := ModuleCat.{u} R))
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) P Q

attribute [irreducible] B modelMap symmetry

/-- All tensor, unit and tower comparisons on perfect objects, characterized on actual
finite-projective models. Proof clauses express naturality for arbitrary derived maps,
all monoidal equations, both tower units, four-ring associativity, and the tensor/unit
squares. The normalizations use the existing balanced maps and their inverse maps.
Source: Stacks 06Y6 and 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
def Coherence : Prop :=
  ∃ (preserves : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R),
    IsPerfectRingComplex P → IsPerfectRingComplex ((B f).obj P)),
  ∃ (tensorPerfect : ∀ (R : CommRingCat.{u}) (P Q : D R),
    IsPerfectRingComplex P → IsPerfectRingComplex Q → IsPerfectRingComplex (P ⊗ Q)),
  ∃ (unitPerfect : ∀ (R : CommRingCat.{u}), IsPerfectRingComplex (𝟙_ (D R))),
  ∃ (_additive : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
      (_hP : IsPerfectRingComplex P) (_hQ : IsPerfectRingComplex Q) (a b : P ⟶ Q),
    (B f).map (a + b) = (B f).map a + (B f).map b),
  ∃ (_linear : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
      (_hP : IsPerfectRingComplex P) (_hQ : IsPerfectRingComplex Q) (r : R) (a : P ⟶ Q),
    (B f).map (r • a) = f.hom r • (B f).map a),
  ∃ (_model : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)),
    IsIso (modelMap f P)),
  ∃ (tensor : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
      (_hP : IsPerfectRingComplex P) (_hQ : IsPerfectRingComplex Q),
    (B f).obj (P ⊗ Q) ≅ (B f).obj P ⊗ (B f).obj Q),
  ∃ (unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), (B f).obj (𝟙_ (D R)) ≅ 𝟙_ (D S)),
  ∃ (comp : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P : D R) (_hP : IsPerfectRingComplex P),
    (B g).obj ((B f).obj P) ≅ (B (f ≫ g)).obj P),
  ∃ (identity : ∀ (R : CommRingCat.{u}) (P : D R) (_hP : IsPerfectRingComplex P),
    (B (𝟙 R)).obj P ≅ P),
  ∃ (_tensor_natural : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q P' Q' : D R)
      (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q)
      (hP' : IsPerfectRingComplex P') (hQ' : IsPerfectRingComplex Q')
      (a : P ⟶ P') (b : Q ⟶ Q'),
    (B f).map (a ⊗ₘ b) ≫ (tensor f P' Q' hP' hQ').hom =
      (tensor f P Q hP hQ).hom ≫ ((B f).map a ⊗ₘ (B f).map b)),
  ∃ (_comp_natural : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P Q : D R) (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q)
      (a : P ⟶ Q),
    (B g).map ((B f).map a) ≫ (comp f g Q hQ).hom =
      (comp f g P hP).hom ≫ (B (f ≫ g)).map a),
  ∃ (_identity_natural : ∀ (R : CommRingCat.{u}) (P Q : D R)
      (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q) (a : P ⟶ Q),
    (B (𝟙 R)).map a ≫ (identity R Q hQ).hom = (identity R P hP).hom ≫ a),
  ∃ (_tensor_model : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b c d : ℤ)
      (_hPa : P.IsStrictlyGE a) (_hPb : P.IsStrictlyLE b)
      (_hQc : Q.IsStrictlyGE c) (_hQd : Q.IsStrictlyLE d)
      (_hPterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (_hQterms : ∀ n : ℤ, Module.Projective R (Q.X n) ∧ Module.Finite R (Q.X n))
      (hP : IsPerfectRingComplex (DerivedCategory.Q.obj P))
      (hQ : IsPerfectRingComplex (DerivedCategory.Q.obj Q)),
    (B f).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        modelMap f (P ⊗ Q) ≫ DerivedCategory.Q.map
          ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P Q).inv =
      (tensor f _ _ hP hQ).hom ≫ (modelMap f P ⊗ₘ modelMap f Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q ((E f).obj P) ((E f).obj Q)),
  ∃ (_unit_model : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S),
    (B f).map (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) ≫
        modelMap f (𝟙_ _) ≫ DerivedCategory.Q.map
          (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
      (unit f).hom ≫ Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat S))),
  ∃ (_comp_model : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (hP : IsPerfectRingComplex (Q.obj P)),
    (B g).map (modelMap f P) ≫ modelMap g ((E f).obj P) ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app P).hom =
      (comp f g _ hP).hom ≫ modelMap (f ≫ g) P),
  ∃ (_identity_model : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (a b : ℤ) (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (hP : IsPerfectRingComplex (Q.obj P)),
    modelMap (𝟙 R) P ≫
        Q.map ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ)).app P).hom =
      (identity R _ hP).hom),
  ∃ (_associativity : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q Z : D R)
      (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q)
      (hZ : IsPerfectRingComplex Z),
    (tensor f (P ⊗ Q) Z (tensorPerfect R P Q hP hQ) hZ).hom ≫
        (tensor f P Q hP hQ).hom ▷ (B f).obj Z ≫
        (α_ ((B f).obj P) ((B f).obj Q) ((B f).obj Z)).hom =
      (B f).map (α_ P Q Z).hom ≫
        (tensor f P (Q ⊗ Z) hP (tensorPerfect R Q Z hQ hZ)).hom ≫
        (B f).obj P ◁ (tensor f Q Z hQ hZ).hom),
  ∃ (_symmetry_compatibility : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
      (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q),
    (B f).map (symmetry R P Q).hom ≫ (tensor f Q P hQ hP).hom =
      (tensor f P Q hP hQ).hom ≫ (symmetry S ((B f).obj P) ((B f).obj Q)).hom),
  ∃ (_left_unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R)
      (hP : IsPerfectRingComplex P),
    (tensor f (𝟙_ (D R)) P (unitPerfect R) hP).hom ≫
        (unit f).hom ▷ (B f).obj P ≫ (λ_ ((B f).obj P)).hom = (B f).map (λ_ P).hom),
  ∃ (_right_unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R)
      (hP : IsPerfectRingComplex P),
    (tensor f P (𝟙_ (D R)) hP (unitPerfect R)).hom ≫
        (B f).obj P ◁ (unit f).hom ≫ (ρ_ ((B f).obj P)).hom = (B f).map (ρ_ P).hom),
  ∃ (_comp_left_unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R)
      (hP : IsPerfectRingComplex P),
    (comp (𝟙 R) f P hP).hom = (B f).map (identity R P hP).hom),
  ∃ (_comp_right_unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R)
      (hP : IsPerfectRingComplex P),
    (comp f (𝟙 S) P hP).hom = (identity S ((B f).obj P) (preserves f P hP)).hom),
  ∃ (_four_ring : ∀ {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U)
      (P : D R) (hP : IsPerfectRingComplex P),
    (B h).map (comp f g P hP).hom ≫ (comp (f ≫ g) h P hP).hom =
      (comp g h ((B f).obj P) (preserves f P hP)).hom ≫ (comp f (g ≫ h) P hP).hom),
  ∃ (_comp_tensor : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P Q : D R) (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q),
    (comp f g (P ⊗ Q) (tensorPerfect R P Q hP hQ)).hom ≫
        (tensor (f ≫ g) P Q hP hQ).hom =
      (B g).map (tensor f P Q hP hQ).hom ≫
        (tensor g ((B f).obj P) ((B f).obj Q) (preserves f P hP) (preserves f Q hQ)).hom ≫
        ((comp f g P hP).hom ⊗ₘ (comp f g Q hQ).hom)),
  ∃ (_comp_coefficient_unit : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T),
    (comp f g (𝟙_ (D R)) (unitPerfect R)).hom ≫ (unit (f ≫ g)).hom =
      (B g).map (unit f).hom ≫ (unit g).hom),
  ∃ (_identity_tensor : ∀ (R : CommRingCat.{u}) (P Q : D R)
      (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q),
    (tensor (𝟙 R) P Q hP hQ).hom ≫
        ((identity R P hP).hom ⊗ₘ (identity R Q hQ).hom) =
      (identity R (P ⊗ Q) (tensorPerfect R P Q hP hQ)).hom),
  ∀ (R : CommRingCat.{u}),
    (unit (𝟙 R)).hom = (identity R (𝟙_ (D R)) (unitPerfect R)).hom

/-- Perfect scalar extension is additive and R-linear, computed termwise on bounded
finite-projective models, with the normalized signed tensor, unit and tower comparisons.
Source: Stacks Project, More on Algebra, Tags 06Y6 and 0GWN; agent-formulated coherence
(blueprint: lem-sf-perfect-scalar-tensor-coherence).

Proof (DAG steps 1--13):
1. Split finite projective modules off finite free modules. Tensor the splittings to prove
   preservation under scalar extension, tensor products and finite sums, with tensor bounds
   [a+c,b+d]. This includes zero modules, empty generating lists and zero rings.
2. Projectives are flat; bounded-above flat complexes are K-flat. Apply the recorded
   fixed-second-factor derived tensor computation over both coefficient rings.
3. Bounded-above projective complexes compute derived Hom by homotopy classes, so their
   homotopy category is equivalent to the full perfect derived subcategory.
4. Termwise extension preserves homotopies, addition and scalar multiplication. Descend
   along that equivalence to obtain additivity and R-linearity on all derived Hom sets.
5. Total tensor preserves homotopies: use h(x) tensor y in the first variable and
   (-1)^deg(x) x tensor k(y) in the second. The unwanted differential terms cancel.
6. The tensor map sends (x tensor y) tensor s to (x tensor s) tensor (y tensor 1).
   Its inverse multiplies the two scalar factors; balance proves both inverse identities.
7. Both maps commute with the signed differential. The coefficient-unit map is
   r tensor s mapped to f(r)s, with inverse s mapped to 1 tensor s.
8. Check naturality on chain maps on pure tensors and then on homotopy classes.
9. Associativity, Koszul symmetry and both unitors commute on homogeneous generators;
   symmetry uses S-balance and the sign (-1)^(pq), including negative degrees.
10. The tower map multiplies g(s)t; its inverse inserts 1. The identity comparison is
    multiplication. These are chain maps, natural on chain maps.
11. Both ring-unit equations are balance. Four-ring associativity is
    h(g(s)t)u = h(g(s))h(t)u.
12. The tower tensor square sends a generator to (x tensor g(s)t) tensor (y tensor 1)
    by both paths. The coefficient-unit square gives (gf)(r)g(s)t. Identity squares
    are balance and multiplication.
13. Lift arbitrary derived morphisms between finite-projective models to homotopy
    classes. Transport the comparisons along model isomorphisms. Full faithfulness
    gives naturality for every derived morphism, independence of models and its cocycle;
    localization and conjugation preserve every equation of steps 9, 11 and 12. -/
theorem perfect_scalar_tensor_coherence : Coherence.{u, w} := by
  sorry

end PerfectScalar
end DerivedCategory

noncomputable section

namespace DerivedCategory.PerfectScalar

private theorem kflat_extend {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (ModuleCat S) (.up ℤ)).kFlat ((E f).obj P) := by
  have hp := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have hp' (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.Acyclic) :
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hp ((HomotopyCategory.quotient _ _).obj L)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hL)).2
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨L, rfl⟩ := N.quotient_obj_surjective
  have hL := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hN
  have h := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat f.hom P hp' L hL
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The complete normalized scalar-coherence interface, with named projections.
Source: Stacks 06Y6 and 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
structure CoherenceData where
  preserves : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, w} R),
    IsPerfectRingComplex.{u, w} P → IsPerfectRingComplex.{u, w} ((B.{u, w} f).obj P)
  tensorPerfect : ∀ (R : CommRingCat.{u}) (P Q : D.{u, w} R),
    IsPerfectRingComplex.{u, w} P → IsPerfectRingComplex.{u, w} Q → IsPerfectRingComplex.{u, w} (P
      ⊗ Q)
  unitPerfect : ∀ (R : CommRingCat.{u}), IsPerfectRingComplex.{u, w} (𝟙_ (D.{u, w} R))
  additive : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, w} R)
      (_hP : IsPerfectRingComplex.{u, w} P) (_hQ : IsPerfectRingComplex.{u, w} Q) (a b : P ⟶ Q),
    (B.{u, w} f).map (a + b) = (B.{u, w} f).map a + (B.{u, w} f).map b
  linear : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, w} R)
      (_hP : IsPerfectRingComplex.{u, w} P) (_hQ : IsPerfectRingComplex.{u, w} Q) (r : R) (a : P ⟶
      Q),
    (B.{u, w} f).map (r • a) = f.hom r • (B.{u, w} f).map a
  model : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)),
    IsIso (modelMap.{u, w} f P)
  tensor : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, w} R)
      (_hP : IsPerfectRingComplex.{u, w} P) (_hQ : IsPerfectRingComplex.{u, w} Q),
    (B.{u, w} f).obj (P ⊗ Q) ≅ (B.{u, w} f).obj P ⊗ (B.{u, w} f).obj Q
  unit : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), (B.{u, w} f).obj (𝟙_ (D.{u, w} R)) ≅ 𝟙_ (D.{u, w} S)
  comp : ∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P : D.{u, w} R) (_hP : IsPerfectRingComplex.{u, w} P),
    (B.{u, w} g).obj ((B.{u, w} f).obj P) ≅ (B.{u, w} (f ≫ g)).obj P
  identity : ∀ (R : CommRingCat.{u}) (P : D.{u, w} R) (_hP : IsPerfectRingComplex.{u, w} P),
    (B.{u, w} (𝟙 R)).obj P ≅ P
/-- Every naturality, finite-projective model and monoidal coherence equation of the
existing interface, on the named comparisons. Source: Stacks 06Y6 and 0GWN
(blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
def CoherenceData.Normalized (coh : CoherenceData.{u, w}) : Prop :=
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q P' Q' : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q)
      (hP' : IsPerfectRingComplex.{u, w} P') (hQ' : IsPerfectRingComplex.{u, w} Q')
      (a : P ⟶ P') (b : Q ⟶ Q'),
    (B.{u, w} f).map (a ⊗ₘ b) ≫ (coh.tensor f P' Q' hP' hQ').hom =
      (coh.tensor f P Q hP hQ).hom ≫ ((B.{u, w} f).map a ⊗ₘ (B.{u, w} f).map b)) ∧
  (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P Q : D.{u, w} R) (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q)
      (a : P ⟶ Q),
    (B.{u, w} g).map ((B.{u, w} f).map a) ≫ (coh.comp f g Q hQ).hom =
      (coh.comp f g P hP).hom ≫ (B.{u, w} (f ≫ g)).map a) ∧
  (∀ (R : CommRingCat.{u}) (P Q : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q) (a : P ⟶ Q),
    (B.{u, w} (𝟙 R)).map a ≫ (coh.identity R Q hQ).hom = (coh.identity R P hP).hom ≫ a) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b c d : ℤ)
      (_hPa : P.IsStrictlyGE a) (_hPb : P.IsStrictlyLE b)
      (_hQc : Q.IsStrictlyGE c) (_hQd : Q.IsStrictlyLE d)
      (_hPterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (_hQterms : ∀ n : ℤ, Module.Projective R (Q.X n) ∧ Module.Finite R (Q.X n))
      (hP : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj P))
      (hQ : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj Q)),
    (B.{u, w} f).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        modelMap.{u, w} f (P ⊗ Q) ≫ DerivedCategory.Q.map
          ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P Q).inv =
      (coh.tensor f _ _ hP hQ).hom ≫ (modelMap.{u, w} f P ⊗ₘ modelMap.{u, w} f Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q ((E.{u} f).obj P) ((E.{u} f).obj Q)) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S),
    (B.{u, w} f).map (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) ≫
        modelMap.{u, w} f (𝟙_ _) ≫ DerivedCategory.Q.map
          (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
      (coh.unit f).hom ≫ Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat S))) ∧
  (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (hP : IsPerfectRingComplex.{u, w} (Q.obj P)),
    (B.{u, w} g).map (modelMap.{u, w} f P) ≫ modelMap.{u, w} g ((E.{u} f).obj P) ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app P).hom =
      (coh.comp f g _ hP).hom ≫ modelMap.{u, w} (f ≫ g) P) ∧
  (∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (a b : ℤ) (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
      (_hterms : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
      (hP : IsPerfectRingComplex.{u, w} (Q.obj P)),
    modelMap.{u, w} (𝟙 R) P ≫
        Q.map ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ)).app P).hom =
      (coh.identity R _ hP).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q Z : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q)
      (hZ : IsPerfectRingComplex.{u, w} Z),
    (coh.tensor f (P ⊗ Q) Z (coh.tensorPerfect R P Q hP hQ) hZ).hom ≫
        (coh.tensor f P Q hP hQ).hom ▷ (B.{u, w} f).obj Z ≫
        (α_ ((B.{u, w} f).obj P) ((B.{u, w} f).obj Q) ((B.{u, w} f).obj Z)).hom =
      (B.{u, w} f).map (α_ P Q Z).hom ≫
        (coh.tensor f P (Q ⊗ Z) hP (coh.tensorPerfect R Q Z hQ hZ)).hom ≫
        (B.{u, w} f).obj P ◁ (coh.tensor f Q Z hQ hZ).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q),
    (B.{u, w} f).map (symmetry.{u, w} R P Q).hom ≫ (coh.tensor f Q P hQ hP).hom =
      (coh.tensor f P Q hP hQ).hom ≫ (symmetry.{u, w} S ((B.{u, w} f).obj P) ((B.{u, w} f).obj
      Q)).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P),
    (coh.tensor f (𝟙_ (D.{u, w} R)) P (coh.unitPerfect R) hP).hom ≫
        (coh.unit f).hom ▷ (B.{u, w} f).obj P ≫ (λ_ ((B.{u, w} f).obj P)).hom = (B.{u, w} f).map (λ_
      P).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P),
    (coh.tensor f P (𝟙_ (D.{u, w} R)) hP (coh.unitPerfect R)).hom ≫
        (B.{u, w} f).obj P ◁ (coh.unit f).hom ≫ (ρ_ ((B.{u, w} f).obj P)).hom = (B.{u, w} f).map (ρ_
      P).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P),
    (coh.comp (𝟙 R) f P hP).hom = (B.{u, w} f).map (coh.identity R P hP).hom) ∧
  (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P),
    (coh.comp f (𝟙 S) P hP).hom = (coh.identity S ((B.{u, w} f).obj P) (coh.preserves f P
      hP)).hom) ∧
  (∀ {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U)
      (P : D.{u, w} R) (hP : IsPerfectRingComplex.{u, w} P),
    (B.{u, w} h).map (coh.comp f g P hP).hom ≫ (coh.comp (f ≫ g) h P hP).hom =
      (coh.comp g h ((B.{u, w} f).obj P) (coh.preserves f P hP)).hom ≫ (coh.comp f (g ≫ h) P
      hP).hom) ∧
  (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
      (P Q : D.{u, w} R) (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q),
    (coh.comp f g (P ⊗ Q) (coh.tensorPerfect R P Q hP hQ)).hom ≫
        (coh.tensor (f ≫ g) P Q hP hQ).hom =
      (B.{u, w} g).map (coh.tensor f P Q hP hQ).hom ≫
        (coh.tensor g ((B.{u, w} f).obj P) ((B.{u, w} f).obj Q) (coh.preserves f P hP)
      (coh.preserves f
      Q hQ)).hom ≫
        ((coh.comp f g P hP).hom ⊗ₘ (coh.comp f g Q hQ).hom)) ∧
  (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T),
    (coh.comp f g (𝟙_ (D.{u, w} R)) (coh.unitPerfect R)).hom ≫ (coh.unit (f ≫ g)).hom =
      (B.{u, w} g).map (coh.unit f).hom ≫ (coh.unit g).hom) ∧
  (∀ (R : CommRingCat.{u}) (P Q : D.{u, w} R)
      (hP : IsPerfectRingComplex.{u, w} P) (hQ : IsPerfectRingComplex.{u, w} Q),
    (coh.tensor (𝟙 R) P Q hP hQ).hom ≫
        ((coh.identity R P hP).hom ⊗ₘ (coh.identity R Q hQ).hom) =
      (coh.identity R (P ⊗ Q) (coh.tensorPerfect R P Q hP hQ)).hom) ∧
  (∀ (R : CommRingCat.{u}),
    (coh.unit (𝟙 R)).hom = (coh.identity R (𝟙_ (D.{u, w} R)) (coh.unitPerfect R)).hom)

private theorem Q_tensor_isIso (R : CommRingCat.{u})
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hk : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P) :
    IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ModuleCat R)) P Q) := by
  have hh := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hk
  have hi := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
    (Qh.{w} (C := ModuleCat R)) (HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ))
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q) hh
  have : IsIso (Functor.LaxMonoidal.μ Qh
      ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)) := hi
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map _) ≫ _)
  infer_instance

private theorem unit_model_isIso (R : CommRingCat.{u}) :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) := by
  have := DerivedCategory.isIso_ε_Qh.{w} (ModuleCat R)
  change IsIso ((Functor.LaxMonoidal.ε Qh ≫ Qh.map
    (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

private theorem normalized_tensor_ext (d e : CoherenceData.{u, w})
    (hd : d.Normalized) (he : e.Normalized)
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, w} R)
    (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q) :
    d.tensor f P Q hP hQ = e.tensor f P Q hP hQ := by
  obtain ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩ := hP
  have hP : IsPerfectRingComplex P := ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩
  obtain ⟨N, c, z, nlo, nhi, nt, ⟨j⟩⟩ := hQ
  have hQ : IsPerfectRingComplex Q := ⟨N, c, z, nlo, nhi, nt, ⟨j⟩⟩
  have hm : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj M) :=
    ⟨M, a, b, hlo, hhi, ht, ⟨Iso.refl _⟩⟩
  have hn : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj N) :=
    ⟨N, c, z, nlo, nhi, nt, ⟨Iso.refl _⟩⟩
  have := d.model f M a b hlo hhi ht
  have := d.model f N c z nlo nhi nt
  have := hhi
  have hk := CochainComplex.kFlat_of_isStrictlyLE_of_flat M b (fun n ↦ by
    have := (ht n).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance)
  have := Q_tensor_isIso S ((E f).obj M) ((E f).obj N) (kflat_extend f M hk)
  have hh : (d.tensor f _ _ hm hn).hom = (e.tensor f _ _ hm hn).hom := by
    apply (cancel_mono ((modelMap f M ⊗ₘ modelMap f N) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q ((E f).obj M) ((E f).obj N))).1
    exact (hd.2.2.2.1 f M N a b c z hlo hhi nlo nhi ht nt hm hn).symm.trans
      (he.2.2.2.1 f M N a b c z hlo hhi nlo nhi ht nt hm hn)
  apply Iso.ext
  apply (cancel_mono ((B f).map i.hom ⊗ₘ (B f).map j.hom)).1
  exact (hd.1 f P Q _ _ hP hQ hm hn i.hom j.hom).symm.trans
    ((congrArg ((B f).map (i.hom ⊗ₘ j.hom) ≫ ·) hh).trans
      (he.1 f P Q _ _ hP hQ hm hn i.hom j.hom))

private theorem normalized_unit_ext (d e : CoherenceData.{u, w})
    (hd : d.Normalized) (he : e.Normalized)
    {R S : CommRingCat.{u}} (f : R ⟶ S) : d.unit f = e.unit f := by
  have := unit_model_isIso S
  apply Iso.ext
  apply (cancel_mono (Functor.LaxMonoidal.ε
    (DerivedCategory.Q (C := ModuleCat S)))).1
  exact (hd.2.2.2.2.1 f).symm.trans (he.2.2.2.2.1 f)

private theorem normalized_comp_ext (d e : CoherenceData.{u, w})
    (hd : d.Normalized) (he : e.Normalized)
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (P : D.{u, w} R) (hP : IsPerfectRingComplex P) :
    d.comp f g P hP = e.comp f g P hP := by
  obtain ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩ := hP
  have hP : IsPerfectRingComplex P := ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩
  have hm : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj M) :=
    ⟨M, a, b, hlo, hhi, ht, ⟨Iso.refl _⟩⟩
  have := d.model (f ≫ g) M a b hlo hhi ht
  have hh : (d.comp f g _ hm).hom = (e.comp f g _ hm).hom := by
    apply (cancel_mono (modelMap (f ≫ g) M)).1
    exact (hd.2.2.2.2.2.1 f g M a b hlo hhi ht hm).symm.trans
      (he.2.2.2.2.2.1 f g M a b hlo hhi ht hm)
  apply Iso.ext
  apply (cancel_mono ((B (f ≫ g)).map i.hom)).1
  exact (hd.2.1 f g P _ hP hm i.hom).symm.trans
    ((congrArg ((B g).map ((B f).map i.hom) ≫ ·) hh).trans
      (he.2.1 f g P _ hP hm i.hom))

private theorem normalized_identity_ext (d e : CoherenceData.{u, w})
    (hd : d.Normalized) (he : e.Normalized)
    (R : CommRingCat.{u}) (P : D.{u, w} R) (hP : IsPerfectRingComplex P) :
    d.identity R P hP = e.identity R P hP := by
  obtain ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩ := hP
  have hP : IsPerfectRingComplex P := ⟨M, a, b, hlo, hhi, ht, ⟨i⟩⟩
  have hm : IsPerfectRingComplex.{u, w} (DerivedCategory.Q.obj M) :=
    ⟨M, a, b, hlo, hhi, ht, ⟨Iso.refl _⟩⟩
  have hh : (d.identity R _ hm).hom = (e.identity R _ hm).hom := by
    exact (hd.2.2.2.2.2.2.1 R M a b hlo hhi ht hm).symm.trans
      (he.2.2.2.2.2.2.1 R M a b hlo hhi ht hm)
  apply Iso.ext
  apply (cancel_mono i.hom).1
  exact (hd.2.2.1 R P _ hP hm i.hom).symm.trans
    ((congrArg ((B (𝟙 R)).map i.hom ≫ ·) hh).trans
      (he.2.2.1 R P _ hP hm i.hom))

private theorem normalized_ext (d e : CoherenceData.{u, w})
    (hd : d.Normalized) (he : e.Normalized) : d = e := by
  have ht : @d.tensor = @e.tensor := by
    funext R S f P Q hP hQ
    exact normalized_tensor_ext d e hd he f P Q hP hQ
  have hu : @d.unit = @e.unit := by
    funext R S f
    exact normalized_unit_ext d e hd he f
  have hc : @d.comp = @e.comp := by
    funext R S T f g P hP
    exact normalized_comp_ext d e hd he f g P hP
  have hi : d.identity = e.identity := by
    funext R P hP
    exact normalized_identity_ext d e hd he R P hP
  cases d
  cases e
  simp only [CoherenceData.mk.injEq]
  exact ⟨ht, hu, hc, hi⟩

/-- The balanced scalar comparisons with every equation and model normalization.
Source: Stacks 06Y6 and 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence).
Proof: follow the thirteen steps of perfect_scalar_tensor_coherence: finite projective
splittings give perfectness, tensor closure and the unit; bounded projectives are K-flat
and K-projective. Descend ordinary balanced scalar maps on those models. On pure tensors
the tensorator inserts one, its inverse multiplies scalars, the unit is multiplication,
and the tower multiplies the two scalar factors. Check naturality, associativity,
Koszul symmetry, both unitors, both tower units, four-ring associativity and the tensor
and unit squares on homogeneous generators. Lift arbitrary derived arrows to homotopy
classes of finite-projective models; full faithfulness preserves every equation.
The unique normalized components are exactly the witnesses of the existing Coherence
statement; collect these witnesses and their equations in the record, in the same order.
For uniqueness, two normalized data agree on each bounded finite-projective model by their
model equations. Every perfect object is isomorphic to such a model. Naturality transports
this agreement to its tensor, tower and identity components, and to the coefficient unit.
Faithfulness of localization on the models identifies the resulting derived maps. All
remaining fields are propositions, so proof irrelevance identifies them. -/
theorem perfect_scalar_tensor_coherence_data :
    ∃! d : CoherenceData.{u, w}, d.Normalized := by
  obtain ⟨preserves, tensorPerfect, unitPerfect, additive, linear, model,
    tensor, unit, comp, identity, hn, hc, hi, hm, hu, hcm, him, ha, hs,
    hl, hr, hcl, hcr, hf, hct, hcu, hit, hiu⟩ := perfect_scalar_tensor_coherence.{u, w}
  let d : CoherenceData.{u, w} :=
    ⟨preserves, tensorPerfect, unitPerfect, additive, linear, model,
      tensor, unit, comp, identity⟩
  have hd : d.Normalized :=
    ⟨hn, hc, hi, hm, hu, hcm, him, ha, hs, hl, hr, hcl, hcr, hf, hct, hcu, hit, hiu⟩
  exact ⟨d, hd, fun e he ↦ normalized_ext e d he hd⟩

/-- The scalar comparisons determined by their normalized finite-projective models.
These model equations determine the data on perfect objects and arbitrary derived
arrows between them; the record does not choose unspecified isomorphisms.
Source: Stacks 06Y6 and 0GWN (blueprint: lem-sf-perfect-scalar-tensor-coherence). -/
@[irreducible] def coherenceData : CoherenceData.{u, w} :=
  perfect_scalar_tensor_coherence_data.exists.choose

end DerivedCategory.PerfectScalar

end
