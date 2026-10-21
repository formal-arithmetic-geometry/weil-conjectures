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
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic

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
