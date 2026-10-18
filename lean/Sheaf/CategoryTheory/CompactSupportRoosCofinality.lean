/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Cofinality of the arithmetic Roos tower

Source: Stacks Project, Cohomology on Sites, Tag 0941, and Modules on Sites,
Tag 03EK; the explicit finite-block comparison and scalar-extension refinement
in the proof of `lem-pur-compact-support-integral-coefficient-comparison`
(blueprint: lem-pur-compact-support-roos-cofinality).

The category parameter below is instantiated by `Mod (underline A)` for a
small site and its constant ring sheaf.  The recorded arithmetic restriction,
selection and block maps are the canonical constructions from Tags 0H9K and
0941.  The theorem is statement-only at this stage.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC r vA vB

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory

/-- The constant coefficient ring, with its commutative-ring structure forgotten only
when forming its module category. Source: Stacks 03EK and 0941
(blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosRing {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] (A : CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj ((constantSheaf J CommRingCat).obj A)

/-- The recorded module category of the constant coefficient ring.
Source: Stacks 03EK and 0941 (blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosModules {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] (A : CommRingCat.{r}) :=
  ringedSiteModules.{r} (compactRoosRing J A)

/-- Termwise application of an additive functor to a complex.
Source: Stacks 03EK, degree-zero scalar extension
(blueprint: lem-pur-compact-support-roos-cofinality). -/
abbrev compactRoosComplexMap {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise application to the objects and transitions of a strict tower complex.
Source: Stacks 03EK and 0941 (blueprint: lem-pur-compact-support-roos-cofinality). -/
abbrev compactRoosTowerMap {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical tensor/product comparison, determined by all product projections.
Source: Stacks 03EK, finite-dual-basis calculation in the node's proof step 6
(blueprint: lem-pur-compact-support-roos-cofinality). -/
noncomputable abbrev compactRoosProductComparison
    {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (compactRoosComplexMap F).obj (strictRoosProduct X) ⟶
      strictRoosProduct ((compactRoosTowerMap F).obj X) :=
  piComparison (compactRoosComplexMap F) (fun n : ℕ ↦ X.asFunctor.obj (op n))

/-- The cofinal maps are a single family, natural for every strict tower map, with
strict identity and composition after equality transport of the reindexed complexes.
`HEq` expresses that transport without choosing a further isomorphism: the index
functors for iterated restriction and restriction by the product are equal.
The target coordinate is `block` and the source coordinate is `selection`.

Source: Stacks 0941 and 0H9K; explicit proof steps 1--5 of this node
(blueprint: lem-pur-compact-support-roos-cofinality).
Proof, following the node's steps 1--5:
1. Write T(i,j) for the transition composite and D=1-s. Finite telescoping gives
   b_e D = D_e a_e. Both product maps commute with internal differentials, hence
   `(y,x) ↦ (b_e y,a_e x)` is the specified map of shifted cones.
2. Let m(i) be the next retained index. Extend a retained source family by
   α(u)_i=T(i,m(i))u_(m(i)/e), including the initial indices before e. Extend a
   retained target family by β(v)_(en)=v_n and zero elsewhere. Then a_e α=1,
   b_e β=1 and D α=β D_e, giving a chain section j of r_e.
3. On U=ker(a_e) and V=ker(b_e), the inverse c of D:U→V is zero at retained
   indices and c(y)_i=Σ_(i≤k<m(i)) T(i,k)y_k otherwise. Telescoping proves cD=1;
   Dc=1 at a retained index follows from b_e y=0. These are finite sheaf maps
   commuting with internal differentials; transition surjectivity is unnecessary.
4. In source-first signed coordinates the kernel differential is
   `(u,v) ↦ (du,Du-dv)`. Its homotopy h(u,v)=(cv,0) satisfies dh+hd=1.
   Composing h with 1-jr_e gives a homotopy from jr_e to 1. Thus H(j) is the
   inverse of H(r_e) in every degree, proving the displayed quasi-isomorphism.
5. A strict tower map commutes with every T(i,j), hence with selection and block.
   Iterated selection selects the product index. The iterated block sum partitions
   the single larger block, giving strict composition; a one-term block gives r_1=1.
   Finally Dγ=0 for a compatible family and r_e(0,γ)=(0,a_e γ), giving exactly
   the two displayed augmentation maps and their equality. -/
theorem compactSupportRoosCofinality
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A : CommRingCat.{max uC vC r})
    [HasExactLimitsOfShape (Discrete ℕ) (compactRoosModules J A)] :
    ∃ ρ : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (e : ℕ) (_he : 1 ≤ e),
        (strictRoosComplex X ⟶
          strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X)),
      (∀ X e he, QuasiIso (ρ X e he) ∧
        ∀ p : ℤ,
          (ρ X e he).f (p + 1) ≫
              (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((block e X.asFunctor).f p)
                ((selection e X.asFunctor).f (p + 1))) ∧
      (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (f : X ⟶ Y) (e : ℕ) (he : 1 ≤ e),
        ∃ (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
          (μe : strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X) ⟶
            strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj Y)),
          (∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((strictRoosProductMap f).f p)
                ((strictRoosProductMap f).f (p + 1))) ∧
          (∀ p : ℤ, μe.f (p + 1) ≫
              (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj Y) p).hom =
            (strictRoosCoordinates ((complexRestriction (compactRoosModules J A) e).obj X) p).hom ≫
              biprod.map ((strictRoosProductMap
                ((complexRestriction (compactRoosModules J A) e).map f)).f p)
                ((strictRoosProductMap
                  ((complexRestriction (compactRoosModules J A) e).map f)).f (p + 1))) ∧
          μ ≫ ρ Y e he = ρ X e he ≫ μe) ∧
      (∀ X, HEq (ρ X 1 (by decide)) (𝟙 (strictRoosComplex X))) ∧
      (∀ X e he f hf,
        HEq (ρ X e he ≫ ρ ((complexRestriction (compactRoosModules J A) e).obj X) f hf)
          (ρ X (e * f) (one_le_mul he hf))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ) (e : ℕ) (he : 1 ≤ e)
          (P : CochainComplex (compactRoosModules J A) ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)),
        (∀ n : ℕ,
          γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) →
        ∃ b : P ⟶ strictRoosComplex X,
          (∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
            biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) γ).f (p + 1))) ∧
          ∃ b' : P ⟶ strictRoosComplex ((complexRestriction (compactRoosModules J A) e).obj X),
            (∀ p : ℤ, b'.f (p + 1) ≫
                (strictRoosCoordinates
                ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
              biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
                γ (e * (n + 1) - 1))).f (p + 1))) ∧
            b ≫ ρ X e he = b') := by
  sorry

/-- Finite-free change of constant coefficients commutes canonically with the actual
Roos complex. The functor `F` is fixed on objects and maps by the recorded sheafified
sectionwise change-of-rings construction, rather than an arbitrary tensor operation.
Its target is the category of modules over the constant sheaf of `B`, so every map
and the resulting isomorphism are B-linear. The coordinate equation specifies the
canonical product and biproduct comparisons, including both shifted cone summands.
Naturality, cofinal restriction, and the scalar extension of augmentations are explicit.

Source: Stacks 03EK, 0941 and the finite-dual-basis refinement in proof steps 6--7
(blueprint: lem-pur-compact-support-roos-cofinality).
Proof, following the node's steps 6--7 (using def-pur-sheaf-tensor-product and
 def-weil-pbc-module-tensor-product):
6. Sheafify sectionwise scalar extension and its maps to obtain the additive F
   with exactly the stated object and morphism formulas. Choose a finite A-basis
   b_a of B with dual maps λ_a. The maps m⊗b ↦ (λ_a(b)m)_a and
   (m_a)_a ↦ Σ_a m_a⊗b_a identify scalar extension with a finite power.
   The basis identity holds on the constant presheaf and then on its sheafification.
   The canonical product comparison becomes the rearrangement of a finite power
   of a countable product. Its inverse is Σ_a (m_(i,a))_i⊗b_a, a finite sum of
   sheaf maps. The basis proves invertibility and does not choose the comparison.
7. The product map sends (m_i)_i⊗b to (m_i⊗b)_i on local tensor generators,
   so it is B-linear and natural. The analogous biproduct comparison commutes
   with negatives, internal differentials and shifts. Since the product comparison
   also commutes with the tower shift s, the displayed two-coordinate map is the
   asserted isomorphism θ of actual complexes. Coordinate selection commutes
   with tensor, and a finite transition sum tensored with b is the same finite
   sum of the tensored transitions. This gives the cofinal square. Applying it
   to (0,γ) gives the stated scalar-extended augmentation. Equality on local
   tensor generators descends through sheafification and proves all naturality. -/
theorem compactSupportRoosFiniteFree
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A B : CommRingCat.{max uC vC r}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B]
    [HasExactLimitsOfShape (Discrete ℕ)
      (compactRoosModules J A)] :
    ∃ (F : compactRoosModules J A ⥤
          compactRoosModules J B)
      (_hF : F.Additive),
      (∀ M, F.obj M = SheafOfModules.changeOfRingsOfUniverses
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M) ∧
      (∀ M N (f : M ⟶ N), HEq (F.map f)
        (SheafOfModules.changeOfRingsHomOfUniverses
          ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M f)) ∧
      ∃ θ : ∀ X : CochainComplex
          (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ,
          (compactRoosComplexMap F).obj (strictRoosComplex X) ≅
            strictRoosComplex ((compactRoosTowerMap F).obj X),
        (∀ X (p : ℤ), (θ X).hom.f (p + 1) ≫
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
          F.map (strictRoosCoordinates X p).hom ≫
            F.biprodComparison ((strictRoosProduct X).X p)
              ((strictRoosProduct X).X (p + 1)) ≫
            biprod.map ((compactRoosProductComparison F X).f p)
              ((compactRoosProductComparison F X).f (p + 1))) ∧
        (∀ X Y (f : X ⟶ Y),
          ∃ (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
            (ν : strictRoosComplex ((compactRoosTowerMap F).obj X) ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj Y)),
          (∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((strictRoosProductMap f).f p)
                ((strictRoosProductMap f).f (p + 1))) ∧
          (∀ p : ℤ, ν.f (p + 1) ≫
              (strictRoosCoordinates ((compactRoosTowerMap F).obj Y) p).hom =
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom ≫
              biprod.map ((strictRoosProductMap ((compactRoosTowerMap F).map f)).f p)
                ((strictRoosProductMap ((compactRoosTowerMap F).map f)).f (p + 1))) ∧
          (compactRoosComplexMap F).map μ ≫ (θ Y).hom = (θ X).hom ≫ ν) ∧
        (∀ X (e : ℕ) (_he : 1 ≤ e),
          ∃ (ρ : strictRoosComplex X ⟶ strictRoosComplex
              ((complexRestriction (compactRoosModules J A) e).obj X))
            (ρB : strictRoosComplex ((compactRoosTowerMap F).obj X) ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj
                ((complexRestriction (compactRoosModules J A) e).obj X))),
          (∀ p : ℤ, ρ.f (p + 1) ≫ (strictRoosCoordinates
              ((complexRestriction (compactRoosModules J A) e).obj X) p).hom =
            (strictRoosCoordinates X p).hom ≫
              biprod.map ((block e X.asFunctor).f p)
                ((selection e X.asFunctor).f (p + 1))) ∧
          (∀ p : ℤ, ρB.f (p + 1) ≫ (strictRoosCoordinates ((compactRoosTowerMap F).obj
              ((complexRestriction (compactRoosModules J A) e).obj X)) p).hom =
            (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom ≫
              biprod.map ((block e ((compactRoosTowerMap F).obj X).asFunctor).f p)
                ((selection e ((compactRoosTowerMap F).obj X).asFunctor).f (p + 1))) ∧
          (compactRoosComplexMap F).map ρ ≫
              (θ ((complexRestriction (compactRoosModules J A) e).obj X)).hom =
            (θ X).hom ≫ ρB) ∧
        (∀ X (P : CochainComplex (compactRoosModules J A) ℤ)
            (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
            (b : P ⟶ strictRoosComplex X),
          (∀ n : ℕ, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) →
          (∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates X p).hom =
            biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) γ).f (p + 1))) →
          ∃ bB : (compactRoosComplexMap F).obj P ⟶
              strictRoosComplex ((compactRoosTowerMap F).obj X),
            (∀ p : ℤ, bB.f (p + 1) ≫
                (strictRoosCoordinates ((compactRoosTowerMap F).obj X) p).hom =
              biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦
                ((compactRoosTowerMap F).obj X).asFunctor.obj (op n))
                  (fun n : ℕ ↦ (compactRoosComplexMap F).map (γ n))).f (p + 1))) ∧
            (compactRoosComplexMap F).map b ≫ (θ X).hom = bB) := by
  sorry

end CategoryTheory
