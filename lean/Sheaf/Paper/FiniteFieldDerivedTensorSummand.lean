/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.FieldTheory.Finite.GaloisField
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The diagonal summand for finite-field derived tensor

Source: Stacks Project, Tag 0C2X, finite-extension diagonal; Tags 03EK, 0GMW,
06YN, 06YS, 06YT and 06YU for the agent-formulated sheaf and derived comparison
(blueprint: lem-pur-finite-field-derived-tensor-summand).

The comparison is expressed as a natural split retraction. Its projector is the tensor-square
coefficient action, and both that action and the quotient map are specified on pure tensors
in every bidegree of the total complex. Thus its split image is exactly the termwise
idempotent summand, and its quotient map is the canonical balanced tensor morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace FiniteFieldDerivedTensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v}]

/-- The existing constant commutative-ring sheaf.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev coefficients (A : Type (max u v)) [CommRing A] :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of A)

/-- Its underlying ring sheaf, using the canonical forgetful functor.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev rings (A : Type (max u v)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj (coefficients J A)

/-- The recorded category of modules over the constant ring sheaf.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Modules (A : Type (max u v)) [CommRing A] :=
  ringedSiteModules.{max u v} (rings J A)

/-- Unbounded cochain complexes of those module sheaves.
Source: Stacks 06YN (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Complexes (A : Type (max u v)) [CommRing A] :=
  CochainComplex (Modules J A) ℤ

/-- The existing total tensor bifunctor, with direct sums along integer diagonals.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def total (A : Type (max u v)) [CommRing A] :
    Complexes J A × Complexes J A ⥤ Complexes J A :=
  Functor.uncurry.obj ((@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The canonical constant section associated to an element of the coefficient ring.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def constantSection (A : Type (max u v)) [CommRing A]
    (X : Cᵒᵖ) (a : A) : (coefficients J A).obj.obj X :=
  ((sheafificationAdjunction J CommRingCat.{max u v}).unit.app
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app X a

/-- A pure tensor in the sheaf tensor, through its sheafification presentation.
Source: Stacks 03EK, 0GMW (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def tensorSection (A : Type (max u v)) [CommRing A]
    (M N : Modules J A) (X : Cᵒᵖ) (m : M.val.obj X) (n : N.val.obj X) :
    ((@tensorObj (Modules J A) _ (SheafOfModules.monoidalCategory
      (coefficients J A)).toMonoidalCategoryStruct M N).val.obj X) :=
  ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app X)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rings J A).obj)).unit.app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app X
        (TensorProduct.tmul ((coefficients J A).obj.obj X) m n))

/-- A pure tensor in bidegree `(i,j)` included in the total complex.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def generator (A : Type (max u v)) [CommRing A]
    (K L : Complexes J A) (i j : ℤ) (X : Cᵒᵖ)
    (m : (K.X i).val.obj X) (n : (L.X j).val.obj X) :
    (((total J A).obj (K, L)).X (i + j)).val.obj X :=
  ((CochainComplex.ιMapBifunctor K L (@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))) i j (i + j) rfl).val.app X)
      (tensorSection J A (K.X i) (L.X j) X m n)

/-- The existing constant-sheaf ring morphism of a field extension.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def coefficientMap (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : rings J F ⟶ rings J B :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom (algebraMap F B)))

/-- Termwise restriction of scalars, using the recorded restriction functor.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def restrictComplex (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : Complexes J B ⥤ Complexes J F :=
  (SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The full subcategory of compatible flat-term K-flat representatives.
Source: Stacks 06YN, 06YS (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def representatives (A : Type (max u v)) [CommRing A] :
    ObjectProperty (Complexes J A) :=
  fun K ↦ K.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, exactFunctor _ _
    ((@curriedTensor (Modules J A) _
      (SheafOfModules.monoidalCategory (coefficients J A))).flip.obj (K.X n))

variable (A : Type (max u v)) [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)]

/-- The existing unbounded derived category.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Derived := DerivedCategory (Modules J A)

/-- The representative comparison for a tensor functor supplied by derived tensor descent.
This is packaging of the recorded tensor-computation clause, not another tensor definition.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
structure Presentation where
  tensor : Derived J A × Derived J A ⥤ Derived J A
  comparison : ((representatives J A).ι.prod (representatives J A).ι) ⋙ total J A ⋙
    DerivedCategory.Q ≅
    (((representatives J A).ι ⋙ DerivedCategory.Q).prod
      ((representatives J A).ι ⋙ DerivedCategory.Q)) ⋙ tensor

variable {J}
variable {F B : Type (max u v)} [Field F] [Field B] [Algebra F B]
  [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]

/-- The source tensor after restriction, as an existing tensor bifunctor composite.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def source (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := (res.prod res) ⋙ TF.tensor

/-- The target tensor followed by restriction.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def target (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := TB.tensor ⋙ res

/-- The canonical source comparison on compatible K-flat representatives.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def sourceComparison (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B)
    (hK : representatives J F ((restrictComplex J F B).obj K))
    (hL : representatives J F ((restrictComplex J F B).obj L)) :
    DerivedCategory.Q.obj ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L)) ≅
      (source TF res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  TF.comparison.app (⟨(restrictComplex J F B).obj K, hK⟩,
    ⟨(restrictComplex J F B).obj L, hL⟩) ≪≫
      TF.tensor.mapIso ((r.app K).prod (r.app L))

/-- The canonical target comparison on flat-term K-flat representatives.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def targetComparison (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B) (hK : representatives J B K) (hL : representatives J B L) :
    DerivedCategory.Q.obj ((restrictComplex J F B).obj ((total J B).obj (K, L))) ≅
      (target TB res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  r.app ((total J B).obj (K, L)) ≪≫ res.mapIso (TB.comparison.app (⟨K, hK⟩, ⟨L, hL⟩))

/-- The canonical coefficient action and balanced tensor map on total complexes,
with their pure-generator characterization in every bidegree.
Source: Stacks 03EK, 0GMW, 06YU
(blueprint: lem-pur-finite-field-derived-tensor-summand). -/
structure ChainComparison where
  chainAction : ∀ K L : Complexes J B,
    (B ⊗[F] B) →+* End ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L))
  chainBalanced :
    ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
      total J B ⋙ restrictComplex J F B
  action_generator : ∀ (K L : Complexes J B) (a b : B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainAction K L) (a ⊗ₜ[F] b)).f (i + j)).val.app X
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) =
    generator J F ((restrictComplex J F B).obj K)
      ((restrictComplex J F B).obj L) i j X
        (constantSection J B X a • m) (constantSection J B X b • n)
  balanced_generator : ∀ (K L : Complexes J B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainBalanced.app (K, L)).f (i + j)).val.app X)
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) = generator J B K L i j X m n

/-- The natural split-retraction formulation of the asserted diagonal-summand isomorphism.
The pure-generator equations pin down the coefficient action and balanced quotient before
localization; the comparison squares pin them down on arbitrary derived objects and arrows.
`balanced ≫ splitting = action e` identifies the split image with the termwise e-image.
Source: Stacks 0C2X, 03EK, 06YU and the node's explicit derived formulation
(blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def HasDiagonalComparison (TF : Presentation J F) (TB : Presentation J B)
    (e : B ⊗[F] B) : Prop :=
  ∃ (res : Derived J B ⥤ Derived J F)
    (restriction : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K))
    (action : (B ⊗[F] B) →+* End (source TF res))
    (balanced : source TF res ⟶ target TB res)
    (splitting : target TB res ⟶ source TF res)
    (chain : ChainComparison (J := J) (F := F) (B := B)),
    (splitting ≫ balanced = 𝟙 (target TB res)) ∧
    (balanced ≫ splitting = action e) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L) (x : B ⊗[F] B),
      DerivedCategory.Q.map (chain.chainAction K L x) ≫
        (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        (action x).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L),
      DerivedCategory.Q.map (chain.chainBalanced.app (K, L)) ≫
        (targetComparison TB res restriction K L hK hL).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        balanced.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))

/-- Finite-field derived tensor over the larger field is the diagonal idempotent summand
of derived tensor over the smaller field, naturally in both unbounded derived variables.
The two nonemptiness clauses also assert existence of the tensor presentations, so the
quantification over presentations cannot make the statement vacuous.

Source: Stacks 0C2X, finite-extension motivation; the explicit projector and derived
comparison are the agent formulation in the node. Sheaf tensor: 03EK, 0GMW;
K-flat resolutions and derived descent: 06YN, 06YS, 06YT, 06YU
(blueprint: lem-pur-finite-field-derived-tensor-summand).

Proof plan:
1. Put q = card B. The finite-field cardinal-power identity gives r^q = r in
   B tensor_F B: Frobenius preserves sums and products, and it fixes pure tensors
   (lem-weil-finite-field-pow-card; def-weil-finite-field-q-elements).
2. For d_b = b tensor 1 - 1 tensor b take e = product_b (1 - d_b^(q-1)). Then
   d_b e = 0 and multiplication sends e to 1. For every r one has
   r e = (mu(r) tensor 1)e, whence e^2 = e. This includes F = B and q = 2.
3. On ordinary sheaf tensors let beta(m tensor_F n) = m tensor_B n. Writing
   e = sum a_i tensor c_i, define s(m tensor_B n) = sum a_i m tensor_F c_i n.
   The annihilator identities ensure B-balancing. The module-sheafification interface
   and bilinear extension extend these formulas to the sheafified constant ring,
   including sections which are only locally constant. Uniqueness gives beta s = 1
   and s beta = e and naturality in both sheaves
   (lem-pc-sites-module-sheafification-interface;
   lem-pc-sites-module-sheafification-bilinear-extension; def-pur-sheaf-tensor-product).
4. A finite F-basis of B gives B_C = F_C^d, using underlying-set compatibility and
   colimit preservation of sheafification. Extension is therefore exact. Restriction
   is exact and preserves sums because its underlying abelian sheaf is unchanged
   (lem-pc-sites-sheafification-underlying-sets;
   lem-weil-pbc-site-r-module-presheaf-sheafification-exact; def-pc-sheaf-restrict-scalars).
5. Choose flat-term K-flat resolutions over B. For an acyclic F-complex A,
   Res Tot((A tensor_F B) tensor_B U) = Tot(A tensor_F Res U). Exact extension
   and B-K-flatness imply F-K-flatness of Res U. The same identity in each degree
   proves flatness of its terms; exact restriction preserves the resolutions
   (lem-pc-kflat-resolution; def-pc-kflat-complex; def-pc-flat-sheaf-modules).
6. Totalize the ordinary maps over all integer bidegrees. B-linear differentials
   commute with e; the splitting t = et + (1-e)t is a splitting of complexes.
   The formulas in step 3 commute with both total differentials and give the
   displayed pure-generator equations and the coefficient tensor-square action
   (def-pc-tensor-complex-sheaves).
7. Apply lem-weil-pbc-site-derived-tensor-descent over both fields. Its computation and
   transformation-uniqueness clauses descend the actions, beta and s to all derived
   arrows, independently of representatives. The two retraction identities identify
   the termwise e-image with Res(P tensor_B^L Q), through the canonical beta.
   On the one-point site these are ordinary module derived categories. No
   boundedness, finite-dimensionality, nonzero complex or nonempty site is used. -/
theorem exists_diagonal_derived_tensor_summand
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{max u v}]
    (F B : Type (max u v))
    [Field F] [Field B] [Finite F] [Finite B] [Algebra F B]
    [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)] :
    ∃ e : B ⊗[F] B,
      e * e = e ∧ Algebra.TensorProduct.lmul' F e = 1 ∧
      (∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) ∧
      Nonempty (Presentation J F) ∧ Nonempty (Presentation J B) ∧
      ∀ (TF : Presentation J F) (TB : Presentation J B), HasDiagonalComparison TF TB e := by
  sorry

end FiniteFieldDerivedTensor
