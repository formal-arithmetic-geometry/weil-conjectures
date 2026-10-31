/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.NormalizedCoefficientDiagramSupplement
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.SystemScalarCoherence
public import Mathlib.CategoryTheory.Products.Basic

import WeilConjectures.SecSmoothPurity.CoefficientComparisonsStrictTotalization
import WeilConjectures.SecSmoothPurity.CoefficientComparisonsUnitComposition

/-! # Simultaneous strict coefficient comparisons

Source: Stacks 03EL and 07A4; the agent calculations in the eight proof steps of
lem-pur-strict-coefficient-comparison-calculus
(blueprint: lem-pur-strict-coefficient-comparison-calculus).

The product index records coefficient changes and all inverse-sequence arrows.
Semilinear arrows are written in their scalar-extension adjoint form. Thus they
are arbitrary chain maps out of scalar extension, including zero maps, rather
than only the scalar-extension units. All tensors are the existing sheafified
module tensor and its signed direct-sum total complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option maxErrors 5
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

private theorem comparison_unique {A : Sheaf J CommRingCat.{w}}
    {B : Sheaf K CommRingCat.{w}} (f : RingedPullback A B)
    (a b : Comparison f) : a = b := by
  let : PreservesFiniteLimits f.uInv := f.finiteLimits
  have : Subsingleton (Comparison f) :=
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
      A B f.RI f.uInv f.I f.coefficient f.L f.hobj f.uPush f.adj f.hmap).2
  exact Subsingleton.elim a b

/-- Unique simultaneous normalized comparisons, satisfying the full strict
coefficient calculus on possibly unbounded complexes.
Source: Stacks 03EL, 07A4 and the eight agent calculations recorded in the node
(blueprint: lem-pur-strict-coefficient-comparison-calculus).

Proof:
1. Apply lem-pur-cochain-pullback-tensor-coherence at each vertex and to each
   identity-topos coefficient arrow to obtain c and sigma. Factor the compatible
   coefficient square in its two orders; scalar association gives kappa.
2. Balance the forward kappa formula using i_X phi = phi' i_Y. Balance its inverse
   using the same square. Their composites are identities on generalized local
   tensors. def-pur-sheaf-tensor-product and
   def-weil-presheaf-modules-sheafification extend these identities uniquely.
3. Sigma inserts one in its second factor; its inverse multiplies the two scalars.
   Tensor balancing proves both formulas and their mutual inverseness. The
   universal property gives naturality and uniqueness of both families.
4. The maps preserve degree. Naturality gives commutation with d tensor 1 and
   1 tensor d separately; additivity preserves (-1)^p. The direct-sum universal
   property in def-pc-tensor-complex-sheaves gives the unbounded chain maps.
5. For an arbitrary semilinear transition, both kappa routes give
   rho(b) i(rho(a)) tensor (1 tensor t(x)); the inverse uses the phi square.
   Sigma and c give (rho(b) tensor t(x)) tensor (1 tensor t(y)). These identities
   hold for every arrow, and for arbitrary scalar-extension adjoints f and g.
6. On b tensor (a tensor (x tensor y)) the two coefficient-square routes give
   (b i(a) tensor (1 tensor x)) tensor (1 tensor (1 tensor y)). Sheafification
   and direct-sum uniqueness give the equality of isomorphisms and inverses.
7. Scalar units multiply a tensor x to ax. Both kappa and sigma then become
   identities. Scalar associators multiply d tensor (b tensor x) to d i(b)
   tensor x; their inverses insert one. These are the adjoint-uniqueness maps
   used in scalarUnit and scalarComp.
8. The two successive kappa routes multiply to d i12(b) i02(a); successive sigma
   routes give (d i12(b) tensor x) tensor (1 tensor y). Balancing, sheafification
   and the direct-sum universal property give every composition equation.
   Equality of isomorphisms gives the inverse equations. No flatness, nonzero
   ring, boundedness or normalization of the sequence transitions was used.
-/
theorem strictCoefficientComparisonCalculus (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) :
    ∃! e : Comparisons d, e.Normalized k ∧ e.Laws k := by
  classical
  let e : Comparisons d :=
    { kappa := fun {i j} t ↦ (scalarAssociation (d.ringed i) (k i) (d.square t) (k j)).symm
      sigmaR := fun t ↦ extensionComparison (d.R.map t)
      sigmaS := fun t ↦ extensionComparison (d.S.map t) }
  have hn : e.Normalized k := by
    intro i j t
    exact (Classical.choose_spec
      (scalarAssociation_existsUnique (d.ringed i) (k i) (d.square t) (k j))).1
  obtain ⟨_, hκ, _, hR, hS, _, _, _, _, hT, _, hSq, _⟩ :=
    coefficientComparisonsStrictTotalization d k e hn
  obtain ⟨_, _, _, _, _, _, _, _, huR, huS, huκ, hcκ⟩ :=
    coefficientComparisonsUnitComposition d k e hn ⟨hκ, hR, hS⟩
  refine ⟨e, ⟨hn, huR, huS, hR, hS, hκ, hSq, huκ, hcκ, hT⟩, ?_⟩
  intro e' he'
  have hk : @e'.kappa = @e.kappa := by
    funext i j t
    have h := (Classical.choose_spec
      (scalarAssociation_existsUnique (d.ringed i) (k i) (d.square t) (k j))).2
        (e'.kappa t).symm (he'.1 t)
    exact congrArg Iso.symm h
  have hr : @e'.sigmaR = @e.sigmaR := by
    funext i j t
    exact comparison_unique _ _ _
  have hs : @e'.sigmaS = @e.sigmaS := by
    funext i j t
    exact comparison_unique _ _ _
  cases e' with
  | mk a b c =>
    change @a = @e.kappa at hk
    change @b = @e.sigmaR at hr
    change @c = @e.sigmaS at hs
    subst a
    subst b
    subst c
    rfl

end CategoryTheory.CochainPullback.StrictCoefficient
