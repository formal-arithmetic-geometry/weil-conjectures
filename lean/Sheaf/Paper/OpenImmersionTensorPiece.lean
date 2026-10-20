/-*
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization


/-!
# The open-immersion piece of the projection formula

Source: Weil conjectures blueprint, proper base change, lemma 1269;
Stacks Project, Tags 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

/-- The full subcategory on objects admitting a bounded finite-projective representative.
This is a global strict-perfect condition, with degreewise splittings and variable ranks;
it imposes no compatibility of the splittings with the differentials.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorCoefficients (R : Sheaf J CommRingCat.{u + 1}) : ObjectProperty (Der R) :=
  fun Q ↦ ∃ F : CochainComplex (Mod R) ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
      Nonempty (StrictPerfectCoefficientPackageOnSite
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F) ∧
      Nonempty (Q ≅ DerivedCategory.Q.obj F)

/-- The left side of the open formula, as a bifunctor on unbounded E and strict-perfect F.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorSource (R : Sheaf J CommRingCat.{u + 1}) (U : C) (a : TensorModel R) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((localizedModuleExtension R U).mapDerivedCategory.prod (openTensorCoefficients R).ι) ⋙
    a.functor

/-- The right side of the open formula; restriction and extension are computed termwise.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorTarget (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (b : TensorModel (R.over U)) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((𝟭 (Der (R.over U))).prod
    ((openTensorCoefficients R).ι ⋙ (localizedModuleRestriction R U).mapDerivedCategory)) ⋙
      b.functor ⋙ (localizedModuleExtension R U).mapDerivedCategory

/-- The canonical restriction-tensor interface, at fixed original site universes.
Source: Stacks 03EL and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
abbrev openTensorRestrictionComparison (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U) :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  TensorComparison (R := R) (S := R.over U)
    (localizedModuleRestriction R U) r.model a b r.ordinaryTensor

/-- The natural open tensor isomorphism with its exact adjunction-unit normalization.
This predicate spells out the canonical map using the existing normalized tensor models.
Source: blueprint lemma 1269; Stacks 03DI and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorFormula (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U)
    (t : openTensorRestrictionComparison R U a b r) : Prop :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  ∃! beta : openTensorSource R U a ≅ openTensorTarget R U b,
      ∀ (E : Der (R.over U)) (F : (openTensorCoefficients R).FullSubcategory),
        (localizedModuleDerivedAdjunction R U).homEquiv _ _
            (beta.inv.app (E, F)) =
          b.functor.map (CategoryTheory.Prod.mkHom
            ((localizedModuleDerivedAdjunction R U).unit.app E)
            (𝟙 ((localizedModuleRestriction R U).mapDerivedCategory.obj F.obj))) ≫
              t.comparison.inv.app
                ((localizedModuleExtension R U).mapDerivedCategory.obj E, F.obj)

/-- The canonical open tensor map is an isomorphism, natural in both derived variables.
The equation characterizes its inverse as the adjunction projection map: its adjunct
is the unit tensored with the restricted coefficient, followed by the inverse of the
canonical restriction-tensor comparison. Thus the direction and normalization are fixed.
The open site is presented on the slice at `ProEt.mk c.i`, with the restricted ring R;
no comparison with any independently chosen coefficient sheaf occurs.

Source: blueprint lemma 1269; Stacks 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).

Proof:
1. Use lem-weil-proetale-weakly-etale-localization to identify the open site with the
   slice, using only its underlying-site equivalence. Exact extension and restriction
   from lem-pur-site-restriction-module-adjunction-exact act termwise on unbounded
   complexes by lem-sf-exact-functor-derived-triangulated. Choose any representative I
   of E; there is no boundedness requirement on I.
2. Transpose the ordinary unit tensored with the restricted module, using the canonical
   comparison of lem-weil-pbc-ringed-topoi-module-pullback-tensor. For a finite free
   coefficient the resulting map is the finite-sum comparison: identify each inclusion
   by its adjunct. The adjunction proves this comparison invertible, including rank zero.
3. For a splitting i,p from def-weil-pbc-strict-perfect-coefficient-package, first apply
   tensor i, then the finite-free inverse, then extension of tensor p. Naturality and pi=1
   give both inverse laws. Inverting the naturality equation proves naturality for
   arbitrary term maps, independently of the chosen splitting.
4. Both coefficient complexes are K-flat: each term is flat as a retract of a finite
   free sheaf, and lem-pc-bounded-above-flat-kflat-site applies. By
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-site-derived-tensor-descent, signed total tensor computes derived tensor.
   For an arbitrary representative I use lem-pc-kflat-resolution; tensoring its
   quasi-isomorphism with the K-flat coefficient preserves quasi-isomorphisms, by
   def-pc-kflat-complex applied to its cone. Exact extension preserves these maps.
5. In degree n sum the inverse term maps over a+r=n. These sums are finite since F is
   bounded. Naturality commutes with both differentials; the second has the same sign
   (-1)^a on each side by def-pc-tensor-complex-sheaves. The total maps are inverse.
   Naturality also holds for homotopies (with sign (-1)^a in the second variable),
   then descends through inversion of quasi-isomorphisms to both derived variables.
   The unit definition identifies the inverse with the stated projection map.
   Adjunction bijectivity determines that inverse, hence the natural isomorphism uniquely. -/
/-
Existence of the normalized open tensor isomorphism. The construction follows
the finite-free retract argument in the proof of blueprint lemma 1269: first
construct the adjunct comparison for finite free coefficients, then transport
it through the degreewise strict-perfect splittings and signed totalization.
The K-flat resolution and descent steps identify this total comparison with the
two derived tensor models. This is the only non-formal existence step; the
main theorem below supplies the formal uniqueness argument.
Source: Stacks 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).
-/
theorem openImmersionTensor_exists {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    letI : (localizedModuleRestriction R (ProEt.mk c.i)).Additive :=
      localizedModuleRestriction_additive R (ProEt.mk c.i)
    ∃ beta : openTensorSource R (ProEt.mk c.i) a ≅
        openTensorTarget R (ProEt.mk c.i) b,
      ∀ (E : Der (R.over (ProEt.mk c.i)))
        (F : (openTensorCoefficients R).FullSubcategory),
        (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv _ _
            (beta.inv.app (E, F)) =
          b.functor.map (CategoryTheory.Prod.mkHom
            ((localizedModuleDerivedAdjunction R (ProEt.mk c.i)).unit.app E)
            (𝟙 ((localizedModuleRestriction R (ProEt.mk c.i)).mapDerivedCategory.obj F.obj))) ≫
              t.comparison.inv.app
                ((localizedModuleExtension R (ProEt.mk c.i)).mapDerivedCategory.obj E, F.obj) := by
  sorry

theorem openImmersionTensor_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    openTensorFormula R (ProEt.mk c.i) a b r t := by
  dsimp [openTensorFormula]
  obtain ⟨beta, hbeta⟩ := openImmersionTensor_exists c R a b r t
  refine ⟨beta, hbeta, ?_⟩
  intro beta' hbeta'
  apply Iso.ext_inv
  ext obj
  exact (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv _ _ |>.injective
    ((hbeta' obj.1 obj.2).trans (hbeta obj.1 obj.2).symm)

end SheafOfModules
