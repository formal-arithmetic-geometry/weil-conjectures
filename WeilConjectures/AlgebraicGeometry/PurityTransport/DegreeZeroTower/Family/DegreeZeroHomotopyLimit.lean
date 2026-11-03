/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.DvrCoefficients.VectorIntegrationDvrCoefficients
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Degree-zero reduction sequences, their homotopy limit and completion maps

Source: thm-pur-vector-bundle-thom, Step 3, as refined by Wei Yang #1412 item 9 and Nailin
Guan #1469/#1471: after restriction of scalars to `R_B`, the finite objects and their quotient
transitions are degree-zero sheaves `Y_n`; their derived limit is taken inside `D(B_proet, R_B)`
as the fibre of `1 - shift` on the product (Stacks 08TC, def-weil-derived-limit), and the
canonical completion maps compare an integral object with it
(blueprint: def-pur-degree-zero-homotopy-limit).

No category of inverse systems is used. The homotopy limit is the mapping cocone of the
degree-zero map `1 - shift : ∏ Y_n → ∏ Y_n` (`towerTransitionEndomorphism`). A map from an
integral object `K` in degrees `≤ 0` is determined by a compatible family of maps to the `Y_n`:
it is the unique map to the kernel sheaf `ker(1 - shift) = lim Y_n` with the prescribed `H^0`
(the `H^0` bijection for `K ≤ 0`, `Y ≥ 0`), followed by the canonical inclusion of the kernel
into the cocone. No map is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport.DegreeZeroTower

open DvrCoefficients

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) (X : Scheme.{u})

/-- Sheaves of `Λ_X`-modules on the pro-etale site. Source: def-pur-conventions
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Modules := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X)

/-- Exact restriction of scalars along a coefficient map, on derived categories.
Source: lem-weil-derived-scalar-extension-restriction-adjunction
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev restriction {c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell) :
    c'.derived ell X ⥤ c.derived ell X :=
  (Mod.comap (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).mapDerivedCategory

/-- The derived scalar-extension/restriction adjunction along a coefficient map.
Source: lem-weil-derived-scalar-extension-restriction-adjunction
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev adjunction {c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell) :
    scalarSixChange a X ⊣ restriction ell c X a :=
  Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)

variable {ell c} (rs : ReductionSystem.{u} ell c)

/-- Restriction along a transition, then along the larger reduction, is restriction along the
smaller reduction. Source: blueprint Step 3, quotient transitions
(blueprint: def-pur-degree-zero-homotopy-limit). -/
def restrictionComp (n : ℕ) :
    restriction ell (rs.level (n + 1)) X (rs.transition n) ⋙
        restriction ell c X (rs.reduction (n + 1)) ≅
      restriction ell c X (rs.reduction n) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp _ _).symm ≪≫
        Mod.comapCongr ((coefficientMap_comp (rs.reduction (n + 1)).hom.hom
          (rs.transition n).hom.hom X).symm.trans
            (congrArg (fun k ↦ coefficientMap k X)
              (congrArg (fun k ↦ k.hom.hom) (rs.comp n)))))

/-- Compatible finite objects: an object at each level and its specified derived
transition `T(Y_(n+1)) → Y_n`. Source: blueprint Step 3
(blueprint: def-pur-degree-zero-homotopy-limit). -/
structure Family where
  /-- The object at level `n+1`. -/
  obj : ∀ n, (rs.level n).derived ell X
  /-- The specified derived scalar transition. -/
  step : ∀ n, (scalarSixChange (rs.transition n) X).obj (obj (n + 1)) ⟶ obj n

variable {X}

/-- Degree-zero cohomology sheaf `H^0`. Source: def-pur-conventions, cohomology sheaves
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev homology0 : c.derived ell X ⥤ Modules ell c X :=
  DerivedCategory.homologyFunctor _ 0

/-- The degree-zero sheaf `H^0` of the restricted finite object at level `n+1`.
Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Family.level (Y : Family X rs) (n : ℕ) : Modules ell c X :=
  (homology0 (X := X)).obj ((restriction ell c X (rs.reduction n)).obj (Y.obj n))

/-- The integral transition `Y_(n+1) → Y_n` after restriction to `Λ_X`: the scalar unit
followed by the restricted specified transition.
Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.integralStep (Y : Family X rs) (n : ℕ) :
    (restriction ell c X (rs.reduction (n + 1))).obj (Y.obj (n + 1)) ⟶
      (restriction ell c X (rs.reduction n)).obj (Y.obj n) :=
  (restriction ell c X (rs.reduction (n + 1))).map
      ((adjunction ell _ X (rs.transition n)).unit.app (Y.obj (n + 1)) ≫
        (restriction ell _ X (rs.transition n)).map (Y.step n)) ≫
    (restrictionComp X rs n).hom.app (Y.obj n)

/-- The scalar change along `R → A_(n+2) → A_(n+1)` is the one along `R → A_(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit). -/
def reductionEq (K : c.derived ell X) (n : ℕ) :
    (scalarSixChange (rs.reduction (n + 1) ≫ rs.transition n) X).obj K ≅
      (scalarSixChange (rs.reduction n) X).obj K :=
  eqToIso (by rw [rs.comp n])

/-- Reductions of an integral object compatible with the family: maps
`T_(R→A_(n+1)) K → Y_n` whose transitions match through the scalar tower.
Source: blueprint Step 3, identification of `K ⊗^L A_n` with `Y_n`
(blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.ReductionCompatible (Y : Family X rs) (K : c.derived ell X)
    (κ : ∀ n, (scalarSixChange (rs.reduction n) X).obj K ⟶ Y.obj n) : Prop :=
  ∀ n, (scalarSixChange (rs.transition n) X).map (κ (n + 1)) ≫ Y.step n =
    (scalarSixTower (rs.reduction (n + 1)) (rs.transition n) X).hom.app K ≫
      (reductionEq rs K n).hom ≫ κ n

/-- The degree-zero cone of an integral object over the sequence: `H^0` of the scalar unit
followed by the restricted reduction comparison.
Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.coneMap (Y : Family X rs) (K : c.derived ell X)
    (κ : ∀ n, (scalarSixChange (rs.reduction n) X).obj K ⟶ Y.obj n) (n : ℕ) :
    (homology0 (X := X)).obj K ⟶ Y.level rs n :=
  (homology0 (X := X)).map
    ((adjunction ell c X (rs.reduction n)).unit.app K ≫
      (restriction ell c X (rs.reduction n)).map (κ n))

/-- The transition `H^0(Y_(n+1)) → H^0(Y_n)` of the restricted degree-zero sheaves.
Source: blueprint Step 3, "with their quotient transitions"
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Family.levelStep (Y : Family X rs) (n : ℕ) : Y.level rs (n + 1) ⟶ Y.level rs n :=
  (homology0 (X := X)).map (Y.integralStep rs n)

/-- The product `∏_n H^0(Y_n)` of the restricted degree-zero sheaves.
Source: Stacks 08TC (blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Family.product (Y : Family X rs) : Modules ell c X :=
  ∏ᶜ Y.level rs

/-- The map `1 - shift` on the product, whose fibre is the derived limit.
Source: Stacks 08TC; def-weil-tower-transition-endomorphism
(blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Family.oneSubShift (Y : Family X rs) : Y.product rs ⟶ Y.product rs :=
  towerTransitionEndomorphism (Y.levelStep rs)

/-- `1 - shift` as a map of complexes concentrated in degree zero.
Source: Stacks 08TC (blueprint: def-pur-degree-zero-homotopy-limit). -/
abbrev Family.oneSubShiftComplex (Y : Family X rs) :
    (HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).obj (Y.product rs) ⟶
      (HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).obj (Y.product rs) :=
  (HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).map (Y.oneSubShift rs)

/-- The derived limit `R lim_n Y_n` in `D(X_proet, Λ_X)`: the mapping cocone (fibre) of
`1 - shift : ∏ Y_n → ∏ Y_n`. Source: blueprint Step 3, "derived inverse limits are taken in
`D(B_proet, R_B)`"; Stacks 08TC; def-weil-derived-limit
(blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.homotopyLimit (Y : Family X rs) : c.derived ell X :=
  DerivedCategory.Q.obj (CochainComplex.mappingCocone (Y.oneSubShiftComplex rs))

/-- The projection `R lim_n Y_n → ∏ Y_n` of the defining triangle.
Source: Stacks 08TC (blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.homotopyLimitProjection (Y : Family X rs) :
    Y.homotopyLimit rs ⟶ (DerivedCategory.singleFunctor _ 0).obj (Y.product rs) :=
  DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (Y.oneSubShiftComplex rs))

/-- The kernel inclusion composed with `1 - shift` vanishes.
Source: Stacks 08TC (blueprint: def-pur-degree-zero-homotopy-limit).
Proof: `δ` of the zero cochain is zero, and `single` sends `ι ≫ (1 - shift) = 0`
(`kernel.condition`) to zero; `Cochain.ofHom 0 = 0`. -/
theorem Family.kernel_comp_eq (Y : Family X rs) :
    CochainComplex.HomComplex.δ (-1) 0 (0 : CochainComplex.HomComplex.Cochain
        ((HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).obj
          (kernel (Y.oneSubShift rs)))
        ((HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).obj
          (Y.product rs)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        ((HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).map
            (kernel.ι (Y.oneSubShift rs)) ≫ Y.oneSubShiftComplex rs) = 0 := by
  sorry

/-- The canonical comparison `lim_n Y_n = ker(1 - shift) → R lim_n Y_n`: the kernel sheaf in
degree zero maps to the cocone by the kernel inclusion and the zero homotopy.
Source: Stacks 08TC, 0CQD (blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.limitComparison (Y : Family X rs) :
    (DerivedCategory.singleFunctor _ 0).obj (kernel (Y.oneSubShift rs)) ⟶ Y.homotopyLimit rs :=
  DerivedCategory.Q.map (CochainComplex.mappingCocone.lift (Y.oneSubShiftComplex rs)
    ((HomologicalComplex.single (Modules ell c X) (ComplexShape.up ℤ) 0).map
      (kernel.ι (Y.oneSubShift rs))) 0 (Y.kernel_comp_eq rs))

/-- A family of maps `g_n : H^0 K → H^0(Y_n)` compatible with the transitions lands in the
kernel of `1 - shift`. Source: Stacks 08TC (blueprint: def-pur-degree-zero-homotopy-limit).
Proof: compose with each projection; `towerTransitionEndomorphism_eq_iff` reduces the claim to
`g_n - g_(n+1) ≫ levelStep n = 0`, which is the hypothesis. -/
theorem Family.lift_oneSubShift (Y : Family X rs) {A : Modules ell c X}
    (g : ∀ n, A ⟶ Y.level rs n) (hg : ∀ n, g (n + 1) ≫ Y.levelStep rs n = g n) :
    Pi.lift g ≫ Y.oneSubShift rs = 0 := by
  sorry

/-- The map `K → R lim_n Y_n` determined by a compatible family `g_n : H^0 K → H^0(Y_n)`, for
`K` in degrees `≤ 0`: the unique map to the kernel sheaf in degree zero with `H^0` equal to the
induced map into the kernel (`H^0` bijection), followed by `limitComparison`. It is the unique
lift of `(g_n)` through `R lim → ∏`, since `Hom(K, (∏ Y_n)[-1]) = 0`.
Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.liftOf (Y : Family X rs) (K : c.derived ell X) [K.IsLE 0]
    (g : ∀ n, (homology0 (X := X)).obj K ⟶ Y.level rs n)
    (hg : ∀ n, g (n + 1) ≫ Y.levelStep rs n = g n) : K ⟶ Y.homotopyLimit rs :=
  (Equiv.ofBijective _ (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
      (X := K) (Y := (DerivedCategory.singleFunctor _ 0).obj (kernel (Y.oneSubShift rs))) 0)).symm
    (kernel.lift _ (Pi.lift g) (Y.lift_oneSubShift rs g hg) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _) ≫
    Y.limitComparison rs

/-- The cone maps of a reduction-compatible integral object are compatible with the
transitions. Source: blueprint Step 3 (blueprint: def-pur-degree-zero-homotopy-limit).
Proof: the composite of the scalar units for `R → A_(n+2)` and `A_(n+2) → A_(n+1)` is the
scalar unit for `R → A_(n+1)` under the scalar tower and restriction compositor (both are
adjunction units of the composite adjunction). Insert the reduction compatibility and
apply `H^0`. -/
theorem Family.coneMap_compatible (Y : Family X rs) (K : c.derived ell X)
    (κ : ∀ n, (scalarSixChange (rs.reduction n) X).obj K ⟶ Y.obj n)
    (hκ : Y.ReductionCompatible rs K κ) (n : ℕ) :
    Y.coneMap rs K κ (n + 1) ≫ Y.levelStep rs n = Y.coneMap rs K κ n := by
  sorry

/-- The canonical completion map `K → R lim_n H^0(Y_n)` of an integral object in degrees
`≤ 0` with reduction-compatible maps `κ_n : K ⊗^L A_n → Y_n`: the lift of the degree-zero cone.
Source: blueprint Step 3, "canonical completion maps"; sk-def-pe-derived-completion
(blueprint: def-pur-degree-zero-homotopy-limit). -/
def Family.completion (Y : Family X rs) (K : c.derived ell X) [K.IsLE 0]
    (κ : ∀ n, (scalarSixChange (rs.reduction n) X).obj K ⟶ Y.obj n)
    (hκ : Y.ReductionCompatible rs K κ) : K ⟶ Y.homotopyLimit rs :=
  Y.liftOf rs K (Y.coneMap rs K κ) (Y.coneMap_compatible rs K κ hκ)

end AlgebraicGeometry.ProEtale.PurityTransport.DegreeZeroTower
