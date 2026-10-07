/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Simple
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GeometricFrobenius

/-!
# Weil sheaves and Weil complexes

Let `k₀` be a finite field, `X` a scheme over `k₀`, `X̄ = X ×_{k₀} k̄` its geometric fiber
and `Fr_X = 𝟙 × σ : X̄ ≅ X̄` its geometric Galois Frobenius
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`). A *Weil sheaf* on `X` is a
constructible étale `ℚ̄_ℓ`-sheaf `F` on `X̄` together with an isomorphism
`φ : Fr_X^* F ≅ F`; a *Weil complex* is an object `K` of the derived category `D(X̄_ét)` with
bounded constructible homology together with an isomorphism `φ : Fr_X^* K ≅ K`. Both are
full subcategories of the categories `CategoryTheory.Endofunctor.IsoAlgebra` of the
pullback endofunctor `Fr_X^*` and of its derived functor.

Weil sheaves form an abelian category, Weil complexes a preadditive category with a shift. A
Weil sheaf is a Weil complex concentrated in degree zero (`WeilSheaf.toComplex`), the
cohomology sheaves `𝓗ᵃ` of a Weil complex are Weil sheaves (`WeilComplex.homologySheaf`),
and both notions pull back along morphisms of `k₀`-schemes (`WeilSheaf.upperStar`,
`WeilComplex.upperStar`), the base change `X̄ ⟶ Ȳ` commuting with the Frobenii.

## Main definitions

- `AlgebraicGeometry.WeilCoefficients`: the category of modules over `ℚ̄_ℓ`, lifted to the
  universe of the étale sites, and `AlgebraicGeometry.WeilCoefficients.toModuleCat`, the
  underlying `ℚ̄_ℓ`-vector spaces.
- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and the category of Weil complexes.
- `AlgebraicGeometry.WeilSheaf.toComplex` and `AlgebraicGeometry.WeilComplex.homologySheaf`.
- `AlgebraicGeometry.WeilSheaf.frobeniusPowIso`: the iterated Weil structure
  `φ_m : (Fr_Xᵐ)^* F ≅ F`.
- `AlgebraicGeometry.WeilSheaf.IsLisse`: the underlying sheaf is locally constant.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse`: a simple object of the category of lisse
  Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.upperStar` and `AlgebraicGeometry.WeilComplex.upperStar`.

## Implementation notes

**These definitions are a scaffold, and the categories are degenerate.** The coefficients are
discrete `ℚ̄_ℓ`-modules on the étale site, and `Scheme.IsConstructibleSheaf` asks for finite
stalks, so every constructible sheaf of `ℚ̄_ℓ`-modules is zero. Hence every Weil sheaf and
every Weil complex is zero, and statements quantified over them are vacuous. Discrete
`ℚ̄_ℓ`-coefficients would be wrong even with finite-dimensional stalks: lisse sheaves would have
finite monodromy. The blueprint (`sk-d-real-weil`) takes constructible pro-étale `E_X`-modules
for a finite extension `E` of `ℚ_ℓ`, and it defines Weil complexes as a Verdier localization of
complexes of Weil sheaves, which is triangulated; the category `WeilComplex` here is not (see
its docstring). Both definitions are to be redone once pro-étale constructible `E_X`-modules
exist. Only the interface, the names and the transport of Frobenius structures along
`φ̄^*` are meant to survive.

The coefficient ring `ℚ̄_ℓ = PadicAlgCl l` lives in `Type`, while Mathlib's
`IsGrothendieckAbelian.{v} (ModuleCat.{v} R)` needs `R : Type v`; hence the `ULift` in
`AlgebraicGeometry.WeilCoefficients`.

Weil complexes live in the unbounded derived category `D(X̄_ét)`, whose functor
`Functor.mapDerivedCategory` is additive and commutes with the shifts. Their carriers are
bounded, so they are objects of the bounded below derived category on the nose.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open Etale

/-- The coefficients of Weil sheaves: modules over `ℚ̄_ℓ`, lifted to `Type (u + 1)`. -/
abbrev WeilCoefficients (l : ℕ) [Fact l.Prime] : Type (u + 2) :=
  ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))

namespace WeilCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- The underlying `ℚ̄_ℓ`-vector space of a module over `ULift ℚ̄_ℓ`, by restriction of scalars
along `ℚ̄_ℓ ≃ ULift ℚ̄_ℓ`. -/
noncomputable abbrev toModuleCat :
    WeilCoefficients.{u} l ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := PadicAlgCl l)).symm.toRingHom

variable {l}

/-- An isomorphism of modules over `ULift ℚ̄_ℓ` as a `ℚ̄_ℓ`-linear isomorphism of the
underlying `ℚ̄_ℓ`-vector spaces. -/
noncomputable def linearEquivOfIso {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (toModuleCat l).obj M ≃ₗ[PadicAlgCl l] (toModuleCat l).obj N :=
  ((toModuleCat l).mapIso e).toLinearEquiv

end WeilCoefficients

section Frobenius

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The pullback `Fr_X^*` of étale sheaves on the geometric fiber `X̄` along its geometric
Galois Frobenius `Fr_X`. -/
noncomputable abbrev WeilSheaf.frobeniusPullback :
    Sheaf (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.smallEtaleTopology
        (WeilCoefficients.{u} l) ⥤
      Sheaf (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.smallEtaleTopology
        (WeilCoefficients.{u} l) :=
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l]

/-- The pullback `Fr_X^*` along the automorphism `Fr_X` of `X̄` is an equivalence. -/
instance : (WeilSheaf.frobeniusPullback k₀ l X).IsEquivalence :=
  Etale.isEquivalence_upperStar _ _

/-- The property of a sheaf `F` on `X̄` with an isomorphism `Fr_X^* F ≅ F` that `F` is
constructible; it cuts out the Weil sheaves. -/
noncomputable abbrev WeilSheaf.objectProperty :
    ObjectProperty (IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)) :=
  (Etale.constructibleSheaf (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget _)

/-- The derived pullback `D(Fr_X^*)` along the geometric Galois Frobenius of `X̄`. -/
noncomputable abbrev WeilComplex.frobeniusPullback :
    DerivedCategory (Sheaf (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.smallEtaleTopology
        (WeilCoefficients.{u} l)) ⥤
      DerivedCategory (Sheaf (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.smallEtaleTopology
        (WeilCoefficients.{u} l)) :=
  (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory

/-- The property of an object `K` of `D(X̄_ét)` with an isomorphism `D(Fr_X^*) K ≅ K` that `K`
is bounded with constructible homology; it cuts out the Weil complexes. -/
noncomputable abbrev WeilComplex.objectProperty :
    ObjectProperty (IsoAlgebra (WeilComplex.frobeniusPullback k₀ l X)) :=
  (Etale.DerivedCategory.boundedConstructible (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget _)

end Frobenius

/-- The category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`: constructible
étale sheaves `F` of `ℚ̄_ℓ`-modules on the geometric fiber `X̄` with an isomorphism
`Fr_X^* F ≅ F`, where `Fr_X` is the geometric Galois Frobenius of `X̄`.

This is a scaffold and it is degenerate: a constructible sheaf has finite stalks, and a
`ℚ̄_ℓ`-vector space with finitely many elements is zero, so every Weil sheaf is zero. The
blueprint (`sk-d-real-weil`) takes constructible pro-étale `E_X`-modules instead, which are
not formalised yet. -/
def WeilSheaf (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type (u + 2) :=
  (WeilSheaf.objectProperty k₀ l X).FullSubcategory

/-- The category of Weil complexes on a `k₀`-scheme `X`: objects `K` of the derived category
of étale sheaves of `ℚ̄_ℓ`-modules on the geometric fiber `X̄` with bounded constructible
homology, with an isomorphism `Fr_X^* K ≅ K` in the derived category, where `Fr_X` is the
geometric Galois Frobenius of `X̄`.

This is a scaffold and it differs from the blueprint (`sk-d-real-weil`) in two ways. Its
homology sheaves are constructible `ℚ̄_ℓ`-sheaves, hence zero, so every Weil complex is zero
(see `AlgebraicGeometry.WeilSheaf`). And the blueprint defines Weil complexes as the Verdier
localization of the homotopy category of complexes of Weil sheaves, while this category only
records an isomorphism `Fr_X^* K ≅ K` in the derived category. Cones are not functorial in
`D(X̄_ét)`, so this category is not triangulated, and its morphisms are not those of the
blueprint category. Statements that need distinguished triangles of Weil complexes, such as
`WeilComplex.derivedLowerShriek`, `fourierTransform` and the open–closed triangle,
cannot be stated on it faithfully. -/
def WeilComplex (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type (u + 2) :=
  (WeilComplex.objectProperty k₀ l X).FullSubcategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

noncomputable instance : Category (WeilSheaf k₀ l X) :=
  inferInstanceAs (Category (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

/-- The closure of the Weil sheaf property under finite products. It is found by search, but
within the search for `Abelian (WeilSheaf k₀ l X)` it exceeds the default
`synthInstance.maxSize`, so it is recorded as an instance. -/
instance : (WeilSheaf.objectProperty k₀ l X).IsClosedUnderFiniteProducts :=
  inferInstance

noncomputable instance : Abelian (WeilSheaf k₀ l X) :=
  inferInstanceAs (Abelian (WeilSheaf.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : Category (WeilComplex k₀ l X) :=
  inferInstanceAs (Category (WeilComplex.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : Preadditive (WeilComplex k₀ l X) :=
  inferInstanceAs (Preadditive (WeilComplex.objectProperty k₀ l X).FullSubcategory)

noncomputable instance : HasShift (WeilComplex k₀ l X) ℤ :=
  inferInstanceAs (HasShift (WeilComplex.objectProperty k₀ l X).FullSubcategory ℤ)

namespace WeilSheaf

/-- A Weil sheaf, viewed as a Weil complex concentrated in degree zero. -/
noncomputable def toComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategorySingleFunctor 0))
    fun F ↦
      have : Scheme.IsConstructibleSheaf F.obj.carrier := F.property
      Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F.obj.carrier 0

instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilSheaf.objectProperty k₀ l X)
    (Q := WeilComplex.objectProperty k₀ l X) _ _

/-- The iterated Weil structure `φ_m : (Fr_Xᵐ)^* F ≅ F` of a Weil sheaf, the ordered composite

`(Fr_X^{m+1})^* F ≅ Fr_X^* (Fr_Xᵐ)^* F --Fr_X^* φ_m--> Fr_X^* F --φ--> F`

built from `Fr_X^{m+1} = Fr_X ≫ Fr_Xᵐ`, with `φ_0` the identification `𝟙^* F ≅ F`. At a
geometric point fixed by `Fr_Xᵐ` up to reparametrisation it induces the Frobenius relative to
`𝔽_{qᵐ}` on the stalk. -/
noncomputable def frobeniusPowIso (F : WeilSheaf k₀ l X) (m : ℕ) :
    (Etale.upperStar (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom).obj F.obj.carrier ≅
        F.obj.carrier :=
  match m with
  | 0 => (Etale.upperStarId _ _).app _
  | m + 1 =>
    (Etale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom _
        (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom])).app _ ≪≫
      (frobeniusPullback k₀ l X).mapIso (F.frobeniusPowIso m) ≪≫ F.obj.str

/-- A Weil sheaf is *lisse* if its underlying étale sheaf is locally constant; it is then
finite locally constant, being constructible. The blueprint notion, lisse of finite rank for
`E_X`-modules, awaits pro-étale coefficients. -/
def IsLisse (F : WeilSheaf k₀ l X) : Prop :=
  Scheme.IsLocallyConstantSheaf F.obj.carrier

/-- A direct sum of lisse Weil sheaves is lisse: the underlying étale sheaf of `F ⊞ G` is the
direct sum of those of `F` and `G`. -/
theorem IsLisse.biprod {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    (F ⊞ G).IsLisse := by
  let Φ := ObjectProperty.ι (objectProperty k₀ l X) ⋙ IsoAlgebra.forget (frobeniusPullback k₀ l X)
  have : Scheme.IsLocallyConstantSheaf (Φ.obj F) := hF
  have : Scheme.IsLocallyConstantSheaf (Φ.obj G) := hG
  have := Scheme.IsLocallyConstantSheaf.biprod (Φ.obj F) (Φ.obj G)
  have : PreservesBinaryBiproducts Φ := preservesBinaryBiproducts_of_preservesBiproducts _
  exact Scheme.IsLocallyConstantSheaf.of_iso (Φ.mapBiprod F G).symm

/-- A Weil sheaf `F` is *irreducible lisse* if it is lisse and nonzero, and every lisse Weil
subsheaf of `F` is zero or all of `F`: it is a simple object of the category of lisse Weil
sheaves, the meaning of "nonzero irreducible lisse Weil sheaf" in the blueprint. On a connected
normal `X` it says that the representation of the Weil group on the geometric generic stalk is
irreducible.

This is weaker than simplicity in the category of all Weil sheaves: a nonzero lisse sheaf `M`
on a curve `U₀` is never simple there, since for a closed point `x` the extension by zero of
`M|_{U₀ ∖ x}` is a nonzero proper subsheaf. (blueprint: `rem-dl-a1-conventions`) -/
def IsIrreducibleLisse (F : WeilSheaf k₀ l X) : Prop :=
  F.IsLisse ∧ ¬ IsZero F ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ F), Mono i → G.IsLisse → IsZero G ∨ IsIso i

/-- A lisse Weil sheaf which is simple in the category of all Weil sheaves is irreducible
lisse. -/
theorem IsLisse.isIrreducibleLisse {F : WeilSheaf k₀ l X} (hF : F.IsLisse) [Simple F] :
    F.IsIrreducibleLisse := by
  refine ⟨hF, Simple.not_isZero F, fun G i _ _ ↦ ?_⟩
  by_cases h : i = 0
  · subst h
    exact Or.inl (IsZero.of_mono_zero G F)
  · exact Or.inr ((Simple.mono_isIso_iff_nonzero i).2 h)

/-- A Weil sheaf `F` is *geometrically irreducible* if its underlying étale sheaf on the
geometric fiber `X̄` is an irreducible local system: for `X̄` connected, the geometric fundamental
representation `π₁(X̄) → GL(F_η̄)` is irreducible. -/
def IsGeometricallyIrreducible (F : WeilSheaf k₀ l X) : Prop :=
  Scheme.IsIrreducibleLocalSystem F.obj.carrier

end WeilSheaf

namespace WeilComplex

/-- The `a`-th cohomology sheaf `𝓗ᵃK` of a Weil complex, in cohomological indexing, with the
Weil structure induced by that of `K`. -/
noncomputable def homologySheaf (a : ℤ) : WeilComplex k₀ l X ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategoryHomologyFunctorIso a))
    fun K ↦ K.property.2 a

instance (a : ℤ) : (homologySheaf (k₀ := k₀) (l := l) (X := X) a).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l X)
    (Q := WeilSheaf.objectProperty k₀ l X) _ _

end WeilComplex

section UpperStar

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback `φ^*` of Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`Etale.upperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def WeilSheaf.upperStar : WeilSheaf k₀ l Y ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.upperStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)))
    fun F ↦
      have : Scheme.IsConstructibleSheaf F.obj.carrier := F.property
      Scheme.IsConstructibleSheaf.upperStar (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
        F.obj.carrier

instance : (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilSheaf.objectProperty k₀ l Y)
    (Q := WeilSheaf.objectProperty k₀ l X) _ _

/-- The pullback `φ^*` of Weil complexes along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
derived pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`Etale.mapDerivedCategoryUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def WeilComplex.upperStar : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.mapDerivedCategoryUpperStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)))
    fun K ↦ K.property.mapDerivedCategory_upperStar _

instance : (WeilComplex.upperStar (k₀ := k₀) (l := l) φ).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l Y)
    (Q := WeilComplex.objectProperty k₀ l X) _ _

end UpperStar

end AlgebraicGeometry
