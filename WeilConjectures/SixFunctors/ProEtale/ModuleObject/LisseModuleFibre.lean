/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UniformizerReduction

/-!
# Fibres of `E_X`- and `𝒪_{E,X}`-modules at geometric points

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. For a
geometric point `y : Spec K ⟶ X` of a scheme `X`, the fibre of an `E_X`-module `G` at `y` is the
`E`-vector space `G_y = Hom(E_{Spec K}, y^* G) = Γ(Spec K, y^* G)`
(`AlgebraicGeometry.ProEtale.padicSubfieldFibre`), `E` acting through the constant sections;
likewise for `𝒪_{E,X}`-modules (`AlgebraicGeometry.ProEtale.padicIntegersFibre`).

The lisse `E_X`-modules are the locally free ones (`AlgebraicGeometry.ProEtale.LisseModule`).
We also define the canonical maps between fibres used to state the compatibilities of the
monodromy:

* `AlgebraicGeometry.ProEtale.globalSectionFibre`: the restriction `Γ(X, G) → G_y`;
* `AlgebraicGeometry.ProEtale.fibreTensor`: the product `G_y × H_y → (G ⊗ H)_y`;
* `AlgebraicGeometry.ProEtale.latticeFibreMap`: for a lattice `ι : M ⟶ L` of an `E_X`-module
  `L`, the induced map `M_y → L_y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
  [MonoidalPreadditive C] {R : C} [MonObj R] [IsCommMonObj R] {K : Type*} [Ring K]

/-- The sections `M ↦ Hom(R, M)` of module objects over a commutative ring object `R`, as
`K`-modules for a ring homomorphism `φ : K →+* Γ R`, `K` acting through `φ`. -/
noncomputable def regularCoyoneda (φ : K →+* MonObj.Γ R) : Mod C R ⥤ ModuleCat K :=
  letI := linearOfRingHom φ
  (linearCoyoneda K _).obj (op (regular R))

/-- The elements of `regularCoyoneda φ M` are the morphisms `R ⟶ M`. -/
def regularCoyonedaEquiv (φ : K →+* MonObj.Γ R) (M : Mod C R) :
    (regularCoyoneda φ).obj M ≃ (regular R ⟶ M) :=
  Equiv.refl _

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

section Fibre

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- The fibre functor `N ↦ Hom(E_{Spec K}, N) = Γ(Spec K, N)` on `E_{Spec K}`-modules, as
`E`-vector spaces, `E` acting through the constant sections of `E_{Spec K}`. -/
noncomputable def padicSubfieldPointFibre (K : Type u) [Field K] :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of K))) ⥤
      ModuleCat.{u + 1} E.1 :=
  Mod.regularCoyoneda (padicSubfieldConstSection ℓ E (Spec (.of K)))

/-- The fibre functor `N ↦ Hom(𝒪_{E,Spec K}, N) = Γ(Spec K, N)` on `𝒪_{E,Spec K}`-modules, as
`𝒪_E`-modules, `𝒪_E` acting through the constant sections of `𝒪_{E,Spec K}`. -/
noncomputable def padicIntegersPointFibre (K : Type u) [Field K] :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (Spec (.of K))) ⥤
      ModuleCat.{u + 1} (integers ℓ E.1) :=
  Mod.regularCoyoneda (padicIntegersConstSection ℓ E (Spec (.of K)))

/-- The elements of the fibre of an `E_{Spec K}`-module `N` are the morphisms
`E_{Spec K} ⟶ N`. -/
noncomputable def padicSubfieldPointFibreEquiv
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of K)))) :
    (padicSubfieldPointFibre ℓ E K).obj N ≃
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of K))) ⟶ N) :=
  Mod.regularCoyonedaEquiv _ N

/-- The elements of the fibre of an `𝒪_{E,Spec K}`-module `N` are the morphisms
`𝒪_{E,Spec K} ⟶ N`. -/
noncomputable def padicIntegersPointFibreEquiv
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (Spec (.of K)))) :
    (padicIntegersPointFibre ℓ E K).obj N ≃
      (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (Spec (.of K))) ⟶
        N) :=
  Mod.regularCoyonedaEquiv _ N

/-- The fibre `G_y = Hom(E_{Spec K}, y^* G) = Γ(Spec K, y^* G)` of an `E_X`-module `G` at a
geometric point `y : Spec K ⟶ X`, as an `E`-vector space. -/
noncomputable abbrev padicSubfieldFibre (y : Spec (.of K) ⟶ X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X) ⥤ ModuleCat.{u + 1} E.1 :=
  (y)^*⟦Profinite.continuousMapRingObj E.1⟧ ⋙ padicSubfieldPointFibre ℓ E K

/-- The fibre `M_y = Hom(𝒪_{E,Spec K}, y^* M) = Γ(Spec K, y^* M)` of an `𝒪_{E,X}`-module `M` at a
geometric point `y : Spec K ⟶ X`, as an `𝒪_E`-module. -/
noncomputable abbrev padicIntegersFibre (y : Spec (.of K) ⟶ X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) ⥤
      ModuleCat.{u + 1} (integers ℓ E.1) :=
  (y)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⋙ padicIntegersPointFibre ℓ E K

/-- The restriction `Γ(X, G) = Hom(E_X, G) → G_y` of global sections to the fibre at `y`. -/
noncomputable def globalSectionFibre (y : Spec (.of K) ⟶ X)
    {G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)}
    (s : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X) ⟶ G) :
    (padicSubfieldFibre ℓ E y).obj G :=
  (padicSubfieldPointFibreEquiv ℓ E _).symm
    ((upperStarObjRegularIso (Profinite.continuousMapRingObj E.1) y).inv ≫
      (y)^*⟦Profinite.continuousMapRingObj E.1⟧.map s)

/-- The product `G_y × H_y → (G ⊗ H)_y` of sections of the fibres, through the monoidal structure
`y^* G ⊗ y^* H ≅ y^* (G ⊗ H)` of the pullback. -/
noncomputable def fibreTensor (y : Spec (.of K) ⟶ X)
    {G H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)}
    (v : (padicSubfieldFibre ℓ E y).obj G) (w : (padicSubfieldFibre ℓ E y).obj H) :
    (padicSubfieldFibre ℓ E y).obj (G ⊗ H) :=
  (padicSubfieldPointFibreEquiv ℓ E _).symm ((λ_ (𝟙_ _)).inv ≫
    (padicSubfieldPointFibreEquiv ℓ E _ v ⊗ₘ padicSubfieldPointFibreEquiv ℓ E _ w) ≫
      (Functor.Monoidal.μIso (y)^*⟦Profinite.continuousMapRingObj E.1⟧ G H).hom)

/-- The map `M_y → L_y` of fibres induced by a morphism `ι : M ⟶ L` from an `𝒪_{E,X}`-module to
an `E_X`-module (for instance a lattice of `L`): a section `m : 𝒪_{E,Spec K} ⟶ y^* M` is sent to
the `E_{Spec K}`-linear extension of `y^* ι ∘ m`. -/
noncomputable def latticeFibreMap (y : Spec (.of K) ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)}
    {L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)}
    (ι : M ⟶ (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj L) :
    (padicIntegersFibre ℓ E y).obj M → (padicSubfieldFibre ℓ E y).obj L :=
  fun m ↦ (padicSubfieldPointFibreEquiv ℓ E _).symm
    ((Mod.extendScalarsObjRegularIso (padicIntegersToPadicSubfield (Spec (.of K)) ℓ E)).inv ≫
    ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield (Spec (.of K)) ℓ E)).homEquiv
      _ _).symm (padicIntegersPointFibreEquiv ℓ E _ m ≫
        (y)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.map ι ≫
          (comapUpperStarIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) y).inv.app L))

end Fibre

section Lisse

variable {ℓ}

/-- The lisse `E_X`-modules: the locally free module objects over `E_X`. -/
abbrev lisseModule (X : Scheme.{u}) :
    ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :=
  IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) X)

/-- The category of lisse `E_X`-modules. -/
abbrev LisseModule (X : Scheme.{u}) : Type (u + 2) :=
  (lisseModule E X).FullSubcategory

/-- The fibre functor `G ↦ G_y` at a geometric point `y`, on lisse `E_X`-modules. -/
noncomputable abbrev lisseFibre {X : Scheme.{u}} {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ X) : LisseModule E X ⥤ ModuleCat.{u + 1} E.1 :=
  ObjectProperty.ι _ ⋙ padicSubfieldFibre ℓ E y

end Lisse

end AlgebraicGeometry.ProEtale
