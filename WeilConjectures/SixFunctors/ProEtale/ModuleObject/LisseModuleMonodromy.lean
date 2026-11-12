/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseModuleFibre

/-!
# Lisse `E`-modules and representations of the fundamental group

Let `X` be a connected scheme, `ℓ` a prime, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of
integers `𝒪_E` and uniformiser `ϖ`, and `Ω` a field with algebraic closure `Ω̄`. For a geometric
point `x̄ : Spec Ω̄ ⟶ X` write `F_x̄` both for the fibre functor on finite étale `X`-schemes, whose
automorphism group is `π₁(X, x̄)`, and for the fibre functor `L ↦ L_x̄ = Γ(Spec Ω̄, x̄^* L)` on
lisse `E_X`-modules (`AlgebraicGeometry.ProEtale.lisseFibre`).

As for lisse `ℚ̄_ℓ`-sheaves (`AlgebraicGeometry.ProEtale.LisseMonodromy`), the monodromy of lisse
`E_X`-modules is packaged as a transport of fibres along paths `τ : F_y ≅ F_z`
(`AlgebraicGeometry.ProEtale.LisseModuleMonodromy`), functorial in the path and compatible with
global sections and with tensor products (unlike the `ℚ̄_ℓ` version, the compatibilities with
reparametrisations of geometric points and with pullbacks along endomorphisms are not recorded).
At a base point `t` the automorphisms of `F_t` act on the fibres
(`AlgebraicGeometry.ProEtale.LisseModuleMonodromy.rep`), and
`AlgebraicGeometry.ProEtale.LisseModuleMonodromy.IsEquivalenceAt` records that the fibre functor
is an equivalence onto the continuous finite-dimensional `E`-representations of `π₁(X, t)`.

The main statement is
`AlgebraicGeometry.ProEtale.exists_lisseModuleMonodromy_of_isIntegrallyClosed_stalk` (blueprint
`proposition-lattices-representations-normal-scheme`): on a connected normal Noetherian scheme
there is a monodromy which is an equivalence at every base point, and the fibre functor is
computed by lattices: for a lisse `𝒪_{E,X}`-submodule `M ⊆ L` with `M[1/ℓ] = L`, the fibre `M_x̄`
is `lim_n (M/ϖⁿM)_x̄` and `L_x̄ = E ⊗_{𝒪_E} M_x̄` through the map induced by `M ⊆ L`, so that
`L ↦ (lim_n (M/ϖⁿM)_x̄) ⊗_{𝒪_E} E` does not depend on `M` up to canonical isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TensorProduct

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing Scheme.FiniteEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) (X : Scheme.{u})
  (Ω : Type u) [Field Ω]

/-- **The monodromy of lisse `E_X`-modules**: the transport of fibres of lisse `E_X`-modules
along paths between geometric points with values in `Ω̄`, in the sense of
`def-wf-fundamental-representation`, functorial in the path, compatible with global sections and
with tensor products. -/
structure LisseModuleMonodromy where
  /-- The transport `L_y ≅ L_z` of fibres of lisse modules along a path `τ : F_y ≅ F_z`. -/
  mono {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z) :
    lisseFibre E y ≅ lisseFibre E z
  /-- Transport along the trivial path is the identity. -/
  mono_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ X) : mono (Iso.refl (fiber y)) = Iso.refl _
  /-- Transport along a composite path is the composite of the transports. -/
  mono_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) :
    mono (τ ≪≫ τ') = mono τ ≪≫ mono τ'
  /-- Global sections restrict to sections of the fibres which are invariant under transport. -/
  mono_globalSections {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
    (G : LisseModule E X)
    (s : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X) ⟶ G.obj) :
    ((mono τ).hom.app G).hom (globalSectionFibre ℓ E y s) = globalSectionFibre ℓ E z s
  /-- Transport is compatible with the product `G_y × H_y → (G ⊗ H)_y` of fibres. -/
  mono_tensor {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
    (G H : LisseModule E X)
    (hGH : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      (G.obj ⊗ H.obj))
    (v : (lisseFibre E y).obj G) (w : (lisseFibre E y).obj H) :
    ((mono τ).hom.app ⟨G.obj ⊗ H.obj, hGH⟩).hom (fibreTensor ℓ E y v w) =
      fibreTensor ℓ E z (((mono τ).hom.app G).hom v) (((mono τ).hom.app H).hom w)

namespace LisseModuleMonodromy

variable {ℓ E X Ω} (M : LisseModuleMonodromy ℓ E X Ω)

/-- Transport along the trivial path is the identity. -/
lemma mono_refl_apply (y : Spec (.of (AlgebraicClosure Ω)) ⟶ X) (G : LisseModule E X)
    (v : (lisseFibre E y).obj G) :
    ((M.mono (Iso.refl (fiber y))).hom.app G).hom v = v := by
  simp [M.mono_refl]

/-- Transport along a composite path is the composite of the transports. -/
lemma mono_trans_apply {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) (G : LisseModule E X) (v : (lisseFibre E y).obj G) :
    ((M.mono (τ ≪≫ τ')).hom.app G).hom v =
      ((M.mono τ').hom.app G).hom (((M.mono τ).hom.app G).hom v) := by
  simp [M.mono_trans]

/-- The monodromy representation of `π₁(X, t) = Aut F_t` on the fibre `G_t` of a lisse module:
an automorphism `g` of the fibre functor acts by transport along the path `g`. -/
noncomputable def rep (t : Spec (.of (AlgebraicClosure Ω)) ⟶ X) (G : LisseModule E X) :
    Representation E.1 (Aut (fiber t)) ((lisseFibre E t).obj G) where
  toFun g := ((M.mono g).hom.app G).hom
  map_one' := LinearMap.ext fun v ↦ M.mono_refl_apply t G v
  map_mul' g h := LinearMap.ext fun v ↦ by
    rw [Aut.Aut_mul_def, M.mono_trans_apply]
    rfl

/-- The monodromy at the base point `t` is an equivalence onto continuous finite-dimensional
representations: the fibres are finite-dimensional, the representations
`AlgebraicGeometry.ProEtale.LisseModuleMonodromy.rep` are continuous, the fibre functor at `t`
is faithful and full onto `π₁(X, t)`-equivariant maps, and every continuous finite-dimensional
`E`-representation of `π₁(X, t)` is the monodromy representation of a lisse module. -/
structure IsEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ X) : Prop where
  /-- The fibres are finite-dimensional. -/
  finiteDimensional (G : LisseModule E X) : FiniteDimensional E.1 ((lisseFibre E t).obj G)
  /-- The monodromy representations are continuous. -/
  continuous_rep (G : LisseModule E X) (φ : Module.Dual E.1 ((lisseFibre E t).obj G))
    (v : (lisseFibre E t).obj G) : Continuous fun g : Aut (fiber t) ↦ φ (M.rep t G g v)
  /-- The fibre functor at `t` is faithful. -/
  faithful {G H : LisseModule E X} (f g : G ⟶ H)
    (h : (lisseFibre E t).map f = (lisseFibre E t).map g) : f = g
  /-- Every equivariant linear map of fibres is the fibre of a morphism. -/
  full {G H : LisseModule E X}
    (φ : (lisseFibre E t).obj G →ₗ[E.1] (lisseFibre E t).obj H)
    (hφ : ∀ g v, φ (M.rep t G g v) = M.rep t H g (φ v)) :
    ∃ f : G ⟶ H, ((lisseFibre E t).map f).hom = φ
  /-- Every continuous finite-dimensional representation is a monodromy representation. -/
  essSurj (V : Type (u + 1)) [AddCommGroup V] [Module E.1 V] [FiniteDimensional E.1 V]
    (ρ : Representation E.1 (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual E.1 V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseModule E X) (e : (lisseFibre E t).obj G ≃ₗ[E.1] V),
      ∀ g v, e (M.rep t G g v) = ρ g (e v)

end LisseModuleMonodromy

variable {ℓ E X}

/-- **The monodromy of lisse `E`-modules on a connected normal scheme is an equivalence**
(blueprint `proposition-lattices-representations-normal-scheme`): on a connected Noetherian
scheme whose local rings are integrally closed domains there is a monodromy of lisse
`E_X`-modules which, at every geometric point `t`, makes the fibre functor at `t` an equivalence
onto the continuous finite-dimensional `E`-representations of `π₁(X, t)`.

The lisse `E_X`-modules have lattices
(`AlgebraicGeometry.ProEtale.exists_lisse_integral_lattice_of_isIntegrallyClosed_stalk`), whose
reductions are finite locally constant étale sheaves, that is finite `π₁(X, t)`-modules (the
Galois correspondence of `FiniteEtale X`); passing to the limit and inverting `ℓ` gives the
representations. -/
theorem exists_lisseModuleMonodromy_isEquivalenceAt_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian X] [CompactSpace X] [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ M : LisseModuleMonodromy ℓ E X Ω, ∀ t, M.IsEquivalenceAt t := by
  sorry

/-- **The fibre of a lisse `E`-module is computed by a lattice** (blueprint
`proposition-lattices-representations-normal-scheme`). Let `ι : M ⟶ L` be a lisse
`𝒪_{E,X}`-submodule of a lisse `E_X`-module with `M[1/ℓ] = L`, `ϖ` a uniformiser of `𝒪_E` and `t`
a geometric point. The fibre `M_t` is the limit `lim_n (M/ϖⁿM)_t` of the fibres of the
reductions, and `L_t = E ⊗_{𝒪_E} M_t` through the map `M_t → L_t` induced by `ι`.

Indeed `t^* M` is free on the geometric point, all pro-étale covers of `Spec Ω̄` being split. -/
theorem nonempty_isLimit_and_exists_linearEquiv_of_isLocallyFree
    (L : LisseModule E X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (ι : M ⟶ (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj L.obj)
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M)
    (hι : Mono ι)
    (hι' : IsIso (((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).homEquiv
      M L.obj).symm ι))
    (ϖ : integers ℓ E.1) (hϖ : IsLocalRing.maximalIdeal (integers ℓ E.1) = Ideal.span {ϖ})
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ X) :
    Nonempty (IsLimit ((padicIntegersFibre ℓ E t).mapCone
      (cokernelEndPowTowerCone (padicIntegersSmul ϖ M)))) ∧
    ∃ e : E.1 ⊗[integers ℓ E.1] (padicIntegersFibre ℓ E t).obj M ≃ₗ[E.1]
        (lisseFibre E t).obj L,
      ∀ m, e (1 ⊗ₜ m) = latticeFibreMap ℓ E t ι m := by
  sorry

/-- **Lisse `E`-modules on connected normal schemes and representations of `π₁`** (blueprint
`proposition-lattices-representations-normal-scheme`). Let `X` be a connected Noetherian scheme
whose local rings are integrally closed domains (e.g. a nonempty connected normal scheme of
finite type over a field), `E/ℚ_ℓ` finite with uniformiser `ϖ`, and `Ω` a field.

* The fibre functor at a geometric point `x̄ : Spec Ω̄ ⟶ X` is computed by lattices: for every
  lisse `𝒪_{E,X}`-submodule `M ⊆ L` with `M[1/ℓ] = L` (which exists by
  `AlgebraicGeometry.ProEtale.exists_lisse_integral_lattice_of_isIntegrallyClosed_stalk`), the
  fibre `M_x̄` is `lim_n (M/ϖⁿM)_x̄` and `L_x̄ ≅ (lim_n (M/ϖⁿM)_x̄) ⊗_{𝒪_E} E` through the map
  induced by `M ⊆ L`. In particular this functor does not depend on the choice of `M` up to
  canonical isomorphism: it is canonically the fibre `L_x̄ = Γ(Spec Ω̄, x̄^* L)`.
* There is a monodromy of lisse `E_X`-modules
  (`AlgebraicGeometry.ProEtale.LisseModuleMonodromy`) for which the fibre functor at every
  geometric point `x̄` is an equivalence between lisse `E_X`-modules and finite-dimensional
  continuous `E`-representations of `π₁(X, x̄) = Aut F_x̄`. -/
theorem exists_lisseModuleMonodromy_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian X] [CompactSpace X] [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    (∀ (L : LisseModule E X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
      (ι : M ⟶ (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj L.obj),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M → Mono ι →
      IsIso (((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).homEquiv
        M L.obj).symm ι) →
      ∀ ϖ : integers ℓ E.1, IsLocalRing.maximalIdeal (integers ℓ E.1) = Ideal.span {ϖ} →
      ∀ t : Spec (.of (AlgebraicClosure Ω)) ⟶ X,
        Nonempty (IsLimit ((padicIntegersFibre ℓ E t).mapCone
          (cokernelEndPowTowerCone (padicIntegersSmul ϖ M)))) ∧
        ∃ e : E.1 ⊗[integers ℓ E.1] (padicIntegersFibre ℓ E t).obj M ≃ₗ[E.1]
            (lisseFibre E t).obj L,
          ∀ m, e (1 ⊗ₜ m) = latticeFibreMap ℓ E t ι m) ∧
    ∃ M : LisseModuleMonodromy ℓ E X Ω, ∀ t, M.IsEquivalenceAt t :=
  ⟨fun L M ι hM hι hι' ϖ hϖ t ↦
    nonempty_isLimit_and_exists_linearEquiv_of_isLocallyFree Ω L M ι hM hι hι' ϖ hϖ t,
    exists_lisseModuleMonodromy_isEquivalenceAt_of_isIntegrallyClosed_stalk Ω hX⟩

end AlgebraicGeometry.ProEtale
