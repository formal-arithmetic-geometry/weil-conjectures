/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Extensions of finite locally constant sheaves over a noetherian ring

Let `Λ` be a noetherian ring and `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of étale sheaves
of `Λ`-modules on a scheme `X`. If `F₁` and `F₃` are finite locally constant, so is `F₂`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

open Opposite

section LocalLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type v'} [Ring Λ]
  [HasSheafify J (ModuleCat.{v'} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{v'} Λ)]

/-- **A morphism out of a constant sheaf at a finite free module lifts locally along an
epimorphism**: given `q : (ι →₀ Λ)_C ⟶ G` with `ι` finite and an epimorphism `p : E ⟶ G`, every
object `T` has a covering sieve over whose members `U` the restriction of `q` to `J.over U`
factors through `p`. -/
theorem exists_mem_forall_exists_lift_constantSheafOverHom {ι : Type v'} [Finite ι]
    {E G : Sheaf J (ModuleCat.{v'} Λ)} (q : (constantSheaf J _).obj (ModuleCat.of Λ (ι →₀ Λ)) ⟶ G)
    (p : E ⟶ G) [Epi p] (T : C) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (g : U ⟶ T), S g →
      ∃ s : (constantSheaf (J.over U) _).obj (ModuleCat.of Λ (ι →₀ Λ)) ⟶ E.over U,
        s ≫ (J.overPullback _ U).map p =
          constantSheafOverHom J _ U _ ≫ (J.overPullback _ U).map q := by
  classical
  let M := ModuleCat.of Λ (ι →₀ Λ)
  let η := CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)
  let t : ι → ToType (G.obj.obj (op T)) := fun k ↦
    q.hom.app (op T) (η.app (op T) (Finsupp.single k 1))
  have hp : Presheaf.IsLocallySurjective J p.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{v'} Λ) p).2 inferInstance
  refine ⟨⨅ k, Presheaf.imageSieve p.hom (t k), J.iInf_mem _ fun k ↦ hp.imageSieve_mem (t k),
    fun U g hg ↦ ?_⟩
  have hg' (k : ι) : Presheaf.imageSieve p.hom (t k) g :=
    (iInf_le (fun k ↦ Presheaf.imageSieve p.hom (t k)) k : _) g hg
  let u : ι → ToType (E.obj.obj (op U)) := fun k ↦ Presheaf.localPreimage p.hom (t k) g (hg' k)
  have hu (k : ι) : p.hom.app (op U) (u k) = G.obj.map g.op (t k) :=
    Presheaf.app_localPreimage p.hom (t k) g (hg' k)
  let L : M ⟶ (sheafSections (J.over U) (ModuleCat Λ)).obj (op (Over.mk (𝟙 U))) |>.obj
      (E.over U) := ModuleCat.ofHom (Finsupp.linearCombination Λ u)
  refine ⟨((constantSheafAdj (J.over U) _ Over.mkIdTerminal).homEquiv M _).symm L, ?_⟩
  apply ((constantSheafAdj (J.over U) _ Over.mkIdTerminal).homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_constantSheafOverHom]
  ext : 1
  refine (Finsupp.lhom_ext' fun k ↦ LinearMap.ext_ring ?_)
  change p.hom.app (op U) (Finsupp.linearCombination Λ u (Finsupp.single k 1)) =
    q.hom.app (op U) (η.app (op U) (Finsupp.single k 1))
  rw [Finsupp.linearCombination_single, one_smul, hu]
  change G.obj.map g.op (q.hom.app (op T) (η.app (op T) (Finsupp.single k 1))) = _
  erw [← NatTrans.naturality_apply q.hom, ← NatTrans.naturality_apply η]
  rfl

end LocalLift

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- The middle term of a short exact sequence of sheaves of modules whose outer terms have
finitely generated stalks has finitely generated stalks. -/
theorem IsFiniteSheaf.of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hS' := hS.map_of_exact Φ
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₁) Ω s)
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃) Ω s)
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
    have hepi : Function.Surjective (Φ.map S.g) :=
      (ModuleCat.epi_iff_surjective _).1 hS'.epi_g
    exact (ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_exact (f := (Φ.map S.f).hom) (g := (Φ.map S.g).hom) hex hepi)

end AlgebraicGeometry.Scheme
