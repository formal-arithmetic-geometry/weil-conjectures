module

public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Exact sequence of supported sections for injective pro-etale complexes

Source: Weil conjectures blueprint, node `lem-pur-support-exact`;
Stacks Project, Tags 03EJ, 03EI, 09AH and 0114 (blueprint: lem-pur-support-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- Apply the actual closed supported inverse image and direct image term by term.
Source: Weil conjectures blueprint, node `lem-pur-support-exact`, displayed first term
(blueprint: lem-pur-support-exact). -/
noncomputable def supportedSectionsComplex
    (R : Type (u + 1)) [CommRing R] [Finite R] {Z U X : Scheme.{u}}
    (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base))
    (I : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ) :
    CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ :=
  letI : PreservesFiniteLimits (finiteClosedUpperShriek R s j) :=
    (finiteSupportedSections_leftExact R s j hcompl).2
  (((s)_*[ModuleCat.{u + 1} R]).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((finiteClosedUpperShriek R s j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)

/-- Extend a section across a monomorphism of pro-etale objects by applying injectivity
 to the corresponding monomorphism of sheafified free modules. Source: the free-module
 argument of blueprint `lem-pur-support-exact`, Stacks Tags 03EJ and 03EI. -/
private theorem restriction_surjective
    (R : Type (u + 1)) [CommRing R] {X : Scheme.{u}}
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [Injective M]
    {V W : X.ProEt} (a : V ⟶ W) [Mono a] :
    Function.Surjective (M.obj.map a.op) := by
  let J := ProEt.topology X
  let P (T : X.ProEt) : Sheaf J (ModuleCat.{u + 1} R) :=
    (presheafToSheaf J _).obj (Sheaf.freeModuleYoneda.{u + 1} R T)
  let t : Sheaf.freeModuleYoneda.{u + 1} R V ⟶
      Sheaf.freeModuleYoneda.{u + 1} R W :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map a) (ModuleCat.free R)
  have ht : Mono t := by
    have (T : X.ProEtᵒᵖ) : Mono (t.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y hxy
      apply ULift.ext
      apply (cancel_mono a).1
      exact congrArg ULift.down hxy
    exact NatTrans.mono_of_mono_app t
  let f : P V ⟶ P W := (presheafToSheaf J _).map t
  have : Mono f := inferInstance
  let e (T : X.ProEt) (g : P T ⟶ M) : M.obj.obj (Opposite.op T) :=
    g.hom.app (Opposite.op T) ((toSheafify J (Sheaf.freeModuleYoneda.{u + 1} R T)).app
      (Opposite.op T) (Sheaf.freeModuleYonedaGen.{u + 1} T))
  intro x
  let b : P V ⟶ M :=
    ⟨sheafifyLift J (Sheaf.freeModuleYonedaHom.{u + 1} V M.obj x) M.property⟩
  let g := Injective.factorThru b f
  refine ⟨e W g, ?_⟩
  have hg : f ≫ g = b := Injective.comp_factorThru b f
  have he : e V b = x := by
    change ((toSheafify J _ ≫ sheafifyLift J
      (Sheaf.freeModuleYonedaHom.{u + 1} V M.obj x) M.property).app
        (Opposite.op V)) _ = x
    rw [toSheafify_sheafifyLift]
    exact Sheaf.freeModuleYonedaHom_gen V M.obj x
  rw [← he, ← hg]
  dsimp [e]
  rw [← ConcreteCategory.comp_apply, ← g.hom.naturality]
  rw [ConcreteCategory.comp_apply]
  congr 1
  change ((toSheafify J _).app (Opposite.op W) ≫ (P W).obj.map a.op)
      (Sheaf.freeModuleYonedaGen.{u + 1} W) =
    ((toSheafify J _).app (Opposite.op V) ≫ f.hom.app (Opposite.op V))
      (Sheaf.freeModuleYonedaGen.{u + 1} V)
  rw [← (toSheafify J _).naturality]
  rw [ConcreteCategory.comp_apply]
  have hgen : (Sheaf.freeModuleYoneda.{u + 1} R W).map a.op
      (Sheaf.freeModuleYonedaGen.{u + 1} W) = Finsupp.single (ULift.up a) 1 := by
    simp [Sheaf.freeModuleYonedaGen, Sheaf.freeModuleYoneda, ModuleCat.free]
  rw [hgen]
  change _ = ((toSheafify J _ ≫ f.hom).app (Opposite.op V))
    (Sheaf.freeModuleYonedaGen.{u + 1} V)
  change _ = ((toSheafify J _ ≫ sheafifyMap J t).app (Opposite.op V))
    (Sheaf.freeModuleYonedaGen.{u + 1} V)
  rw [← toSheafify_naturality]
  dsimp [t]
  simp [Sheaf.freeModuleYonedaGen, ModuleCat.free]
  rfl

/-- The canonical supported-section inclusion and open restriction unit are short exact
for a termwise injective complex and a quasi-compact open complement.
Source: Weil conjectures blueprint, node `lem-pur-support-exact`; Stacks Project,
Tags 03EJ, 03EI, 09AH and 0114 (blueprint: lem-pur-support-exact).
Proof:
1. Use the source library's restriction/direct-image adjunction, induced from the site
   composition/base-change adjunction. Its unit on V is restriction to V times_X U.
   Uniqueness of left adjoints transports this to the specified inverse-image unit;
   the transport is the direct image of an isomorphism.
2. The inclusion V times_X U into V gives an injection on representable bases, hence a
   monomorphism of free module presheaves (`lem-weil-pbc-free-yoneda-presheaf-module`).
   Exact sheafification preserves this monomorphism
   (`lem-weil-pbc-ringed-site-module-sheafification-exact`).
3. The free-module Hom bijection and sheafification adjunction identify precomposition
   with this map with restriction of sections: evaluate on the identity basis element.
   The source library supplies the explicit free-module morphism and generator equation.
4. Injectivity of each I.X n extends every such section across that monomorphism
   (`def-sp-injective-resolutions`). Thus the open unit is sectionwise surjective and
   consequently epic in every degree.
5. Its kernel is the supported-section sheaf. For a quasi-compact complement its closed
   adjunction unit identifies this kernel with s_*s^!I.X n (`def-pur-flasque-support`).
   Naturality makes the kernel inclusions and open units chain maps, with zero composite.
6. The sequence is short exact in each degree (`def-weil-pbc-exact-sequence`); the abelian
   degreewise criterion gives short exactness of complexes
   (`lem-weil-pbc-cochain-complexes-degreewise-exact`). No boundedness or K-injectivity is
   used. The equations below specify the canonical maps, rather than arbitrary maps
   between the same three objects. -/
theorem shortExact_sectionsWithSupport
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Z U X : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base))
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)) ℤ)
    [∀ n, Injective (I.X n)] :
    ∃ (f : supportedSectionsComplex R s j hcompl I ⟶ I)
      (g : I ⟶ (((j)^*[ModuleCat.{u + 1} R] ⋙ (j)_*[ModuleCat.{u + 1} R]).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I),
      (∀ n, (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) s).unit.app
          ((finiteSupportedSections R j).obj (I.X n)) ≫ f.f n =
        (finiteSupportedSectionsι R j).app (I.X n)) ∧
      (∀ n, g.f n =
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app (I.X n)) ∧
      ∃ (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  let A := ModuleCat.{u + 1} R
  let adj := upperStarLowerStarAdjunction A j
  have h_epi (M : Sheaf (ProEt.topology X) A) [Injective M] :
      Epi (adj.unit.app M) := by
    let adj' := openImmersionRestrictionLowerStarAdjunction A j
    have hu : adj.unit.app M = adj'.unit.app M ≫
        (lowerStar A j).map ((adj.leftAdjointUniq adj').inv.app M) := by
      rw [← adj.unit_leftAdjointUniq_hom_app adj' M, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    rw [hu]
    suffices Epi (adj'.unit.app M) from inferInstance
    have hsurj (V : X.ProEt) : Function.Surjective
        (((adj'.unit.app M).hom).app (Opposite.op V)) := by
      change Function.Surjective (M.obj.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
          trivial).counit.app V).op)
      let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
        inferInstance trivial).counit.app V
      have : Mono a := by
        have : Mono a.left := by
          change Mono (pullback.fst V.hom j)
          infer_instance
        exact (MorphismProperty.Over.forget @WeaklyEtale ⊤ X ⋙ Over.forget X).mono_of_mono_map
          (show Mono a.left from inferInstance)
      exact restriction_surjective R M a
    have (V : X.ProEtᵒᵖ) : Epi (((adj'.unit.app M).hom).app V) :=
      (ModuleCat.epi_iff_surjective _).2 (hsurj V.unop)
    have : Epi (adj'.unit.app M).hom := NatTrans.epi_of_epi_app _
    exact (sheafToPresheaf (ProEt.topology X) A).epi_of_epi_map
      (show Epi (adj'.unit.app M).hom from inferInstance)
  have := finiteSupportedClosedComparison_isIso R s j hcompl
  let q := asIso (finiteSupportedClosedComparison R s j)
  let inc : finiteClosedUpperShriek R s j ⋙ lowerStar A s ⟶ 𝟭 _ :=
    q.inv ≫ finiteSupportedSectionsι R j
  let f : supportedSectionsComplex R s j hcompl I ⟶ I :=
    { f n := inc.app (I.X n)
      comm' n m _ := (inc.naturality (I.d n m)).symm }
  let g : I ⟶ ((upperStar A j ⋙ lowerStar A j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I :=
    { f n := adj.unit.app (I.X n)
      comm' n m _ := (adj.unit.naturality (I.d n m)).symm }
  have hzero (M : Sheaf (ProEt.topology X) A) : inc.app M ≫ adj.unit.app M = 0 := by
    change q.inv.app M ≫ (finiteSupportedSectionsι R j).app M ≫ adj.unit.app M = 0
    have h := congr_app (kernel.condition adj.unit) M
    simpa only [finiteSupportedSectionsι, NatTrans.comp_app, NatTrans.app_zero,
      comp_zero] using
      congrArg (fun t ↦ q.inv.app M ≫ t) h
  have w : f ≫ g = 0 := by
    ext n : 1
    exact hzero (I.X n)
  refine ⟨f, g, ?_, fun _ ↦ rfl, w, ?_⟩
  · intro n
    change q.hom.app (I.X n) ≫ (q.inv.app (I.X n) ≫ _) = _
    simp
  · apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have := h_epi (I.X n)
    let S := ShortComplex.mk ((finiteSupportedSectionsι R j).app (I.X n))
      (adj.unit.app (I.X n)) (congr_app (kernel.condition adj.unit) (I.X n))
    have hs : S.ShortExact := by
      have hk : IsLimit (KernelFork.ofι S.f S.zero) := by
        exact KernelFork.mapIsLimit _ (kernelIsKernel adj.unit)
          ((CategoryTheory.evaluation _ _).obj (I.X n))
      exact { exact := S.exact_of_f_is_kernel hk
              mono_f := mono_of_isLimit_fork hk }
    let e : S ≅ (ShortComplex.mk f g w).map
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) n) :=
      ShortComplex.isoMk (q.app (I.X n)) (Iso.refl _) (Iso.refl _)
        (by dsimp [S, f, inc]; simp) (by simp [S, g])
    exact ShortComplex.shortExact_of_iso e hs

end AlgebraicGeometry.ProEtale
