/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.CoherentArtinRees
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.QuasicoherentSheafHom
import Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal
import Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Coherent homomorphisms over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB (blueprint:
lem-weil-pbc-coherent-homs-over-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Maps on the complement of `V(𝓘)` extend to maps from `𝓘ⁿ𝓖`. Let `X` be a Noetherian
scheme (locally Noetherian and quasi-compact), `𝓕` quasi-coherent, `𝓖` coherent and `𝓘` a
quasi-coherent sheaf of ideals. The open `U = X ∖ V(𝓘)` is given by its points: `x ∈ U` iff
the stalk inclusion `𝓘ₓ ⟶ 𝒪_{X,x}` is surjective, i.e. `𝓘ₓ = 𝒪_{X,x}` (so `V(𝓘)` is closed).
`𝓘ⁿ𝓖 ⊆ 𝓖` is `idealModuleProduct (idealSheafPower I.toModulesι n).2 G` with its inclusion
`idealModuleProductι`; at `n = 0` this is the image of the isomorphism `𝒪_X ⊗ 𝓖 ⟶ 𝓖`,
i.e. `𝓖` itself. Then `𝓘|_U = 𝒪_U` and `(𝓘ⁿ𝓖)|_U = 𝓖|_U` (the restriction to `U` of the
inclusion is an isomorphism); `r n m h` is the inclusion `𝓘ᵐ𝓖 ⊆ 𝓘ⁿ𝓖`; the diagram `D` is
`n ↦ Hom(𝓘ⁿ𝓖, 𝓕)` (identified by `e`) with restriction along `r`; the cocone `c` sends `χ`
to `χ|_U` read on `𝓖|_U` through `(𝓘ⁿ𝓖)|_U = 𝓖|_U`; and the canonical map
`colim_n Hom(𝓘ⁿ𝓖, 𝓕) ⟶ Hom_{𝒪_U}(𝓖|_U, 𝓕|_U)` is bijective. In particular every `ψ` on `U`
is `χ|_U` for some `n` and `χ : 𝓘ⁿ𝓖 ⟶ 𝓕`.
Restriction to `U` is `SheafOfModules.overFunctor X.ringCatSheaf U`.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB
(blueprint: lem-weil-pbc-coherent-homs-over-open).

Proof:
1. `V(𝓘)` is closed and meets an affine `W` in `V(𝓘(W))`
   (lem-weil-pbc-quasi-coherent-ideal-zero-set-affine); on affines inside `U` the ideal
   contains `1`, which glues, so `𝓘|_U = 𝒪_U`, and by induction `(𝓘ⁿ𝓖)|_U = 𝓖|_U`; the
   powers decrease, so the maps `ρ_n : χ ↦ χ|_U` are compatible.
2. `X` is quasi-separated and every open is quasi-compact; `𝓘ⁿ`, `𝓘ⁿ𝓖` and
   `𝓘ⁿ ⊗ 𝓖` are coherent, coherent modules are of finite presentation.
3. For `𝓖 = 𝒪_X` the map is `χ ↦ χ_U(1)` into `Γ(U, 𝓕)`, injective by
   lem-weil-pbc-sections-over-quasi-compact-open (1).
4. Surjectivity reduces to coherent `𝓕` by extending the finite type image of `1 ↦ s`
   (lem-weil-pbc-module-finite-type-submodule-extension).
5. For coherent `𝓕` the `𝓘ᴺ`-torsion subsheaves stabilize at some `𝓗 = 𝓕_n`, and
   `𝓘ⁿ𝓗 = 0` (ACC, lem-weil-pbc-noetherian-acc-quasi-coherent).
6. Artin-Rees gives `𝓕' = 𝓘ᵐ𝓕` without `𝓘`-torsion and with `𝓕'|_U = 𝓕|_U`.
7. lem-weil-pbc-sections-over-quasi-compact-open (2) for `𝓕'` gives surjectivity, hence
   the case `𝓖 = 𝒪_X`.
8. `𝓔 = 𝓗om(𝓖, 𝓕)` is quasi-coherent with `𝓔(U) = Hom(𝓖|_U, 𝓕|_U)`; apply step 7 to it.
9. `ψ` gives `φ : 𝓘ⁿ ⟶ 𝓔`, i.e. `φ̃ : 𝓣 = 𝓘ⁿ ⊗ 𝓖 ⟶ 𝓕`; `π : 𝓣 ⟶ 𝓖` has image `𝓘ⁿ𝓖`
   and kernel `𝓚`.
10. `𝓘ⁿ𝓚 = 0`, computed on affines.
11. Artin-Rees for `𝓚 ⊆ 𝓣` gives `𝓘ᵐ𝓣 ≅ 𝓘ⁿ⁺ᵐ𝓖` via `π`.
12. `φ̃ ∘ π'⁻¹ : 𝓘ⁿ⁺ᵐ𝓖 ⟶ 𝓕` restricts to `ψ` on `U` (surjectivity).
13. If `χ|_U = 0`, its image is coherent supported in `V(𝓘)`, killed by some `𝓘ᵗ`
    (lem-weil-pbc-coherent-support-power-ideal-kills), so `χ` vanishes on `𝓘ⁿ⁺ᵗ𝓖`
    (injectivity). -/
structure CoherentHomsOverOpenData {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) where
  U : X.Opens
  r : ∀ (n m : ℕ), n ≤ m →
    (idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
      idealModuleProduct (idealSheafPower I.toModulesι n).2 G)
  hU : ∀ x : X, x ∈ U ↔ Function.Surjective
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom
  hW : ∀ (W : X.Opens), W ≤ U → Function.Bijective (I.toModulesι.app W)
  hIso : ∀ n : ℕ, IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
    (idealModuleProductι (idealSheafPower I.toModulesι n).2 G))
  hcomp : ∀ (n m : ℕ) (h : n ≤ m),
    r n m h ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
      idealModuleProductι (idealSheafPower I.toModulesι m).2 G
  hcolim : ∃ (D : ℕ ⥤ AddCommGrpCat.{u})
    (e : ∀ n : ℕ, D.obj n ≅
      AddCommGrpCat.of (idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F))
    (c : D ⟶ (Functor.const ℕ).obj
      (AddCommGrpCat.of ((SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf U).obj F))),
    (∀ (n m : ℕ) (h : n ≤ m)
      (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
      (e m).hom (D.map (homOfLE h) ((e n).inv χ)) = r n m h ≫ χ) ∧
    (∀ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
      (SheafOfModules.overFunctor X.ringCatSheaf U).map
          (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫
        c.app n ((e n).inv χ) =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map χ) ∧
    Function.Bijective (colimit.desc D ⟨_, c⟩)

/-- The structural data exists (the geometric part of Lemma 01YB).
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
The proof follows Steps 1--11 and 13 of the displayed proof above: construct the
complement and transition maps, establish the coherence and finiteness facts,
apply the sections-over-a-quasi-compact-open result to obtain the cocone and its
bijective colimit map, and use the support-power-ideal argument for injectivity.
These constructions are packaged in `CoherentHomsOverOpenData`; no arbitrary
witness is chosen. (blueprint: lem-weil-pbc-coherent-homs-over-open-data) -/
theorem coherent_homs_over_open_data {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    Nonempty (CoherentHomsOverOpenData I F G) := by
  sorry

/-- The extension clause follows from the structural data in Lemma 01YB.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
Given `d.hcolim`, use surjectivity of its colimit map to represent any morphism
on `d.U` by a colimit class. The filtered colimit of the groups `D.obj n` is
represented by an element at some finite stage; the cocone compatibility in
`d.hcolim` identifies that representative with the restriction of a map from
`idealModuleProduct (idealSheafPower I n) G`, giving the required `n` and `χ`.
This step uses no additional geometric assertion.
(blueprint: lem-weil-pbc-coherent-homs-over-open-extension) -/
theorem coherent_homs_over_open_extension {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (d : CoherentHomsOverOpenData I F G) :
    ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf d.U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf d.U).obj F,
      ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
        (SheafOfModules.overFunctor X.ringCatSheaf d.U).map
            (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
          (SheafOfModules.overFunctor X.ringCatSheaf d.U).map χ := by
  sorry

theorem coherent_homs_over_open {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules)
    [F.IsQuasicoherent] (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∃ (U : X.Opens)
      (r : ∀ (n m : ℕ), n ≤ m →
        (idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
          idealModuleProduct (idealSheafPower I.toModulesι n).2 G)),
      (∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom) ∧
      (∀ (W : X.Opens), W ≤ U → Function.Bijective (I.toModulesι.app W)) ∧
      (∀ n : ℕ, IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map
        (idealModuleProductι (idealSheafPower I.toModulesι n).2 G))) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
          idealModuleProductι (idealSheafPower I.toModulesι m).2 G) ∧
      (∃ (D : ℕ ⥤ AddCommGrpCat.{u})
        (e : ∀ n : ℕ, D.obj n ≅
          AddCommGrpCat.of (idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F))
        (c : D ⟶ (Functor.const ℕ).obj
          (AddCommGrpCat.of ((SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
            (SheafOfModules.overFunctor X.ringCatSheaf U).obj F))),
        (∀ (n m : ℕ) (h : n ≤ m)
          (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (e m).hom (D.map (homOfLE h) ((e n).inv χ)) = r n m h ≫ χ) ∧
        (∀ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (SheafOfModules.overFunctor X.ringCatSheaf U).map
              (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫
            c.app n ((e n).inv χ) =
          (SheafOfModules.overFunctor X.ringCatSheaf U).map χ) ∧
        Function.Bijective (colimit.desc D ⟨_, c⟩)) ∧
      ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
          (SheafOfModules.overFunctor X.ringCatSheaf U).obj F,
        ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
          (SheafOfModules.overFunctor X.ringCatSheaf U).map
              (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
            (SheafOfModules.overFunctor X.ringCatSheaf U).map χ := by
  obtain ⟨d⟩ := coherent_homs_over_open_data I F G hG
  refine ⟨d.U, d.r, d.hU, d.hW, d.hIso, d.hcomp, d.hcolim, ?_⟩
  exact coherent_homs_over_open_extension I F G hG d

end AlgebraicGeometry.Scheme
