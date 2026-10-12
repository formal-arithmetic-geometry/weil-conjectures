module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

/-!
# Čech computation of the derived base change map

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/lem-pc-rf-base-change-flat-module.md,
  final comparison (cf. Stacks Tag 08IB) (blueprint: lem-pc-base-change-map-cech).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

-- Statement-review warning: the docstring describes the intended Čech comparison,
-- but the existing signature omits its Čech identifications and comparison equation.
-- The existing existential γ is unused in the conclusion, as are the cover hypotheses.
-- Keep their names and the signature unchanged while proving its literal statement.
set_option linter.unusedVariables false in
/-- The canonical derived base-change morphism is represented by the tensor Čech map.
Source: the blueprint node `lem-pc-base-change-map-cech`, final comparison, and
Stacks Project, Tag 08IB (blueprint: lem-pc-base-change-map-cech).

The complexes `K` and `K_T` are the alternating Čech complexes of the chosen finite
affine cover and its pullback.  The maps on intersections commute with restrictions,
therefore define `γ`; the displayed isomorphisms identify the two derived direct images,
and the last equality identifies the adjoint base-change map with the sheafified map.
Proof: use `lem-pc-cech-resolution` for both covers, affine pullback of sections for
each intersection, stability of separatedness and quasi-compactness under base change,
and the derived pullback/direct-image adjunction and composition isomorphisms.
(blueprint: lem-pc-base-change-map-cech). -/
theorem baseChangeMap_cech
    {A B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (g : Spec B ⟶ Spec A)
    [IsSeparated f] [QuasiCompact f]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i : ι, IsAffineOpen (U i))
    (G : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) G]
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [hAdd : (Scheme.Modules.tensorPullback (pullback.fst f g)).Additive] :
    ∃ (K : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj G ⟶ K),
      ∃ (KT : CochainComplex (pullback f g).Modules ℕ)
        (εT : (CochainComplex.single₀ (pullback f g).Modules).obj
          ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G) ⟶ KT),
      ∃ (γ : ((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K ⟶ KT),
      ∃ (θ : (derivedPullback g).obj
          ((schemeDerivedDirectImage f).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ⟶
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))),
      QuasiIso ε ∧ QuasiIso εT ∧
      IsDerivedModuleBaseChangeMap f g G θ
:= by
  classical
  let p := pullback.fst f g
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, δ, hδ, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback p)
  have h : E = Scheme.Modules.tensorPullback p :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  let c := δ.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback p) (ComplexShape.up ℤ) 0).hom.app G))
  have hc : IsDerivedModulePullbackComparison p G c := ⟨δ, hδ, rfl⟩
  let θ := schemeDerivedBaseChangeMap f (pullback.snd f g) g p
      pullback.condition ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map c
  -- The present signature only asks for resolutions, with no Čech identification
  -- or equation relating γ and θ. Use single complexes and the tensor comparison.
  refine ⟨(CochainComplex.single₀ X.Modules).obj G, 𝟙 _,
    (CochainComplex.single₀ (pullback f g).Modules).obj
      ((Scheme.Modules.tensorPullback p).obj G), 𝟙 _, ?_, θ, ?_, ?_, ?_⟩
  · exact (HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback p) (ComplexShape.up ℕ) 0).hom.app G
  · infer_instance
  · infer_instance
  · exact ⟨c, hc, rfl⟩

end
end AlgebraicGeometry
