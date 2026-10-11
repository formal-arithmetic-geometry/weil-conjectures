import Sheaf.AlgebraicGeometry.CechResolution
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
import Mathlib.Algebra.Homology.Homotopy

/-!
# Čech computation of the derived base change map

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/lem-pc-rf-base-change-flat-module.md,
  final comparison (cf. Stacks Tag 08IB) (blueprint: lem-pc-base-change-map-cech).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

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
  sorry

end
end AlgebraicGeometry
