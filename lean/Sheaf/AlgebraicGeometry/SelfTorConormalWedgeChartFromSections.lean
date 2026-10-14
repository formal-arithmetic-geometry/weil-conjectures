module
public import Sheaf.AlgebraicGeometry.SelfTorAffineSection
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AffineConormalSections
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
/-- Sheafification of the affine conormal section calculation.
Source: Stacks Project, Tags 01R3 (conormal) and 01I6 (affine
quasi-coherent sheaves, full faithfulness, and exterior powers).
(blueprint: new-t2-self-tor-conormal-wedge-chart-from-sections).
Proof: Let V be the inverse-image chart. It is affine since i is a closed
immersion and U is affine. The conormal module is quasi-coherent: its ideal
module is quasi-coherent, and pullback preserves quasi-coherence. On principal
opens its sections are localizations of its sections on V. Exterior powers
commute with localization, so the exterior sheaf E restricted to V is
quasi-coherent as well. Use exteriorSheaf_restrict_iso to identify it with
the exterior sheaf formed on V. The restriction of T(M) to V is quasi-coherent:
on U the restricted pushforward is the associated A-module M, and its pullback
to the closed chart is the associated B-module B tensor_A M, where B = A/I.
Identify the over-site sheaves with module sheaves on the open subscheme V.
For quasi-coherent module sheaves on an affine scheme, a B-linear map on global
sections extends uniquely: on a principal open D(f) use its localization,
x/f^k mapping to e(x)/f^k, and glue over this basis. Apply this to both e and
e.symm. Their composites are identities on all principal opens, hence as sheaf
maps. Transport this isomorphism back to the over-site. Its component at the
terminal open is e by construction, proving the displayed equation for every
section. This step uses no pure-wedge equation and no choice of a section map.
For the empty chart both sheaves are zero and the same construction applies. -/
theorem exists_selfTor_conormal_wedge_chart_from_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens)
    (e : let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
      let E := Scheme.Modules.exteriorSheaf N n
      let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
      ((E.over (i ⁻¹ᵁ U.1)).val.obj
            (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
          ((T.obj M).over (i ⁻¹ᵁ U.1)).val.obj
            (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorSheaf N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ x : (E.over (i ⁻¹ᵁ U.1)).val.obj
        (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))) x =
          e x := by sorry
end AlgebraicGeometry
