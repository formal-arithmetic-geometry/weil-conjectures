module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Blowup.Affine.ReesGrading
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Componentwise multiplication map; this is the affine gluing step in Tag 02O8.
Source: Stacks Project, coherent.tex, Tag 02O8, lines 5330--5400.
(blueprint: lem-weil-pbc-ideal-powers-rees-multiplication-component)

Proof: on each affine open, multiplication by the coefficient preserves the ideal-power
product by the ideal-power and extended-ideal section formulas. These local maps agree on
overlaps and glue to a module-sheaf morphism; the displayed formula is the resulting
coefficient identity.
-/
theorem idealPowersReesMultiplication_component {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent] :
    let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
    let graded := reesGrading I
    ∀ (m k : ℕ) (b : graded k), ∃ mu : G m ⟶ G (m + k),
      ∀ (U : X.Opens) (s : (G m).val.obj (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
          U).hom ((mu.app U) s) =
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
          (b.val.val.coeff k)) •
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
          U).hom s := by
  sorry

end AlgebraicGeometry
