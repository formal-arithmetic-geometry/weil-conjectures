module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Canonical relative affinization of a qcqs morphism

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism;
Tag 01LX, lemma-spec-properties
(blueprint: lem-trf-qcqs-relative-affinization-map).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The direct-image structure algebra of a qcqs morphism is quasi-coherent and has
an affine relative-spectrum realization with a morphism from the original scheme.
Every affine-base chart identifies that morphism with the Gamma--Spec unit.
Here `Under.mk ⟨f.c⟩` is the natural algebra `f_* O_X`. The chart is explicitly
`(π ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op U))`, so its section map
is exactly the component of `a`, using the canonical global-section identifications.

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism;
Tag 01LX, lemma-spec-properties (1), (3)
(blueprint: lem-trf-qcqs-relative-affinization-map).

Proof:
1. The structure module is quasi-coherent: on affine opens it is the tilde module
of the ring, by lem-weil-pbc-spec-tilde-free-module with rank one. Apply
pqf-lem-pushforward-qcoh to f and that module. Its pushforward is the underlying
module of the displayed algebra (def-weil-pbc-comm-algebra-sheaf).
2. Apply clause (2) of lem-weil-pbc-affine-morphism-relative-spec to this algebra.
It gives Y, an affine π, the algebra isomorphism a, and the isomorphic charts
on every affine open U, with section maps a_U.
3. Apply lem-weil-pbc-affine-algebra-local-maps to a.inv, with target π and
source f. It gives maps from f-inverse-images of affine base opens to Y, over S,
agreeing on overlaps; their section maps are a_U inverse. The source inverse
images and intersections of base opens need not be affine.
4. These source opens cover X, since affine opens cover S. Glue the local maps
by lem-weil-pbc-scheme-morphism-gluing to get c. The same gluing uniqueness
shows c ≫ π = f, by checking this equality on that cover.
5. Restrict to any affine base open U. The section map of the composite of c_U
and the chart is a_U followed by its inverse, hence the identity. The bijection
lem-weil-pbc-morphism-into-affine-scheme therefore identifies it with the
Gamma--Spec unit. `Opens.toSpecΓ` includes the canonical `topIso` transport
from sections on the ambient open to global sections of its open subscheme. -/
theorem qcqs_relative_affinization_map {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (Scheme.CommAlgebraSheaf.toModule
      (Under.mk (⟨f.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))).IsQuasicoherent ∧
    ∃ (Y : Scheme.{u}) (π : Y ⟶ S), IsAffineHom π ∧
      ∃ (a : (Under.mk (⟨f.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) : S.CommAlgebraSheaf) ≅
        (Under.mk (⟨π.c⟩ : S.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj Y.sheaf) : S.CommAlgebraSheaf))
        (c : X ⟶ Y) (hc : c ≫ π = f),
        ∀ (U : S.Opens), IsAffineOpen U →
          IsIso ((π ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op U))) ∧
          c.resLE (π ⁻¹ᵁ U) (f ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hc]) ≫
            (π ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op U)) =
          (f ⁻¹ᵁ U).toSpecΓ := by
  classical
  -- The structure module is quasi-coherent by the existing unit-module instance.
  have := SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := X.ringCatSheaf)
  have hq := Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f
    (SheafOfModules.unit X.ringCatSheaf)
  refine ⟨hq, ?_⟩
  let A : ObjectProperty.FullSubcategory
      (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
    ⟨Under.mk (⟨f.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf), hq⟩
  obtain ⟨_, E, hobj, _, _, hchart, _⟩ := affine_morphism_relative_spec S
  let Y := (E.inverse.obj A).unop.obj.left
  let π : Y ⟶ S := (E.inverse.obj A).unop.obj.hom
  have : IsAffineHom π := (E.inverse.obj A).unop.property
  let a : A.obj ≅ (Under.mk (⟨π.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj Y.sheaf) :
        S.CommAlgebraSheaf) :=
    asIso ((E.counitIso.app A).inv.hom ≫ eqToHom (hobj (E.inverse.obj A).unop))
  obtain ⟨k, hw, hk, ha⟩ := affine_algebra_local_maps f π a.inv
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let c : X ⟶ Y := 𝒰.glueMorphisms k hk
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ c = k U :=
    𝒰.ι_glueMorphisms k hk U
  have hc : c ≫ π = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ c ≫ π = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  have hsec (U : S.affineOpens) :
      c.appLE (π ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← hc, Scheme.Hom.comp_preimage]) = a.inv.right.hom.app (op U.1) := by
    have e : ⊤ ≤ k U ⁻¹ᵁ (π ⁻¹ᵁ U.1) := by
      rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
      simp
    -- Recover the section map of c by cancelling the open-subscheme top transport.
    have ea := ha U e
    simp only [← hi U] at ea
    rw [Scheme.Hom.comp_appLE] at ea
    simp only [Scheme.Opens.ι_appLE] at ea
    apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
    simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Category.assoc,
      ← Functor.map_comp] at ea ⊢
    convert ea using 1
    congr 1
  refine ⟨Y, π, inferInstance, a, c, hc, ?_⟩
  intro U hU
  refine ⟨hchart A U hU, ?_⟩
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_appLE, hsec ⟨U, hU⟩,
    Category.assoc, ← Spec.map_comp]
  have he : a.hom.right.hom.app (op U) ≫ a.inv.right.hom.app (op U) = 𝟙 _ := by
    exact congrArg (fun z ↦ z.right.hom.app (op U)) a.hom_inv_id
  rw [he, Spec.map_id]
  exact Category.comp_id _

end AlgebraicGeometry
