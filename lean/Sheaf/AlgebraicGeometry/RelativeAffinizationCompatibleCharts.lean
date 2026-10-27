module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Compatible affine charts for relative affinization

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism;
Tags 01LW and 01LX, relative spectrum and its charts
(blueprint: lem-a1-relative-affinization-compatible-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A qcqs morphism has a quasi-coherent direct-image structure algebra and an affine
relative spectrum with compatible local maps from inverse images of affine base opens.
The algebra is `Under.mk ⟨h.c⟩`: its sections on `U` are sections of `O_Z` on `h ⁻¹ᵁ U`,
and its structure map is induced by `h`. The chart associated to `α` is explicitly
`(π ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U))`.
Its composite with `e U` is the canonical Gamma--Spec map, with the canonical
`Opens.topIso` identification of ambient-open sections and open-subscheme global sections.
Agreement on overlaps is expressed on the pullback of the source open inclusions.
No source open or overlap is required to be affine, and the base is arbitrary.

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism;
Tags 01LW and 01LX; Schemes, Tag 01HI
(blueprint: lem-a1-relative-affinization-compatible-charts).

Proof:
1. On each affine open of Z the structure module is the tilde of the ring, by
lem-weil-pbc-spec-tilde-free-module with rank one. Thus it is quasi-coherent
(pqf-def-coherent). Apply pqf-lem-pushforward-qcoh to the qcqs morphism h. Its
pushforward is the underlying module of the displayed direct-image algebra
(def-weil-pbc-comm-algebra-sheaf).
2. Apply lem-weil-pbc-affine-morphism-relative-spec (2) to obtain Y, an affine π,
and the algebra isomorphism α. Its chart over every affine U has section map α_U
and is an isomorphism.
3. Apply lem-weil-pbc-affine-algebra-local-maps with f = h, g = π, and α.inv.
It supplies maps k_U into Y over S, agreeing on overlaps, with section map α_U inverse.
Their images lie in π inverse image U. Factor uniquely through this open subscheme
by lem-weil-pbc-morphism-factors-through-open-subscheme to obtain e_U.
The equality over S and the monomorphism U into S show that e_U is over U.
4. The chart composite has ring map α_U followed by α_U inverse, hence the identity.
By lem-weil-pbc-morphism-into-affine-scheme it is the canonical Gamma--Spec map,
even when the source open is not affine. Since e_U followed by its target inclusion
is k_U, the overlap equality from step 3 gives the displayed compatibility. -/
theorem relative_affinization_compatible_charts {Z S : Scheme.{u}} (h : Z ⟶ S)
    [QuasiCompact h] [QuasiSeparated h] :
    (Scheme.CommAlgebraSheaf.toModule
      (Under.mk (⟨h.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj Z.sheaf))).IsQuasicoherent ∧
    ∃ (Y : Scheme.{u}) (π : Y ⟶ S), IsAffineHom π ∧
      ∃ (α : (Under.mk (⟨h.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj Z.sheaf) : S.CommAlgebraSheaf) ≅
        (Under.mk (⟨π.c⟩ : S.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj Y.sheaf) : S.CommAlgebraSheaf)),
        (∀ U : S.affineOpens,
          IsIso ((π ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U.1)))) ∧
        ∃ e : ∀ U : S.affineOpens, (h ⁻¹ᵁ U.1).toScheme ⟶ (π ⁻¹ᵁ U.1).toScheme,
          (∀ U : S.affineOpens, e U ≫ (π ∣_ U.1) = h ∣_ U.1) ∧
          (∀ U : S.affineOpens,
            e U ≫ (π ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U.1)) =
              (h ⁻¹ᵁ U.1).toSpecΓ) ∧
          (∀ U V : S.affineOpens,
            Limits.pullback.fst (h ⁻¹ᵁ U.1).ι (h ⁻¹ᵁ V.1).ι ≫ e U ≫ (π ⁻¹ᵁ U.1).ι =
              Limits.pullback.snd (h ⁻¹ᵁ U.1).ι (h ⁻¹ᵁ V.1).ι ≫ e V ≫ (π ⁻¹ᵁ V.1).ι) := by
  sorry

end AlgebraicGeometry
