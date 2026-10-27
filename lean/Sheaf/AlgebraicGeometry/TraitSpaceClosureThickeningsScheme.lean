module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Schematicity from a trait's horizontal closure and infinitesimal fibres

Source: Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques
sur une base de dimension 1, Proposition 1.3.2, printed pages 20–21
(blueprint: lem-sfb-trait-space-closure-thickenings-scheme).

The horizontal closure is specified by its kernel ideal on every affine étale chart.
The special fibres are presheaf fibre products over the terminal presheaf of the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated locally finite type algebraic space over a trait is a scheme if its
horizontal closure and all positive infinitesimal special fibres are schemes.
Source: Anantharaman, Proposition 1.3.2, printed pages 20–21
(blueprint: lem-sfb-trait-space-closure-thickenings-scheme).

Proof:
1. Take affine opens in an étale scheme atlas. Their images are quasi-compact open
subspaces covering Y (lem-a1-space-etale-open-image). Each such open V is finite type
and separated over the Noetherian trait, hence Noetherian
(def-sfb-space-morphism-properties, lem-sfb-space-noetherian-coherent-acc).
Quasi-compactness after affine base change follows from the affine tensor-product
atlas (lem-trf-space-fibre-products-etale-covers). No quasi-compactness of Y is used.
2. The quasi-coherent kernel ideals ker(π^m) form an ascending chain
(lem-sfb-space-qcoh-kernels-colimits). Coherent ACC makes it stationary at some N ≥ 1
on V (lem-sfb-space-noetherian-coherent-acc). On affine charts their union is the
localization kernel defining C, so π^N kills its ideal I
(lem-sfb-space-closed-ideal-correspondence).
3. Put D = Y_N restricted to V, with ideal J = π^N O_V. If π^N b lies in I, then b
is itself π-power torsion, hence π^N b = 0. Thus I ∩ J = 0. Both C restricted to V
and D are open subschemes of the assumed schemes; their intersection E is closed
in both (def-a1-space-open-subspace, def-weil-closed-immersion).
4. Glue these schemes along E (lem-sfb-ferrand-scheme-pushout). The closed map from E
has fibres empty or singletons, so the affine-neighbourhood condition holds. The
scheme pushout is also an algebraic-space pushout
(lem-sfb-ferrand-pushout-space-agreement).
5. Since I ∩ J = 0, V is the same pushout (lem-sfb-closed-space-union-pushout).
Uniqueness gives a scheme representing V. All such V lie in the largest schematic
open (lem-sfb-space-largest-schematic-open); their point images cover, so that open
is Y (lem-a1-space-point-open-calculus). This includes empty Y and uses only local N.
-/
theorem isScheme_of_trait_closure_thickenings
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (Y : AlgebraicSpace (Spec (CommRingCat.of R)))
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (hft : ∀ (U : Over (Spec (CommRingCat.of R)))
      (a : yoneda.obj U ⟶ Y.obj.obj), IsEtale a → LocallyOfFiniteType U.hom)
    (C : ClosedSubspace Y)
    (hclosure : ∀ (B : CommRingCat.{u}) (φ : CommRingCat.of R ⟶ B)
      (a : yoneda.obj (Over.mk (Spec.map φ)) ⟶ Y.obj.obj), IsEtale a →
      ∃ (U : Over (Spec (CommRingCat.of R))) (p : U ⟶ Over.mk (Spec.map φ))
        (q : yoneda.obj U ⟶ (C.val : AlgebraicSpace (Spec (CommRingCat.of R))).obj.obj),
        IsPullback q (yoneda.map p) C.val.arrow.hom.hom a ∧
          RingHom.ker (((Scheme.ΓSpecIso B).inv ≫ Scheme.Γ.map p.left.op).hom) =
            RingHom.ker (algebraMap B (Localization.Away (φ.hom π))))
    (hC : ∃ U : Over (Spec (CommRingCat.of R)),
      Nonempty ((C.val : AlgebraicSpace (Spec (CommRingCat.of R))).obj.obj ≅ yoneda.obj U))
    (hthick : ∀ n : ℕ, 1 ≤ n → ∃ U : Over (Spec (CommRingCat.of R)),
      Nonempty (Limits.pullback (terminal.from Y.obj.obj)
        (terminal.from (yoneda.obj (Over.mk (Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π ^ n}))))))) ≅
            yoneda.obj U)) :
    ∃ U : Over (Spec (CommRingCat.of R)), Nonempty (Y.obj.obj ≅ yoneda.obj U) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
