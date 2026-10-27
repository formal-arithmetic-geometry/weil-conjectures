module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace

/-! # Smooth maps with nonempty integral geometric fibres

Source: Stacks Project, Morphisms of Spaces, Tags 03ZE, 03KL and 042S;
Spaces over Fields, Tag 0AD4 (blueprint: def-sfb-smooth-integral-space-map).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smoothness, separatedness and finite presentation, with nonempty integral geometric
fibres, for an arbitrary map to a represented scheme. Integrality is irreducibility on
points and reducedness on every étale chart; no group law or section is assumed.
Source: Stacks, Tags 03ZE, 03KL, 042S and 0AD4
(blueprint: def-sfb-smooth-integral-space-map). -/
def SmoothIntegralSpaceMap {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (p : X ⟶ schemeSpace T) : Prop :=
  MapIsLocally (@Smooth) p ∧ MapIsSeparated p ∧
    MapIsLocallyOfFinitePresentation p ∧ MapIsQuasiCompact p.hom.hom ∧
    MapIsQuasiCompact (pullback.diagonal p.hom.hom) ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ T.left),
      IrreducibleSpace (Point (Limits.pullback p.hom.hom
        (yoneda.map (Over.homMk (U := Over.mk (s ≫ T.hom)) (V := T) s rfl)))) ∧
      ∀ (U : Over S)
        (a : yoneda.obj U ⟶ Limits.pullback p.hom.hom
          (yoneda.map (Over.homMk (U := Over.mk (s ≫ T.hom)) (V := T) s rfl))),
        IsEtale a → AlgebraicGeometry.IsReduced U.left

/-- The second projection of the actual sheaf fibre product.
Source: Stacks, Tags 02X2 and 03ZE (blueprint: def-sfb-smooth-integral-space-map). -/
def integralSpaceBaseChangeMap {S : Scheme.{u}} {X : AlgebraicSpace S} {T U : Over S}
    (p : X ⟶ schemeSpace T) (a : U ⟶ T) :
    enlargedFibreProduct p (groupSchemeMap a) ⟶ schemeSpace U :=
  ObjectProperty.homMk (Limits.pullback.snd p.hom (groupSchemeMap a).hom)

end AlgebraicGeometry.AlgebraicSpace
