/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
public import Sheaf.AlgebraicGeometry.SingleComplexOpenSquareComparison

/-! # Coherence of open pullback squares

Source: Stacks Project, Tag 0D5S, and Tag 0DJ9, first paragraph.
(blueprint: lem-pc-t2-open-pullback-cube).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The two paths around a commuting cube of pullback comparisons agree.
Source: Stacks Project, cohomology.tex, Tag 0D5S; perfect.tex, Tag 0DJ9.
(blueprint: lem-pc-t2-open-pullback-cube).

Proof: Expand each open square as the inverse open-pullback comparison,
composition comparison, equality transport, inverse composition comparison,
and open-pullback comparison. Naturality of composition comparisons moves the
open-pullback factors through the adjacent functors. Cancel each neighboring
open comparison with its inverse. Apply associativity of the pinned composition
comparisons to the triples j,U.ι,f; U'.ι,g',f; f' restricted,V'.ι,g; and
j,f restricted,V.ι. The outer square equality and the two restriction equalities
identify the resulting composite scheme morphisms; equality transports coincide
by proof irrelevance. Both paths reduce to the same comparison with the total
composite. Cancel the remaining composition comparisons. The calculation uses
only functoriality and invertible comparisons, hence applies to empty opens,
zero objects, and arbitrary unbounded complexes. No direct image or adjunction
counit occurs in this assertion. -/
theorem singleComplexOpen_pullback_cube
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (h₀ : j ≫ (f ∣_ V) = (f' ∣_ V') ≫ g.resLE V V' hV')
    (M : schemeDerivedCategory S) :
    let q := singleComplexOpenSquareComparison f f' g g' h
    let q₀ := singleComplexOpenSquareComparison
      (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j h₀
    let RS := (schemeOpenRestriction S V).mapDerivedCategory
    let RX' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let d := singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
      (morphismRestrict_ι f V)
    let d' := singleComplexOpenPullbackSquareIso f' V' (f' ⁻¹ᵁ V') (f' ∣_ V')
      (morphismRestrict_ι f' V')
    let e := singleComplexOpenPullbackSquareIso g V V' (g.resLE V V' hV')
      (Scheme.Hom.resLE_comp_ι g hV')
    let e' := singleComplexOpenPullbackSquareIso g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    q₀.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
        e'.hom.app ((derivedPullback f).obj M) =
      (derivedPullback (f' ∣_ V')).map (e.hom.app M) ≫
        d'.hom.app ((derivedPullback g).obj M) ≫ RX'.map (q.app M) := by sorry

end AlgebraicGeometry
