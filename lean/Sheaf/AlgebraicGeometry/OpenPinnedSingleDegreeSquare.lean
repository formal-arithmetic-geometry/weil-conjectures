/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import Sheaf.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes

/-! # The geometric restriction square for the pinned single-complex counits
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The component of the composition-pinned tensor counit in degree n.
This is constructed from the counit fixed by the composition structure; its
universal property determines that counit up to the natural isomorphism used
in downstream comparisons. No arbitrary module or complex is chosen.
Source: Stacks Project, Tag 08HY
(blueprint: lem-pc-open-pinned-single-degree-square). -/
def pinnedSingleDegreeTensorComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) (n : ℤ) :
    (derivedPullback k).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj M) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback k).obj M) :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  ε.app ((HomotopyCategory.singleFunctor _ n).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) n).hom.app M))

/-- Natural restriction isomorphisms commute with the base-change mate for the
single components of the pinned counits. This contains only the geometric part
of open compatibility: neither arbitrary witnessing counits nor truncation or
comparison automorphisms occur in this statement.
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U; Steps 1, 2 and the
reference-counit part of Step 3 of stage3-open-fixed-counits-compatibility.
(blueprint: lem-pc-open-pinned-single-degree-square).

Proof: Write Z = f' inverse-image W. A cone over U and W composes to a cone
over X and S'. The original pullback property gives its unique lift to X',
which factors through Z. Hence Z is the pullback P of fA and gA, with the
same projections. Use this identification throughout. Restriction has exact
extension by zero as a left adjoint, so preserves K-injectives. Computing
Rf and Rf' on K-injective resolutions gives their natural restriction
isomorphisms (08FE). Restriction preserves K-flat complexes as well: extend
an acyclic test complex by zero, apply the extension-by-zero tensor projection
formula, and use exactness. Thus the pullback computations on K-flat
resolutions give the natural restriction isomorphisms for Lg and Lg'.
Combine the Lg and Rf comparisons with exact single-complex restriction to
obtain a. Combine the Rf' comparison with ordinary tensor restriction along
Z = P and the exact single-complex identification to obtain b.

Transpose both sides of the displayed square under the derived adjunctions
pinned to the composition counits. On the K-flat and K-injective representatives,
both transposes are tensor reassociation followed by the pullback of the
same direct-image counit. The underived restriction square commutes, including
units, counits and reassociations. Apply it termwise to the resolutions, then
localize. This proves equality of the transposes and hence of their mates
(08HY). The termwise single-complex identification identifies the last maps
with pinnedSingleDegreeTensorComparison. All comparisons are natural in G,
so the same functor isomorphisms a and b work for every G. This works in any
integer degree, with empty opens, and with zero modules. It uses no flatness,
properness, or affineness hypothesis on G or the schemes. -/
theorem open_pinned_single_degree_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (n : ℤ) (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let p := pullback.fst fA gA
    let q := pullback.snd fA gA
    let T := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n
    let T0 := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n
    let T' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n
    let TP := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∃ a : ((T ⋙ schemeDerivedDirectImage f) ⋙ derivedPullback g) ⋙ R ≅
        ((schemeOpenRestriction X U ⋙ T0) ⋙ schemeDerivedDirectImage fA) ⋙
          derivedPullback gA,
    ∃ b : ((Scheme.Modules.tensorPullback g' ⋙ T') ⋙ schemeDerivedDirectImage f') ⋙ R ≅
        ((schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback p) ⋙ TP) ⋙
          schemeDerivedDirectImage q,
    ∀ G : X.Modules,
      R.map (schemeDerivedBaseChangeMap f f' g g' sq.w (T.obj G) ≫
          (schemeDerivedDirectImage f').map (pinnedSingleDegreeTensorComparison g' G n)) ≫
        b.hom.app G =
      a.hom.app G ≫
        (schemeDerivedBaseChangeMap fA q gA p pullback.condition
            (T0.obj ((schemeOpenRestriction X U).obj G)) ≫
          (schemeDerivedDirectImage q).map
            (pinnedSingleDegreeTensorComparison p ((schemeOpenRestriction X U).obj G) n))
    := by sorry

end AlgebraicGeometry
