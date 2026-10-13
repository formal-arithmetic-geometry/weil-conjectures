/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare
import Sheaf.AlgebraicGeometry.ModulePullbackComparisonDegreeAutomorphism
/-! General open restriction compatibility used by fixed counits.
(blueprint: stage3-open-fixed-counits-compatibility). -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
private theorem pinned_comparison_isComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) (n : ℤ) :
    IsModulePullbackComparisonInDegree k M n (pinnedSingleDegreeTensorComparison k M n) := by
  classical
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  refine ⟨ε, ?_, rfl⟩
  exact Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k

set_option linter.unusedVariables false in
-- Keep the original comparison-proof binder hc0; it is introduced again after the lets.
set_option maxHeartbeats 1000000 in
-- Elaborating the explicit comparison witnesses needs a larger heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open restriction compatibility for single modules in every integer degree.
Source: Stacks Project, Tags 08FE and 08HY.
(blueprint: stage3-open-fixed-counits-compatibility).
Generalizes the degree-zero compatibility statement of
CanonicalModuleBaseChangeOpenComparisonCompat, whose proof imports the fixed-counit
item and therefore cannot be imported here without a cycle.
Proof: put Z = f' inverse-image W and P = U times_V W. Composing a cone
on U and W with their open inclusions and applying the original pullback
property gives a unique lift through Z. Thus Z and P are isomorphic, with the
same projections. Restriction of a K-injective complex remains K-injective,
since restriction has exact extension by zero as a left adjoint. Consequently
08FE computes both direct-image restriction comparisons on representatives.
Restriction of K-flat complexes remains K-flat: extend an acyclic test complex
by zero, tensor before restriction, and use exactness and the projection
formula for extension by zero. Compute pullback restriction on these K-flat
representatives. The termwise single-complex identification in degree n and
ordinary tensor-pullback restriction supply the source and target isomorphisms.

First take comparison components from the counits pinned to the composition
structure. Transpose the two base-change maps under the pinned derived
adjunctions, as in 08HY. Both transposes are the pullback of the direct-image
counit following tensor reassociation. The underived restriction square
commutes termwise, including its units, counits and reassociations. Localizing
this equality on the resolutions gives equal transposes and hence equal mates.
Transporting the resolution models to the recorded derived functors gives
the required commuting square for these reference comparison components.

For arbitrary witnessing counits, resolve G(n) by a flat complex supported in
degrees at most n. Right exactness of tensor pullback identifies H^n of the
counit comparison with ordinary tensor pullback, so it is an isomorphism;
left-derived pullback of G(n) lies in degrees at most n. Maps from this object
to a single module in degree n are determined by H^n, by truncation orthogonality.
For reference c1 and arbitrary c, form the target-module automorphism
H^n(c1) inverse followed by H^n(c), using the single/homology identifications.
The preceding uniqueness gives c = c1 followed by this automorphism in degree n.
Apply the same argument to H and c0 on P. If A and B are the images of these
two automorphisms under restriction and direct image, replace the reference
target isomorphism b by A inverse followed by b followed by B. Cancellation
then gives precisely the displayed equality; the source isomorphism is unchanged.
This degree-n truncation argument applies equally for negative and positive n.
Empty opens give zero categories, zero modules give zero arrows, and full opens
recover the original square under the open-scheme comparisons. No flatness or
nonemptiness hypothesis on G or the schemes is used. -/
theorem restricted_base_change_compatibility_single_degree
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules) (n : ℤ)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : (∃ ε : DerivedCategory.Qh.{w} ⋙ derivedPullback g' ⟶
          (Scheme.Modules.tensorPullback g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
              (moduleRings X'.toRingedSpace)),
        (derivedPullback g').IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
          c = ε.app ((HomotopyCategory.singleFunctor _ n).obj G) ≫
            DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G))))
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj H
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∀ (c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H))
    (hc0 : (∃ ε : DerivedCategory.Qh.{w} ⋙ derivedPullback (pullback.fst fA gA) ⟶
          (Scheme.Modules.tensorPullback (pullback.fst fA gA)).mapHomotopyCategory
              (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
              (moduleRings (pullback fA gA).toRingedSpace)),
        (derivedPullback (pullback.fst fA gA)).IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
          c0 = ε.app ((HomotopyCategory.singleFunctor _ n).obj H) ≫
            DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                (Scheme.Modules.tensorPullback (pullback.fst fA gA))
                  (ComplexShape.up ℤ) n).hom.app H)))),
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          (derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H)),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
        := by
  classical
  dsimp only
  intro c0 hc0
  let U := f ⁻¹ᵁ V
  let fA := f ∣_ V
  let gA := g.resLE V W hWV
  let H : U.toScheme.Modules := (schemeOpenRestriction X U).obj G
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let c₁ := pinnedSingleDegreeTensorComparison.{u, w} g' G n
  let c₂ := pinnedSingleDegreeTensorComparison.{u, w} p H n
  have hc₁ : IsModulePullbackComparisonInDegree g' G n c₁ :=
    pinned_comparison_isComparison g' G n
  have hc₂ : IsModulePullbackComparisonInDegree p H n c₂ :=
    pinned_comparison_isComparison p H n
  obtain ⟨α, hα⟩ :=
    modulePullbackComparison_degree_target_automorphism.{u, w} g' G n c₁ c hc₁ hc
  obtain ⟨γ, hγ⟩ :=
    modulePullbackComparison_degree_target_automorphism.{u, w} p H n c₂ c0 hc₂ hc0
  obtain ⟨a, b, hb⟩ := open_pinned_single_degree_square.{u, w} f g g' f' sq n V W hWV
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n
  let T0 := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n
  let A := R.mapIso ((schemeDerivedDirectImage f').mapIso (T.mapIso α))
  let B := (schemeDerivedDirectImage q).mapIso (T0.mapIso γ)
  refine ⟨a.app G, A.symm ≪≫ b.app G ≪≫ B, ?_⟩
  have h :
      (R.map (schemeDerivedBaseChangeMap f f' g g' sq.w _ ≫
        (schemeDerivedDirectImage f').map c₁) ≫ A.hom) ≫
          (A.symm ≪≫ b.app G ≪≫ B).hom =
        (a.app G).hom ≫
          ((schemeDerivedBaseChangeMap fA q gA p pullback.condition _ ≫
            (schemeDerivedDirectImage q).map c₂) ≫ B.hom) := by
    simpa only [R, U, fA, gA, H, p, q, c₁, c₂, Functor.comp_obj, Iso.app_hom,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun k => k ≫ B.hom) (hb G)
  simpa only [A, B, R, T, T0, U, fA, gA, H, p, q, Functor.comp_obj, c₁, c₂, hα, hγ,
    Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using h

end AlgebraicGeometry
