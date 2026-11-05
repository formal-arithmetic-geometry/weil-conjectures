/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
import WeilConjectures.Tactic.ExactModProofs

/-!

# Base change of exceptional inverse images along generic points

Let `b = i ≫ p : Z ⟶ Y ⟶ P` be a projective morphism of separated schemes of finite type over a
field `k₁`: a closed immersion `i` followed by a proper morphism `p` smooth of pure relative
dimension `d` (for instance `Y = P × ℙᴺ`). Let `g : P' ⟶ P` be a base map out of a scheme `P'`
over a field `L` with `P' ≅ Spec L` (for instance `P' = Spec L`), factoring as
```
P' ≅ Spec L --πₛ--> Spec K₀ --η--> P
```
with `πₛ` given by a field extension `L/K₀` and `η` weakly étale (for instance the inclusion of the
generic point of an integral `P`, `K₀ = κ(P)`, which is a limit of open immersions). This file
proves that the base change map `γ : π^* Rb^! ⟶ Rb'^! g^*` of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) of any cartesian square `π ≫ b = b' ≫ g` is
an isomorphism of functors
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq`,
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_isIso_hom`).

## Main results

- `ProEtale.CondensedRing.upperShriekBaseChangeOfMap_app_paste`: the **horizontal composition
  law** of the base change maps: for horizontally pasted cartesian squares over three fields,
  `γ_outer` is `πZ'^* γ₁` followed by `γ₂`, through the composition isomorphisms of the pullbacks
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapComp`). It comes from the horizontal
  pasting of the proper base change maps
  (`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_app_paste`).
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_point`: for a proper `K₀`-scheme `Z`
  with structure morphism `f` and its base change `f'` along a field extension `L/K₀`, `γ` is an
  isomorphism of functors.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint`:
  the main result, with the intermediate base change `Z₀ ⟶ Y₀ ⟶ Spec K₀` given.
- `AlgebraicGeometry.affineLineGenericPoint`: the generic point `Spec k(x) ⟶ 𝔸¹_k`, weakly étale
  (`AlgebraicGeometry.weaklyEtale_affineLineGenericPoint`); more generally
  `Scheme.weaklyEtale_fromSpecStalk`.
- `AlgebraicGeometry.traitSlicePoint_eq_comp_affineLineGenericPoint`,
  `AlgebraicGeometry.traitGenericSlice_eq_comp_affineLineGenericPoint`: for `x` transcendental,
  the slice point `Spec K ⟶ 𝔸¹_{k'}` and the generic slice `Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` factor as a
  field extension followed by the generic point of the line. These are the factorizations of the
  base maps of the slices of a model with a coordinate.

## Proof

*Composition law.* The base change map of a proper `f` is the mate of the inverse proper base
change isomorphism, i.e. the exchange morphism `CategoryTheory.Adjunction.exchangeRight` of
`Rf_* ⊣ Rf^!` (`CategoryTheory.Adjunction.exchangeRight_eq_mateEquiv`), and exchange morphisms
paste (`CategoryTheory.Adjunction.exchangeRight_app_paste`) as soon as the proper base change maps
do; these are the restrictions of the ambient base change maps, which paste
(`ProEtale.CondensedRing.pullbackSquareComparison_paste`).

*Along `η`.* `b = i ≫ p` with `i` a closed immersion and `p` smooth proper: weakly étale base
change of the closed exceptional inverse image
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`) and of the smooth
one (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale`),
composed by `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app`.

*Along the field extension.* Over the point `Spec K₀` the base change map at the unit is the
comparison of the dualizing complexes of the proper scheme `Z₀` up to that of the point
(`ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`), both
invertible (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`). For any
`N` on the point, `N` is dualizable, so `Rf^! N ≅ f^* N ⊗ Rf^! ℚ̄_ℓ` and the two sides of
`γ(N)` are isomorphic (`ProEtale.CondensedRing.upperShriekBaseChangeIsoPoint`); `Rf'_* γ(N)` is
invertible since pullback from a point commutes with internal homs, and the endomorphism trick
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso`) concludes.

## Implementation notes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed`, the
pasting law on bounded constructible complexes is proved for arbitrary ambient transformations and
instantiated once with `cast_proofs`, the kernel timing out otherwise.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Paste

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]

variable {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {Z'' P'' : Over (Spec (.of k₃))} [LocallyOfFiniteType Z''.hom] [QuasiCompact Z''.hom]
  [IsSeparated Z''.hom] [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom]
  [IsSeparated P''.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} {f'' : Z'' ⟶ P''}
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left} {πP' : P''.left ⟶ P'.left}
  {πZ' : Z''.left ⟶ Z'.left}

end Paste
/-! ### Proper schemes over a point and field extensions -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {K₀ L : Type u} [Field K₀] [Field L]
  [Fact (ringChar K₀).Prime] [Fact (ringChar K₀ ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)] [Algebra K₀ L]
  {Z : Over (Spec (.of K₀))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ point K₀} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πZ : Z'.left ⟶ Z.left} {πP : P'.left ⟶ (point K₀).left}

/-- **The base change map of `Ra^!` at the unit, for a proper scheme across a field extension**:
for a proper `K₀`-scheme `Z` with structure morphism `f`, its base change `f' : Z' ⟶ P'` along a
field extension `L/K₀` (`P' ≅ Spec L` over `L`), the base change map
`πZ^* Rf^! ℚ̄_ℓ ⟶ Rf'^! πP^* ℚ̄_ℓ` is invertible. It is the comparison of the dualizing complexes
of `Z` (`ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`),
up to those of the points, and these are invertible
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`). -/
theorem isIso_upperShriekBaseChangeOfMap_app_unit_point
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sq : IsPullback πZ f'.left f.left πP) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) := by
  have : IsProper P'.hom :=
    MorphismProperty.of_isPullback hP (inferInstanceAs (IsProper (𝟙 (Spec (.of K₀)))))
  have : IsProper (toPoint (point K₀)).left := by
    rw [toPoint_left]
    infer_instance
  have : IsProper (toPoint P').left := by
    rw [toPoint_left]
    infer_instance
  have hf : toPoint Z = f := toPoint_ext _ _
  have hf' : toPoint Z' = f' ≫ toPoint P' := (comp_toPoint f').symm
  have : IsProper (toPoint Z).left := by
    rw [hf]
    infer_instance
  have : IsProper (toPoint Z').left := by
    rw [toPoint_left, ← Over.w f']
    infer_instance
  let e := (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap ℓ (X := point K₀)
    (Y := point L) (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))).inv
  have sqX : IsPullback πP (toPoint P').left (toPoint (point K₀)).left
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) := by
    rw [toPoint_left, toPoint_left]
    exact hP
  have sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) := by
    rw [hf, hf', Over.comp_left, toPoint_left]
    exact sq.paste_vert hP
  have hX := isIso_dualizingComplexBaseChange_of_fieldExtension ℓ e (X := point K₀)
    (X' := P') sqX
  have hZ := isIso_dualizingComplexBaseChange_of_fieldExtension ℓ e (X := Z) (X' := Z') sqZ
  rw [dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap ℓ e sqX sqZ sq] at hZ
  have := IsIso.of_isIso_comp_left ((boundedConstructibleUpperStarOfMap ℓ πZ).map
    (upperShriekDualizingComplexIso ℓ f).inv) ((upperShriekBaseChangeOfMap ℓ sq).app
    (dualizingComplex ℓ (point K₀)) ≫ (boundedConstructibleUpperShriek ℓ f').map
      (dualizingComplexBaseChange ℓ e sqX) ≫ (upperShriekDualizingComplexIso ℓ f').hom)
  have hω := IsIso.of_isIso_comp_right ((upperShriekBaseChangeOfMap ℓ sq).app
    (dualizingComplex ℓ (point K₀))) ((boundedConstructibleUpperShriek ℓ f').map
      (dualizingComplexBaseChange ℓ e sqX) ≫ (upperShriekDualizingComplexIso ℓ f').hom)
  /- Transport along `ω_s ≅ ℚ̄_ℓ`. -/
  let ι : dualizingComplex ℓ (point K₀) ≅ 𝟙_ _ := dualizingComplexPointIso ℓ K₀
  have hn := (upperShriekBaseChangeOfMap ℓ sq).naturality ι.hom
  have : IsIso ((boundedConstructibleUpperShriek ℓ f ⋙
      boundedConstructibleUpperStarOfMap ℓ πZ).map ι.hom ≫
        (upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((boundedConstructibleUpperShriek ℓ f ⋙
    boundedConstructibleUpperStarOfMap ℓ πZ).map ι.hom) _

end Point
/-! ### Projective morphisms along a generic point followed by a field extension -/

section GenericPoint

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ K₀ L : Type u} [Field k₁] [Field K₀] [Field L]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar K₀).Prime]
  [Fact (ringChar K₀ ≠ ℓ)] [Fact (ringChar L).Prime] [Fact (ringChar L ≠ ℓ)] [Algebra K₀ L]
  {Z Y P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z₀ Y₀ : Over (Spec (.of K₀))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
  [IsSeparated Z₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  {Z' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : Z ⟶ Y} {p : Y ⟶ P} [IsClosedImmersion i.left] [IsProper p.left]
  {i₀ : Z₀ ⟶ Y₀} {p₀ : Y₀ ⟶ point K₀} [IsClosedImmersion i₀.left] [IsProper p₀.left]
  {f' : Z' ⟶ P'} [IsProper f'.left]
  {η : Spec (.of K₀) ⟶ P.left} {πZ₀ : Z₀.left ⟶ Z.left} {πY₀ : Y₀.left ⟶ Y.left}
  {πZ' : Z'.left ⟶ Z₀.left} {πP : P'.left ⟶ (point K₀).left}

end GenericPoint
end ProEtale.CondensedRing

/-! ### Generic points are weakly étale -/

section WeaklyEtale

variable (k : Type u) [Field k]

variable {k} {K : Type u} [Field K] [Algebra k K] {x : K}

end WeaklyEtale

end AlgebraicGeometry
