/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Smooth proper completion of a smooth curve over a finite field

A smooth geometrically connected curve `U₀` over a finite field `K = 𝔽_q` embeds as a dense
open subscheme of a curve `C₀` which is *proper* over `K` and still smooth and geometrically
connected, the boundary `C₀ \ U₀` being a finite set of closed points.

Separatedness of `U₀` over `K` is part of `AlgebraicGeometry.IsCurve` and is necessary: a
compactification of `p` forces `p` to be separated
(`AlgebraicGeometry.Compactification.isSeparated`), so the affine line with doubled origin has
none.

The proof works over any perfect field `K`. Nagata's compactification theorem embeds `U₀` as an
open subscheme of a scheme `Z` proper over `K`. Let `C₀` be the relative normalization of `Z` in
`U₀`, i.e. the normalization of `Z` in the function field of `U₀` restricted to `U₀`. Since
normalization commutes with the smooth base change `U₀ ⟶ Z`, the curve `U₀` is a dense open
subscheme of `C₀`; the morphism `C₀ ⟶ Z` is finite, so `C₀` is proper over `K`; it is integral of
dimension `dim U₀ = 1` and has integrally closed local rings because `U₀` has. Being normal of
dimension one, `C₀` is regular, hence smooth over the perfect field `K`. The boundary is the
complement of a nonempty open subset of an irreducible noetherian space of dimension one, hence
a finite set of closed points, and `C₀` is geometrically connected since it contains the
geometrically connected `U₀` as a dense open subscheme.

## Main statements

- `AlgebraicGeometry.exists_smooth_properCompactification`: the smooth proper completion of a
  smooth geometrically connected curve over a finite field.
- `AlgebraicGeometry.exists_smooth_properCompactification_of_perfectField`: the same over a
  perfect field, recording also that the completion is integral and `U₀` dense in it.
- `AlgebraicGeometry.IsCurve.exists_projectiveClosure`: an integral curve over a field is a dense
  open subscheme of an integral closed subscheme of projective space.
- `AlgebraicGeometry.exists_smooth_projectiveCompactification`: a normal geometrically connected
  curve of pure dimension one over a perfect field is smooth and has a smooth projective
  geometrically connected completion with finite boundary.
- `AlgebraicGeometry.IsCurve.isQuasiProjective`: a smooth curve over a field is
  quasi-projective.
- `AlgebraicGeometry.IsConnectedCurve.exists_smooth_properCompactification`: a smooth connected
  curve over an algebraically closed field is a dense open subscheme of a smooth proper
  connected curve, with finite boundary.
- `AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top`: a proper open subscheme of a smooth
  proper connected curve over an algebraically closed field is affine.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {U : Scheme.{u}}

/-- Blueprint `lem-wf-finite-field-curve-quasi-projective`: Finite-field curves admit a
projective closure.

An integral curve `U` over a field `K` (separated, of finite type, of dimension at most one)
admits a locally closed immersion `j ≫ ι` into a projective space `ℙ(n; Spec K)` over `K`, where
`ι : X ⟶ ℙ(n; Spec K)` is a closed immersion of an integral scheme `X` and `j : U ⟶ X` is an open
immersion with dense image; thus `X` is the scheme-theoretic closure of `U` in `ℙ(n; Spec K)`.
The input is that `U` has an ample invertible sheaf (Stacks `0A25`). -/
theorem IsCurve.exists_projectiveClosure (p : U ⟶ Spec (.of K)) [IsCurve p] [IsIntegral U] :
    ∃ (n : Type u) (_ : Finite n) (X : Scheme.{u}) (ι : X ⟶ ℙ(n; Spec (.of K))) (j : U ⟶ X),
      IsClosedImmersion ι ∧ IsOpenImmersion j ∧ IsIntegral X ∧ DenseRange j.base ∧
      j ≫ ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)) = p :=
  sorry

/-- The smooth proper completion of a smooth geometrically connected curve `U` over a perfect
field `K`: there is a compactification `c` of `p : U ⟶ Spec K` whose ambient scheme `c.Z` is an
integral smooth geometrically connected curve over `K` containing `U` as a dense open subscheme
with complement a finite set of closed points.

`c.Z` is the relative normalization of a Nagata compactification of `U` in `U`. -/
theorem exists_smooth_properCompactification_of_perfectField [PerfectField K]
    (p : U ⟶ Spec (.of K)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ c : Compactification p, IsIntegral c.Z ∧ IsCurve c.g ∧ SmoothOfRelativeDimension 1 c.g ∧
      GeometricallyConnected c.g ∧ DenseRange c.i.base ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  -- `U` is integral of dimension one, with integrally closed local rings.
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_smooth p
  obtain ⟨x, -⟩ := p.surjective (Classical.arbitrary _)
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace U := IsRegular.irreducibleSpace U
  have : IsReduced U := isReduced_of_isReduced_stalk U
  have : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced U
  have hdimU : topologicalKrullDim U = 1 :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mp inferInstance
  have hnormU := isIntegrallyClosed_stalk_of_isRegular (X := U) hdimU.le
  -- Nagata's compactification `U ⟶ Z ⟶ Spec K`, and the normalization of `Z` in `U`.
  obtain ⟨c₀, -⟩ := exists_isDense_compactification p
  have := c₀.isProper
  have := c₀.isOpenImmersion
  have : QuasiCompact c₀.i := by
    have : QuasiCompact (c₀.i ≫ c₀.g) := c₀.comm ▸ inferInstance
    exact .of_comp c₀.i c₀.g
  have : IsFinite c₀.i.fromNormalization := c₀.i.isFinite_fromNormalization c₀.g
  let c : Compactification p :=
    { Z := c₀.i.normalization
      g := c₀.i.fromNormalization ≫ c₀.g
      i := c₀.i.toNormalization
      comm := by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, ← c₀.comm]
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have : IsIntegral c.Z := inferInstanceAs (IsIntegral c₀.i.normalization)
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsProper c.g := c.isProper
  -- `c.Z` has dimension one.
  have : Nonempty c.i.opensRange := ⟨⟨c.i.base x, x, rfl⟩⟩
  have hdim : topologicalKrullDim c.Z = 1 := by
    rw [← topologicalKrullDim_opens_eq c.g c.i.opensRange, ← hdimU]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso c.i.isoOpensRange).isHomeomorph).symm
  have hcurve : IsCurve c.g := { krullDim_le_one := hdim.le }
  -- `c.Z` is normal of dimension one, hence regular, hence smooth.
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_isIntegrallyClosed_stalk
    (fun z ↦ ⟨inferInstance, c₀.i.isIntegrallyClosed_stalk_normalization hnormU z⟩) hdim.le
  have : Smooth c.g := smooth_of_isRegular c.g
  have hsmooth : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr hdim
  -- `c.Z` is geometrically connected.
  have : Nonempty U := ⟨x⟩
  have : GeometricallyConnected (c.i ≫ c.g) := c.comm ▸ inferInstance
  have hconn := GeometricallyConnected.of_isOpenImmersion c.i c.g
  -- The boundary is a finite set of closed points.
  have hopen : IsOpen (Set.range c.i.base) := c.i.isOpenEmbedding.isOpen_range
  have hne : (Set.range c.i.base).Nonempty := ⟨_, x, rfl⟩
  have : CompactSpace c.Z := (quasiCompact_iff_compactSpace c.g).mp inferInstance
  have : IsNoetherian c.Z := ⟨⟩
  exact ⟨c, inferInstance, hcurve, hsmooth, hconn, hopen.dense hne,
    hopen.finite_compl_of_topologicalKrullDim_le_one hdim.le hne,
    fun z hz ↦ hopen.isClosed_singleton_of_mem_compl hdim.le hne hz⟩

/-- Blueprint `sk-i-real-compactification`: Smooth proper completion.

Every smooth geometrically connected curve `U₀` over a finite field `K` admits a smooth proper
completion: a compactification `c : Compactification p` of the structure morphism
`p : U₀ ⟶ Spec K` whose ambient scheme `c.Z = C₀` is again a smooth geometrically connected
curve over `K`, and whose boundary `C₀ \ U₀` is a finite set of closed points of `C₀`.

The open immersion `U₀ ⟶ C₀` and the properness of `C₀ ⟶ Spec K` are part of the data of a
`Compactification`, so they do not appear among the conclusions. -/
theorem exists_smooth_properCompactification
    {K : Type u} [Field K] [Finite K] {U : Scheme.{u}} (p : U ⟶ Spec (.of K)) [IsCurve p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] :
    ∃ c : Compactification p, IsCurve c.g ∧ SmoothOfRelativeDimension 1 c.g ∧
      GeometricallyConnected c.g ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  obtain ⟨c, -, h₁, h₂, h₃, -, h₄, h₅⟩ := exists_smooth_properCompactification_of_perfectField p
  exact ⟨c, h₁, h₂, h₃, h₄, h₅⟩

/-- Blueprint `lem-wf-curve-normal-smooth-compactification`: Smooth proper compactification of a
normal finite-field curve.

Let `U` be a normal geometrically connected curve of pure dimension one over a perfect field `K`
(for instance a finite field): its local rings are integrally closed domains and
`dim U = 1`. Then `U` is smooth over `K`, and there is a compactification `c` of `U` whose
ambient scheme `c.Z` is a smooth geometrically connected curve over `K` which is *projective*,
i.e. admits a closed immersion into a projective space over `K`, in which `U` is a dense open
subscheme with finite complement. -/
theorem exists_smooth_projectiveCompactification [PerfectField K] (p : U ⟶ Spec (.of K))
    [IsCurve p] [GeometricallyConnected p]
    (hU : ∀ x : U, IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x))
    (hdim : topologicalKrullDim U = 1) :
    SmoothOfRelativeDimension 1 p ∧ ∃ c : Compactification p, IsCurve c.g ∧
      SmoothOfRelativeDimension 1 c.g ∧ GeometricallyConnected c.g ∧
      (∃ (n : Type u) (_ : Finite n) (ι : c.Z ⟶ ℙ(n; Spec (.of K))), IsClosedImmersion ι ∧
        ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)) = c.g) ∧
      DenseRange c.i.base ∧ (Set.range c.i.base)ᶜ.Finite := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_isIntegrallyClosed_stalk hU hdim.le
  have : Smooth p := smooth_of_isRegular p
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace U := irreducibleSpace_of_isDomain_stalk U fun x ↦ (hU x).1
  have hsmooth : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mpr hdim
  refine ⟨hsmooth, ?_⟩
  obtain ⟨c, hint, hcurve, hsm, hconn, hdense, hfin, -⟩ :=
    exists_smooth_properCompactification_of_perfectField p
  -- The projective closure `X` of `c.Z` is `c.Z` itself, since `c.Z` is proper.
  obtain ⟨n, hn, X, ι, j, hι, hj, -, hjd, hcomm⟩ := IsCurve.exists_projectiveClosure c.g
  have := c.isProper
  have : IsProper (j ≫ ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K))) := hcomm ▸ inferInstance
  have : IsProper j := .of_comp j (ι ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)))
  have : Surjective j := by
    refine ⟨fun y ↦ ?_⟩
    have : Set.range j.base = Set.univ := by
      rw [← (j.isClosedMap.isClosed_range).closure_eq, hjd.closure_range]
    exact Set.range_eq_univ.mp this y
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hj, ‹_›⟩
  exact ⟨c, hcurve, hsm, hconn, ⟨n, hn, j ≫ ι, inferInstance, by simpa using hcomm⟩, hdense,
    hfin⟩

/-- **Smooth curves are quasi-projective.** A smooth curve `U` over a field `K` (separated, of
finite type, of dimension at most one) admits an immersion into a projective space over `K`.
The proof glues embeddings of the members of a finite affine cover one at a time, using
sections of line bundles separating the finitely many points outside the overlap (Stacks
`0A25`). (blueprint: `lem-sc-curves-quasi-projective`) -/
theorem IsCurve.isQuasiProjective (p : U ⟶ Spec (.of K)) [IsCurve p] [Smooth p] :
    IsQuasiProjective p :=
  sorry

/-- **Compactification of a smooth curve.** A smooth connected curve `U` over an algebraically
closed field `K` admits a compactification `c` whose ambient scheme `c.Z` is a smooth proper
connected curve over `K`, in which `U` is open with complement a finite set of closed points.

The compactification is the normalization of a Nagata compactification of `U` in `U`, as in
`AlgebraicGeometry.exists_smooth_properCompactification_of_perfectField`; the blueprint uses the
normalization of the closure of `U` in a projective space instead.
(blueprint: `lem-sc-compactification`) -/
theorem IsConnectedCurve.exists_smooth_properCompactification [IsAlgClosed K]
    (p : U ⟶ Spec (.of K)) [IsConnectedCurve p] [Smooth p] :
    ∃ c : Compactification p, IsConnectedCurve c.g ∧ Smooth c.g ∧ (Set.range c.i.base)ᶜ.Finite ∧
      ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z) := by
  have := IsConnectedCurve.connectedSpace' p
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular U := IsRegular.of_smooth p
  have : IrreducibleSpace U := IsRegular.irreducibleSpace U
  have : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := p))
  letI : U.Over (Spec (.of K)) := ⟨p⟩
  have : GeometricallyConnected p := GeometricallyConnected.of_isSepClosed (k := K) U
  obtain ⟨c, hint, hcurve, hsm, -, -, hfin, hclosed⟩ :=
    exists_smooth_properCompactification_of_perfectField p
  have : Smooth c.g := SmoothOfRelativeDimension.smooth 1 c.g
  have hconn : IsConnectedCurve c.g :=
    { toIsCurve := hcurve
      connectedSpace := inferInstance
      krullDim_eq_one := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mp hsm }
  exact ⟨c, hconn, inferInstance, hfin, hclosed⟩

/-- **Open subschemes of a proper curve are affine.** Let `C` be a smooth proper connected curve
over an algebraically closed field `K`. Every open subscheme `V ≠ C` is affine: its complement
`S` is a finite nonempty set of closed points, the effective divisor `D = ∑_{P ∈ S} [P]` has
positive degree, so `𝒪(D)` is ample, and `V = C ∖ D` is affine.
(blueprint: `lem-sc-affine-open-proper`) -/
theorem IsConnectedCurve.isAffine_of_ne_top [IsAlgClosed K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [IsConnectedCurve p] [Smooth p] [IsProper p] (V : C.Opens)
    (hV : V ≠ ⊤) : IsAffine V :=
  sorry

end AlgebraicGeometry
