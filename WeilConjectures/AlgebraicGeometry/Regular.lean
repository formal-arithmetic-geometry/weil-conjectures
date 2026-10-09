/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular schemes

A scheme is *regular* if all of its local rings are regular local rings. Mathlib has the
predicate `IsRegularLocalRing` on commutative rings but no class for schemes, so it is
introduced here; it is a hypothesis of the divisor sequence and of Grothendieck's residue
injection for the Brauer group.

## Main statements

- `AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`: a scheme étale over a regular scheme
  is regular.
- `AlgebraicGeometry.isRegularLocalRing_stalk_pullback`: a product of regular schemes locally
  of finite type over a perfect field is regular.
- `AlgebraicGeometry.IsRegular.of_smooth`: a scheme smooth over a field is regular.
- `AlgebraicGeometry.smooth_of_isRegular`: a regular scheme locally of finite type over a perfect
  field is smooth over it.
- `AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk`: a locally noetherian scheme of
  dimension at most one whose local rings are integrally closed domains is regular.
- `AlgebraicGeometry.isIntegrallyClosed_stalk_of_isRegular`: conversely, the local rings of a
  regular locally noetherian scheme of dimension at most one are integrally closed.
- `AlgebraicGeometry.IsRegular.irreducibleSpace`: a connected locally noetherian regular scheme
  is irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.of_smooth_of_geometricallyConnected`: a smooth
  morphism with geometrically connected fibres has geometrically irreducible fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme is *regular* if the local ring at each of its points is a regular local ring. -/
@[mk_iff]
class IsRegular (X : Scheme.{u}) : Prop where
  /-- The local ring of a regular scheme at any point is a regular local ring. -/
  isRegularLocalRing_stalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.isRegularLocalRing_stalk

/-- The spectrum of a field is regular: its local ring is the localization of the field at its
zero ideal. -/
instance IsRegular.spec_field (k : Type u) [Field k] : IsRegular (Spec (.of k)) :=
  ⟨fun z ↦ IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of k) z).commRingCatIsoToRingEquiv.symm⟩

/-- A scheme étale over a regular scheme is regular: an étale local homomorphism of local rings
is flat with regular (indeed trivial) closed fibre, so it preserves regularity. -/
theorem isRegularLocalRing_stalk_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  sorry

/-- The product of two regular schemes locally of finite type over a perfect field `k` is
regular: over a perfect field such schemes are smooth, and smoothness is stable under base
change and composition. -/
theorem isRegularLocalRing_stalk_pullback {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (z : ↥(pullback f g)) :
    IsRegularLocalRing ((pullback f g).presheaf.stalk z) :=
  sorry

/-- Let `V` be an affine open of a scheme `X` and `R → Γ(X, V)` an étale ring map from a regular
ring `R`. Then the local rings of `X` at the points of `V` are regular: they are localizations of
`Γ(X, V)` at primes (`IsRegularLocalRing.localization_of_etale`). -/
theorem IsAffineOpen.isRegularLocalRing_stalk_of_etale {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsRegularRing R] {V : X.Opens} (hV : IsAffineOpen V) (φ : R →+* Γ(X, V))
    (hφ : φ.Etale) (x : X) (hx : x ∈ V) : IsRegularLocalRing (X.presheaf.stalk x) := by
  algebraize [φ]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  have := IsRegularLocalRing.localization_of_etale (R := R) (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  exact .of_ringEquiv (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- A scheme smooth over a field `k` is regular: the local rings of a smooth `k`-scheme are
regular local rings, hence domains (`IsRegularLocalRing.isDomain`). Near any point `X` is étale
over an affine space `𝔸ⁿ_k`, whose local rings are regular, and étale maps preserve regularity.

(blueprint: `lem-sc-smooth-regular`) -/
theorem IsRegular.of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] : IsRegular X := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact smoothOfRelativeDimension_comp (n := d) (m := 0) _ _
  obtain ⟨W, hW, hxW, φ, hφ⟩ :=
    SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field (V.ι ≫ f) d ⟨x, hx⟩
  have := hW.isRegularLocalRing_stalk_of_etale φ hφ _ hxW
  exact .of_ringEquiv (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv

/-- A regular scheme locally of finite type over a perfect field `k` is smooth over `k`: at a
point `x` the residue field is finitely generated over the perfect field `k`, hence separably
generated, and a regular local `k`-algebra essentially of finite type with such a residue field
is smooth over `k` (Stacks `00TV`). This is the main input of
`AlgebraicGeometry.Scheme.smooth_fromNormalization_comp` (blueprint:
`lem-sc-normalized-curve-smooth`). -/
theorem smooth_of_isRegular {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsRegular X] : Smooth f :=
  sorry

/-- A locally noetherian scheme of dimension at most one whose local rings are integrally closed
domains is regular: each local ring is a field or a discrete valuation ring.
(blueprint: `lem-sc-normal-dim1-dvr`) -/
theorem IsRegular.of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 1) : IsRegular X := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨_, _⟩ := hX x
  exact .of_isIntegrallyClosed _ ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)

/-- **The normalized curve over a perfect field is smooth.** Let `X` be an integral scheme of
finite type and of dimension one over a perfect field `k`. Its normalization `X^ν` in the function
field is normal of dimension one, so its local rings are fields or discrete valuation rings; hence
`X^ν` is regular, and therefore smooth over `k` (`AlgebraicGeometry.smooth_of_isRegular`).
(blueprint: `lem-sc-normalized-curve-smooth`) -/
theorem Scheme.smooth_fromNormalization_comp {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim X = 1) : Smooth (X.fromNormalization ≫ q) := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  have : IsLocallyNoetherian X.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromNormalization ≫ q)
  -- the local rings of `Spec k(X)` are integrally closed
  have hK (x : Spec X.functionField) :
      IsIntegrallyClosed ((Spec X.functionField).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec X.functionField).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec X.functionField).Opens))
    have := (isAffineOpen_top (Spec X.functionField)).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec X.functionField, ⊤) :=
      .of_equiv (Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have : IsRegular X.normalization := IsRegular.of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, X.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization hK y⟩)
    (X.topologicalKrullDim_normalization q ▸ hdim).le
  exact smooth_of_isRegular _

/-- The local rings of a regular locally noetherian scheme of dimension at most one are
integrally closed: each of them is a field or a discrete valuation ring. -/
theorem isIntegrallyClosed_stalk_of_isRegular {X : Scheme.{u}} [IsRegular X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
  IsRegularLocalRing.isIntegrallyClosed _ ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)

/-- **Smooth curves are normal.** The local rings of a scheme of dimension at most one which is
smooth over a field `k` are integrally closed: they are regular local rings
(`AlgebraicGeometry.IsRegular.of_smooth`) of dimension at most one, hence fields or discrete
valuation rings. (blueprint: `lem-sc-smooth-normal`) -/
theorem isIntegrallyClosed_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := IsRegular.of_smooth f
  isIntegrallyClosed_stalk_of_isRegular hdim x

/-- A connected locally noetherian regular scheme is irreducible, since its local rings, being
regular, are integral domains. -/
theorem IsRegular.irreducibleSpace (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IrreducibleSpace X :=
  irreducibleSpace_of_isDomain_stalk X fun _ ↦ inferInstance

/-- A nonempty connected locally noetherian regular scheme is integral: it is irreducible
(`AlgebraicGeometry.IsRegular.irreducibleSpace`), and reduced since its local rings are
integral domains. -/
theorem IsRegular.isIntegral (X : Scheme.{u}) [IsRegular X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IsIntegral X :=
  have := IsRegular.irreducibleSpace X
  have := isReduced_of_isReduced_stalk X
  isIntegral_of_irreducibleSpace_of_isReduced X

/-- A smooth morphism with geometrically connected fibres has geometrically irreducible fibres:
a base change of it to a field is smooth over that field, hence regular and locally noetherian,
and connected, hence irreducible. -/
theorem GeometricallyIrreducible.of_smooth_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIrreducible f where
  geometrically_irreducibleSpace _ _ y _ fst snd h := by
    have := GeometricallyConnected.geometrically_connectedSpace y fst snd h
    have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    have := LocallyOfFiniteType.isLocallyNoetherian snd
    have := IsRegular.of_smooth snd
    exact IsRegular.irreducibleSpace _

/-- **Smooth morphisms are geometrically reduced.** A base change of a smooth morphism to a
field is smooth over that field, hence regular, so its local rings are regular local rings,
which are integral domains. -/
theorem GeometricallyReduced.of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced _ _ y _ fst snd h := by
    have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    have := LocallyOfFiniteType.isLocallyNoetherian snd
    have := IsRegular.of_smooth snd
    exact isReduced_of_isReduced_stalk _

end AlgebraicGeometry
