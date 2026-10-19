/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
/-!
# Reducedness and density for generic restrictions of smooth covers

Source: Stacks Project, Tags 033B and 01UA.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem smooth_algebra_reduced_of_domain (A B : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    _root_.IsReduced B := by
  have : _root_.IsReduced (TensorProduct A (FractionRing A) B) :=
    Algebra.Smooth.isReduced_of_field (FractionRing A) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A (FractionRing A) B)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A (FractionRing A)))

private theorem smooth_source_reduced_of_integral {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsIntegral S] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨U, hU, V, hV, hxV, e, _⟩ := Smooth.exists_isStandardSmooth f x
    have : Nonempty U := ⟨⟨f x, e hxV⟩⟩
    have hsm := f.smooth_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    have : _root_.IsReduced Γ(X, V) := smooth_algebra_reduced_of_domain Γ(S, U) Γ(X, V)
    have : IsReduced V.toScheme := isReduced_of_isOpenImmersion hV.isoSpec.hom
    exact isReduced_of_injective (V.ι.stalkMap ⟨x, hxV⟩).hom
      (asIso (V.ι.stalkMap ⟨x, hxV⟩)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

/-- The generic restriction of an étale cover of a smooth scheme over an integral
base is dominant, and the cover is reduced.

Source: Stacks Project, Tag 033B (smooth algebras over reduced rings),
and Tag 01UA (flat morphisms locally of finite presentation are open).
(blueprint: lem-sbc-finite-etale-generic-fibre-cover-density)

Proof: The composite X → C → S is smooth, hence flat with geometrically reduced
fibres. On affine charts its ring maps are smooth over reduced rings, so the
source rings are reduced by 033B; localizing gives reduced stalks and hence X.
For density take any nonempty open subset of X. The smooth composite maps it
to a nonempty open of S by 01UA, which contains the generic point since S is
integral. A point over that generic point lifts to the generic fibre: the
spectrum of S's generic stalk is the one-point spectrum of its function field,
and the cartesian pullback has a point over every compatible pair of points.
Pasting the two given squares identifies this fibre with Xη. Hence every
nonempty open of X meets the image of ψX. This proves dominance, including
when X is empty, where the empty image is dense. -/
theorem genericFibre_cover_reduced_and_dominant {S C : Scheme.{u}} [IsIntegral S]
    (c : C ⟶ S) [Smooth c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Xη : Scheme.{u}} (πX : X ⟶ C) [Etale πX]
    (πXη : Xη ⟶ Cη) (ψX : Xη ⟶ X)
    (hX : IsPullback ψX πXη πX j) : IsReduced X ∧ IsDominant ψX := by
  have : Smooth (πX ≫ c) := inferInstance
  refine ⟨smooth_source_reduced_of_integral (πX ≫ c), ?_⟩
  have hd : Dense (Set.range (S.fromSpecStalk (genericPoint S))) := by
    have hg : Dense ({genericPoint S} : Set S) := by
      rw [dense_iff_closure_eq]
      exact (genericPoint_spec S).def
    exact hg.mono (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨IsLocalRing.closedPoint _, S.fromSpecStalk_closedPoint⟩)
  have hp := hX.paste_vert hCη.flip
  have : IsDominant (pullback.fst (πX ≫ c) (S.fromSpecStalk (genericPoint S))) := by
    constructor
    change Dense (Set.range (pullback.fst (πX ≫ c)
      (S.fromSpecStalk (genericPoint S))))
    rw [Pullback.range_fst]
    exact hd.preimage (πX ≫ c).isOpenMap
  rw [← hp.isoPullback_hom_fst]
  infer_instance
end AlgebraicGeometry.Scheme
