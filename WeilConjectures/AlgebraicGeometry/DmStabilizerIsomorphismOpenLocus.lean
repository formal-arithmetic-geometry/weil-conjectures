/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties
public import WeilConjectures.AlgebraicGeometry.OpenModuliSubstack
public import WeilConjectures.AlgebraicGeometry.FiniteStackSchemeTests
public import WeilConjectures.AlgebraicGeometry.ModuliInertia
public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The open stabilizer-isomorphism locus

Source: Stacks Project, stacks-morphisms.tex, Tag 0DUA,
lemma-stabilizer-preserving-unramified, specialized to representable etale maps
and finite target inertia (blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus).

The inertia construction retains vertical automorphisms and conjugating arrows.
The comparison lands in the actual 2-fibre product, not an arbitrary equivalent
category. Points, their atlas topology, and open substacks use the existing interfaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A stack map sends an inertia object `(a, alpha)` to `(f(a), f(alpha))`.
Source: Stacks, canonical inertia comparison, Tag 0DUA
(blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus). -/
def moduliInertiaMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : BasedFunctor (moduliInertia F) (moduliInertia G) where
  obj x := ⟨f.obj x.obj, f.toFunctor.mapIso x.automorphism, by
    change (f.toFunctor ⋙ G.p).map x.automorphism.hom =
      𝟙 ((f.toFunctor ⋙ G.p).obj x.obj)
    rw [f.w]
    exact x.vertical⟩
  map a := ⟨f.map a.val, by
    simpa only [Functor.mapIso_hom, Functor.map_comp] using congrArg f.map a.property⟩
  map_id x := Subtype.ext (f.map_id x.obj)
  map_comp a b := Subtype.ext (f.map_comp a.val b.val)
  w := by
    change moduliInertiaForget F ⋙ f.toFunctor ⋙ G.p = _
    rw [f.w]
    rfl

/-- The canonical comparison `I_F -> F ×_G I_G` has identity comparison on objects.
Source: Stacks, Tag 0DUA, remark-get-property-auts-from-diagonal
(blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus). -/
def moduliInertiaComparison {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) :
    BasedFunctor (moduliInertia F) (moduliTwoFiberProduct f (moduliInertiaProjection G)) where
  obj x := ⟨⟨x.obj, (moduliInertiaMap f).obj x, 𝟙 (f.obj x.obj)⟩,
    inferInstance, inferInstance⟩
  map a := ObjectProperty.homMk
    ⟨a.val, (moduliInertiaMap f).map a, by
      change f.map a.val ≫ 𝟙 _ = 𝟙 _ ≫ f.map a.val
      simp⟩
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact (moduliInertiaMap f).map_id x
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact (moduliInertiaMap f).map_comp a b
  w := rfl

/-- The point class of an object in a field fibre of the given stack.
Source: Stacks, atlas topology and Tag 0DUA
(blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus). -/
def moduliFiberPoint {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    {K : Type u} [Field K] {a : Spec (.of K) ⟶ S}
    (x : Functor.Fiber F.p (Over.mk a)) : ModuliPoints F :=
  Quot.mk _ ⟨x.val, K, inferInstance, ⟨by rw [x.property]; exact Iso.refl _⟩⟩

/-- The locus of points having a geometric representative with isomorphic stabilizers.
For DM stacks over an algebraically closed field the stabilizer spaces are etale;
thus bijectivity on their field points is exactly isomorphism of those group spaces.
The map is the automorphism homomorphism of the actual functor on the fibre.
Source: Stacks, Tag 0DUA and remark-identify-automorphism-groups
(blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus). -/
def moduliStabilizerIsomorphismLocus {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Set (ModuliPoints F) :=
  {p | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (a : Spec (.of Ω) ⟶ S) (x : Functor.Fiber F.p (Over.mk a)),
    moduliFiberPoint x = p ∧
      Function.Bijective ((moduliFiberMap f (Over.mk a)).mapAut (X := x))}

/-- For a representable etale map of DM stacks with finite target inertia, the
stabilizer-isomorphism locus is open, is the point space of an open substack, and
its canonical inertia comparison is an isomorphism of stacks (an equivalence over
schemes). Openness is the closed-complement predicate of the existing atlas topology.
Source: Stacks, Tag 0DUA, lemma-stabilizer-preserving-unramified
(blueprint: lem-sfb-dm-stabilizer-isomorphism-open-locus).

Proof:
1. For `a` over `T`, set `H = Aut(fa)` and `G = Aut(a)`. Finite target inertia
   represents `H` by a finite `T`-scheme. The space `X = F ×_G T` is etale.
   Its identity section and its translate by the universal automorphism over `H`
   pull its diagonal back to the canonical map `G -> H`: the defining equation
   is exactly `f(v) = alpha`. This description is natural on all scheme tests.
2. By lem-sfb-space-unramified-permanence, `X -> T` is unramified. By
   lem-sfb-unramified-space-open-diagonal, this makes `G -> H` an open immersion.
   Neither separatedness nor flatness of the inertia projection is needed.
3. On an etale surjective atlas `U -> F`, the complement `C` of `G` in `H` has
   closed image under the finite map `H -> U`, by
   lem-weil-pbc-finite-closed-map-finite-fibres. The inverse image of the locus is
   `U` minus this image: a nonempty complement has a geometric point after taking
   an algebraic closure of its residue field. The same test proves independence
   of geometric representative, including after common algebraically closed extension.
4. By lem-sfb-stack-topology-open-substacks the atlas test proves openness and
   supplies the strictly full open substack with exactly this point space.
5. Over every scheme mapping to this open substack, the open `G` inside finite `H`
   has empty complement, since a point of that complement would yield a geometric
   point outside the locus. Thus `G -> H` is an isomorphism, even on nonreduced tests.
   Fullness identifies the source automorphisms. Each target inertia object has a
   unique lifted automorphism, naturally in pullback. Conjugation compatibility
   follows from injectivity of the stabilizer map, giving the inverse to the
   displayed canonical comparison. The point-space equality includes every point
   with isomorphic geometric stabilizers. -/
theorem dm_stabilizer_isomorphism_open_locus {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (f : BasedFunctor F G) (hF : IsDeligneMumfordModuliStack F)
    (hG : IsDeligneMumfordModuliStack G) (hf : IsRepresentableByAlgebraicSpaces f)
    (het : IsEtaleModuliMap f)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection G)) :
    ModuliPointIsClosed F (moduliStabilizerIsomorphismLocus f)ᶜ ∧
      ∃ U : OpenModuliSubstack F,
        Set.range (moduliPointMap (fullModuliInclusion F U.property)) =
          moduliStabilizerIsomorphismLocus f ∧
        Functor.IsEquivalence
          (moduliInertiaComparison ((fullModuliInclusion F U.property).comp f)).toFunctor := by
  sorry

end CategoryTheory
