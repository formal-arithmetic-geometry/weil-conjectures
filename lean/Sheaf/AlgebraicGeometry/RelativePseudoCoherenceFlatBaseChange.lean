module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.FlatPullbackTorIndependent
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry

/-! # Flat base change of relative pseudo-coherent complexes

Source: Stacks Project, More on Morphisms, Tag 09UR, lemma-base-change-relative-pseudo-coherent,
flat-base-change specialization (blueprint: lem-sfb-relative-pseudocoherence-flat-base-change).

## Main statements

* `isMPseudoCoherentRelativeTo_of_flatBaseChange` states preservation in a fixed degree.
* `isPseudoCoherentRelativeTo_of_flatBaseChange` states the pseudo-coherent consequence.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Flat base change preserves relative `m`-pseudo-coherence of arbitrary derived objects.
Source: Stacks Project, More on Morphisms, Tag 09UR, lemma-base-change-relative-pseudo-coherent,
flat-base-change specialization (blueprint: lem-sfb-relative-pseudocoherence-flat-base-change).
Proof (the five steps of the node):
1. Choose affine covers V of S and U of their preimages, and closed embeddings
   i : U → affine n-space over V as in def-sfb-relative-pseudo-coherent-complex.
   Cover each g⁻¹(V) by affine W (lem-weil-pbc-affine-opens-basis). The U ×_V W cover
   the corresponding preimages in X ×_S S' by lem-weil-pbc-open-immersion-base-change;
   they are affine with tensor-product rings by lem-weil-pbc-fibre-product-affine-spectra.
2. The base-changed ambient space is affine n-space over W
   (def-nagata-relative-affine-space and def-pc-fibre-product), and i' is closed by
   lem-weil-pbc-closed-immersion-base-change. The map W → V is flat, so its ambient
   base change h is flat by lem-weil-pbc-flat-morphism-base-change. Finite generators
   of the original polynomial presentation remain generators after tensoring.
   On a general affine target open, refine by principal affine opens using
   lem-weil-pbc-spec-localization-away-basic-open and
   lem-weil-pbc-affine-ideals-closed-subscheme; adjoining the inverse of the defining
   element also gives finite generation there. Hence f' is locally of finite type
   (def-weil-finite-type-morphism); Mathlib supplies this as a base-change instance.
3. Use lem-pc-ringed-spaces-derived-pullback-composition to identify the restriction
   of Lq*E with the local derived pullback of E|U. Flatness of h gives stalkwise
   Tor independence by lem-sc-flat-pullback-tor-independent; switch its factors by
   lem-weil-pbc-tor-symmetry. Apply
   lem-sfb-tor-independent-closed-pushforward-comparison to obtain
   Ri'_*(Lq*E restricted to U ×_V W) ≅ Lh*(Ri_*(E|U)). This comparison applies to
   arbitrary unbounded complexes and requires no quasi-coherence of E.
4. Apply lem-sfb-derived-pullback-m-pseudocoherent to Ri_*(E|U). Transport the local
   strictly perfect approximations through the isomorphism of step 3: the induced
   cohomology maps stay isomorphisms above m and surjective in degree m
   (def-sfb-m-pseudo-coherent-complex). The base-changed covers and embeddings now
   witness def-sfb-relative-pseudo-coherent-complex for f' and Lq*E.
5. The all-degree consequence applies steps 1--4 separately to each integer m;
   def-sfb-relative-pseudo-coherent-complex does not require uniform covers in m.
-/
theorem isMPseudoCoherentRelativeTo_of_flatBaseChange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] [Flat g] (m : ℤ)
    (E : schemeDerivedCategory X)
    (hE : IsMPseudoCoherentRelativeTo f m E) :
    IsMPseudoCoherentRelativeTo (pullback.snd f g) m
      ((derivedPullback (pullback.fst f g)).obj E) := by
  sorry

/-- Flat base change preserves relative pseudo-coherence in all degrees.
Source: Stacks Project, More on Morphisms, Tag 09UR, lemma-base-change-relative-pseudo-coherent,
flat-base-change specialization (blueprint: lem-sfb-relative-pseudocoherence-flat-base-change).
Proof: unfold def-sfb-relative-pseudo-coherent-complex to obtain the hypothesis in
each integer degree. Apply `isMPseudoCoherentRelativeTo_of_flatBaseChange` in that degree,
and use the same definition to conclude. The affine covers and embeddings can depend on m.
-/
theorem isPseudoCoherentRelativeTo_of_flatBaseChange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] [Flat g]
    (E : schemeDerivedCategory X)
    (hE : IsPseudoCoherentRelativeTo f E) :
    IsPseudoCoherentRelativeTo (pullback.snd f g)
      ((derivedPullback (pullback.fst f g)).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
