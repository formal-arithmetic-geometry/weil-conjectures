module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Sheaf.AlgebraicGeometry.FlatMaximalDominanceBaseChange
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-!
# Reduced base change on alteration objects and generators

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, 1.1.5,
1.2.3 (fourth bullet), 1.2.5--1.2.8, 2.1.1 and 2.3.4, printed pp. 23--28
(blueprint: lem-per-alteration-generators-reduced-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- Ordinary base change along a flat map with reduced fibres after all finite residue-field
extensions restricts to alteration categories, preserves their terminal objects and pullbacks,
and preserves both kinds of prime-to-ell generators. The categorical pullback is the reduced
closed union of the components of the ordinary product dominating components of the base.
Source: ILO, Travaux de Gabber, Exposé II, 1.1.5, 1.2.3--1.2.8, 2.1.1 and 2.3.4
(blueprint: lem-per-alteration-generators-reduced-base-change).

Proof plan (the six steps of the node):
1. Finite type and Noetherianity survive base change. Convert the finite-extension fibre
   hypothesis to geometric reducedness using
   `lem-trf-geometric-reducedness-finite-inseparable-test`,
   `lem-weil-pbc-affine-scheme-reduced-iff`,
   `lem-weil-pbc-fibre-product-affine-spectra` and `lem-trf-reduced-scheme-open-cover`.
   Apply `lem-per-flat-geometrically-reduced-pullback`. Maximal dominance follows from
   `lem-per-flat-maximal-dominance-base-change`; finiteness of generic residue fields follows
   from `lem-per-generic-fibre-finiteness-criterion` and scalar extension of finite algebras.
2. The scheme pullback universal property (`def-pc-fibre-product`) gives the maps and the
   functor laws, and identifies the pullback of the identity of S with the identity of S'.
3. For X → Z ← Y, use `lem-per-alteration-cover-calculus` and
   `lem-per-dominant-part-coreflection` to form the reduced dominant part P of C = X ×_Z Y.
   After base change P' is reduced by step 1. Its support is the dominant part of C': one
   inclusion uses maximal dominance, and the other uses that a generic point of S' maps to
   a generic point of S and that the generic fibres of C are finite. The finite-type facts
   use `lem-sfb-finite-type-composition-base-change`,
   `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-proper-fp-permanence`.
   Uniqueness in `lem-weil-pbc-reduced-induced-closed-subscheme` identifies the two reduced
   closed subschemes.
4. Identify C' with X' ×_{Z'} Y' by the scheme universal property. The product description
   of `lem-per-alteration-cover-calculus` proves universality; transport along the unique
   isomorphism of universal cones handles every original universal cone.
5. Étaleness survives by `lem-weil-pbc-etale-covering-base-change`. For each new target
   point, apply `lem-per-prime-to-ell-residue-base-change` to an old prime-to-ell lift.
   `lem-weil-pbc-fibre-product-points` and `lem-weil-pbc-fibre-product-point-residue-field`
   identify the residue field of the resulting point in the ordinary product.
6. Properness and surjectivity survive by `lem-weil-pbc-proper-base-change` and
   `lem-weil-pbc-surjective-base-change`. Flatness of the projection
   (`lem-weil-pbc-flat-morphism-base-change`) sends generic points to generic points.
   Use the same residue-base-change lemma to obtain a prime-to-ell lift. It is generic
   because it lies in a finite generic fibre (the generic-fibre finiteness criterion).
   Finiteness of all other generic residue extensions follows through their intermediate
   residue fields over the base. These are the two maximal prime-to-ell finiteness clauses.
-/
theorem alteration_generators_reduced_baseChange
    {S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S'] [IsReduced S] [IsReduced S']
    (h : S' ⟶ S) [Flat h]
    (hred : ∀ (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]
      [Module.Finite (S.residueField s) K],
      IsReduced (pullback h
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
          S.fromSpecResidueField s)))
    (ell : ℕ) [Fact ell.Prime] :
    ∃ F : Alt S ⥤ Alt S',
      F ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ Over.pullback h ∧
      (∀ T : Alt S, IsTerminal T → Nonempty (IsTerminal (F.obj T))) ∧
      (∀ (P X Y Z : Alt S) (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z),
        IsPullback p q f g → IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) ∧
      (∀ (X Y Z : Alt S) (f : X ⟶ Z) (g : Y ⟶ Z),
        ∃ (P : Alt S) (p : P ⟶ X) (q : P ⟶ Y), IsPullback p q f g ∧
          ∃ j : P.obj.left ⟶ pullback f.hom.left g.hom.left,
            IsClosedImmersion j ∧
            j ≫ pullback.fst f.hom.left g.hom.left = p.hom.left ∧
            j ≫ pullback.snd f.hom.left g.hom.left = q.hom.left ∧
            Set.range j = ⋃₀ {C | C ∈ irreducibleComponents
                ↥(pullback f.hom.left g.hom.left) ∧
              ∃ η : ↥(pullback f.hom.left g.hom.left), IsGenericPoint η C ∧
                closure ({(pullback.fst f.hom.left g.hom.left ≫ X.obj.hom) η} : Set S)
                  ∈ irreducibleComponents S}) ∧
      (∀ {I : Type w} {T : Alt S} (U : I → Alt S) (f : ∀ i, U i ⟶ T),
        IsPrimeToEllDecomposedEtaleFamily ell U f →
          IsPrimeToEllDecomposedEtaleFamily ell (fun i ↦ F.obj (U i))
            (fun i ↦ F.map (f i))) ∧
      (∀ (U T : Alt S) (f : U ⟶ T),
        IsProper f.hom.left → Surjective f.hom.left →
          IsMaximallyPrimeToEllFinite ell f.hom.left →
            IsProper (F.map f).hom.left ∧ Surjective (F.map f).hom.left ∧
              IsMaximallyPrimeToEllFinite ell (F.map f).hom.left) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
