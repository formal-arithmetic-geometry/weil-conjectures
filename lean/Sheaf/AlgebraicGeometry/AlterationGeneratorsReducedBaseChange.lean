/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Reduced flat base change of alteration objects, products and generators

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II 1.1.5,
1.2.3 (fourth bullet), 1.2.5--1.2.8, 2.1.1 and 2.3.4, printed pp. 23--28
(blueprint: lem-per-alteration-generators-reduced-base-change).

The equation after forgetting to the over category specifies ordinary scheme base change
on objects and morphisms. Universal cones are taken in `Alt`, whose products are the
reduced dominant parts of ordinary products. The closed-immersion and exact-image clause
makes this distinction explicit. No regularity or normal crossings is assumed or concluded.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- Reduced flat base change preserves alteration objects, categorical products and both
classes of generators. Source: ILO II 1.1.5, 1.2.3--1.2.8, 2.1.1 and 2.3.4, pp. 23--28
(blueprint: lem-per-alteration-generators-reduced-base-change).

Proof:
1. Finite type is stable under ordinary scheme base change. A flat morphism is generalizing,
   and maximal dominance is stable under flat base change (II 1.1.5). The generically finite
   condition is preserved by tensoring the finite generic residue algebras. The fibre
   hypothesis is geometric reducedness; flat ascent of reducedness from each reduced object
   shows that its ordinary base change is reduced (II 1.2.3, fourth bullet). It is therefore
   an object of `Alt S'`. Restrict the ordinary over-category pullback functor; the resulting
   functor has exactly the asserted underlying objects and maps.
2. The identity of a reduced base is terminal (II 1.2.3, first bullet). Its ordinary pullback
   is the identity of the new base up to the canonical projection isomorphism, so terminal
   objects are preserved.
3. For a cospan, form its ordinary product and retain the reduced union of the components
   dominating a component of the base (II 1.2.5). The coreflection into maximally dominant
   reduced schemes gives the universal cone (II 1.2.6). Its map into the ordinary product
   is a closed immersion with exactly the stated image. Every universal cone is uniquely
   isomorphic to this one, compatibly with both projections. Flat base change commutes
   with this dominant part: the inverse image of the generic dense locus stays dense by
   maximal dominance, and formation of its closure commutes with flat base change.
   Reduced base change leaves its reduced structure reduced by step 1. Ordinary products
   commute with base change, so the resulting cone is again universal in `Alt S'`.
4. An etale generator remains etale after ordinary base change. Given a point of the new
   target, choose a good prime-to-ell residue lift over its image. Tensor its finite residue
   extension with the new residue field. The finite algebra has a residue factor of degree
   prime to ell (II 1.2.7): split off the purely inseparable part, whose degree is a power
   of the characteristic, and use the sum of degrees for the separable part. This gives
   a good lift of the new point, proving the decomposed-family assertion (II 2.1.1).
5. Properness and surjectivity are stable under ordinary base change. At the generic points,
   use maximal dominance from step 1 and the same finite-residue tensor argument of
   II 1.2.7 to preserve maximal prime-to-ell finiteness. Thus the second generating kind
   is preserved as well. These are the generator calculations underlying II 2.3.4. -/
theorem alteration_generators_reduced_baseChange
    {S S' : Scheme.{u}} [IsReduced S] [IsReduced S']
    [IsNoetherian S] [IsNoetherian S'] (h : S' ⟶ S) [Flat h]
    (hred : ∀ (s : S) (L : Type u) [Field L]
      [Algebra (S.residueField s) L] [Module.Finite (S.residueField s) L],
      IsReduced (pullback (h.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)))))
    (ell : ℕ) [Fact ell.Prime] :
    ∃ F : Alt S ⥤ Alt S',
      F ⋙ (ObjectProperty.ι _ : Alt S' ⥤ Over S') =
        (ObjectProperty.ι _ : Alt S ⥤ Over S) ⋙ Over.pullback h ∧
      PreservesLimitsOfShape (Discrete PEmpty.{1}) F ∧
      (∀ (T X Y P : Alt S) (f : X ⟶ T) (g : Y ⟶ T)
        (p : P ⟶ X) (q : P ⟶ Y), IsPullback p q f g →
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g) ∧
          ∃ j : P.obj.left ⟶ pullback f.hom.left g.hom.left,
            IsClosedImmersion j ∧
            j ≫ pullback.fst f.hom.left g.hom.left = p.hom.left ∧
            j ≫ pullback.snd f.hom.left g.hom.left = q.hom.left ∧
            Set.range j = {z | ∃ c ∈ irreducibleComponents
              (pullback f.hom.left g.hom.left : Scheme.{u}), z ∈ c ∧
              closure ((pullback.fst f.hom.left g.hom.left ≫ X.obj.hom) '' c) ∈
                irreducibleComponents S}) ∧
      (∀ (T : Alt S) (I : Type w) (U : I → Alt S) (f : ∀ i, U i ⟶ T),
        IsPrimeToEllDecomposedEtaleFamily ell U f →
          IsPrimeToEllDecomposedEtaleFamily ell (fun i ↦ F.obj (U i))
            (fun i ↦ F.map (f i))) ∧
      (∀ (T U : Alt S) (f : U ⟶ T),
        IsProper f.hom.left → Surjective f.hom.left →
        IsMaximallyPrimeToEllFinite ell f.hom.left →
          IsProper (F.map f).hom.left ∧ Surjective (F.map f).hom.left ∧
            IsMaximallyPrimeToEllFinite ell (F.map f).hom.left) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
