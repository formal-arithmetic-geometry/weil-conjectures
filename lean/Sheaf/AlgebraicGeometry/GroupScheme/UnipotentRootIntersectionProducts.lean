/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Data.List.OfFn
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.Connected.Basic

/-! # Scheme intersections of Borels with a common torus

Source: Milne, Algebraic Groups (2017), 21.66--21.69, pp.444--446,
21.77, formula (136), and 21.79(a), pp.448--449; 21.84, p.451.
(blueprint: lem-sfb-unipotent-root-intersection-products)

Intersections are fibre products of the underlying F-schemes, not reduced
subschemes or intersections of rational points. Ordered multiplication is pinned
by its composite with the closed inclusion into G. The supplied root enumeration
lists exactly the common positive character weights, in any order.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Common-torus Borel intersections are smooth connected root products.
The radical hypotheses are precisely the maximality characterization in
`reductive_borel_pair_structure`. The root factors have precisely the tangent
and normalization characterization in `reductive_root_subgroup_parametrizations`.
Equality of the two radical intersections is an isomorphism over V, hence equality
as closed subobjects. The two multiplication maps are fixed as maps into G.
The final clause records smoothness and connectedness after algebraically closed
extension; all displayed isomorphisms and their defining equalities also base
change by applying `Over.pullback` (which preserves products and pullbacks).
The empty product is the terminal F-scheme, and its Borel intersection is T.

Source: Milne, 21.66--21.69, pp.444--446, 21.77, formula (136), and 21.79(a),
pp.448--449, with opposite Borels in 21.84.
(blueprint: lem-sfb-unipotent-root-intersection-products)

Proof plan, following the eight steps of the DAG node:
1. Use lem-sfb-regular-cocharacter-borel-description to write B' = P(lambda).
   Regularity makes every root pairing nonzero. Its Lie formula and
   lem-sfb-reductive-borel-pair-structure identify the common positive roots
   with the positive lambda weights among the positive roots of B.
2. Extend the given ordering by the other positive roots. The equivariant
   multiplication isomorphism of lem-sfb-borel-root-product-coordinates and
   the parametrizations of lem-sfb-reductive-root-subgroup-parametrizations
   identify V with affine space, with lambda acting as t^n_alpha on coordinates.
3. An extending orbit of a point of V factors through V: for its closed ideal J
   in the affine coordinate algebra of G, every image of j in J vanishes in
   A[t,t^-1]. The injection A[t] into A[t,t^-1], valid even for nonreduced A,
   makes it vanish already in A[t]. This uses def-weil-closed-immersion.
4. Laurent coefficient comparison forces exactly the negative-weight coordinates
   to vanish. For the ideal I of V intersect B' and the coordinate ideal K,
   the universal point over R/K gives I contained in K, and the universal point
   over R/I gives the reverse inclusion. Thus this is equality of schemes.
5. Apply the Borel root coordinates also to B'. Every common root subgroup
   lies in V', so the product factors through V intersect V'. Conversely
   V' is contained in B'. These inclusions are inverse over V, giving e.
6. Restrict V times T isomorphic to B from the Borel-pair structure theorem.
   Since T is contained in B', vt belongs to B' exactly when v does. The
   inverse is b mapped to (b p(b)^-1,p(b)). Substitute steps 4 and 5 to obtain
   the second ordered multiplication map with its stated composite into G.
7. Root parametrizations identify the intersections with affine space or its
   product with a split torus. Polynomial/Laurent coordinate rings are smooth:
   lift variables and units across square-zero quotients. They are domains,
   whose zero primes lie in every nonempty basic open, hence connected.
   These are def-sc-gm-ga, def-sbc-smooth-morphisms and
   def-weil-connected-scheme applied to these explicit coordinate algebras.
8. The equations, ordered multiplication and inverse maps extend by scalars.
   Fibre products commute with this extension, and the coordinate rings replace
   F by E, proving the last clause. When r = 0 the coordinate product is
   Spec F, both radical intersections are trivial and B intersect B' is T.
   This includes torus groups and the trivial group, in every characteristic. -/
theorem unipotent_root_intersection_products
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B B' V V' : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F n))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (iB' : B' ⟶ G) (hB' : IsBorelGroupScheme iB'.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    (j' : T ⟶ B') (hj' : j' ≫ iB' = iT)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hQproper : IsProper Q.hom)
    (hQfinite : LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (iV : V ⟶ B) (iV' : V' ⟶ B')
    (hV : IsClosedSubgroupScheme iV.hom.hom ∧ IsNormalSubgroupScheme iV.hom.hom ∧
      Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧ SolvableGroupStructure.IsUnipotent V ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ V, f ≫ iV = iN)
    (hV' : IsClosedSubgroupScheme iV'.hom.hom ∧ IsNormalSubgroupScheme iV'.hom.hom ∧
      Smooth V'.X.hom ∧ ConnectedSpace V'.X.left ∧ SolvableGroupStructure.IsUnipotent V' ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B'),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ V', f ≫ iV' = iN)
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X) (aB' : ModObj T.X B'.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (haB' : aB'.smul = (j'.hom.hom ⊗ₘ 𝟙 B'.X) ≫ GrpObj.conj B'.X)
    (r : ℕ) (α : Fin r → (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hαinj : Function.Injective α)
    (hαpos : ∀ χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      (∃ i : Fin r, α i = χ) ↔ χ.hom.hom ≠ 1 ∧
        @TorusCharacterTangent.weightSpace F _ T G aG χ ≠ ⊥ ∧
        @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥ ∧
        @TorusCharacterTangent.weightSpace F _ T B' aB' χ ≠ ⊥)
    (R : Fin r → Grp (Over (Spec (.of F)))) (iR : ∀ i : Fin r, R i ⟶ G)
    (hR : ∀ i : Fin r,
      IsClosedSubgroupScheme (iR i).hom.hom ∧ Smooth (R i).X.hom ∧
      ConnectedSpace (R i).X.left ∧ @TorusCharacterTangent.IsStable F _ T G aG _ (iR i) ∧
      (GrpObj.differential (iR i).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG (α i)) :
    Smooth (pullback iB.hom.hom iB'.hom.hom).hom ∧
    ConnectedSpace (pullback iB.hom.hom iB'.hom.hom).left ∧
    Smooth (pullback (iV ≫ iB).hom.hom iB'.hom.hom).hom ∧
    ConnectedSpace (pullback (iV ≫ iB).hom.hom iB'.hom.hom).left ∧
    Smooth (pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom).hom ∧
    ConnectedSpace (pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom).left ∧
    (∃ e : pullback (iV ≫ iB).hom.hom iB'.hom.hom ≅
        pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom,
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _) ∧
    (∃ mV : (∏ᶜ fun i : Fin r ↦ (R i).X) ⟶
        pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom,
      IsIso mV ∧ mV ≫ pullback.fst _ _ ≫ (iV ≫ iB).hom.hom =
        (List.ofFn (fun i : Fin r ↦
          Pi.π (fun l : Fin r ↦ (R l).X) i ≫ (iR i).hom.hom)).prod) ∧
    (∃ mB : (∏ᶜ fun i : Fin r ↦ (R i).X) ⊗ T.X ⟶
        pullback iB.hom.hom iB'.hom.hom,
      IsIso mB ∧ mB ≫ pullback.fst _ _ ≫ iB.hom.hom =
        (fst (∏ᶜ fun i : Fin r ↦ (R i).X) T.X ≫
          (List.ofFn (fun i : Fin r ↦
            Pi.π (fun l : Fin r ↦ (R l).X) i ≫ (iR i).hom.hom)).prod) *
        (snd (∏ᶜ fun i : Fin r ↦ (R i).X) T.X ≫ iT.hom.hom)) ∧
    (r = 0 → Nonempty ((∏ᶜ fun i : Fin r ↦ (R i).X) ≅ Over.mk (𝟙 (Spec (.of F)))) ∧
      ∃ eT : T.X ≅ pullback iB.hom.hom iB'.hom.hom,
        eT.hom ≫ pullback.fst _ _ ≫ iB.hom.hom = iT.hom.hom) ∧
    ∀ (E : Type u) [Field E] [Algebra F E] [IsAlgClosed E],
      Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback iB.hom.hom iB'.hom.hom)).hom ∧
      ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback iB.hom.hom iB'.hom.hom)).left ∧
      Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback (iV ≫ iB).hom.hom iB'.hom.hom)).hom ∧
      ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback (iV ≫ iB).hom.hom iB'.hom.hom)).left ∧
      Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom)).hom ∧
      ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
        (pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom)).left := by
  sorry

end AlgebraicGeometry
