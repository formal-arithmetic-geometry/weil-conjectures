/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module

/-! # Kunneth for quasi-coherent cohomology over a field

Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`
(blueprint: lem-sc-picard-kunneth-qcoh).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical cup-product map is an isomorphism, functorial for pullback over k.
The equivalence goes from the direct sum to product cohomology; its value on every pure
summand tensor specifies the canonical map uniquely. The second clause is its pullback
compatibility on generators, with the canonical coefficient identification.
Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`
(blueprint: lem-sc-picard-kunneth-qcoh).

Proof, following the node's eight steps:
1. Choose finite affine covers U of X and V of Y. Their product cover W by U_i x_{Spec(k)} V_j is
finite and affine: products of affine opens are affine by lem-weil-pbc-fibre-product-affine-
spectra. By lem-sc-picard-affine-diagonal-intersections the intersection of two affine opens of X
(resp. Y) is affine, so by induction on the number of members every finite intersection
U_{i_0..i_p} (resp. V_{j_0..j_p}) is affine, and W_{(i_0j_0)..(i_pj_p)} = U_{i_0..i_p} x_k
V_{j_0..j_p} is affine. Refinement pullbacks (W refines pr_1^{-1}U and pr_2^{-1}V) and the signed
Cech cup construction give the map Tot(Cech(U,F) tensor_k Cech(V,G)) \to Cech(W,pr_1^*F tensor
pr_2^*G).

2. The field-linear algebra Kunneth lemma lem-sc-qcoh-cech-total-tensor-iso identifies the direct
sum of tensor products of the two Cech cohomologies with the cohomology of the total tensor
complex, by the map [a] tensor [b] \mapsto [a tensor b].

3. The Cech comparison theorem lem-sc-cech-comparison-map-iso-affine, together with its
naturality, identifies those Cech cohomology groups with H^p(X,F), H^q(Y,G), and H^n(X x_k
Y,pr_1^*F tensor pr_2^*G). The Cech cup compatibility lemma identifies the resulting map with
pullback along the projections followed by the sheaf cup product.

4. For a short exact sequence 0 \to F \to F' \to F'' \to 0 of quasi-coherent modules, sections on
every affine intersection U_{i_0..i_p} are exact by pqf-lem-affine-vanishing (Tag 01XB), and
tensoring the resulting short exact sequence of k-vector spaces with any k-vector space is exact
(k is a field). On the affine W_{(i_0j_0)..(i_pj_p)} = U_{i_0..i_p} x_k V_{j_0..j_p} the sections
of pr_1^*F tensor pr_2^*G are F(U_{i_0..i_p}) tensor_k G(V_{j_0..j_p}), naturally in F and G, by
lem-weil-pbc-module-pullback-affine-sections (sections of a pullback on affines are the base
change of the sections), lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-quasi-
coherent-tensor-product-affine-sections. Thus the Cech complexes and their tensor-total complexes
form short exact sequences of complexes, and the map of Step 1 is a map of short exact sequences.
The long exact cohomology sequences and the five lemma give a 2-out-of-3 principle: if the map of
Step 1 is a quasi-isomorphism for two of F, F', F'' (with G fixed), it is one for the third; by
Steps 2 and 3 this is the Kunneth assertion. The same holds in the variable G.

5. Finite cohomological dimension on X and the universal-delta-functor embedding lemma give an
induction on d(F)=max{d | H^d(X,F) != 0}: embed F into F' with higher cohomology zero, let F'' be
the cokernel, and use the 2-out-of-3 principle because d(F'')<d(F). Repeating in Y reduces to the
case where F and G have cohomology only in degree zero.

6. Degree-zero case: H^p(X,F)=0 and H^q(Y,G)=0 for p,q>0. Put H = pr_1^*F tensor pr_2^*G. For
every affine open V of Y, pr_2^{-1}(V) = X x_k V, and the cover U_V = (U_i x_k V) of X x_k V has
affine finite intersections U_{i_0..i_p} x_k V by Step 1 and lem-weil-pbc-fibre-product-affine-
spectra. By lem-sc-cech-comparison-map-iso-affine, H^q(X x_k V, H) is the cohomology of
Cech(U_V,H), and as in Step 4 (lem-weil-pbc-module-pullback-affine-sections, lem-weil-pbc-quasi-
coherent-tensor-product-affine-sections) Cech(U_V,H) = Cech(U,F) tensor_k G(V); tensoring over the
field k is exact, so H^q(X x_k V,H) = H^q(Cech(U,F)) tensor_k G(V) = H^q(X,F) tensor_k G(V) (lem-
sc-cech-comparison-map-iso-affine on X), which is 0 for q>0 and Gamma(X,F) tensor_k G(V) for q=0.
By lem-weil-pbc-higher-direct-image-presheaf, R^q pr_{2,*}H is the sheaf associated to V \mapsto
H^q(X x_k V,H), with stalks the colimits of these groups over neighbourhoods of a point; the
affine opens are cofinal among these, so R^q pr_{2,*}H = 0 for q>0. For q=0, choose a k-basis
(e_s) of Gamma(X,F); the map from the direct sum of copies of G indexed by s to pr_{2,*}H, sending
t in G(V) at index s to pr_1^*e_s tensor pr_2^*t, is on every affine V the map from the direct sum
of the G(V) (lem-weil-pbc-qcqs-cohomology-direct-sum with p=0 on the affine, hence quasi-compact
and quasi-separated, V) to Gamma(X,F) tensor_k G(V), an isomorphism; isomorphisms on a basis of
opens give isomorphisms on stalks, so pr_{2,*}H = Gamma(X,F) tensor_k G.

7. The diagonal of Y is affine, hence quasi-compact, so Y is quasi-compact and quasi-separated; by
lem-weil-pbc-qcqs-cohomology-direct-sum, H^p(Y, Gamma(X,F) tensor_k G) is the direct sum of copies
of H^p(Y,G), which is 0 for p>0, and its global sections are Gamma(X,F) tensor_k Gamma(Y,G). With
Step 6, H^p(Y,R^q pr_{2,*}H) = 0 for all q >= 0 and p > 0, so by lem-pc-leray-degenerate-sections
(2) the edge map H^q(X x_k Y,H) \to Gamma(Y,R^q pr_{2,*}H) is an isomorphism for every q: the
product cohomology is zero above degree zero and in degree zero is Gamma(X,F) tensor_k Gamma(Y,G).
Both sides of the Kunneth map are thus concentrated in degree zero, where the canonical map is s
tensor t \mapsto pr_1^*s . pr_2^*t (lem-sc-picard-cech-cup-pullback-compat in degree 0), which is
the isomorphism just obtained. With Steps 4 and 5 this proves the Kunneth isomorphism.

8. Functoriality. Let u:X'\to X and v:Y'\to Y be morphisms of schemes over k and w = u x_k v : X'
x_k Y' \to X x_k Y, so that pr_1 o w = u o pr_1' and pr_2 o w = v o pr_2' (def-pc-fibre-product);
identify w^*(pr_1^*F tensor pr_2^*G) with pr_1'^*u^*F tensor pr_2'^*v^*G by lem-pc-module-
pullback-identity-composition and lem-weil-pbc-module-pullback-tensor. The claim is w^*(pr_1^*a
cup pr_2^*b) = pr_1'^*u^*a cup pr_2'^*v^*b for a in H^p(X,F), b in H^q(Y,G). With U, V, W as in
Step 1, a = c_U(alpha) and b = c_V(beta) for Cech cocycles alpha, beta (lem-sc-cech-comparison-
map-iso-affine). Use the covers u^{-1}U, v^{-1}V and W' = w^{-1}W, which refines pr_1'^{-1}u^{-1}U
and pr_2'^{-1}v^{-1}V by (i,j) \mapsto i, j since w^{-1}(U_i x V_j) is contained in
w^{-1}pr_1^{-1}U_i = pr_1'^{-1}u^{-1}U_i. By lem-sc-picard-cech-cup-pullback-compat (a), each
pullback in the claim is computed by the refinement cochain map, whose components are pullbacks of
sections; by lem-pc-module-pullback-identity-composition the cochains obtained from alpha along w
after pr_1 and along pr_1' after u coincide (both are pullback of the components along pr_1 o w =
u o pr_1'), and likewise for beta. By lem-weil-pbc-module-pullback-tensor (w^*(s tensor t) = w^*s
tensor w^*t) the refinement cochain map along w sends the signed Cech cup product of two cochains
to the cup product of their images. By lem-sc-picard-cech-cup-pullback-compat (b) the Cech cup
products induce the sheaf cup products on X x_k Y and on X' x_k Y'. Hence both sides of the claim
are c_{W'} of the same cochain, which proves the functoriality clause.
-/
theorem picard_kunneth_qcoh (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal f)] [IsAffineHom (Limits.pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (∀ n : ℕ, ∃ e :
      (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        scalarCohomology f F i.val.1 ⊗[k] scalarCohomology g G i.val.2) ≃ₗ[k]
          scalarCohomology (Limits.pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n,
      ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : scalarCohomology f F i.val.1) (b : scalarCohomology g G i.val.2),
        e (DirectSum.lof k _
          (fun j : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
            scalarCohomology f F j.val.1 ⊗[k] scalarCohomology g G j.val.2) i
          (a ⊗ₜ[k] b)) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (Limits.pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
              (externalCup f g F G i.val.1 i.val.2 a b)) ∧
    (∀ (X' Y' : Scheme.{w}) (f' : X' ⟶ Spec (CommRingCat.of k))
      (g' : Y' ⟶ Spec (CommRingCat.of k)) (u : X' ⟶ X) (v : Y' ⟶ Y)
      (hu : u ≫ f = f') (hv : v ≫ g = g') (w : Limits.pullback f' g' ⟶ Limits.pullback f g)
      (h₁ : w ≫ Limits.pullback.fst f g = Limits.pullback.fst f' g' ≫ u)
      (h₂ : w ≫ Limits.pullback.snd f g = Limits.pullback.snd f' g' ≫ v)
      (p q : ℕ) (a : scalarCohomology f F p) (b : scalarCohomology g G q),
      scalarCohomologyMap (Limits.pullback.fst f' g' ≫ f')
        (externalCupPullbackIso f g f' g' u v w h₁ h₂ F G).hom (p + q)
        (scalarCohomologyPullback (Limits.pullback.fst f g ≫ f) (Limits.pullback.fst f' g' ≫ f') w
          (by rw [← Category.assoc, h₁, Category.assoc, hu])
          (externalCupCoefficients f g F G) (p + q) (externalCup f g F G p q a b)) =
        externalCup f' g' ((tensorPullback u).obj F) ((tensorPullback v).obj G) p q
          (scalarCohomologyPullback f f' u hu F p a)
          (scalarCohomologyPullback g g' v hv G q b)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
