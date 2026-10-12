/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.Algebra.Homology.TensorKunneth
import Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechCupPullbackCompat
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # The isomorphism clause of the quasi-coherent Kunneth theorem

(blueprint: lem-sc-picard-kunneth-qcoh-iso-exists).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The isomorphism clause of the quasi-coherent Kunneth theorem.
Source: Stacks Project, Varieties, Tag 0BED, Lemma varieties-lemma-kunneth.
(blueprint: lem-sc-picard-kunneth-qcoh-iso-exists).

Proof:
1. Choose finite affine covers U of X and V of Y. Their product cover W by U_i x_{Spec(k)} V_j
is finite and affine: products of affine opens are affine by
lem-weil-pbc-fibre-product-affine-spectra. By lem-sc-picard-affine-diagonal-intersections the
intersection of two affine opens of X (resp. Y) is affine, so by induction on the number of
members every finite intersection U_{i_0..i_p} (resp. V_{j_0..j_p}) is affine, and
W_{(i_0j_0)..(i_pj_p)} = U_{i_0..i_p} x_k V_{j_0..j_p} is affine. Refinement pullbacks (W
refines pr_1^{-1}U and pr_2^{-1}V) and the signed Cech cup construction give the map
Tot(Cech(U,F) tensor_k Cech(V,G)) \to Cech(W,pr_1^*F tensor pr_2^*G).

2. The field-linear algebra Kunneth lemma lem-sc-qcoh-cech-total-tensor-iso identifies the
direct sum of tensor products of the two Cech cohomologies with the cohomology of the total
tensor complex, by the map [a] tensor [b] \mapsto [a tensor b].

3. The Cech comparison theorem lem-sc-cech-comparison-map-iso-affine, together with its
naturality, identifies those Cech cohomology groups with H^p(X,F), H^q(Y,G), and H^n(X x_k
Y,pr_1^*F tensor pr_2^*G). The Cech cup compatibility lemma identifies the resulting map with
pullback along the projections followed by the sheaf cup product.

4. For a short exact sequence 0 \to F \to F' \to F'' \to 0 of quasi-coherent modules, sections
on every affine intersection U_{i_0..i_p} are exact by pqf-lem-affine-vanishing (Tag 01XB), and
tensoring the resulting short exact sequence of k-vector spaces with any k-vector space is exact
(k is a field). On the affine W_{(i_0j_0)..(i_pj_p)} = U_{i_0..i_p} x_k V_{j_0..j_p} the
sections of pr_1^*F tensor pr_2^*G are F(U_{i_0..i_p}) tensor_k G(V_{j_0..j_p}), naturally in F
and G, by lem-weil-pbc-module-pullback-affine-sections (sections of a pullback on affines are
the base change of the sections), lem-weil-pbc-fibre-product-affine-spectra and
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections. Thus the Cech complexes and their
tensor-total complexes form short exact sequences of complexes, and the map of Step 1 is a map
of short exact sequences. The long exact cohomology sequences and the five lemma give a
2-out-of-3 principle: if the map of Step 1 is a quasi-isomorphism for two of F, F', F'' (with G
fixed), it is one for the third; by Steps 2 and 3 this is the Kunneth assertion. The same holds
in the variable G.

5. Use finite quasi-coherent cohomological dimension to assign F the least nonnegative bound d
such that H^p(X,F)=0 for p>d (thus the zero module also has bound 0). If d>0, embed F in an
acyclic quasi-coherent F' and let F'' be its cokernel. The long exact sequence gives H^p(X,F'')
= H^{p+1}(X,F) for p>0, so F'' has bound at most d-1. First prove the comparison for acyclic F
and all G by the analogous induction on the bound for G, whose base has both modules acyclic.
Then induct on the bound for F with arbitrary fixed G, using the two-out-of-three principle and
the already proved acyclic case. The d=0 case includes modules whose entire cohomology vanishes.

6. Degree-zero case: H^p(X,F)=0 and H^q(Y,G)=0 for p,q>0. Put H = pr_1^*F tensor pr_2^*G. For
every affine open V of Y, pr_2^{-1}(V) = X x_k V, and the cover U_V = (U_i x_k V) of X x_k V has
affine finite intersections U_{i_0..i_p} x_k V by Step 1 and
lem-weil-pbc-fibre-product-affine-spectra. By lem-sc-cech-comparison-map-iso-affine, H^q(X x_k
V, H) is the cohomology of Cech(U_V,H), and as in Step 4
(lem-weil-pbc-module-pullback-affine-sections,
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections) Cech(U_V,H) = Cech(U,F) tensor_k
G(V); tensoring over the field k is exact, so H^q(X x_k V,H) = H^q(Cech(U,F)) tensor_k G(V) =
H^q(X,F) tensor_k G(V) (lem-sc-cech-comparison-map-iso-affine on X), which is 0 for q>0 and
Gamma(X,F) tensor_k G(V) for q=0. By lem-weil-pbc-higher-direct-image-presheaf, R^q pr_{2,*}H is
the sheaf associated to V \mapsto H^q(X x_k V,H), with stalks the colimits of these groups over
neighbourhoods of a point; the affine opens are cofinal among these, so R^q pr_{2,*}H = 0 for
q>0. For q=0, choose a k-basis (e_s) of Gamma(X,F); the map from the direct sum of copies of G
indexed by s to pr_{2,*}H, sending t in G(V) at index s to pr_1^*e_s tensor pr_2^*t, is on every
affine V the map from the direct sum of the G(V) (lem-weil-pbc-qcqs-cohomology-direct-sum with
p=0 on the affine, hence quasi-compact and quasi-separated, V) to Gamma(X,F) tensor_k G(V), an
isomorphism; isomorphisms on a basis of opens give isomorphisms on stalks, so pr_{2,*}H =
Gamma(X,F) tensor_k G.

7. The diagonal of Y is affine, hence quasi-compact, so Y is quasi-compact and quasi-separated;
by lem-weil-pbc-qcqs-cohomology-direct-sum, H^p(Y, Gamma(X,F) tensor_k G) is the direct sum of
copies of H^p(Y,G), which is 0 for p>0, and its global sections are Gamma(X,F) tensor_k
Gamma(Y,G). With Step 6, H^p(Y,R^q pr_{2,*}H) = 0 for all q >= 0 and p > 0, so by
lem-pc-leray-degenerate-sections (2) the edge map H^q(X x_k Y,H) \to Gamma(Y,R^q pr_{2,*}H) is
an isomorphism for every q: the product cohomology is zero above degree zero and in degree zero
is Gamma(X,F) tensor_k Gamma(Y,G). Both sides of the Kunneth map are thus concentrated in degree
zero, where the canonical map is s tensor t \mapsto pr_1^*s . pr_2^*t
(lem-sc-picard-cech-cup-pullback-compat in degree 0), which is the isomorphism just obtained.
With Steps 4 and 5 this proves the Kunneth isomorphism.

Extend the nonnegative Cech complexes by zero to integer degrees before applying
tensor_kunneth. The negative-degree cohomologies vanish, so negative-index summands
contribute zero; reindex the remaining summands by p + q = n in natural numbers.
The scalar Ext comparison identifies resolution classes with the recorded derived
O-module cohomology. Restriction of scalars preserves the section pairing and the
normalized pullback units, so the Cech cup and pullback formulas compute externalCup.
Thus the pure-tensor equation holds for every cohomology class, since every class has
a cocycle representative. The equivalence is determined by these generators.
The canonical maps are k-linear. In degree zero this is the section tensor map;
zero modules and empty schemes give zero groups on both sides.
-/
theorem picard_kunneth_iso_exists (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal f)] [IsAffineHom (Limits.pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∀ n : ℕ, ∃ e :
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
              (externalCup f g F G i.val.1 i.val.2 a b) := by
  sorry
end
end AlgebraicGeometry.Scheme.Modules
