/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Blowup.Gluing
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.Blowup.Affine.Defs

/-!
# Globalizing finite ordinary point-blowup towers

Source: Stacks Project, Resolution of Surfaces, Tag 0BFY, converse construction,
and Tag 0BFX (blueprint: lem-per-local-ordinary-point-blowups-globalize).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Finite ordinary reduced point-blowup towers over the local schemes at distinct closed
points globalize, with all intermediate comparison squares and structural stalk isomorphisms.
Finite opposite ordinal categories encode exactly the arrows of each finite tower. The initial
isomorphisms identify level zero with the specified base, including every zero-length case.
The Cartesian squares express the prescribed base changes, and their commuting squares express
insertion of identity arrows. The restrictions are by the actual structure maps over the base.

Source: Stacks Project, Resolution of Surfaces, Tags 0BFY (converse) and 0BFX
(blueprint: lem-per-local-ordinary-point-blowups-globalize).

Proof plan:
1. Order the pairs $(i,k)$ with $1\leq i\leq r$ and $0\leq k<n_i$ lexicographically. This is a
word of length $N=\sum_i n_i$. At stage $j$ let $a_i(j)$ count the letters with first coordinate
$i$ already used. We construct by induction an integral normal Noetherian $Z_j\to S$, isomorphic
to $U$ over $U$, and isomorphisms $Z_j\times_SS_i\cong T_{i,a_i(j)}$ over $S_i$, compatible with
every preceding arrow. Initially $Z_0=S$, $a_i(0)=0$, and the isomorphisms are the identity base
changes. If the word is empty this already gives the required identity tower.
Uses: def-pc-fibre-product.
2. Here is the localization calculation used at every stage, including the next stage before its
normality is known. For any morphism $f:Z\to S$ put $Z_i=Z\times_SS_i$ with projection $p_i$. On
an affine $V=\operatorname{Spec}A\subset S$ containing $s_i$, write $s_i=\mathfrak p_i$ and
$M=A\setminus\mathfrak p_i$. The canonical local-scheme morphism is
$\operatorname{Spec}A_{\mathfrak p_i}\to V$. If $W=\operatorname{Spec}B\subset f^{-1}(V)$, its
pullback has ring $B\otimes_AA_{\mathfrak p_i}=M^{-1}B$ by the cited localization-base-change
statement. The localization-spectrum embedding identifies this chart with the primes $\mathfrak
q\subset B$ avoiding the image of $M$. These chart identifications agree on restrictions because
they are all induced by $p_i$. Thus $p_i$ identifies $|Z_i|$ with
$f^{-1}(\operatorname{gen}(s_i))$ with its subspace topology. In particular the points over
$s_i$ correspond bijectively, with their fibre subspace topologies.
Uses: lem-weil-pbc-spec-local-ring-canonical-morphism, lem-weil-pbc-localization-base-change,
lem-weil-pbc-localization-spectrum-embedding.
3. For a prime $\mathfrak q$ occurring in the preceding calculation, let $\mathfrak
q'=M^{-1}\mathfrak q$. Every element of $M$ is already a unit in $B_{\mathfrak q}$. Consequently
the maps $B_{\mathfrak q}\to(M^{-1}B)_{\mathfrak q'}$ and $(b/m)/(c/n)\mapsto bn/(mc)$ are
inverse ring homomorphisms: the denominators $m,c$ avoid $\mathfrak q$, and checking their two
composites on fractions gives the identity. Using the affine description of local rings gives
$\mathcal O_{Z,p_i(t)}\cong\mathcal O_{Z_i,t}$, by the actual structural local homomorphism. In
particular $p_i$ is flat: its stalk modules are the base local rings themselves, whose tensor
functor is the identity. For every point of $Z$ over $s_i$ this proves precisely the local-ring
identification required in the item.
Uses: lem-weil-pbc-spec-local-ring-canonical-morphism, lem-weil-pbc-localization-base-change,
def-weil-flat-morphism.
4. Suppose $j<N$ and the next letter is $(i,a_i(j))$. Let $t$ be the prescribed reduced closed
center in $T_{i,a_i(j)}$. Through the induction isomorphism it is a point of $Z_j\times_SS_i$
over $s_i$, hence corresponds to a unique $z\in Z_j$ over $s_i$ by step 2. The point $t$ is
closed in the local fibre, so $z$ is closed in the global fibre. This fibre is a closed subspace
of $Z_j$, being the inverse image of the closed singleton $\{s_i\}$; therefore $z$ is closed in
$Z_j$. Give $\{z\}$ its reduced induced closed subscheme structure. The cited reduced-subscheme
statement gives its quasi-coherent ideal $\mathcal I_z$, equal on every affine chart containing
$z$ to the maximal ideal of $z$, and equal to the unit ideal on charts missing $z$. By the
induction hypothesis $Z_j$ has an affine open cover by spectra of Noetherian rings, so it is
locally Noetherian, and the ring $R$ of every affine open $\operatorname{Spec}R\subseteq Z_j$ is
Noetherian. Hence $\mathcal I_z(\operatorname{Spec}R)$, which is $R$ or the maximal ideal of
$z$, is finitely generated by the definition of a Noetherian ring. Thus $\mathcal I_z$ is a
quasi-coherent ideal whose restriction to every affine open is a finitely generated ideal; in
particular it is of finite type.
Uses: lem-weil-pbc-reduced-induced-closed-subscheme, def-weil-pbc-noetherian-ring, pqf-def-
locnoeth, pqf-lem-affine-open-locnoeth.
5. The center pulls back with its reduced structure, not just its support. For the active $i$,
in the charts of step 2 containing $z$, let $\mathfrak q$ be its maximal ideal. Its pullback
ideal is $M^{-1}\mathfrak q$ and the quotient is $M^{-1}(B/\mathfrak q)=B/\mathfrak q$, since
$M\cap\mathfrak q=\varnothing$ and $B/\mathfrak q$ is a field. Thus it is exactly the reduced
point corresponding to $t$, by uniqueness of the reduced induced structure. For $\ell\ne i$, the
canonical map $S_\ell\to S$ has image the generalizations of $s_\ell$; it misses the distinct
closed point $s_i$. Hence the inverse image of $z$ in $Z_j\times_SS_\ell$ is empty and the
pulled-back ideal is the unit ideal. Explicitly, on any chart where the center is present, the
maximal ideals of $s_i$ and $s_\ell$ in $A$ are distinct, so an element of the former outside
the latter is zero in the point quotient and becomes invertible after localization at $s_\ell$.
The localized quotient is therefore zero. These ideal equalities agree on affine overlaps.
Uses: lem-weil-pbc-localization-base-change, lem-weil-pbc-spec-local-ring-canonical-morphism,
lem-weil-pbc-reduced-induced-closed-subscheme.
6. Define $Z_{j+1}=\operatorname{Bl}_{\mathcal I_z}(Z_j)$ by the global blowup construction. The
projections $Z_j\times_SS_\ell\to Z_j$ are flat by step 3, so the flat-base-change comparison is
an isomorphism. Together with step 5, it identifies the active base change with the prescribed
blowup $T_{i,a_i(j)+1}\to T_{i,a_i(j)}$. On every other local factor the center is empty; the
complement isomorphism identifies its blowup with that factor by its structure map. Compose
these comparisons with the induction isomorphisms and the fibre-product associativity
isomorphisms. Set $a_i(j+1)=a_i(j)+1$ and keep the other counts fixed. All comparison
isomorphisms are over their old factors, so their squares with the new arrows commute; previous
squares remain those of the induction hypothesis.
Uses: def-nagata-global-blowup, thm-nagata-blowup-flat-base-change, thm-nagata-global-blowup-
complement, def-pc-fibre-product.
7. The ideal $\mathcal I_z$ is nonzero. Indeed, if it were zero, on every affine of the gluing
construction its Rees algebra would have zero positive-degree part, since $0^n=0$ for $n>0$. Its
Proj is empty: the standard opens at positive-degree elements are all empty (the only such
element is zero) and they cover Proj. Thus the glued blowup $Z_{j+1}$ would be empty. But its
active base change is $T_{i,a_i(j)+1}$ by step 6, which is nonempty by the assumed integrality
of the prescribed stages. This is a contradiction. Now the cited integral-blowup theorem,
applied to the integral $Z_j$ and its nonzero finite-type ideal $\mathcal I_z$, proves that
$Z_{j+1}$ is integral.
Uses: def-nagata-global-blowup, def-nagata-global-blowup-glue-data, def-nagata-global-blowup-
local-model, def-nagata-affine-blowup, def-nagata-rees-algebra, def-nagata-affine-proj, def-pc-
integral-scheme, lem-per-integral-blowup-projective-geometry.
8. The arrow $Z_{j+1}\to Z_j$ is proper by the properness statement for a finite-type quasi-
coherent blowup ideal. Proper includes finite type; since $Z_j$ is Noetherian, the finite-type-
over-Noetherian statement makes $Z_{j+1}$ Noetherian. The blowup-complement statement gives an
isomorphism away from $z$. In particular this arrow restricts to an isomorphism over $U$, and
composing it with the already constructed isomorphism over $U$ preserves that induction
condition.
Uses: lemma-nagata-blowup-proper, def-weil-proper-morphism, lem-weil-pbc-finite-type-over-
noetherian, thm-nagata-global-blowup-complement.
9. To check normality of $Z_{j+1}$, a point mapping into $U$ has the same local ring as its
image in the normal $S$, by the isomorphism over $U$. Any other point maps to some $s_\ell$ and,
by steps 2 and 3 applied to $Z_{j+1}\to S$, its local ring is isomorphic to that of the
corresponding point in $Z_{j+1}\times_SS_\ell\cong T_{\ell,a_\ell(j+1)}$. These prescribed
stages are normal by hypothesis. In both cases the local ring is an integrally closed domain, so
$Z_{j+1}$ is normal in exactly the sense in the statement. This completes the induction without
assuming that an arbitrary ordinary blowup preserves normality.
Uses: def-weil-pbc-normal-ring.
10. After all $N$ letters, $a_i(N)=n_i$ and every required local arrow has occurred in its
original order; other letters gave precisely the inserted identity arrows. The induction
supplies all intermediate integrality, normality, Noetherianity and the arrowwise properness and
complement isomorphisms. Steps 2 and 3 supply the asserted point and local-ring correspondences
at every intermediate stage. If the prescribed centers are singular, their local rings are not
regular. At each chosen global center the local ring is isomorphic to the corresponding local
center ring by step 3; regularity of a Noetherian local ring, and its failure, is invariant
under ring isomorphism directly from the generator and Krull-dimension definition. Thus every
global center is singular. The empty word covers both $r=0$ and the case when every $n_i=0$.
Uses: def-weil-regular-scheme.
-/
theorem local_ordinary_point_blowups_globalize
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x))
    (r : ℕ) (s : Fin r → S) (hs : Function.Injective s)
    (hclosed : ∀ i : Fin r, IsClosed ({s i} : Set S))
    (n : Fin r → ℕ)
    (T : ∀ i : Fin r, (Fin (n i + 1))ᵒᵖ ⥤ Scheme.{u})
    (t0 : ∀ i : Fin r, (T i).obj (op 0) ≅ Spec (S.presheaf.stalk (s i)))
    (hT : ∀ (i : Fin r) (j : Fin (n i + 1)),
      IsIntegral ((T i).obj (op j)) ∧
      ∀ x : (T i).obj (op j),
        IsDomain (((T i).obj (op j)).presheaf.stalk x) ∧
        IsIntegrallyClosed (((T i).obj (op j)).presheaf.stalk x))
    (c : ∀ (i : Fin r) (j : Fin (n i)), (T i).obj (op j.castSucc))
    (hc : ∀ (i : Fin r) (j : Fin (n i)),
      IsClosed ({c i j} : Set ((T i).obj (op j.castSucc))))
    (hover : ∀ (i : Fin r) (j : Fin (n i)),
      ((T i).map (homOfLE (Fin.zero_le j.castSucc)).op ≫ (t0 i).hom) (c i j) =
        IsLocalRing.closedPoint (S.presheaf.stalk (s i)))
    (hbl : ∀ (i : Fin r) (j : Fin (n i)),
      ∃ e : (T i).obj (op j.succ) ≅
        (Scheme.IdealSheafData.vanishingIdeal ⟨{c i j}, hc i j⟩).blowup,
        (T i).map (homOfLE j.castSucc_le_succ).op =
          e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{c i j}, hc i j⟩).blowupMap) :
    ∃ (Z : (Fin ((∑ i : Fin r, n i) + 1))ᵒᵖ ⥤ Scheme.{u})
      (z0 : Z.obj (op 0) ≅ S)
      (a : ∀ i : Fin r, Fin ((∑ k : Fin r, n k) + 1) →o Fin (n i + 1))
      (q : ∀ (i : Fin r) (j : Fin ((∑ k : Fin r, n k) + 1)),
        (T i).obj (op (a i j)) ⟶ Z.obj (op j))
      (d : ∀ j : Fin (∑ i : Fin r, n i), Z.obj (op j.castSucc))
      (hd : ∀ j : Fin (∑ i : Fin r, n i),
        IsClosed ({d j} : Set (Z.obj (op j.castSucc)))),
      (∀ i : Fin r, a i 0 = 0 ∧ a i (Fin.last (∑ k : Fin r, n k)) = Fin.last (n i)) ∧
      (∀ j : Fin (∑ i : Fin r, n i), ∃ i : Fin r,
        (a i j.succ).val = (a i j.castSucc).val + 1 ∧
        ∀ k : Fin r, k ≠ i → a k j.succ = a k j.castSucc) ∧
      (∀ j : Fin ((∑ i : Fin r, n i) + 1),
        IsIntegral (Z.obj (op j)) ∧ IsNoetherian (Z.obj (op j)) ∧
        ∀ x : Z.obj (op j), IsDomain ((Z.obj (op j)).presheaf.stalk x) ∧
          IsIntegrallyClosed ((Z.obj (op j)).presheaf.stalk x)) ∧
      (∀ j : Fin (∑ i : Fin r, n i),
        ∃ e : Z.obj (op j.succ) ≅
          (Scheme.IdealSheafData.vanishingIdeal ⟨{d j}, hd j⟩).blowup,
          Z.map (homOfLE j.castSucc_le_succ).op =
            e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{d j}, hd j⟩).blowupMap) ∧
      (∀ j : Fin (∑ i : Fin r, n i),
        IsProper (Z.map (homOfLE j.castSucc_le_succ).op) ∧
        IsIso (Z.map (homOfLE j.castSucc_le_succ).op ∣_ (⟨{d j}, hd j⟩ :
          Closeds (Z.obj (op j.castSucc))).compl) ∧
        ∃ i : Fin r,
          (Z.map (homOfLE (Fin.zero_le j.castSucc)).op ≫ z0.hom) (d j) = s i) ∧
      (∀ (i : Fin r) (j : Fin ((∑ k : Fin r, n k) + 1)),
        IsPullback (q i j)
          ((T i).map (homOfLE (Fin.zero_le (a i j))).op ≫ (t0 i).hom)
          (Z.map (homOfLE (Fin.zero_le j)).op ≫ z0.hom) (S.fromSpecStalk (s i))) ∧
      (∀ (i : Fin r) (j : Fin (∑ k : Fin r, n k)),
        q i j.succ ≫ Z.map (homOfLE j.castSucc_le_succ).op =
          (T i).map (homOfLE ((a i).monotone j.castSucc_le_succ)).op ≫ q i j.castSucc) ∧
      (∀ (i : Fin r) (j : Fin ((∑ k : Fin r, n k) + 1))
        (z : Z.obj (op j)),
        (Z.map (homOfLE (Fin.zero_le j)).op ≫ z0.hom) z = s i →
        ∃ t : (T i).obj (op (a i j)), q i j t = z ∧ IsIso ((q i j).stalkMap t)) ∧
      (∀ j : Fin ((∑ i : Fin r, n i) + 1),
        IsIso ((Z.map (homOfLE (Fin.zero_le j)).op ≫ z0.hom) ∣_
          (⟨Set.range s, (by
            simpa only [Set.range_eq_iUnion] using isClosed_iUnion_of_finite hclosed)⟩ :
              Closeds S).compl)) ∧
      ((∀ (i : Fin r) (j : Fin (n i)),
        ¬ IsRegularLocalRing (((T i).obj (op j.castSucc)).presheaf.stalk (c i j))) →
        ∀ j : Fin (∑ i : Fin r, n i),
          ¬ IsRegularLocalRing ((Z.obj (op j.castSucc)).presheaf.stalk (d j))) := by
  sorry

end AlgebraicGeometry
