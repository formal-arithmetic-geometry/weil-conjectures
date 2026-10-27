/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.RingTheory.HenselizationAtPrime
public import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.PrimePairColimitIndEtaleModel
import Sheaf.RingTheory.InitialHenselianColimitComparison
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Ind-étaleness of a henselization at a prime

Source: Stacks Project, Algebra, Tag 04GN, property (2), applied to a prime
localization (blueprint: lem-trf-henselization-prime-ind-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingHom

private theorem indEtale_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) : f.IndEtale := by
  rw [IndEtale.iff_ind_etale]
  exact MorphismProperty.le_ind _ _ (Etale.of_bijective hf)

private theorem indEtale_of_across {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IndEtaleAcrossUniverses) : f.IndEtale := by
  have h := (indEtale_of_bijective (ULift.ringEquiv (R := S)).toRingHom
    (ULift.ringEquiv (R := S)).bijective).comp
      (hf.comp (indEtale_of_bijective (ULift.ringEquiv (R := R)).symm.toRingHom
        (ULift.ringEquiv (R := R)).symm.bijective))
  simpa only [RingHom.comp_ulift_eq] using h

/-- The canonical composite from `A` to an ordinary henselization of `Aₚ` is ind-étale.
Source: Stacks Project, Algebra, Tag 04GN (2), applied to `Aₚ`; Tag 04GQ for
henselization, Tag 00CR for localization, and Tag 097K for ind-étale composition.
(blueprint: lem-trf-henselization-prime-ind-etale).

Proof plan, following all seven steps of the node:

1. Set $R=A_{\mathfrak p}$ and $S=A\setminus\mathfrak p$. Since $\mathfrak p$ is prime, $1\in S$
   and $s,t\in S$ imply $st\in S$. Apply [lem-weil-pbc-localization-colimit-principal-
   localizations] with $P=A$: $R$ is the filtered colimit of $A_s$, indexed by the small
   divisibility preorder on $S$, with its canonical structural map from $A$. Apply clause (2) of
   [lem-weil-pbc-etale-algebra-finite-presentation-localization] to the identity etale map $A\to
   A$ to see that $A\to A_s$ is etale, and then clause (1), now to $A\to A_s$, to see that each
   $A_s$ has finite presentation. Thus $A\to R$ is ind-etale by [def-weil-pbc-ind-etale-algebra].

2. Put $\mathfrak m=\mathfrak pR$ and $k=R/\mathfrak m$. The ring $R$ is local: a fraction $a/s$
   outside $\mathfrak pR$ has $a\notin\mathfrak p$, and then $s/a$ is its inverse; $\mathfrak pR$
   is proper since a prime contains no denominator in $S$. Apply [lem-weil-pbc-pair-henselization]
   to $(R,\mathfrak m)$. Its category of etale $R$-algebras $B$ with
   $k\xrightarrow{\sim}B/\mathfrak mB$ is essentially small and filtered; take a small skeleton
   for the stated colimit and denote the diagram by $(B_i)$ and its colimit coprojections by
   $\iota_i:B_i\to C$. This gives an $R$-algebra structure $\eta_C:R\to C$, a henselian pair
   $(C,J)$ with $J=\mathfrak mC$, and an induced isomorphism $e_C:k\xrightarrow{\sim}C/J$. Each
   $B_i$ has finite presentation by clause (1) of [lem-weil-pbc-etale-algebra-finite-presentation-
   localization].

3. The henselian pair from Step 2 is local by a direct use of [def-weil-pbc-henselian-
   terminology]. For $z\in J$, the finite cyclic $C$-algebra $D=C/(1-z)$ has $JD=D$, so $D/JD=0$.
   Its sole idempotent has both $0$ and $1$ of $D$ as lifts; uniqueness gives $D=0$, so $1-z$ is a
   unit of $C$. If $x\notin J$, the field $C/J\cong k$ supplies $y\in C$ with $1-xy\in J$, so $xy$
   and hence $x$ are units. Thus $C$ is local with maximal ideal $J$ and is henselian local
   because $(C,J)$ is henselian. The structural residue-field isomorphism $e_C:k\to C/J$ also
   gives $\eta_C^{-1}(J)=\mathfrak m$, so $\eta_C$ is local.

4. Write $\eta_H:R\to H$ for the given local map. By [def-weil-pbc-henselization-at-prime], $H$ is
   henselian local. Put $k_C=C/\mathfrak m_C=C/J$. Its local structure map induces $e_H:k\to
   k_H=H/\mathfrak m_H$. Apply [lem-weil-pbc-map-into-henselian-colimit] with base $R$, source
   algebra $C$, target $H$, prime $\mathfrak q=\mathfrak m_C$, and residue map $\tau=e_H\circ
   e_C^{-1}:k_C\to k_H$. Locality of $\eta_C$ and $\eta_H$ gives contraction $\mathfrak m$ on both
   sides, and $\tau$ is a $k$-algebra map. The lemma gives a local $R$-algebra map $f:C\to H$.
   Apply the defining universal property of $H$, with henselian local target $C$ and local map
   $\eta_C$, to obtain a local $R$-algebra map $g:H\to C$. Thus $f\eta_C=\eta_H$ and
   $g\eta_H=\eta_C$.

5. Both $g\circ f$ and $\mathrm{id}_C$ are local $R$-algebra endomorphisms of $C$. On residue
   fields, $(\overline g\circ\overline f)\circ e_C=e_C$, since both maps are over $R$; cancel the
   isomorphism $e_C$ to get $\overline g\circ\overline f=\mathrm{id}_{k_C}$. Uniqueness in [lem-
   weil-pbc-map-into-henselian-colimit], now with source and henselian target $C$, prime
   $\mathfrak m_C$ and residue map $\mathrm{id}_{k_C}$, gives $g\circ f=\mathrm{id}_C$. Both
   $f\circ g$ and $\mathrm{id}_H$ are local maps satisfying $h\eta_H=\eta_H$, so the uniqueness in
   [def-weil-pbc-henselization-at-prime], with target $H$, gives $f\circ g=\mathrm{id}_H$. Hence
   $f$ and $g$ are inverse $R$-algebra isomorphisms. This does not assume in advance that $H$ has
   residue field $k$.

6. Use the same small filtered diagram $(B_i)$ and replace its colimit coprojections by
   $j_i=f\circ\iota_i:B_i\to H$. These form a cocone since $f$ is an $R$-algebra map. To verify
   the colimit property of [def-weil-pbc-category-colimit], take any compatible $R$-algebra cocone
   $\mu_i:B_i\to T$. The original colimit gives a unique $u:C\to T$ with $u\iota_i=\mu_i$. This
   $u$ respects $R$: choose any stage $i$ (the index category is nonempty) with structural map
   $\eta_i:R\to B_i$; then $u\eta_C=u\iota_i\eta_i=\mu_i\eta_i=\eta_T$. Then $u\circ g:H\to T$
   satisfies $(u\circ g)j_i=u\iota_i=\mu_i$. Conversely, if $v:H\to T$ has $vj_i=\mu_i$,
   uniqueness for $C$ gives $v\circ f=u$, whence $v=u\circ g$. Thus $H$, with its given structural
   map $\eta_H=f\eta_C$, is a filtered colimit of the same etale finitely presented $R$-algebras.
   By [def-weil-pbc-ind-etale-algebra], $R\to H$ is ind-etale.

7. Steps 1 and 6 give ind-etale maps $A\to R$ and $R\to H$ for the specified structural maps.
   Apply the composition clause of [lem-weil-pbc-ind-etale-stability] to conclude that the
   canonical composite $A\to A_{\mathfrak p}\to H$ is ind-etale. No argument or cited statement
   required Noetherianity.
-/
theorem henselization_prime_indEtale
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime p) H] [HenselianLocalRing H]
    (hH : Algebra.IsHenselizationAtPrime A p H) :
    ((algebraMap (Localization.AtPrime p) H).comp
      (algebraMap A (Localization.AtPrime p))).IndEtale := by
  classical
  let R := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal R
  let P : ObjectProperty (Under (CommRingCat.of R)) := fun B ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
      Function.Bijective (Ideal.quotientMap (m.map B.hom.hom) B.hom.hom
        Ideal.le_comap_map)
  have hp := RingTheory.pair_henselization R m
  let : EssentiallySmall.{u} P.FullSubcategory := hp.1
  let : IsFiltered P.FullSubcategory := hp.2.1
  let I := Skeleton (SmallModel.{u} P.FullSubcategory)
  let e : I ≌ P.FullSubcategory :=
    (skeletonEquivalence (SmallModel.{u} P.FullSubcategory)).trans
      (equivSmallModel P.FullSubcategory).symm
  let : IsFiltered I := IsFiltered.of_equivalence e.symm
  let F := e.functor ⋙ P.ι
  let c := colimit.cocone F
  have hc := isColimitOfPreserves (Under.forget (CommRingCat.of R))
    (colimit.isColimit F)
  obtain ⟨_, _, _, ⟨hC, hmax⟩, hlocal, hres, _, hindC, hindA⟩ :=
    RingTheory.prime_pair_colimit_indEtale_model A p I
      (skeleton_skeletal _) e c hc
  let C := c.pt.right
  let : HenselianLocalRing C := hC
  let : Algebra R C := c.pt.hom.hom.toAlgebra
  let : IsLocalHom (algebraMap R C) := hlocal
  let : IsLocalHom (algebraMap R H) := hH.1
  have hres' : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)) := by
    have hq : ∀ (J : Ideal C) (hJ : m ≤ J.comap (algebraMap R C)),
        J = IsLocalRing.maximalIdeal C →
        Function.Bijective (Ideal.quotientMap J (algebraMap R C) hJ) →
        Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)) := by
      intro J hJ heq
      subst J
      have he : Ideal.quotientMap (IsLocalRing.maximalIdeal C)
          (algebraMap R C) hJ = IsLocalRing.ResidueField.map (algebraMap R C) := by
        apply Ideal.Quotient.ringHom_ext
        ext x
        rfl
      intro hb
      exact he ▸ hb
    exact hq _ Ideal.le_comap_map hmax.symm hres
  obtain ⟨f, g, _, _, _, _, hgf, hfg, _⟩ :=
    Algebra.initial_henselian_colimit_comparison R C H hindC hres' hH.2
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hleft (z : C) : g (f z) = z := DFunLike.congr_fun hgf z
      simpa only [hleft] using congrArg g h
    · intro y
      exact ⟨g y, DFunLike.congr_fun hfg y⟩
  have h := (indEtale_of_bijective f.toRingHom hf).comp
    (indEtale_of_across _ hindA)
  have heq : f.toRingHom.comp (c.pt.hom.hom.comp (algebraMap A R)) =
      (algebraMap R H).comp (algebraMap A R) := by
    ext a
    exact f.commutes (algebraMap A R a)
  rwa [heq] at h

end RingHom
