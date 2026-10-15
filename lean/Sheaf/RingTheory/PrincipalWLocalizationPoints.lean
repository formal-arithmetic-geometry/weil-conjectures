/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.RingTheory.PrincipalWLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.WLocalClopenPartitions
import WeilConjectures.RingTheory.ProEtale.WLocal

/-! # Points and components of the principal w-localization

Source: blueprint, proper base change, lemma "Points of the affine w-localization", order 1223
(blueprint: lem-weil-pbc-w-localization-points).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace PrincipalWLocalization

/-- The prime-pair description, local rings, component schemes, and closed points of the
finite-partition principal w-localization. The closed immersion from `Spec A_x` with image the
first-coordinate fibre equips that fibre with its canonical affine scheme structure. Its ring
map is an `A`-algebra map, so these identifications respect the structural morphism to `Spec A`.
The homeomorphism on closed points and the continuous first-coordinate map use the patch
rather than the Zariski topology on `Spec A`.

Source: blueprint order 1223 (blueprint: lem-weil-pbc-w-localization-points).
Proof:
1. Use the small directed set of all finite constructible partitions and all allowed denominators
from [def-weil-pbc-w-localization]; importantly, denominators are not fixed once and for all.
Write $B_i=\prod_{E\in\mathcal P_i}A_{f_{i,E}}$. For a prime $q\subset W$, its inverse image in
$B_i$ selects exactly one component: the finitely many orthogonal component idempotents sum to
$1$, so exactly one is outside the prime (at least one by their sum, at most one by their zero
pairwise products). The prime contains every other component and is the inverse image of a prime
of the selected factor. Under refinement the selected part must lie in the previously selected
part, by the transition formula for these idempotents.

2. The selected parts have the finite intersection property: a common refinement selects a
nonempty subset of their intersection. Each part is a closed subset of the patch space by its
finite Boolean description in [def-weil-pbc-w-local]. Compactness of that space from [lem-weil-
pbc-w-local-partition] gives a point $x$ in all of them. It is unique: if two primes differ on
$f\in A$, the partition by the nonempty members of $D(f),V(f)$ separates them. Thus every stage
selects precisely its part containing $x$. Let $y=q\cap A$. It is prime, since inverse image
preserves the defining primality equations. If $f\notin x$, take the partition by $D(f),V(f)$ and
denominator $f$ on $D(f)$; If $e$ is that factor's idempotent, its inverse for $f$ gives an
element $u$ of the product with $fu=e$. Since $e\notin q$, primality implies $f\notin q\cap A=y$.
Hence $y\subseteq x$.

3. Conversely fix primes $y\subseteq x$. In stage $i$, project to the part $E_i$ containing $x$;
since $E_i\subset D(f_{i,E_i})$, its denominator is outside $x$ and hence outside $y$. The
universal property [lem-weil-pbc-ring-localization-universal-property] gives $A_{f_{i,E_i}}\to
A_y\to\kappa(y)$ [def-weil-pbc-localization-at-prime]. These maps from $B_i$ are compatible under
refinement, because the chosen part refines the old one and the localization maps agree on $A$.
They induce $W\to\kappa(y)$; its kernel is a prime $q_{x,y}$ since the target is a field. Its
contraction is $y$, and its selected parts contain $x$. This is inverse to the previous
assignment: in a selected factor $a/f^n$ belongs to a prime contracting to $y$ exactly when $a\in
y$, since $f$ is a unit. Consequently two primes with the same $(x,y)$ have identical inverse
images at every stage and are equal, as every element of $W$ has a stage representative [lem-pc-
filtered-colimit-commrings-elementwise].

4. At $q_{x,y}$, localization of $B_i$ kills the unselected components: each other component
idempotent is annihilated by the selected idempotent, which is inverted. The resulting local ring
is $(A_{f_{i,E_i}})_{yA_{f_{i,E_i}}}\cong A_y$. Indeed, fractions $a/f^n$ outside that prime have
$a\notin y$; localizing therefore inverts exactly the elements required for $A_y$. The mutually
inverse maps are supplied by [lem-weil-pbc-ring-localization-universal-property]. Under these
identifications every transition map is the identity on $A_y$, since it fixes $A$ and its
inverses. The localization-colimit statement [lem-weil-pbc-filtered-colimit-localization-at-prime]
gives $W_{q_{x,y}}\cong A_y$. The affine stalk identification in [lem-weil-pbc-spec-map-stalk-
localization] identifies this with the scheme's local ring.

5. For every constructible $E\subseteq\operatorname{Spec}A$, the characteristic vector of $E$ in
the partition by $E$ and its complement, with denominators $1$, defines an idempotent $e_E\in W$.
Empty parts are omitted; $e_\emptyset=0$ and $e_X=1$. Refinement makes this independent of the
presentation and gives $e_{E\cap F}=e_Ee_F$ and $e_{X\setminus E}=1-e_E$. Under the point
description, $D(e_E)$ is exactly the set of pairs whose first coordinate lies in $E$. These sets
are clopen by [lem-weil-pbc-spec-clopen-idempotent], and constructible sets form a basis of the
patch topology by [def-weil-pbc-w-local]. Therefore $\pi:\operatorname{Spec}W\to
(\operatorname{Spec}A)_{\rm patch}$, $(x,y)\mapsto x$, is continuous. Distinct fibres are
separated by a clopen set $D(e_E)$.

6. Fix $x$, and let $J_x$ be the ideal generated by $1-e_E$ for all constructible $E$ containing
$x$. Selecting the part containing $x$ and mapping $A_f\to A_x$ at every stage gives a compatible
homomorphism $\rho_x:W\to A_x$, by [lem-weil-pbc-ring-localization-universal-property]. It kills
$J_x$. It is surjective: for $a/s\in A_x$, refine by $D(s),V(s)$ and choose denominator $s$ on
$D(s)$; the tuple $a/s$ on this part and zero on its complement maps to $a/s$. For the kernel,
represent $b\in W$ at a stage using [lem-pc-filtered-colimit-commrings-elementwise]. Modulo $J_x$,
it equals its selected coordinate $a/f^n$ multiplied by the corresponding idempotent. If
$\rho_x(b)=0$, there is $s\notin x$ with $sa=0$ in $A$ by the fraction equality in [def-weil-pbc-
localization-at-prime]. Refine by $D(s),V(s)$ and multiply all denominators on the $D(s)$ parts by
$s$. On the part containing $x$ the selected coordinate becomes zero. Thus $e_Fb=0$ for a
constructible $F$ containing $x$, and $b=(1-e_F)b\in J_x$. This proves $W/J_x\cong A_x$.

7. A prime $q$ contains $J_x$ exactly when its selected part at every partition contains $x$,
equivalently when its first coordinate is $x$: $e_E(1-e_E)=0$ and $e_E+(1-e_E)=1$ imply that
exactly one of $e_E,1-e_E$ belongs to $q$. Thus $q$ contains the generators of $J_x$ exactly when
its first coordinate lies in every constructible neighbourhood of $x$; the $D(f),V(f)$ partitions
show that this coordinate is $x$. Primes of $W/J_x$ are precisely the primes of $W$ containing
$J_x$, by inverse image along the quotient and passage to the quotient ideal; their basic opens
agree with the restrictions of $D(b)$ from $W$. On each such basic open, the ring is
$(W/J_x)_{\bar b}=W_b/J_xW_b$: both sides have the universal property of killing $J_x$ and
inverting $b$. These identifications commute with restriction because they fix the images of
elements of $W$. Therefore the closed fibre $\pi^{-1}(x)$, with its canonical affine scheme
structure $\operatorname{Spec}(W/J_x)$ [def-weil-affine-spectrum], is isomorphic to
$\operatorname{Spec}A_x$ by step 6. Equivalently it is obtained by inverting all $e_E$ with $x\in
E$, since an invertible idempotent equals $1$, and conversely an idempotent equal to $1$ is
invertible. Both constructions therefore have the same universal property.

8. The spectrum of the local ring $A_x$ is connected. Its maximal ideal is $xA_x$ [def-weil-pbc-
localization-at-prime]; an open neighbourhood of this point contains a basic open $D(a/s)$
containing it, where $a\notin x$, and $a/s$ is a unit. Such a basic open is the entire spectrum.
Thus any partition into two disjoint open subsets has an empty member. Step 7 makes each fibre
connected. Any connected subset meeting two fibres would be separated by the clopen set of step 5,
a contradiction. Hence the fibres are exactly the connected components.

9. Specialization of prime points is inclusion of their ideals: $V(q)$ is the closure of $q$ by
the definition of the Zariski closed sets. A specialization cannot change the first coordinate,
because the clopen sets $D(e_E)$ separate different coordinates. Inside the closed fibre
$\operatorname{Spec}A_x$, the unique closed point is its maximal ideal $xA_x$, namely $(x,x)$.
Every $(x,y)$ specializes to $(x,x)$; no $(x,x)$ has a further specialization. Thus the closed
points of $\operatorname{Spec}W$ are exactly the diagonal pairs. If $y\subsetneq x$, choose $f\in
x\setminus y$. The open $D(e_{V(f)})\cap D(f)$ contains $(x,y)$ and contains no diagonal pair. The
union of these opens over all $f\in A$ is precisely the complement of the diagonal, which is
therefore closed.

10. Identify the diagonal with $\operatorname{Spec}A$ by $x\mapsto(x,x)$. The restriction of
$D(e_E)$ is $E$, so its subspace topology contains the patch topology. Conversely represent $b\in
W$ by a tuple $(a_E/f_E^{n_E})_E$ in a stage, using [lem-pc-filtered-colimit-commrings-
elementwise]. At $(x,x)$, $b$ is outside the prime exactly when $x$ lies in a part $E$ and
$a_E\notin x$. Hence the restriction of $D(b)$ is the finite union $\bigcup_E(E\cap D(a_E))$, a
constructible set and a patch open [def-weil-pbc-w-local]. Since basic opens form a basis for the
Zariski topology, the two topologies coincide. Each connected component has its unique diagonal
closed point by steps 8 and 9, and their set is closed by step 9; these are exactly the w-local
conditions.

11. The construction [def-weil-pbc-w-localization] presents $W$ as an ind-Zariski, hence ind-
etale, $A$-algebra [def-weil-pbc-ind-etale-algebra]. By [lem-weil-pbc-ind-etale-stability], its
map is weakly etale, which includes flatness by [def-weil-pbc-ind-etale-algebra]. Its spectrum map
sends $(x,y)$ to $y$ by step 3, and is surjective since every prime $x$ is the image of $(x,x)$.
The flat-surjective-spectrum criterion [lem-weil-pbc-flat-surjective-spectrum-faithfully-flat] now
proves faithful flatness. If $A$ is the zero ring, both spectra and the set of pairs are empty and
$W$ is the zero ring (the empty product at its sole partition); the same flat-surjective criterion
applies, so this case is included.
-/
theorem points (A : Type u) [CommRing A] :
    ∃ e : PrimeSpectrum (algebra A) ≃
        {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q : PrimeSpectrum (algebra A),
        PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2) ∧
      (∀ q : PrimeSpectrum (algebra A),
        Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A]
          Localization.AtPrime (e q).val.2.asIdeal)) ∧
      (@Continuous (PrimeSpectrum (algebra A)) (PrimeSpectrum A) inferInstance
        (constructibleTopology (PrimeSpectrum A)) (fun q ↦ (e q).val.1)) ∧
      (∀ q : PrimeSpectrum (algebra A),
        connectedComponent q = {r | (e r).val.1 = (e q).val.1}) ∧
      (∀ x : PrimeSpectrum A,
        ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) ∧
          Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) ∧
      (∀ q : PrimeSpectrum (algebra A),
        q ∈ closedPoints (PrimeSpectrum (algebra A)) ↔ (e q).val.1 = (e q).val.2) ∧
      IsClosed (closedPoints (PrimeSpectrum (algebra A))) ∧
      (∃ h : @Homeomorph (PrimeSpectrum A)
          (closedPoints (PrimeSpectrum (algebra A)))
          (constructibleTopology (PrimeSpectrum A)) inferInstance,
        ∀ x : PrimeSpectrum A, (e (h x).val).val = (x, x)) ∧
      Module.FaithfullyFlat A (algebra A) ∧ IsWLocalRing (algebra A) := by
  sorry

end PrincipalWLocalization
