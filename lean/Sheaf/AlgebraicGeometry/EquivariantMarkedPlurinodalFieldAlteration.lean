module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.ReducedNormalization
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants
import Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite
import Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient

/-!
# Equivariant marked plurinodal alteration over a field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Lemma 2.2,
printed pp. 149--150, the application of Vidal 2004b, Proposition 4.4.3.
(blueprint: lem-sfb-equivariant-plurinodal-field-alteration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Equivariant marked nodal towers retain the radicial constant extension and the
single-kernel-orbit assertion over a dense open. The first stage is identified with Spec F;
the displayed structural maps ensure that the top alteration is over the original field.
Quasi-splitness is stated on the actual residue-field fibres: every nonsmooth point and
both points of its componentwise normalization are rational over the base residue field.
No condition on the permutation of markings by stabilizers is imposed.

Source: ILO, Expose X, Lemma 2.2 proof, pp. 149--150, before the applications of
Vidal 4.4.4; de Jong, Families of curves and alterations, Theorem 5.9.
(blueprint: lem-sfb-equivariant-plurinodal-field-alteration).

Proof (the fourteen steps of the node):
1. Use strong induction on $d$, proving also the following strengthened form: the input finite
   group may act nonfaithfully; the map to $X$ is H-projective; and, for $N=\ker(J\to H)$, the
   finite extension of function fields satisfies $k(T_d)^N/k(X)$ purely inseparable. All schemes
   in the tower are finite type over their constant field. The dense-open orbit assertion will
   be deduced uniformly in the final steps. For $d=0$, the zero-dimensional properness lemma
   makes $X$ finite over $k$. Its coordinate ring is a finite field extension $L/k$. Geometric
   integrality forces $L=k$: a nontrivial separable part splits after algebraic closure, and a
   nontrivial purely inseparable part creates nilpotents. Take $F=k$, $J=H$, $a=\mathrm{id}$ and
   the length-zero tower. Its boundary is empty, since a nowhere dense closed subset of a point
   is empty. All strengthened claims are immediate.
   Uses: lem-pc-dim-zero-finite-over-field, def-pc-geometrically-irreducible.
2. For $d=1$, apply the one-curve reduction node with $C=X$, $Y=\operatorname{Spec}k$ and $E=Z$.
   Its zero-dimensional clause gives $B=\operatorname{Spec}e$ and $D=\varnothing$. Set $F=e$,
   $J=G$, $T_1=V$ and $a=c$. The single marked nodal curve is smooth over $B$ because $D$ is
   empty, and its sections contain $a^{-1}Z$. The reduction node gives H-projectivity, the
   constant-field assertion $e^{\ker\alpha}/k$, and the strengthened function-field assertion
   $k(V)^{\ker\alpha}/k(X)$. Thus only the uniform dense-open verification remains for this
   case. Henceforth assume $d\geq2$.
   Uses: lem-sfb-equivariant-single-curve-nodal-reduction.
3. Apply the equivariant curve-pencil node to obtain $\pi:X'\to X$ and $g:X'\to Y$. The inverse
   image $E=\pi^{-1}Z$ is invariant and nowhere dense: $\pi$ is an isomorphism over a dense open
   and the generic point maps outside $Z$. Apply the one-curve reduction to $g,E$, obtaining
   $e,G,\alpha,B,V,v,c,b,D$ and sections $s_j$. Here $Y$ has dimension $d-1$, $B$ is normal
   proper geometrically integral over $e$, and $\dim_e B=d-1$: the alteration $B\to Y$ is proper
   with finite function-field extension, so dimensions agree by the closed-dominant dimension
   lemma; replacing $k$ by the finite extension $e$ does not change chains of irreducible closed
   subsets. Write $A=\ker\alpha$. Retain $e^A/k$ and $k(V)^A/k(X')$ purely inseparable.
   Uses: lem-sfb-equivariant-curve-pencil, lem-sfb-equivariant-single-curve-nodal-reduction,
   lem-trf-closed-dominant-dimension.
4. Apply the strengthened induction hypothesis in dimension $d-1$ to the $e$-scheme $B$, the
   finite group $G$ and its invariant nowhere dense boundary $D$. This gives $F/e$, a surjection
   $\beta:J\to G$, an H-projective alteration $h:P\to B$, and a marked quasi-split tower
   $P=T_{d-1}\to\cdots\to T_0=\operatorname{Spec}F$. Put $Q=\ker\beta$. The inductive data give
   $h^{-1}D\subseteq Z_{d-1}$, $F^Q/e$ purely inseparable and $k(P)^Q/k(B)$ purely inseparable.
   This is the induction hypothesis, not an invocation of the present theorem in unchanged
   dimension. No faithfulness of $G$ on $B$ is required in the strengthened claim.
5. Define $T_d=V\times_B P$, let $f_d:T_d\to P$ be the projection and let $a$ be the composite
   $T_d\to V\xrightarrow c X'\xrightarrow\pi X$. The diagonal $J$-action is defined by its
   action on $P$ and its action through $\beta$ on $V$; the fibre-product universal property
   gives its group law and equivariance. The base-change clauses of the one-curve node supply
   H-projectivity, flatness, finite presentation, nonempty connected reduced nodal geometric
   fibres, quasi-splitness, and smooth geometrically integral generic fibre for $f_d$. Dominance
   of $h$ ensures that this generic fibre is a field extension of the generic fibre of $v$. Pull
   back the sections $s_j$ to $P$; the identities $v s_j=\mathrm{id}$ and pairwise disjointness
   persist in the cartesian square.
   Uses: lem-sfb-equivariant-single-curve-nodal-reduction, def-pc-fibre-product.
6. The ordinary fibre product $T_d=V\times_B P$ is reduced. To check precisely the hypothesis of
   the flat geometrically reduced pullback lemma, fix any field $K$ and map
   $\operatorname{Spec}K\to B$. Choose an algebraic closure $\Omega/K$. Apply the arbitrary-
   base-change clause of the one-curve node over K; its geometric-fibre clause makes
   $V\times_B\operatorname{Spec}\Omega$ reduced. For every affine chart $\operatorname{Spec}A$
   in $V\times_B\operatorname{Spec}K$, its scalar extension has ring $A\otimes_K\Omega$. The map
   $A\to A\otimes_K\Omega$ is injective: a $K$-linear functional $\Omega\to K$ sending $1$ to
   $1$, obtained by extending $1$ to a basis, gives a retraction after tensoring. A nilpotent of
   $A$ therefore vanishes, so the $K$-fibre is reduced. This is the elementary descent from
   algebraically closed fibres to the field-valued hypothesis actually stated by the pullback
   lemma. The base $P$ is reduced because it is integral. It is locally Noetherian by finite
   type over $F$ and the finite-type-over-Noetherian lemma; $\operatorname{Spec}F$ is Noetherian
   since a field has only the ideals $0$ and $F$. Apply the pullback lemma with $h=v$, $Y=V$,
   $S=B$, $T=P$ and $T\to S=h:P\to B$; it requires flatness of $v$, supplied by the one-curve
   node, and imposes no flatness condition on $P\to B$. The result $P\times_B V$ is our $T_d$ by
   the symmetry of the fibre-product universal property.
   Uses: lem-sfb-equivariant-single-curve-nodal-reduction, lem-sfb-flat-geometrically-reduced-
   pullback, lem-weil-pbc-finite-type-over-noetherian, def-pc-fibre-product, lem-weil-pbc-fibre-
   product-affine-spectra.
7. The same ordinary fibre product is integral. The affine flatness criterion and the flat-
   module torsion-free lemma make its generic fibre over $P$ schematically dense: on affine
   charts over a domain $R$, a flat algebra injects into its localization at $R\setminus\{0\}$.
   If a nonempty affine basic open missed that fibre, its defining nonnilpotent element would
   become nilpotent after localization, contradicting this injection and reducedness. The
   generic fibre is integral by the one-curve node and dominance of $P\to B$, so its closure is
   irreducible and is the whole space. Thus $T_d$ is integral. Put $K=k(B)$, $M=k(P)$ and
   $L=k(V)$. Geometric integrality of the generic fibre of $v$ says $L\otimes_K M$ is a domain;
   since $M/K$ is finite, it is a finite-dimensional domain over $L$, hence a field. The affine
   fibre-product formula and localization identify it with the function field $k(T_d)$.
   Uses: lem-sfb-equivariant-single-curve-nodal-reduction, def-pc-geometrically-irreducible,
   lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-flat-morphism-affine-criterion,
   lem-trf-flat-module-torsionfree-domain, lem-weil-pbc-fibre-product-affine-spectra.
8. Let $Z_d=f_d^{-1}Z_{d-1}\cup\bigcup_j s'_j(P)$, with $s'_j$ the pulled-back sections. Pulling
   back $c^{-1}E\subseteq v^{-1}D\cup\bigcup_j s_j(B)$ and using $h^{-1}D\subseteq Z_{d-1}$
   gives $a^{-1}Z\subseteq Z_d$. Every point of $P\setminus Z_{d-1}$ maps into $B\setminus D$,
   so the smoothness clause of the one-curve node makes $f_d$ smooth there. The lower tower
   already has the same properties by induction. Section unions and the recursively defined
   boundaries are $J$-stable. Quasi-splitness is the residue-field rationality of nodes and
   their two branches, preserved by base change; it does not prohibit the group from permuting
   the sections.
   Uses: lem-sfb-equivariant-single-curve-nodal-reduction.
9. The projection $T_d\to V$ is the base change of the H-projective surjection $h$. The base-
   change and composition lemmas make $a=\pi c\operatorname{pr}_V$ H-projective and surjective.
   This also makes it projective in the projective-bundle sense: use the free module $\mathcal
   O_X^{n+1}$ in an H-projective embedding. The tensor calculation in the preceding step shows
   that $k(T_d)/k(V)$ is finite. The one-curve reduction gives $k(V)/k(X')$ finite, while
   $k(X')=k(X)$ by the pencil. Hence $k(T_d)/k(X)$ is finite. The same finite-field argument
   applies to the lower-dimensional inductive map, and all maps to which these permanence
   statements are applied have already been constructed.
   Uses: lem-pc-projective-base-change, lem-trf-h-projective-composition, lem-weil-pbc-
   surjective-base-change, lem-trf-surjective-morphism-composition, def-trf-projective-bundle-
   morphism, lem-sfb-equivariant-curve-pencil, lem-sfb-equivariant-single-curve-nodal-reduction.
10. Set $E_0=M^Q$. In $k(T_d)=L\otimes_K M$, the group $Q$ acts trivially on $L$. Apply the
   tensor-invariants node over the field $E_0$, with vector space $L\otimes_K E_0$ and extension
   $M/E_0$. Associativity of tensor products gives $(L\otimes_K M)^Q=L\otimes_K E_0$. This
   subalgebra is a field (it is the fixed subfield of a field). It is purely inseparable over
   $L$: in characteristic $p>0$, take a common $p$-power sending the finitely many coefficients
   of an element in $L\otimes_K E_0$ into $K$ and expand by Frobenius; in characteristic zero
   $E_0=K$. Put $N=\ker(\alpha\beta)$. The surjection $N\to A$ has kernel $Q$. For $z\in
   k(T_d)^N$ a $p$-power lies in $L$ by the preceding calculation, and lies in $L^A$ since $z$
   was $N$-fixed. A further $p$-power lies in $k(X')=k(X)$ by the one-curve node. This proves
   the strengthened generic assertion. The identical two-power argument with $F^Q/e$ and $e^A/k$
   gives $F^N/k$ purely inseparable. In characteristic zero both arguments use the first power.
   This establishes the induction.
   Uses: lem-weil-pbc-tensor-field-extension-galois-invariants, lem-sfb-equivariant-single-
   curve-nodal-reduction.
11. It remains to obtain the dense open in every dimension, including the one-curve and length-
   zero cases. The scheme $X$ is Noetherian by finite type over a field. Choose a nonempty
   affine open $\operatorname{Spec}R\subseteq X$. The morphism $a$ is H-projective, hence
   projective, and its generic fibre is zero-dimensional because its function-field extension is
   finite. The projective-generically-finite lemma supplies a smaller nonempty affine open $U$
   on which $a$ is finite. It remains surjective, since we restricted a surjective map on its
   target. Write $a^{-1}U=\operatorname{Spec}S$, with $S$ finite over $R=\mathcal O_X(U)$ and a
   domain, and let $K_X=\operatorname{Frac}R$, $P_X=\operatorname{Frac}S$. The subgroup $N$
   fixes $X$ and $k$, so acts on this affine $k$-scheme over $U$. The finite quotient node
   applies with its orbit-in-an-affine hypothesis witnessed by the whole affine scheme. It gives
   $\operatorname{Spec}(S^N)$ as quotient, geometric quotient fibres equal to $N$-orbits, and
   $S^N$ finite over $R$.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-fin-projective-generically-finite, lem-
   sfb-admissible-finite-type-field-quotient, lem-sc-integral-function-field-affine-fraction.
12. We have $\operatorname{Frac}(S^N)=P_X^N$. Indeed, for $x=s/t\in P_X^N$, the nonzero
   denominator $b=\prod_{n\in N}n(t)$ lies in $S^N$, and $bx\in S$ is invariant; hence
   $x=(bx)/b$. The finite-dimensional generic algebra $(S^N)\otimes_RK_X$ is a domain, so is
   this fixed field, which the induction proved purely inseparable over $K_X$. Choose finitely
   many $R$-module generators $r_i$ of $S^N$. In characteristic $p$ choose a common $q=p^m$ with
   $r_i^q\in K_X$; in characteristic zero take $q=1$. After inverting one nonzero $s\in R$ all
   these powers lie in $R[1/s]$. Frobenius then gives $r^q\in R[1/s]$ for every
   $r\in(S^N)[1/s]$. Two homomorphisms from this algebra to any field agreeing on $R[1/s]$ agree
   on all elements, since $q$th roots in a field are unique. The field-valued criterion in the
   radicial node therefore makes $\operatorname{Spec}(S^N)[1/s]\to\operatorname{Spec}R[1/s]$
   universally injective.
   Uses: def-weil-radicial-morphism.
13. Replace $U$ by $\operatorname{Spec}R[1/s]$. For any geometric point of $U$, the intermediate
   quotient has at most one geometric point by universal injectivity. It has at least one
   because $a$ is surjective and factors through it. The geometric-fibre statement of the finite
   quotient node now says that the entire geometric fibre of $a^{-1}U\to U$ is one $N$-orbit.
   The map is finite surjective by construction, and $U$ is dense because $X$ is integral.
   Together with the inductively constructed tower, boundary, constant extension and group
   surjection this proves every clause of the corrected statement.
   Uses: lem-sfb-admissible-finite-type-field-quotient, def-weil-radicial-morphism.
-/
theorem exists_equivariant_marked_plurinodal_field_alteration
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
    [IsIntegral X] [IsProper p] [GeometricallyIntegral p]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (H : Type u) [Group H] [Finite H]
    (α : H →* Aut X) (β : H →* (k ≃+* k)) (hfaithful : Function.Injective α)
    (hsemilinear : ∀ h : H, (α h).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (β h⁻¹).toRingHom))
    (Z : Closeds X) (hZ : IsNowhereDense (Z : Set X))
    (hstable : ∀ h : H, (α h).hom '' (Z : Set X) = (Z : Set X)) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra k F), Module.Finite k F ∧
      ∃ (J : Type u) (_ : Group J) (_ : Finite J) (ρ : J →* H)
        (γ : J →* (F ≃+* F)), Function.Surjective ρ ∧
        (∀ (g : J) (c : k), γ g (algebraMap k F c) = algebraMap k F (β (ρ g) c)) ∧
        (∃ K : IntermediateField k F,
          (∀ c : F, c ∈ K ↔ ∀ g : ρ.ker, γ g.val c = c) ∧ IsPurelyInseparable k K) ∧
        ∃ (d : ℕ) (T : Fin (d + 1) → Scheme.{u})
          (q : ∀ i, T i ⟶ Spec (.of F)) (e₀ : T 0 ≅ Spec (.of F))
          (f : ∀ i : Fin d, T i.succ ⟶ T i.castSucc)
          (τ : ∀ i, J →* Aut (T i))
          (B : ∀ i, Closeds (T i)) (m : Fin d → ℕ)
          (s : ∀ i : Fin d, Fin (m i) → (T i.castSucc ⟶ T i.succ))
          (a : T (Fin.last d) ⟶ X),
          topologicalKrullDim X = (d : WithBot ℕ∞) ∧
          (∀ i, IsIntegral (T i)) ∧ q 0 = e₀.hom ∧
          (∀ i : Fin d, f i ≫ q i.castSucc = q i.succ) ∧
          a ≫ p = q (Fin.last d) ≫ Spec.map (CommRingCat.ofHom (algebraMap k F)) ∧
          IsProjectiveBundle a ∧ Surjective a ∧
          (∀ (i : Fin (d + 1)) (g : J), (τ i g).hom ≫ q i =
            q i ≫ Spec.map (CommRingCat.ofHom (γ g⁻¹).toRingHom)) ∧
          (∀ (i : Fin d) (g : J), (τ i.succ g).hom ≫ f i =
            f i ≫ (τ i.castSucc g).hom) ∧
          (∀ g : J, (τ (Fin.last d) g).hom ≫ a = a ≫ (α (ρ g)).hom) ∧
          (B 0 : Set (T 0)) = ∅ ∧
          (∀ i : Fin d,
            IsProjectiveBundle (f i) ∧ Flat (f i) ∧ GeometricallyReduced (f i) ∧
            ∃ hfp : LocallyOfFinitePresentation (f i),
              @HasNodalGeometricFibres _ _ (f i) hfp ∧
              (∃ y : T i.castSucc, IsGenericPoint y Set.univ ∧
                Smooth ((f i).fiberToSpecResidueField y) ∧
                GeometricallyIntegral ((f i).fiberToSpecResidueField y)) ∧
              (∀ j : Fin (m i), s i j ≫ f i = 𝟙 (T i.castSucc)) ∧
              Pairwise (fun j l : Fin (m i) ↦ Disjoint (Set.range (s i j))
                (Set.range (s i l))) ∧
              (∀ j : Fin (m i), Set.range (s i j) ⊆
                (@Scheme.Hom.smoothLocus _ _ (f i) hfp : Set (T i.succ))) ∧
              (B i.succ : Set (T i.succ)) =
                (f i) ⁻¹' (B i.castSucc : Set (T i.castSucc)) ∪
                  ⋃ j : Fin (m i), Set.range (s i j) ∧
              Smooth ((f i) ∣_ (⟨(B i.castSucc : Set (T i.castSucc))ᶜ,
                (B i.castSucc).isClosed.isOpen_compl⟩ : (T i.castSucc).Opens)) ∧
              (∀ g : J, (τ i.succ g).hom '' (⋃ j : Fin (m i), Set.range (s i j)) =
                ⋃ j : Fin (m i), Set.range (s i j)) ∧
              (∀ (y : T i.castSucc) (x : (f i).fiber y),
                (¬ ∃ V : ((f i).fiber y).Opens, x ∈ V ∧
                  Smooth (V.ι ≫ (f i).fiberToSpecResidueField y)) →
                Function.Surjective
                  (((f i).fiberToSpecResidueField y).residueFieldMap x).hom ∧
                Nat.card {z : ((f i).fiber y).reducedNormalization //
                  ((f i).fiber y).fromReducedNormalization z = x} = 2 ∧
                ∀ z : ((f i).fiber y).reducedNormalization,
                  ((f i).fiber y).fromReducedNormalization z = x →
                  Function.Surjective
                    ((((f i).fiber y).fromReducedNormalization ≫
                      (f i).fiberToSpecResidueField y).residueFieldMap z).hom)) ∧
          a ⁻¹' (Z : Set X) ⊆ (B (Fin.last d) : Set (T (Fin.last d))) ∧
          ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U) ∧ Surjective (a ∣_ U) ∧
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
              Set.range x ⊆ (U : Set X) →
              (∃ t : Spec (.of Ω) ⟶ T (Fin.last d), t ≫ a = x) ∧
              ∀ t₁ t₂ : Spec (.of Ω) ⟶ T (Fin.last d),
                t₁ ≫ a = x → t₂ ≫ a = x →
                ∃ g : ρ.ker, t₁ ≫ (τ (Fin.last d) g.val).hom = t₂ := by
  sorry

end AlgebraicGeometry
