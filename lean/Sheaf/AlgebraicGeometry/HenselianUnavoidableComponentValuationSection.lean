/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Integral
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.FieldTheory.Normal.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Absolute valuation sections through unavoidable components

Source: Stacks Project, Tag 05GU, together with Anantharaman, Lemma 4.2.1,
printed pp. 55–56, and henselian integral permanence, Tag 092X.
(blueprint: lem-sfb-henselian-unavoidable-component-valuation-section)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical generic test of the integral closure, induced by its inclusion in the
ambient field. Source: Stacks Project, Algebra, integral closure, Tags 00GO and 0308.
(blueprint: lem-sfb-henselian-unavoidable-component-valuation-section) -/
noncomputable def integralClosureGenericTest (R K Ω : Type u) [CommRing R] [Field K] [Field Ω]
    [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω)))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R Ω) Ω))) (by
    dsimp only [Over.mk_hom, Over.map_obj_hom]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact IsScalarTower.algebraMap_apply R K Ω r)

/-- An unavoidable generic connected component admits absolute valuation sections in
all its geometric connected components. Openness of a subfunctor is expressed on every
scheme test by the image criterion for factorization through an open subscheme.

Source: Stacks Project, Tag 05GU; Anantharaman, Lemma 4.2.1, printed pp. 55–56;
Tags 092X, 09IG, 00PD, 081I, 03N0, 04L7, 09GU and 0BR4.
(blueprint: lem-sfb-henselian-unavoidable-component-valuation-section)

Proof (the twelve steps of the DAG node):
1. The integral-closure lemma applied to $R\subset K\subset\Omega$ makes $B$ a domain integral
   over $R$, integrally closed in $\Omega$, with fraction field $\Omega$. Its only idempotents are
   $0,1$: $e(e-1)=0$ in a domain. The henselian-permanence lemma therefore makes $B$ henselian
   local and $R\to B$ local. In particular its closed point lies over $s$.
   Uses:
   - lem-weil-pbc-integral-closure-algebraic-extension-normal
   - lem-trf-integral-component-henselian-permanence
2. For every finite subextension $E/K$ of $\Omega/K$, denote the integral closure of $R$ in $E$ by
   $A_E$. The integral-closure lemma gives its fraction field $E$ and normality. The
   finite-extension Dedekind lemma makes $A_E$ Noetherian of dimension one. Henselian permanence
   makes this domain local, with $R\to A_E$ local; hence the normal-local-dimension-one criterion
   makes $A_E$ a DVR. Here a DVR is Noetherian because all its ideals are principal, and has
   dimension one by the DVR equivalences, so all hypotheses of the Dedekind lemma hold. These
   conclusions apply also to an abstract finite extension after choosing a $K$-embedding into
   $\Omega$.
   Uses:
   - lem-weil-pbc-integral-closure-algebraic-extension-normal
   - lem-sc-integral-closure-dedekind-surjective-fibres
   - lem-trf-integral-component-henselian-permanence
   - lem-sc-normal-dim1-dvr
   - def-sc-discrete-valuation-ring
3. For $a\in\Omega^\times$, $E=K(a)$ is finite because $a$ is algebraic. In the DVR $A_E$, write
   $a=b/c$ with $b,c\ne0$. Writing each as a unit times a power of a uniformizer gives $a=u t^n$
   with $n\in\mathbf Z$. If $n\ge0$ then $a\in A_E$; otherwise $a^{-1}\in A_E$. Since
   $A_E\subseteq B$, this proves the displayed valuation-ring condition. Together with step 1 it
   proves the entire ring clause.
   Uses:
   - lem-weil-pbc-dvr-unit-times-uniformizer-power
4. Apply the finite-normalization model lemma to the given fpqc presentation of $X$. Its base $R$
   is Noetherian of dimension one as in step 2. It is normal: if a fraction $a$ has negative
   uniformizer exponent, then $a^{-1}$ belongs to the maximal ideal; dividing a monic integral
   equation of degree $d$ by $a^d$ would give $1$ plus an element of that ideal equal to zero.
   Thus every integral fraction has nonnegative exponent and belongs to $R$. Obtain a finite
   extension $L/K$ and a flat separated scheme $Y$ of finite presentation representing
   $X_{\operatorname{Spec}A_L}$, with $\operatorname{Spec}A_L\to S$ fpqc. Embed $L$ into $\Omega$
   by the algebraic-extension embedding lemma. Step 2 makes $A=A_L$ a henselian DVR with fraction
   field $L$. Put $S'=\operatorname{Spec}A$, with closed point $s'$. Finite presentation implies
   finite type from its affine presentations, so $Y$ is Noetherian by the
   finite-type-over-Noetherian lemma. No finiteness of $A$ as an $R$-module is used.
   Uses:
   - lem-sfb-fpqc-finite-presentation-normalization-model
   - lem-weil-pbc-algebraic-extension-embeds-algebraically-closed
   - def-sc-discrete-valuation-ring
   - lem-weil-pbc-finite-type-over-noetherian
   - lem-weil-pbc-dvr-unit-times-uniformizer-power
5. The finite-type $K$-scheme $X_\eta$ is Noetherian and has finitely many irreducible components,
   which cover it. Partition these finitely many components by the equivalence relation generated
   by nonempty intersection. Each class has connected union; different classes give disjoint
   closed unions. Thus those unions are exactly the connected components, and each is clopen. In
   particular $C$ is a nonempty clopen finite-type $K$-scheme, with finitely many irreducible
   components. Its pullback $C_L$ is clopen in $Y_L=X_\eta\times_K L$ and is a closed subscheme
   there. The immersion $j:C_L\to Y$ is quasi-compact: for each affine
   $V=\operatorname{Spec}H\subset Y$, $V_L=D(\pi)=\operatorname{Spec}H[1/\pi]$ for a uniformizer
   $\pi\in R$, and $j^{-1}(V)$ is closed in that affine. This argument does not put any Noetherian
   hypothesis on the original fpqc chart.
   Uses:
   - lem-weil-pbc-finite-type-over-noetherian
   - lem-weil-pbc-noetherian-finitely-many-components
   - lem-sc-irreducible-components-cover
   - def-weil-closed-immersion
6. Let $Z\hookrightarrow Y$ be the scheme-theoretic image of $j$. The quasi-compact image
   interface gives $|Z|=\overline{|C_L|}$ and the factorization through $Z$. Formation of this
   image commutes with flat base change. In particular $Z_L=C_L$, since restriction to the generic
   fibre is flat and the image of a closed immersion is that closed subscheme. On $S''=S'\times_S
   S'$ the two pullbacks of $Y$ represent the same sheaf $X_{S''}$, and the two pullbacks of $C_L$
   both identify with $C\times_S S''$. The projections $S''\to S'$ are flat, being base changes of
   the fpqc map $S'\to S$. Consequently the two pullbacks of $Z$ agree as closed subschemes under
   that identification. The complements $V=Y\setminus |Z|$ therefore agree on the overlap as well.
   Uses:
   - lemma-nagata-scheme-image-ideal-qc
   - lem-sfb-scheme-image-flat-base-change
   - def-weil-pbc-fpqc-covering
7. These compatible complements give an open subfunctor $U\subset X$. Explicitly, for a scheme
   test $H\to X$, use the fpqc cover $H'=H\times_S S'\to H$ and the map $H'\to Y$. The inverse
   image of $V$ is an open of $H'$ whose two pullbacks agree. Open-subscheme fpqc descent gives a
   unique open $H_U\subset H$. Uniqueness makes this construction compatible with every change of
   test scheme, so it defines the required open subfunctor. The fpqc sheaf equalizer condition
   identifies its pullback to $S'$ with $V$. By $Z_L=C_L$, its generic fibre is $X_\eta\setminus
   C$. If $Z_{s'}$ were empty, $V_{s'}=Y_{s'}$ and fpqc descent would give $U_s=X_s$. That would
   violate unavoidability, because its generic fibre is the union of all connected components
   other than the nonempty component $C$. Hence $Z_{s'}\ne\varnothing$.
   Uses:
   - lem-weil-pbc-open-subscheme-fpqc-descent
   - def-weil-pbc-fpqc-covering
8. The Noetherian scheme $C_L$ has finitely many irreducible components $F_1,\ldots,F_n$, covering
   it. Thus $|Z|=\bigcup_i\overline{F_i}$, a finite union of closures inside $Y$. Some
   $\overline{F_i}$ meets $Y_{s'}$. Give that closed subset its reduced induced structure $W$. It
   is nonempty, reduced and irreducible, hence integral. It dominates $S'$ because $F_i\subset
   Y_L$ is nonempty. It is finite type over $A$: on a finite affine cover of $Y$, its coordinate
   rings are quotients of the finite-type coordinate algebras of $Y$. Its generic fibre is the
   reduced structure on $F_i$, in particular is nonempty and maps into the open subscheme
   $C_L\subset Y_L$. The image containment here gives factorization through an open, without any
   assertion of factorization through a closed subscheme from point containment alone. Also
   $W_{s'}\ne\varnothing$ by construction.
   Uses:
   - lem-weil-pbc-noetherian-finitely-many-components
   - lem-sc-irreducible-components-cover
   - lem-weil-pbc-reduced-induced-closed-subscheme
   - def-pc-integral-scheme
9. Apply dense-generic trait selection over the DVR $A$ to the integral finite-type dominant
   scheme $W$, its nonempty special fibre, and the nonempty open $W_L\subset W_L$. It supplies a
   DVR $V$, a local injection $A\to V$, finite fraction-field extension $E/L$, and an $S'$-map
   $\operatorname{Spec}V\to W\to Y$. Its generic restriction lies in $C_L$, and its closed point
   is in $Y_{s'}$. Extend the fixed embedding $L\hookrightarrow\Omega$ to $E\hookrightarrow\Omega$
   by the algebraic-extension embedding lemma. Since $E/L$ and $L/K$ are finite, $E/K$ is finite
   (products of finite spanning sets span the tower).
   Uses:
   - lem-sfb-dense-generic-trait-selection
   - lem-weil-pbc-algebraic-extension-embeds-algebraically-closed
10. Under that embedding, $V$ equals $A_E$. Indeed every element of $A_E$ is integral over
   $R\subset V$, so belongs to $V$: otherwise its inverse is in the maximal ideal of $V$ by the
   uniformizer-power formula, and division of a monic integral equation by its leading power gives
   $1$ plus an element of that maximal ideal equal to zero. For a uniformizer $t$ of $A_E$, write
   $\pi=u t^e$ in $A_E$ for the uniformizer $\pi\in R$. Since $R\to A_E$ is local, $e>0$. Since
   $R\to A\to V$ is local, $\pi$ is not a unit of $V$; $u$ is a unit there, so $t$ is not a unit
   there. Every $x\in E^\times$ has form $v t^n$ with $v\in A_E^\times$ and $n\in\mathbf Z$, by
   writing its numerator and denominator as uniformizer powers. If $x\in V$ and $n<0$, then
   $t^{-1}=v^{-1}x t^{-n-1}\in V$, a contradiction. Thus $V\subset A_E$, proving equality. Pull
   the section of $X$ just obtained back along
   $\operatorname{Spec}B\to\operatorname{Spec}A_E=\operatorname{Spec}V$ to obtain $x_0\in X(B)$.
   Its generic value $z_0\in C_\Omega$ lies in a connected component $D_0$. The underlying point
   $p\in C$ has residue field $F=\kappa(p)$ embedded in $E$, so $F/K$ is finite.
   Uses:
   - def-sc-discrete-valuation-ring
   - lem-weil-pbc-dvr-unit-times-uniformizer-power
11. Fix the prescribed component $D\subset C_\Omega$. By the geometric-component-surjectivity
   lemma applied to the nonempty connected finite-type $K$-scheme $C$, $D\to C$ is surjective:
   apply the lemma to $(C_\Omega)_{\mathrm{red}}$, whose reduction map is the identity on
   underlying spaces. Step 5 supplies its finite-irreducible-component hypothesis. There is
   consequently a point $z\in D$ over $p$. The fibre above $p$ is
   $\operatorname{Spec}(F\otimes_K\Omega)$ by the affine fibre-product lemma. This algebra is
   finite-dimensional over $\Omega$; its residue fields are finite over $\Omega$ (a
   finite-dimensional domain is a field), and so are $\Omega$ by algebraic closedness. Hence $z$
   is an $\Omega$-point, specified by an embedding $\beta:F\to\Omega$. Write $\alpha:F\to\Omega$
   for the embedding specifying $z_0$.
   Uses:
   - lem-sfb-geometric-connected-component-surjective
   - def-weil-pbc-scheme-reduction
   - lem-weil-pbc-fibre-product-affine-spectra
12. View $\Omega$ as an algebraic extension of $F$ through $\alpha$. Extend $\beta$ to a field map
   $\tau:\Omega\to\Omega$ using the algebraic-extension embedding lemma. It fixes $K$. Since
   $\Omega/K$ is algebraic normal, the normal-embeddings lemma, with the identity embedding as its
   fixed embedding, says that $\tau$ is a $K$-automorphism. It satisfies $\tau\alpha=\beta$.
   Integrality over $R$ is preserved by $\tau$ and by $\tau^{-1}$, by applying them to monic
   equations, so $\tau(B)=B$. Precompose $x_0:\operatorname{Spec}B\to X$ with
   $\operatorname{Spec}(\tau|_B)$. On the generic fibre the resulting $\Omega$-point corresponds
   to $\tau\alpha=\beta$, hence is exactly $z$ and lies in $D$. This is the desired $x\in X(B)$.
   The unique closed point of $\operatorname{Spec}B$ lies above $s$ by step 1, so the closed value
   is in $X_s$.
   Uses:
   - lem-weil-pbc-algebraic-extension-embeds-algebraically-closed
   - lem-sfb-normal-embeddings-automorphism-transitive
No group structure or smoothness is used. -/
theorem henselian_unavoidable_component_valuation_section
    (R K Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosure K Ω]
    (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (max u v))
    (hX : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) X)
    (hchart : ∃ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)),
      Presieve.singleton t ∈ Scheme.fpqcPrecoverage (Spec (CommRingCat.of R)) ∧
      ∃ Y : Over T, Nonempty (((Over.map t).op ⋙ X).RepresentableBy Y) ∧
        IsSeparated Y.hom ∧ Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
        QuasiCompact Y.hom ∧ QuasiSeparated Y.hom)
    (Xη : Over (Spec (CommRingCat.of K)))
    (eη : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).op ⋙ X).RepresentableBy Xη)
    (Xs : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (es : ((Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).op ⋙ X).RepresentableBy
      Xs)
    (hη : LocallyOfFiniteType Xη.hom ∧ QuasiCompact Xη.hom)
    (hs : LocallyOfFiniteType Xs.hom ∧ QuasiCompact Xs.hom)
    (C : Xη.left.Opens) (hC : ∃ p : Xη.left, (C : Set Xη.left) = connectedComponent p)
    (hunavoidable : ∀ U : Subfunctor X,
      (∀ (H : Over (Spec (CommRingCat.of R))) (x : X.obj (op H)),
        ∃ W : H.left.Opens, ∀ (Z : Over (Spec (CommRingCat.of R))) (f : Z ⟶ H),
          X.map f.op x ∈ U.obj (op Z) ↔ Set.range f.left ⊆ (W : Set H.left)) →
      (∀ H : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R))),
        U.obj (op ((Over.map (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue R)))).obj H)) = Set.univ) →
      (∃ W : Xη.left.Opens,
        (∀ p ∈ W, connectedComponent p ⊆ (W : Set Xη.left)) ∧
        ∀ (H : Over (Spec (CommRingCat.of K))) (f : H ⟶ Xη),
          eη.homEquiv f ∈ U.obj (op ((Over.map (Spec.map
            (CommRingCat.ofHom (algebraMap R K)))).obj H)) ↔
              Set.range f.left ⊆ (W : Set Xη.left)) →
      ∀ (H : Over (Spec (CommRingCat.of K))) (f : H ⟶ Xη),
        Set.range f.left ⊆ (C : Set Xη.left) →
          eη.homEquiv f ∈ U.obj (op ((Over.map (Spec.map
            (CommRingCat.ofHom (algebraMap R K)))).obj H))) :
    ∃ (_ : IsLocalRing (integralClosure R Ω)),
      IsFractionRing (integralClosure R Ω) Ω ∧
      (∀ a : Ω, a ≠ 0 → a ∈ integralClosure R Ω ∨ a⁻¹ ∈ integralClosure R Ω) ∧
      ∀ (D : Set (pullback (C := Scheme.{u}) (C.ι ≫ Xη.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))))
        (_ : ∃ p : pullback (C := Scheme.{u}) (C.ι ≫ Xη.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))), D = connectedComponent p),
        ∃ x : X.obj (op (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap R (integralClosure R Ω)))))),
          ∃ (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ Xη)
            (z : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶
              Over.mk (pullback.snd (C.ι ≫ Xη.hom)
                (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))),
            z.left ≫ pullback.fst (C.ι ≫ Xη.hom)
              (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≫ C.ι = g.left ∧
            eη.homEquiv g = X.map (integralClosureGenericTest R K Ω).op x ∧
            z.left (IsLocalRing.closedPoint Ω) ∈ D ∧
            (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω))))
              (IsLocalRing.closedPoint (integralClosure R Ω)) = IsLocalRing.closedPoint R := by
  sorry

end AlgebraicGeometry
