module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Semilinear Galois domination of an alteration

Source: de Jong, Families of curves and alterations (1997), Sections 3.2, 3.8 and 5.3,
pp. 605, 608 and 613; ILO, Expose X, Theorem 3.4, Step 4 and Remark 3.3.2.
(blueprint: lem-sfb-semilinear-galois-alteration-domination).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Every integral alteration is dominated by a normal projective semilinear Galois alteration.
The field algebras below are the canonical generic-stalk algebras, not chosen embeddings.
The intermediate field `K` is characterized as the fixed field of the entire kernel of `ρ`.
Inverses in the scalar compatibility account for the contravariance of `Spec`.

Source: de Jong (1997), Sections 3.2, 3.8 and Situation 5.3, pp. 605, 608 and 613;
ILO, Expose X, Theorem 3.4 Step 4 and Remark 3.3.2.
(blueprint: lem-sfb-semilinear-galois-alteration-domination).

Proof (the fifteen steps of the node):

1. Put $K=k(S)$ and $L=k(T)$, with the inclusion induced by $r$. Since $r$ is finite over a dense
   open, $L/K$ is finite. Write $A_h=(h^{-1})^*$ for the induced left action of $H$ on $K$, and
   let $H_0$ be its image in $\operatorname{Aut}(K)$. This is a finite faithful group of field
   automorphisms. Put $F=K^{H_0}=K^H$. Apply the finite-field-action theorem to $H_0$: $K/F$ is
   finite Galois. Hence $L/F$ is finite: if $(u_i)$ spans $K/F$ and $(v_j)$ spans $L/K$, then
   $(u_iv_j)$ spans $L/F$. Passing to $H_0$ here does not replace the original group $H$ in the
   conclusion.
   Uses: lem-wf-finite-field-action-fixed-degree.

2. Choose a finite normal extension $M/F$ containing $L$ by finite normal closure. If $L/K$ is
   separable, make the following more specific choice instead: separability in the tower
   $F\subseteq K\subseteq L$ gives $L/F$ separable, and the finite-Galois-receiving lemma for the
   single extension $L/F$ gives a finite Galois $M/F$ containing a copy of $L$. Identify $L$ with
   that copy. In either choice $M/K$ is finite, since an $F$-spanning set also spans over $K$, and
   it is normal by normality over intermediate fields. No separability is assumed for the first
   choice.
   Uses: lem-weil-pbc-finite-extension-in-finite-normal-extension, lem-zl-separable-permanence,
   lem-weil-pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-normal-extension-
   normal-over-intermediate.

3. Define $J=\{(h,\sigma)\in H\times\operatorname{Aut}_F(M):\sigma|_K=A_h\}$ with componentwise
   multiplication, and let $\rho(h,\sigma)=h$. The defining condition is preserved by
   multiplication and inverses. For each $h$, apply normal-intermediate-isomorphism lifting to the
   normal extension $M/F$ and the $F$-isomorphism $A_h:K\to K$. This supplies $\sigma$, so $\rho$
   is surjective. The automorphisms of $M/F$ form a subset of the finite set of $F$-embeddings
   $M\to M$, so $J$ is finite. Finally $N=\ker\rho$ identifies with the whole group
   $\operatorname{Aut}_K(M)$, by $\sigma\mapsto(1,\sigma)$. Keeping pairs, rather than only their
   second coordinates, retains every element of a possibly nonfaithful $H$.
   Uses: lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-finite-extension-finitely-
   many-embeddings.

4. Let $u:B\to S$ be the normalization of $S$ in $M$. The normalization-in-residue-field-extension
   theorem, applied to the generic point of $S$ and $M/K$, gives that $B$ is normal integral and
   $k(B)=M$, with the canonical $\operatorname{Spec}M\to B$ its generic-point inclusion. It is the
   affine integral-closure construction of the cited definition. Finiteness of normalization in a
   finite function-field extension applies because $S$ is integral of finite type over the field
   $k$; hence $u$ is finite. The scheme $\operatorname{Spec}k$ is Noetherian (a field has only the
   ideals $0$ and $k$). Thus finite-over-projective over this affine base makes $B$ H-projective
   over $k$. In particular $B$ is of finite type over $k$.
   Uses: def-fin-normalization-extension, lem-weil-pbc-normalization-in-residue-field-extension,
   lem-fin-normalization-extension-finite, lem-fin-finite-over-projective, lem-kun-projective-
   implies-proper, def-weil-proper-morphism.

5. The $J$-action on the generic point $\operatorname{Spec}M$ is
   $a_j=\operatorname{Spec}(\sigma_j^{-1})$; it lies over the geometric action $h_j=\rho(j)$ on
   $S$. It extends to $B$ directly on integral-closure charts: the isomorphism on the base rings
   and $\sigma_j^{-1}$ carry integral elements to integral elements, since applying them to a
   monic equation again gives a monic equation. The same assertion for the inverse gives a ring
   isomorphism. These isomorphisms commute with localization, so glue by the normalization
   construction. Their composites agree on each chart with the specified field composites, hence
   give the group law. We have $u\circ a_j=h_j\circ u$, and on $k$ this is precisely the
   prescribed action through $\rho$. This argument needs no action on $T$.
   Uses: def-fin-normalization-extension.

6. The scheme $T$ is integral, separated and of finite type over $k$: properness of $r$ and
   projectivity of $S/k$ give properness of $T/k$. Apply integral Chow over $k$ to obtain an
   integral finite-type $Y$, a proper surjection $\pi:Y\to T$ which is an isomorphism over a
   nonempty open $U\subseteq T$, and an immersion $i:Y\to\mathbf P^n_k$. The composite $Y\to
   T\to\operatorname{Spec}k$ is proper. The target $\mathbf P^n_k$ is separated; proper-over-
   separated makes $i$ proper. Proper-immersion-closed then makes $i$ a closed immersion. Thus $Y$
   is H-projective over $k$. Set $v=r\pi:Y\to S$. The generic fibre $T_K$ is
   $\operatorname{Spec}L$, because $r$ is finite over a dense open and $T$ is integral. Its only
   point is the generic point of $T$ and lies in $U$. Consequently $Y_K\cong\operatorname{Spec}L$
   as well. Let $f:\operatorname{Spec}M\to Y$ be the map induced by $L\hookrightarrow M$.
   Uses: lem-kun-projective-implies-proper, lem-weil-pbc-proper-composition, def-weil-proper-
   morphism, lem-weil-pbc-integral-chow-relatively-ample, lem-weil-pbc-projective-space-proj-
   separated, lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed.

7. For $j\in J$ let $Y_j$ be the same abstract scheme $Y$ with structural map $h_jv:Y_j\to S$, and
   with $k$-structure induced from this map. This $k$-structure is the corresponding scalar twist
   of $Y/k$ along the automorphism of $k$ induced by $h_j$. Hence $Y_j/k$ is H-projective, by base
   change of its projective embedding along that automorphism. Form $P=B\times_S\prod_{j\in
   J}Y_j$. It is projective over $k$: first take the product over $k$ of the closed projective
   embeddings of $B$ and the $Y_j$, and iterate Segre. The equalities of their maps to $S$ cut out
   $P$ as a closed subscheme of this product. Indeed each equality is a pullback of the closed
   diagonal of the separated $k$-scheme $S$, and their finite intersection is an iterated closed
   immersion. Closed immersions are stable under base change and composition. Thus $P$ has an
   absolute closed projective embedding, whether or not $P$ is integral.
   Uses: lem-pc-projective-base-change, def-pc-fibre-product, lem-chow-segre, def-weil-proper-
   morphism, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-closed-immersion-products.

8. For $g\in J$ define the action on $P$ by $b\mapsto a_g(b)$ and $y_j\mapsto y'_{gj}=y_j$. This
   is a morphism of schemes: $h_{gj}v(y_j)=h_g(h_jv(y_j))=h_gu(b)=u(a_gb)$ is exactly the common-
   base equality required by the fibre product. On $k$ it is semilinear through $h_g$. Reindexing
   twice gives $(gg')j$, so the identity, product and inverse laws follow on all projections from
   the fibre-product universal property. Define $q:\operatorname{Spec}M\to P$ by the generic
   inclusion into $B$ and components $f_j=f\circ a_{j^{-1}}$ into $Y_j$. Since $vf$ is the generic
   map to $S$, $h_jvf_j$ equals this generic map. Moreover $f_{gj}\circ a_g=f\circ
   a_{j^{-1}g^{-1}}\circ a_g=f_j$, and the $B$-component is equivariant. Thus $q$ is
   $J$-equivariant.
   Uses: def-pc-fibre-product.

9. Let $C$ be the reduced induced closed subscheme on $\overline{\{q(*)\}}\subseteq P$. It exists
   by the reduced-closed-subscheme theorem. This closure is irreducible, so $C$ is integral. Its
   function field and generic fibre can be read without choosing a component: over $K$ the
   $B$-factor is $\operatorname{Spec}M$ and each $Y_j$-factor is a spectrum of a finite field
   extension of $K$ (the twist of $L/K$). Thus the coordinate ring of $P_K$ is a tensor product of
   finitely many finite-dimensional $K$-algebras and is finite-dimensional. The map to $M$ induced
   by $q$ is surjective because its $M$-factor is the identity. Its kernel is maximal, and the
   corresponding closed point has residue field exactly $M$. Closure and reduction restrict to
   this closed point on the generic fibre: on an affine chart the closure ideal is the kernel of
   the map to $M$, and localization at $K$ localizes this kernel. Hence $C_K=\operatorname{Spec}M$
   and $k(C)=M$. As a closed subscheme of $P$, $C$ is H-projective over $k$.
   Uses: lem-weil-pbc-reduced-induced-closed-subscheme, def-pc-integral-scheme, def-weil-closed-
   immersion, def-sc-function-field.

10. The action on $P$ preserves $q(*)$ as a point, by equivariance of $q$, and therefore preserves
   its closure. Each ambient automorphism restricts uniquely to $C$, by uniqueness of the reduced
   induced closed structure. Uniqueness also shows that these restrictions obey the group law. The
   projection $C\to B\to S$ is consequently equivariant. This does not assert that $Y$ or $T$
   carries any action.
   Uses: lem-weil-pbc-reduced-induced-closed-subscheme.

11. Let $\nu:W\to C$ be the normalization in $k(C)=M$. The normalization theorem gives a finite
   surjective birational map; thus $W$ is integral and $k(W)=M$. Its local rings are normal: on an
   affine domain chart $A$ of $C$, the normalization ring is the integral closure of $A$ in
   $\operatorname{Frac}(A)=M$, a normal domain by the integral-closure lemma, and its
   localizations are normal domains by localization of normal domains. Finite-over-projective,
   applied with affine Noetherian base $\operatorname{Spec}k$, makes $W/k$ H-projective. In
   particular $W$ is of finite type and proper over $k$. The finite map $\nu$ restricts on the
   generic fibre to the identity of $\operatorname{Spec}M$: over an affine open
   $\operatorname{Spec}A_0\subseteq S$, the generic fibre is the localization at
   $A_0\setminus\{0\}$, integral closure commutes with localization (the localization clause of
   the normalization-in-an-extension definition, whose case $L=K$ is this normalization), and on
   the generic fibre the chart ring is $M$, which is already integrally closed in $M$. Hence
   $W_K=\operatorname{Spec}M$.
   Uses: def-sc-normalization, def-fin-normalization-extension, lem-sc-normalization-exists, lem-
   weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-localization-normal-domain,
   lem-fin-finite-over-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism.

12. For $g\in J$, apply dominant lifting through absolute normalization to the dominant map
   $W\xrightarrow{\nu}C\xrightarrow{g}C$. Its source $W$ is integral with integrally closed local
   rings, so it lifts uniquely to $\widetilde g:W\to W$. The identity lift is the identity; the
   composite of two lifts lies over the corresponding product on $C$, so uniqueness proves the
   product law. Lifting $g^{-1}$ gives its inverse. Therefore this is a $J$-action. The
   normalization map is equivariant, and so is $b:W\to C\to B\to S$. On generic fields this is
   precisely the original action on $M$ (normalization is birational), and its scalar action on
   $k$ is the one through $\rho$.
   Uses: lem-sbc-normalization-dominant-lift.

13. Choose an absolute closed embedding $i_W:W\hookrightarrow\mathbf P^n_k$. The map $(b,i_W):W\to
   S\times_k\mathbf P^n_k=\mathbf P^n_S$ is a closed immersion: its graph $W\to S\times_k W$ is
   the pullback of the closed diagonal of the separated scheme $S/k$ along $(s,w)\mapsto(s,b(w))$;
   compose it with $\mathrm{id}_S\times i_W$. Both maps are closed immersions by base change and
   composition. This proves that $b$ is H-projective in the required global convention, and hence
   proper. Its image is closed and contains the generic point of $S$, so it is surjective. The
   scheme $S$ is Noetherian by finite type over the Noetherian scheme $\operatorname{Spec}k$. Thus
   on a nonempty affine open $\operatorname{Spec}A\subseteq S$, $A$ is a Noetherian domain. The
   base change of $b$ is projective with generic fibre $\operatorname{Spec}M$, of dimension zero.
   Projective-generically-finite therefore makes it finite over a nonempty open of
   $\operatorname{Spec}A$, a dense open of integral $S$. Thus $b$ is an alteration.
   Uses: def-weil-proper-morphism, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-closed-
   immersion-products, lem-kun-projective-implies-proper, lem-weil-pbc-proper-closed-image, lem-
   weil-pbc-finite-type-over-noetherian, lem-pc-projective-base-change, lem-fin-projective-
   generically-finite.

14. Let $t$ be $W\to C\hookrightarrow P\to Y_1=Y\xrightarrow{\pi}T$. The defining common-base
   equality of the fibre product gives $rt=b$ as morphisms, so $t$ is an $S$-morphism. The
   equality holds on the whole scheme, not merely on its points or its generic field. No
   equivariance of $t$ is requested or used.
   Uses: def-pc-fibre-product.

15. We identified $k(W)=M$ and $N=\operatorname{Aut}_K(M)$, with that actual action on the generic
   field. Since $M/K$ is normal algebraic, the fixed-field theorem gives $M^N/K$ purely
   inseparable. It is finite: a $K$-linearly independent subset of the subfield $M^N$ is still
   independent in the finite-dimensional space $M$. This proves the invariant clause, including
   characteristic zero, where purely inseparable means equality. Also $k(W)/k(S)=M/K$ is finite.
   In the separable case, $M/F$ was chosen Galois. Every element's minimal polynomial over $K$
   divides its separable minimal polynomial over $F$, so $M/K$ is separable as well as normal and
   finite. The finite-Galois-fixed-field theorem then yields $M^{\operatorname{Aut}_K(M)}=K$, the
   required strengthened conclusion.
   Uses: lem-weil-pbc-normal-extension-fixed-field-purely-inseparable, lem-weil-pbc-finite-galois-
   fixed-field.
-/
theorem exists_semilinear_galois_alteration_domination
    (k : Type u) [Field k] (S T : Scheme.{u})
    (pS : S ⟶ Spec (.of k)) [IsIntegral S] [IsIntegral T]
    [IsHProjective pS] [LocallyOfFiniteType pS] [QuasiCompact pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σS : H →* Aut S)
    (hsemilinear : ∀ h : H, (σS h).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (r : T ⟶ S) [IsProper r] [Surjective r]
    (hrfinite : ∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (r ∣_ U)) :
    ∃ (J : Type (max u v)) (_ : Group J) (_ : Finite J) (ρ : J →* H),
      Function.Surjective ρ ∧
      ∃ (W : Scheme.{u}) (_ : IsIntegral W) (pW : W ⟶ Spec (.of k))
        (σW : J →* Aut W) (b : W ⟶ S) (_ : Surjective b) (t : W ⟶ T),
        IsHProjective pW ∧ LocallyOfFiniteType pW ∧ QuasiCompact pW ∧
        (∀ w : W, IsDomain (W.presheaf.stalk w) ∧
          IsIntegrallyClosed (W.presheaf.stalk w)) ∧
        b ≫ pS = pW ∧ t ≫ r = b ∧
        (∀ j : J, (σW j).hom ≫ pW =
          pW ≫ Spec.map (CommRingCat.ofHom (σk (ρ j⁻¹)).toRingHom)) ∧
        (∀ j : J, (σW j).hom ≫ b = b ≫ (σS (ρ j)).hom) ∧
        IsHProjective b ∧ IsProper b ∧
        (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (b ∣_ U)) ∧
        ∃ (A : Algebra S.functionField W.functionField),
          A = b.dominantFunctionFieldAlgebra ∧
          Module.Finite S.functionField W.functionField ∧
          ∃ K : IntermediateField S.functionField W.functionField,
            (∀ z : W.functionField, z ∈ K ↔
              ∀ j : ρ.ker, (Scheme.functionFieldAut (σW j.val)).hom z = z) ∧
            Module.Finite S.functionField K ∧ IsPurelyInseparable S.functionField K ∧
            (@Algebra.IsSeparable S.functionField T.functionField _ _
                r.dominantFunctionFieldAlgebra →
              Algebra.IsSeparable S.functionField W.functionField ∧ K = ⊥) := by
  sorry

end AlgebraicGeometry
