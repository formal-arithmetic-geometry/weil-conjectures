/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Pullback naturality of the canonical absolute-Frobenius trivialization

Source: Stacks Project, Tag 0F6W, `lemma-relative-frobenius-weakly-etale`, and the
DAG proof extending main-20261015 `lem-trf-absolute-frobenius-site.proof.md`
(blueprint: lem-pur-frobenius-trivialization-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The canonical absolute-Frobenius trivialization is natural under every scheme
map and is compatible with addition of Frobenius exponents.

Source: Stacks Project, Tag 0F6W, `lemma-relative-frobenius-weakly-etale`; the
pullback and iterate compatibility is the agent deduction recorded in the DAG
`lem-pur-frobenius-trivialization-pullback`, extending the last paragraph of
main-20261015 `lem-trf-absolute-frobenius-site.proof.md`
(blueprint: lem-pur-frobenius-trivialization-pullback).

Proof (the six steps of the DAG):

1. Write $B_h(V)=V\times_{S,h}T$ for base change along $h:T\to S$, with its projection to $T$, as
in [def-weil-proetale-inverse-image]. An equality of maps into a fibre product is checked on its
two projections, by [def-pc-fibre-product]. For any characteristic-$p$ scheme map $h:T\to S$, its
maps on sections satisfy $h^\sharp(a^{p^b})=h^\sharp(a)^{p^b}$; the underlying maps of both
Frobenii are identities. Thus $hF_T^b=F_S^bh$, using [def-weil-absolute-frobenius-scheme]. In
particular $r_{V/T}^{(b)}=(F_V^b,v)$ is defined. For $b=1$, the explicit geometric assertion in
the statement of [lem-trf-absolute-frobenius-site] is precisely Stacks Tag 0F6W: relative
Frobenius of a weakly etale object is an isomorphism. Every scheme over a characteristic-$p$
scheme is itself of characteristic $p$, since each structure ring map sends $p\cdot1=0$ to
$p\cdot1=0$. For general $b$, start with $r^{(0)}=\mathrm{id}$ under
$B_{\mathrm{id}}\cong\mathrm{id}$ and compose $r_V^{(b)}$ with $r_{B_{F_T^b}V}^{(1)}$. The latter
is an isomorphism because $B_{F_T^b}V$ remains a weakly etale site object by
[def-weil-proetale-inverse-image]. The base-change identification $B_{F_T}B_{F_T^b}\cong
B_{F_T^{b+1}}$ keeps the outermost projections; the composite has projections $F_V^{b+1}$ and $v$,
hence is exactly $r^{(b+1)}$. This proves by induction that every $r^{(b)}$ is an isomorphism. For
a site arrow $a:V\to V'$, both $B_{F_T^b}(a)r_V^{(b)}$ and $r_{V'}^{(b)}a$ have projections
$aF_V^b=F_{V'}^ba$ and $v$, so are equal. This is naturality in the site object, not a Cartesian
assertion about $u$.

2. Put $H_T^{(b)}=(F_T^b)_*$ on $A_T$-module sheaves. By the direct-image formula and module
adjunction of [def-weil-pbc-proetale-operations], its value on a sheaf $M$ at $V$ is
$M(B_{F_T^b}V)$. Restriction defines a natural isomorphism $d_{T,M}^{(b)}:H_T^{(b)}M\to M$, whose
component is $M(r_{V/T}^{(b)})$. Step 1 proves compatibility with every restriction, and
functoriality of $M$ proves naturality in $M$. These are $A_T$-linear maps: the
constant-coefficient structure map of [prop-weil-pbc-proetale-constant-ring-map] preserves each
constant section, as does restriction along $r$; locally every coefficient section is a constant,
so the actions agree. The same argument shows that the coefficient identifications for a composite
of scheme maps equal the composites of the coefficient identifications: their adjuncts send every
constant $a$ to the constant $a$, and the constant sheaf is the sheafification of the constant
presheaf [def-weil-pbc-proetale-site]. Let $P_T^{(b)}=(F_T^b)^*$ on module sheaves. Apply
[lem-weil-pbc-conjugate-iso-unit-equation] to $P_T^{(b)}\dashv H_T^{(b)}$ and the identity
adjunction, with right-adjoint isomorphism $(d_T^{(b)})^{-1}:\mathrm{id}\to H_T^{(b)}$. It gives
$s_T^{(b)}:P_T^{(b)}\xrightarrow{\sim}\mathrm{id}$, characterized by
$H_T^{(b)}(s_{T,N}^{(b)})\eta_N=(d_{T,N}^{(b)})^{-1}$. This fixes the direction of the adjoint
trivialization in the statement; for $b=0$ it is the identity under the identity-pullback
identification.

3. For a site object $v:V\to Y$, set $W=B_uV=V\times_YX$, with projections $\pi_V,\pi_X$. There is
a canonical isomorphism $j_V:B_{F_X^b}(B_uV)\xrightarrow{\sim}B_u(B_{F_Y^b}V)$: both fibre
products are identified with $V\times_{Y,F_Y^bu}X$. In test-scheme coordinates it takes
$((z,x_0),x)$, where $x_0=F_X^b(x)$, to $((z,u(x)),x)$. Its inverse inserts $x_0=F_X^b(x)$. The
two maps $j_Vr_{W/X}^{(b)}$ and $B_u(r_{V/Y}^{(b)})$ from $W$ to $B_uB_{F_Y^b}V$ have the same
$V$-projection $F_V^b\pi_V$ and $X$-projection $\pi_X$. Here $F_W^b$ has projections
$F_V^b\pi_V,F_X^b\pi_X$ by Step 1. The fibre-product uniqueness in [def-pc-fibre-product]
therefore gives $j_Vr_{W/X}^{(b)}=B_u(r_{V/Y}^{(b)})$. This equality holds on morphisms of
schemes, including their structure-sheaf maps. Using [def-weil-proetale-inverse-image],
restriction along $j_V^{-1}$ gives the canonical isomorphism
$e:u_*H_X^{(b)}\xrightarrow{\sim}H_Y^{(b)}u_*$. Contravariance of sections applied to the
displayed equality gives $d_Y^{(b)}u_*\circ e=u_*d_X^{(b)}$. All maps are module maps by Step 2.

4. Write $L=u^*$, $R=u_*$, $P=P_Y^{(b)}$, $Q=H_Y^{(b)}$, $S=P_X^{(b)}$, and $T=H_X^{(b)}$. The
composite adjunctions of [def-weil-pbc-composite-adjunction] are $LP\dashv QR$ and $SL\dashv RT$.
Applying [lem-weil-pbc-conjugate-iso-unit-equation] to $e:RT\cong QR$ gives the canonical
comparison $c^0:LP\cong SL$. To check that this is the ordinary pullback-composition
identification, use the inverse-image presentation in [def-weil-proetale-inverse-image]. For any
scheme map $h$ and site object $V$ on its target, the unit sends $m\in N(V)$ to the sheafified
colimit class indexed by $(V,\mathrm{id}_{B_hV})$, with value $m$. For composable $h,k$, the
iterated unit sends $m$ to the nested class indexed first by $(V,\mathrm{id}_{B_kV})$ and then by
$(B_kV,\mathrm{id}_{B_hB_kV})$. Under $B_hB_kV\cong B_{kh}V$, flattening the two identity indices
gives exactly the single class indexed by $(V,\mathrm{id}_{B_{kh}V})$. Thus the ordinary
inverse-image composition comparison carries the composite unit to the direct unit. Applying this
to the two factorizations $uF_X^b=F_Y^bu$ gives on right adjoints exactly restriction along
$j_V^{-1}$, namely $e$. The uniqueness assertion of [lem-weil-pbc-conjugate-iso-unit-equation]
therefore identifies its left-adjoint comparison with $c^0$. In the inverse-image/tensor
presentation of [def-weil-pbc-proetale-operations], the composition map inserts a unit, $m\otimes
a\mapsto(m\otimes1)\otimes a$; its inverse multiplies the middle scalar into $a$. Tensor balancing
proves the two composites are identities. Step 2 ensures that both routes use the same coefficient
map. Thus this is the termwise canonical map specifying the derived comparison in
[lem-weil-pbc-proetale-derived-pullback-composition]. To verify the required equality without
assuming a mate-pasting theorem, fix $N$ on $Y$, $M$ on $X$ and $a:LN\to M$, with adjunct
$a^\#:N\to RM$. Write $\eta^L,\eta^P,\eta^S$ for the units of $L\dashv R$, $P\dashv Q$, $S\dashv
T$, so $a^\#=R(a)\eta^L_N$. The first adjunct, under $LP\dashv QR$, is $QR(a\circ
Ls_{Y,N}^{(b)})Q(\eta^L_{PN})\eta^P_N=Q(a^\#)Q(s_{Y,N}^{(b)})\eta^P_N=Q(a^\#)(d_{Y,N}^{(b)})^{-1}=
(d_{Y,RM}^{(b)})^{-1}a^\#$:
the first equality uses naturality of $\eta^L$, the second the unit equation of Step 2, and the
third naturality of $d_Y^{-1}$. For the second adjunct, first use $SL\dashv RT$. The $S$-adjunct
of $a\circ s_{X,LN}^{(b)}$ is
$T(a)T(s_{X,LN}^{(b)})\eta^S_{LN}=T(a)(d_{X,LN}^{(b)})^{-1}=(d_{X,M}^{(b)})^{-1}a$. Applying the
$L$-adjunction gives $R((d_{X,M}^{(b)})^{-1})a^\#$. Finally precomposition with $c^0$ changes this
adjunct by $e_M$, by the defining unit equation for $c^0$ and naturality of $e$. Thus the second
adjunct is $e_M\circ R((d_X^{(b)})^{-1}_M)\circ a^\#$. Step 3, inverted, says $e_M
R((d_X^{(b)})^{-1}_M)=(d_Y^{(b)})^{-1}_{RM}$. These adjuncts agree. Taking $M=LN$ and
$a=\mathrm{id}$ and using injectivity of the adjunction bijection proves
$(s_X^{(b)}L)c^0=Ls_Y^{(b)}$ on module sheaves.

5. For $b_1,b_2\geq0$, identify $B_{F_T^{b_1}}B_{F_T^{b_2}}V$ with $B_{F_T^{b_1+b_2}}V$ by keeping
its $V$-projection and its last $T$-projection. The composite
$V\xrightarrow{r_V^{(b_2)}}B_{F_T^{b_2}}V$ followed by
$r_{B_{F_T^{b_2}}V}^{(b_1)}:B_{F_T^{b_2}}V\to B_{F_T^{b_1}}B_{F_T^{b_2}}V$
has these projections $F_V^{b_1+b_2}$ and $v$, so is $r_V^{(b_1+b_2)}$, by [def-pc-fibre-product]
and [def-weil-absolute-frobenius-scheme]. Applying contravariant sections proves, under
$H_T^{(b_1+b_2)}\cong H_T^{(b_2)}H_T^{(b_1)}$, the identity $d_T^{(b_1+b_2)}=d_T^{(b_2)}\circ
H_T^{(b_2)}d_T^{(b_1)}$. Inverting gives
$(d_T^{(b_1+b_2)})^{-1}=H_T^{(b_2)}((d_T^{(b_1)})^{-1})\circ(d_T^{(b_2)})^{-1}$. The Hom bijection
of the composite adjunction in [def-weil-pbc-composite-adjunction] is the composite of its two Hom
bijections. To compute this bijection explicitly, abbreviate $P_i=P_T^{(b_i)}$, $H_i=H_T^{(b_i)}$,
$s_i=s_T^{(b_i)}$, $d_i=d_T^{(b_i)}$, with unit $\eta_i:\mathrm{id}\to H_iP_i$. The adjunct of
$s_{2,N}\circ s_{1,P_2N}$ under $P_1P_2\dashv H_2H_1$ is
$H_2H_1(s_{2,N})H_2H_1(s_{1,P_2N})H_2(\eta_{1,P_2N})\eta_{2,N}=H_2H_1(s_{2,N})H_2(d_{1,P_2N}^{-1})
\eta_{2,N}=H_2(d_{1,N}^{-1})H_2(s_{2,N})\eta_{2,N}=H_2(d_{1,N}^{-1})d_{2,N}^{-1}$.
These equalities use respectively the unit equation for $s_1$, naturality of $d_1^{-1}$, and the
unit equation for $s_2$. Preceding this transformation by the canonical composition comparison,
whose unit normalization was checked in Step 4, identifies this with its adjunct under
$P_T^{(b_1+b_2)}\dashv H_T^{(b_1+b_2)}$. The unit equation and uniqueness in
[lem-weil-pbc-conjugate-iso-unit-equation] identify it with $s_T^{(b_1+b_2)}$. This proves the
addition law with the order of factors in the statement. The case where either exponent is zero
uses the identity adjunction and the identity $r^{(0)}$; induction with $b_1=1$ gives the $b$-fold
iterate.

6. All module pullbacks in Steps 2--5 are exact and their derived pullbacks are induced termwise
on complexes, by [def-weil-pbc-proetale-operations]; no scheme-flatness assumption is required,
since the coefficient maps are isomorphisms by [prop-weil-pbc-proetale-constant-ring-map]. Apply
every $s$ and $c^0$ termwise. They commute with differentials by naturality, and the equalities of
Steps 4 and 5 hold in each degree, hence on complexes. By
[lem-weil-pbc-localization-universal-property](2) these natural isomorphisms descend to the
unbounded derived categories, and by (3) the equalities remain equalities of natural
transformations there. The descended $s_T^{(b)}$ is exactly $\tau_T^{(b)}$ as defined in the item.
The descended comparisons are the canonical composition maps of
[lem-weil-pbc-proetale-derived-pullback-composition]: both are natural isomorphisms between the
same functors on $D(V_{\mathrm{proet}},A)$, and on a K-flat complex with flat terms both are the
class of the termwise canonical isomorphism of module pullbacks (for the descended map by
construction, for $c_{h,k}$ by its statement). Every complex $\mathcal G^\bullet$ receives a
quasi-isomorphism $\mathcal K^\bullet\to\mathcal G^\bullet$ from a K-flat complex with flat terms
[lem-pc-kflat-resolution], which is an isomorphism in the derived category; naturality of both
transformations along it shows that they agree at $\mathcal G^\bullet$. Thus Step 4 gives
$(\tau_X^{(b)}Lu^*)c_{u,b}=Lu^*\tau_Y^{(b)}$, and Step 5 gives exactly the asserted addition law.
Every site and its module category uses the fixed small-skeleton convention of
[def-weil-pbc-proetale-site], so the localizations and adjunctions are on the stated categories.
-/
theorem absoluteFrobenius_proEtale_trivialization_pullback
    (p : ℕ) (hp : Nat.Prime p) (A : Type u) [CommRing A] [Finite A] :
    ∃ (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
        𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n)),
      (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
        ∃ hV : (p : Γ(V.left, ⊤)) = 0,
          ((r X hX n).hom.app V).left ≫
              pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n) ∧
      ∃ (comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
          proEtaleConstantRingPullback A (f ≫ g) ≅
            proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f),
        (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
          (m : ((proEtaleConstantRingPushforward A f ⋙
            proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
          ((conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
            (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
              (Opposite.op V) m =
            M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m) ∧
        ∃ (tau : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
            proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) n) ≅ 𝟭 _),
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
            (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
            (m : M.val.obj (Opposite.op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).map ((tau X hX n).hom.app M)).val.app
                  (Opposite.op V) m = M.val.map ((r X hX n).inv.app V).op m) ∧
          (∀ (X Y : Scheme.{u}) (hX : X.IsCharacteristic p)
            (hY : Y.IsCharacteristic p) (u : X ⟶ Y) (b : ℕ),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) b ≫ u =
                u ≫ Y.iterateFrobenius hp (hY.2 ⊤) b,
              (proEtaleFrobeniusDerivedComp A u
                (Y.iterateFrobenius hp (hY.2 ⊤) b)
                (comp u (Y.iterateFrobenius hp (hY.2 ⊤) b))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (X.iterateFrobenius hp (hX.2 ⊤) b) u
                  (comp (X.iterateFrobenius hp (hX.2 ⊤) b) u)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A u)
                  (proEtaleFrobeniusDerivedIso A (tau X hX b)).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A (tau Y hY b)).hom
                (proEtaleConstantRingDerivedPullback A u) ≫
                (Functor.leftUnitor _).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (a b : ℕ),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) a ≫
                X.iterateFrobenius hp (hX.2 ⊤) b =
                  X.iterateFrobenius hp (hX.2 ⊤) (a + b),
              (proEtaleFrobeniusDerivedIso A (tau X hX (a + b))).hom =
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b)
                  (comp (X.iterateFrobenius hp (hX.2 ⊤) a)
                    (X.iterateFrobenius hp (hX.2 ⊤) b))).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A
                    (X.iterateFrobenius hp (hX.2 ⊤) b))
                  (proEtaleFrobeniusDerivedIso A (tau X hX a)).hom ≫
                (Functor.rightUnitor _).hom ≫
                (proEtaleFrobeniusDerivedIso A (tau X hX b)).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) 0 = 𝟙 X,
              r X hX 0 =
                (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm ≪≫
                  eqToIso (congrArg proEtaleBaseChange w.symm)) := by
  sorry

end AlgebraicGeometry.Scheme
