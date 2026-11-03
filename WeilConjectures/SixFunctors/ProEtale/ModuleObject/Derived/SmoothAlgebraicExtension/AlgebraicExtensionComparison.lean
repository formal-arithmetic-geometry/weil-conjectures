/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!
# Smooth purity comparisons under algebraic extension of the ground field

Source: latest blueprint, `part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/`
`sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md`,
Steps 1--4 and the general-field reduction (Houyi DM #1396).
(blueprint: lem-pur-smooth-algebraic-extension-comparison).

The compactification, the two right adjunctions, and the Cartesian representatives are
explicit. The exchange, unit, Tate and trace maps below are constructions from the published
maps. In particular no invertibility of a smooth orientation is an input.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.SmoothAlgebraicExtension

/-- Restrict the actual total derived pullback along any scheme morphism to bounded
constructible complexes. Source: Cartesian coefficients and the general-field reduction
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Dᵇc(Y)⟦Profinite.padicAlgClRingObj ell⟧ ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj ell⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ell) f)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme
      (Profinite.padicAlgClRingObj ell) f K.obj K.property)

/-- The scalar-unit multiplication comparison, lifted through the full inclusion.
Source: general-field reduction, the map e
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def unitIso (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Y)).IsMonoidal]
    [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X)).IsMonoidal] :
    (pull ell f).obj (𝟙_ _) ≅ 𝟙_ _ :=
  ObjectProperty.isoMk _ (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ell) f)

/-- Prime invertibility on a scheme over a field of different characteristic, with the
actual residue-field structural ring homomorphism. Source: Tate pullback in Step 1
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
@[instance_reducible]
def primeInvertible (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k ≠ ell)] (X : Over (Spec (.of k))) :
    ∀ x : X.left, Invertible (ell : X.left.residueField x) :=
  fun x ↦ (show IsUnit (ell : X.left.residueField x) by
    have h : IsUnit (ell : k) :=
      (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
        (Fact.out : ringChar k ≠ ell)).isUnit
    simpa using h.map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom).invertible

/-- Identify the closure presentation's ordered tensor powers with the actual upstream
Tate powers. Both recursions start at the regular unit and have the same scalar-extended
root line as their last factor. Source: Step 1, the actual Tate-object identification
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def closureLineIso (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    PurityTransport.Coefficient.line ell .closure X d ≅ tateTwistNat X ell d := by
  induction d with
  | zero => exact Iso.refl _
  | succ d ih => exact tensorIso ih (Iso.refl _)

/-- Apply degree-zero localization and the specified even shift to the tensor-power
identification. Source: Step 1, the actual shifted Tate complex
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def closureDerivedLineIso (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    PurityTransport.Coefficient.derivedLine ell .closure X d ≅
      (tateTwistDerived X ell d) ⟦2 * (d : ℤ)⟧ :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso (closureLineIso ell X d))

/-- The actual root-projection-normalized shifted Tate isomorphism. The chosen coordinates
are fixed by every finite root projection, scalar multiplication and the tensor-power
recursion; the zero power is the coefficient-unit comparison.
Source: Step 1, Cartesian Tate comparison
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def tateIso (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    (moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ell) f).obj
      ((tateTwistDerived Y ell d) ⟦2 * (d : ℤ)⟧) ≅
        (tateTwistDerived X ell d) ⟦2 * (d : ℤ)⟧ :=
  (moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ell) f).mapIso
      (closureDerivedLineIso ell Y d).symm ≪≫
    (Classical.choice (PurityTransport.linePullCoordinates_nonempty ell
      PurityTransport.Coefficient.closure f)).derived ell d ≪≫
    closureDerivedLineIso ell X d

section Compactification

variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (c : Compactification f.left)

/-- The normalized trace in the supplied compactification, transported along the existing
common-refinement comparison to the compactification defining smoothTrace.
Source: Steps 3--4, normalized trace of the chosen compactification
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def trace (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    (boundedConstructibleLowerShriekOfCompactification ell c).obj
      (boundedConstructibleTateTwist ell X d (2 * d)) ⟶
        𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ell⟧) :=
  (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ell c
    (compactificationOverField f)).hom.app _ ≫ smoothTrace ell f d

end Compactification

section Exchange

variable (ell : ℕ) [Fact ell.Prime]
  {k L : Type u} [Field k] [Field L]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  [Fact (ringChar L).Prime] [Fact (ringChar L ≠ ell)]
  {X Y : Over (Spec (.of k))} {X' Y' : Over (Spec (.of L))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {u : X'.left ⟶ X.left} {v : Y'.left ⟶ Y.left}
  (sq : IsPullback u f'.left f.left v) (c : Compactification f.left)

/-- Inclusion coordinates for the left side of compact-support exchange.
Source: Step 1, restrictions of the ordinary derived functors
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def exchangeSource :
    (boundedConstructibleLowerShriekOfCompactification ell c ⋙ pull ell v) ⋙
        (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (detSfCompactSupport (Profinite.padicAlgClRingObj ell) c ⋙
          detSfDerivedPullback (Profinite.padicAlgClRingObj ell) v) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ell c)
      (detSfDerivedPullback (Profinite.padicAlgClRingObj ell) v) ≪≫
    Functor.associator _ _ _

/-- Inclusion coordinates for the right side of compact-support exchange.
Source: Step 1, restrictions of the ordinary derived functors
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def exchangeTarget :
    (pull ell u ⋙ boundedConstructibleLowerShriekOfCompactification ell
      (c.ofIsPullback sq)) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (detSfDerivedPullback (Profinite.padicAlgClRingObj ell) u ⋙
          detSfCompactSupport (Profinite.padicAlgClRingObj ell) (c.ofIsPullback sq)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pull ell u)
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ell
        (c.ofIsPullback sq)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.associator _ _ _

/-- The specified proper-then-open compact-support exchange, restricted through the fully
faithful inclusion. This definition does not assume its invertibility.
Source: Step 1, det-prop-sf-cbc(b)
(blueprint: lem-pur-smooth-algebraic-extension-comparison). -/
def exchange :
    boundedConstructibleLowerShriekOfCompactification ell c ⋙ pull ell v ⟶
      pull ell u ⋙ boundedConstructibleLowerShriekOfCompactification ell
        (c.ofIsPullback sq) :=
  ((Functor.whiskeringRight _ _ _).obj (boundedConstructible _).ι).preimage
    ((exchangeSource ell (v := v) c).hom ≫
      Functor.whiskerLeft (boundedConstructible _).ι
        (((compactSupportCondensedFormalism (Profinite.padicAlgClRingObj ell)).shriekBaseChange
          c (c.ofIsPullback sq) (pullback.fst c.g v)
          (c.isPullback_i_ofIsPullback sq)
          (c.isPullback_g_ofIsPullback sq).flip).natTrans) ≫
      (exchangeTarget ell sq c).inv)

end Exchange

/-- Smooth purity comparisons for an algebraic extension of the ground field.

Source: latest blueprint, sk-thm-purity-transport.proof.md, Steps 1--4,
general-field reduction under Houyi DM #1396.
(blueprint: lem-pur-smooth-algebraic-extension-comparison).

1. The schemes in each row, including the compactification, are separated finite type over their
respective fields; after extension they remain so. A field is Noetherian (its only ideals are
$0$ and itself), so [pqf-lem-locnoeth-lft] and quasi-compactness imply both rows are Noetherian;
$\ell$ is invertible since $p\ne\ell$. Apply [det-prop-sf-cbc](b) to this compactification and
the arbitrary map $v$. This gives precisely $b:v^*F\simeq F_Lu^*$ specified in the statement.
Apply the same result to integral coefficients below. Its hypothesis is on the original
compactification; it does not require $Y_L$ to be finite type over $k$. Thus an infinite
algebraic extension, or a purely inseparable one, is included.

2. Construct the root-line pullback map by pulling the limit projections to each $\mu_{\ell^n}$
and using the canonical finite-root pullback maps. The source and target lines are locally free
of rank one by [lem-pur-twist-sheaf-locally-free]. On the pullback of its compatible-root
trivializing cover, this map sends the chosen compatible generator to that same generator, so is
the identity over the coefficient-unit comparison. It is consequently an isomorphism. The
balanced maps $R\otimes_{\mathbf Z}\mu_{\ell^n}\to\mu_{\ell^n}$ are isomorphisms
($R/\ell^n=\mathbf Z/\ell^n$); the level $n=0$ is zero and imposes no condition on the positive-
index limit. Thus this is also the comparison for the actual upstream limit of free internal
modules in [def-pur-condensed-tate-twists]. Take its $d$-fold tensor power, extend scalars and
shift to obtain $q:u^*T_f\simeq T_{f_L}$. All maps commute with the root projections, tensor
balancing and scalar-unit multiplication, so also identify the $w,u$ of [def-route-smooth-
orientation]. At $d=0$ they are the coefficient-unit maps.

3. Put $R_T=p_T^*\underline{\mathbf Z}_\ell$, let $r_T$ be derived reduction, and write
$P_f=r_XM$ for the actual shifted root tower whose integral realization is $M$. Use the
simultaneous reduction/pullback comparison $\nu_h:r_{T'}h^*\simeq h_\bullet^*r_T$ of [lem-sp-
reduction-derived-monoidal-tower]. Denote by $d_f:r_YF_0\simeq F_{f,\bullet}r_X$ the specified
whole-tower proper/open reduction mate of [lem-sp-current-composition-integral-edge]. These
comparisons intertwine the geometric compact-support exchanges. Indeed, expand $d_f$ as its
proper counit mate followed by the open-unit conjugate. Paste its pullback/scalar square with
the geometric square using [lem-weil-pbc-mate-pasting], first for the proper adjunction and then
for the open adjunction. The inner inverse-image squares commute by the balanced quotient map
$h^{-1}(x\otimes\bar a)\mapsto h^{-1}x\otimes\bar a$. The resulting two outer mates are
$$F_{f_L,\bullet}(\nu_u)\,d_{f_L}\,r_{Y_L}(b^0)=b^\bullet_{r_X(-)}\,v_\bullet^*(d_f)\,\nu_v.$$
This is a calculation in the derived diagram categories, before evaluation; $d_f$ is the
specified mate, so no detection of equality by its finite evaluations is used.

4. Let $t_0=\epsilon^0F_0(h_0)$ be the integral trace in [def-route-smooth-orientation], and let
$q_0:u^*M\simeq M_L$ be the integral root-line map of Step 2. The counit formula in [lem-sp-
current-composition-integral-edge] says, after the unit/root identifications, that
$$r_Y(t_0)=\tau_f\,d_{f,M}.$$ Here the cancellation of the reduction/limit counit with the
reduction of $h_0=L(a_f)$ is the triangle identity for $r\dashv L$; $a_f$ is the whole diagonal
orientation used in [lem-pur-tower-diagonal-finite-evaluation]. Apply the whole-tower trace
equality of [lem-pur-diagonal-tower-trace-geometric-change] and paste the exchange identity of
Step 3. It identifies the reductions of $$t_{0,L}F_{0,L}(q_0)b^0_M\quad\hbox{and}\quad
e_0v^*(t_0).$$ The reduction equivalence [sk-lem-sp-tower] on the Noetherian scheme $Y_L$ is
fully faithful, so these integral morphisms are equal. This uses one equality in the derived
tower category and full faithfulness, rather than separate finite-level equalities or commuting
arbitrary pullbacks with infinite limits.

5. For $S_T=-\otimes^L_{R_T}\Omega_T$, the scalar/pullback comparisons are the balanced maps of
[lem-sfb-internal-scalar-pullback-normalization]. The unrestricted direct-image square in [lem-
fix-condensed-scalar-exchange-coherence] applied to the proper part of the compactification
gives its scalar/geometric cube. For the open part, both scalar comparison and geometric
comparison are the conjugates of the restriction/pullback square: transpose, use the same
balanced map, and transpose back. By [lem-weil-pbc-mate-pasting] their cube commutes as well.
Composing these two cubes gives the compact-support cube for the maps of [def-sf-condensed-
scalar-compact-support-map]. This argument uses the unrestricted direct-image clause, not the
later compact-support clause with a common-field and cohomological-dimension hypothesis. Apply
$S$ to the integral equality in Step 4 and paste this cube and the root/unit squares from Step
2. Substitute the definition $t_f=uS(t_0)b_M^{-1}F(w^{-1})$. The scalar support maps are
invertible by [lem-sf-listed-compact-support-iso]; its finite-Tor condition holds by [lem-
integral-ctf-equals-bc]. Cancel these inverse comparisons. The resulting equality is exactly
$$t_{f_L}F_L(q)b_{T_f}=e\,v^*(t_f).$$

6. It remains to prove invertibility of the specified exceptional mate, without assuming a
smooth $\Omega$ adjunction. Construct the explicit adjunction first, as in blueprint Step 2,
separately over $k$ and over $L$. For every finite coefficient field $E$, [lem-pur-general-
integral-diagonal-comparison] supplies the natural isomorphism $h_E:J_E\simeq H_E$, with
$J_E=f^*(-)(d)[2d]$ and $H_E$ the right adjoint of [lem-sp-current-composition-integral-edge].
Transporting its Hom bijection along $h_E^{-1}$ gives $F_E^{\mathrm{int}}\dashv J_E$ with counit
$\epsilon^EF_E^{\mathrm{int}}(h_E)$. For $E=\mathbf Q_\ell$ its unit-component counit is exactly
$t_0$, since that node identifies $h_E$ with the inverse diagonal/DNC tower map used to define
$h_0$. These results have arbitrary-field hypotheses. No $\Omega$ purity theorem or algebraic-
closure reduction is used here.

7. For finite $E/\mathbf Q_\ell$, take integral models $M_0,K_0$ for arbitrary $M\in
D^b_c(X,E)$, $K\in D^b_c(Y,E)$. By [det-sp-rational-localized-hom] and Step 6 the natural Hom
chain is $$\operatorname{Hom}(F_EM,K)\simeq\operatorname{Hom}(F_E^{\mathrm{int}}M_0,K_0)\otimes_
{O_E}E\simeq\operatorname{Hom}(M_0,J_EK_0)\otimes_{O_E}E\simeq\operatorname{Hom}(M,f_E^*K(d)[2d]
).$$ Twists commute with the displayed scalars by their root-line comparison and [lem-pur-
ordinary-line-derived-scalar-comparison]. Each arrow is induced by the same scalar and counit
maps. Independence of model follows from naturality: any change of model is an isomorphism in
the localized Hom category, and the chain commutes with its pre/postcomposition; its inverse
therefore gives the inverse change. This constructs the explicit rational adjunction. For finite
$E\subset F$, the counit identity of [lem-pur-integral-adjoint-finite-free-coefficient-
comparison] and the equation for $h_E$ in [lem-pur-general-integral-diagonal-comparison] show
the Hom chains commute with coefficient extension. They obey the coefficient-composition
cocycle: the $h_E$ and $v_{E,F}$ by those two nodes, and the scalar compact-support comparisons
by [lem-sf-condensed-scalar-compact-support-cocycle-ambient].

8. Now use clauses 1–2 of [det-sp-qbar-finite-descent] to descend any finite diagram of objects
and arrows to one finite coefficient field. Use [lem-sf-listed-compact-support-iso] for $F$ (its
finite-Tor input holds by [lem-integral-ctf-equals-bc]) and scalar/pullback normalization for
$f^*$; thus the cohomological-dimension hypothesis of clause 3 is not needed. Step 7 commutes
with extension to larger finite fields. Taking its filtered colimit gives, naturally in $M,K$,
$$\operatorname{Hom}(F_\Omega M,K)\simeq\varinjlim_E\operatorname{Hom}(F_EM_E,K_E)\simeq\varinjl
im_E\operatorname{Hom}(M_E,f_E^*K_E(d)[2d])\simeq\operatorname{Hom}(M,f_\Omega^*K(d)[2d]).$$
Finite-diagram descent and the coefficient cocycle identify chains made with different models,
hence define an adjunction $F_\Omega\dashv J_\Omega$. Its counit at the unit, after the root-
projection identification $J_\Omega\mathbf1\simeq T_f$, is exactly
$uS(t_0)b_M^{-1}F(w^{-1})=t_f$: the counit is the inverse Hom image of the identity, and every
arrow in the chain is the specified scalar extension of the integral counit. The same argument
applies to $f_L$ over $L$.

9. Apply [det-sp-unique-right-adjoint] to the explicit adjunction just constructed and each
supplied adjunction $F\dashv G$, $F_L\dashv G_L$. At the coefficient units this gives
isomorphisms $a:T_f\simeq G\mathbf1_Y$, $a_L:T_{f_L}\simeq G_L\mathbf1_{Y_L}$ satisfying
$\epsilon F(a)=t_f$ and $\epsilon_LF_L(a_L)=t_{f_L}$. Form $c=a_Lq(u^*a)^{-1}$. Naturality of
$b$ and Step 5 give $$\epsilon_LF_L(c)b_{G\mathbf1}\,v^*F(a)=t_{f_L}F_L(q)b_{T_f}=e\,v^*(t_f)=e\
,v^*(\epsilon)\,v^*F(a).$$ Cancel the isomorphism $v^*F(a)$. Hence $c$ has exactly the counit-
transpose equation defining $\beta$. The adjunction Hom bijection makes that transpose unique,
so $\beta=c$ is an isomorphism. This also proves the requested counit equation. The trace
equation is already Step 5. Invertibility of the two comparison orientations was proved from the
independent integral and scalar Hom constructions, rather than assumed or imported from the
parent purity node.
-/
theorem comparison
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    letI : Fact (ringChar L).Prime :=
      ⟨(Algebra.ringChar_eq k L) ▸ (Fact.out : (ringChar k).Prime)⟩
    letI : Fact (ringChar L ≠ ell) :=
      ⟨(Algebra.ringChar_eq k L) ▸ (Fact.out : ringChar k ≠ ell)⟩
    ∀ {X Y : Over (Spec (.of k))} {X' Y' : Over (Spec (.of L))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      (f : X ⟶ Y) (f' : X' ⟶ Y')
      (u : X'.left ⟶ X.left) (v : Y'.left ⟶ Y.left)
      (_sqY : IsPullback v Y'.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (sq : IsPullback u f'.left f.left v)
      (d : ℕ) [SmoothOfRelativeDimension d f.left]
      (c : Compactification f.left),
    letI : SmoothOfRelativeDimension d f'.left :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback sq
        (inferInstance : SmoothOfRelativeDimension d f.left)
    letI := primeInvertible ell X
    letI := primeInvertible ell X'
    let F := boundedConstructibleLowerShriekOfCompactification ell c
    let FL := boundedConstructibleLowerShriekOfCompactification ell (c.ofIsPullback sq)
    let U := pull ell u
    let V := pull ell v
    let TY := 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ell⟧)
    let TYL := 𝟙_ (Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ell⟧)
    let T := boundedConstructibleTateTwist ell X d (2 * d)
    let TL := boundedConstructibleTateTwist ell X' d (2 * d)
    let e : V.obj TY ≅ TYL := unitIso ell v
    let q : U.obj T ≅ TL := ObjectProperty.isoMk _ (tateIso ell u d)
    ∀ (G : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ell⟧ ⥤
        Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ell⟧)
      (Gext : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ell⟧ ⥤
        Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ell⟧)
      (a : F ⊣ G) (aL : FL ⊣ Gext),
    ∃ b : F ⋙ V ≅ U ⋙ FL,
      b.hom = exchange ell sq c ∧
      (let beta : U.obj (G.obj TY) ⟶ Gext.obj TYL :=
        (aL.homEquiv _ _)
          (b.inv.app (G.obj TY) ≫ V.map (a.counit.app TY) ≫ e.hom)
       IsIso beta ∧
        b.hom.app (G.obj TY) ≫ FL.map beta ≫ aL.counit.app TYL =
          V.map (a.counit.app TY) ≫ e.hom) ∧
      b.hom.app T ≫ FL.map q.hom ≫ trace ell f' (c.ofIsPullback sq) d =
        V.map (trace ell f c d) ≫ e.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.SmoothAlgebraicExtension
