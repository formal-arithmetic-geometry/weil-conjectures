/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Integral chart logification and strict first-order restriction

Source: ILO, Exposé VI 1.1, printed p.69 (associated-log conventions referring to
Kato (1988), §1), and the chart argument in XVI Proposition 3.6.3, printed p.252.
The arbitrary-scheme construction and strict-thickening calculation are the
agent-formulated auxiliary input specified by the DAG, rather than an ILO theorem.
(blueprint: lem-per-integral-chart-logification-thickening).

The quotient presheaf and the log, fine and morphism notions are reused verbatim.
No locally Noetherian hypothesis is imposed. The associated sheaf is characterized
by its sheafification unit and structural formula, so the existential presentation
specifies the canonical object up to its unique chart-preserving isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Evaluation of a log map on the global chart, in the adjoint presentation of
`a⁻¹L → K`. Source: ILO VI 1.1; XVI 3.6.3, p.252
(blueprint: lem-per-integral-chart-logification-thickening). -/
noncomputable def integralChartCompose {T S : Scheme.{max u v}} {P : Type v}
    [CommMonoid P] (β : P →* Γ(T, ⊤)) (L : EtaleLogStructure T)
    (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj) (K : EtaleLogStructure S)
    (a : S ⟶ T) (H : K.HomAlong L a) :
    ULift.{u, v} P →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 S))) :=
  (H.sectionMap (Scheme.Etale.mk (𝟙 T)) (Scheme.Etale.mk (𝟙 S)) a
    ((Category.comp_id a).trans (Category.id_comp a).symm)).comp (associatedLogIota β L η)

/-- The stalk presentation, normalized on every pair and every neighbourhood.
Source: ILO VI 1.1 and the explicit germ calculation in the DAG
(blueprint: lem-per-integral-chart-logification-thickening). -/
def IntegralChartStalkPresentation {T : Scheme.{max u v}} {P : Type v} [CommMonoid P]
    (β : P →* Γ(T, ⊤)) (L : EtaleLogStructure T)
    (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj) : Prop :=
  ∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
    ∃ e : divisorialChartPushout (P := ULift.{u, v} P)
      (associatedLogStalkBeta β t).mrangeRestrict ≅ L.toEtalePrelogStructure.stalk t,
      ∀ (W : T.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (p : P) (b : Γ(W.left, ⊤)ˣ),
        e.hom ((divisorialChartCongruence (P := ULift.{u, v} P)
          (associatedLogStalkBeta β t).mrangeRestrict).mk'
            (ULift.up p, Units.map (strictLocalGerm T t W w).hom.toMonoidHom b)) =
          L.toEtalePrelogStructure.germ t W w
            (η.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} P)
              (associatedLogBetaLift β W).mrangeRestrict).mk' (ULift.up p, b)))

/-- The ideal stalk, formed from germs of the defining ideal on étale neighbourhoods.
Here reduction of functions is along `W ×[T] T₀ → W`; this is the étale ideal sheaf
of the closed immersion, including its nilpotents. Source: Stacks Tag 05WS and the
DAG's Step 9 (blueprint: lem-per-integral-chart-logification-thickening). -/
noncomputable def integralChartThickeningIdeal {T₀ T : Scheme.{u}}
    (j : T₀ ⟶ T) {Ω : Type (u)} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T₀) : Ideal (strictLocalRing T (t ≫ j)) :=
  Ideal.span {x | ∃ (W : T.Etale) (w : (Scheme.pointSmallEtale (t ≫ j)).fiber.obj W)
    (s : Γ(W.left, ⊤)), (pullback.fst W.hom j).appTop s = 0 ∧
      strictLocalGerm T (t ≫ j) W w s = x}

/-- Strictness and the nonempty torsor fibres on corresponding geometric stalks.
The ring and monoid maps are specified on all germs of relative test diagrams;
they are therefore the canonical maps, rather than arbitrary surjections.
The kernel congruence explicitly presents the pushout by the new unit group.
Source: ILO VI 1.1 conventions; the DAG's Steps 9--12
(blueprint: lem-per-integral-chart-logification-thickening). -/
def IntegralChartThickeningStalks {T₀ T : Scheme.{u}} (j : T₀ ⟶ T)
    (L : EtaleLogStructure T) (L₀ : EtaleLogStructure T₀) (H : L₀.HomAlong L j) : Prop :=
  ∀ (Ω : Type (u)) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T₀),
    ∃ (r : strictLocalRing T (t ≫ j) →+* strictLocalRing T₀ t)
      (q : L.toEtalePrelogStructure.stalk (t ≫ j) →* L₀.toEtalePrelogStructure.stalk t),
      (∀ (W : T.Etale) (V : T₀.Etale)
        (w : (Scheme.pointSmallEtale (t ≫ j)).fiber.obj W)
        (z : (Scheme.pointSmallEtale t).fiber.obj V)
        (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ j),
        z.left ≫ k = w.left →
          (∀ s : Γ(W.left, ⊤), r (strictLocalGerm T (t ≫ j) W w s) =
            strictLocalGerm T₀ t V z (k.appTop s)) ∧
          ∀ m : L.monoidSheaf.obj.obj (op W),
            q (L.toEtalePrelogStructure.germ (t ≫ j) W w m) =
              L₀.toEtalePrelogStructure.germ t V z (H.sectionMap W V k hk m)) ∧
      Function.Surjective r ∧ RingHom.ker r = integralChartThickeningIdeal j t ∧
      RingHom.ker r ^ 2 = ⊥ ∧
      (∀ b : (strictLocalRing T (t ≫ j))ˣ,
        q (L.unitsIn (t ≫ j) b) = L₀.unitsIn t (Units.map r.toMonoidHom b)) ∧
      Function.Surjective (q.coprod (L₀.unitsIn t)) ∧
      Con.ker (q.coprod (L₀.unitsIn t)) =
        conGen (fun x y ↦ ∃ b : (strictLocalRing T (t ≫ j))ˣ,
          x = (L.unitsIn (t ≫ j) b, 1) ∧ y = (1, Units.map r.toMonoidHom b)) ∧
      Function.Surjective q ∧
      (∀ (m m' : L.toEtalePrelogStructure.stalk (t ≫ j)), q m = q m' →
        ∃! c : RingHom.ker r, ∃ b : (strictLocalRing T (t ≫ j))ˣ,
          b.val = 1 + c.val ∧ m' = m * L.unitsIn (t ≫ j) b) ∧
      (∀ c : RingHom.ker r, ∃! b : (strictLocalRing T (t ≫ j))ˣ,
        b.val = 1 + c.val) ∧
      ∀ c d : RingHom.ker r,
        (1 + c.val) * (1 + d.val) = 1 + (c.val + d.val)

/-- The sheaf-local torsor assertion: reduction is locally surjective, and two
sections with equal reductions have a unique difference in the additive kernel
ideal. Units in the log sections give its action, with structural value `1+c`.
No surjectivity on global log sections is asserted.
Source: Stacks Tags 03SI, 03PU; the DAG's Step 13
(blueprint: lem-per-integral-chart-logification-thickening). -/
def IntegralChartThickeningLocal {T₀ T : Scheme.{u}} (j : T₀ ⟶ T)
    (L : EtaleLogStructure T) (L₀ : EtaleLogStructure T₀) (H : L₀.HomAlong L j) : Prop :=
  ∃ ρ : L.monoidSheaf.obj ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ j).op ⋙ L₀.monoidSheaf.obj,
    (∀ (W : T.Etale) (m : L.monoidSheaf.obj.obj (op W)),
      ρ.app (op W) m = H.sectionMap W
        ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W)
        (pullback.fst W.hom j) (pullback.condition) m) ∧
    Presheaf.IsLocallySurjective T.smallEtaleTopology ρ ∧
    (∀ (W : T.Etale) (m m' : L.monoidSheaf.obj.obj (op W)),
      ρ.app (op W) m = ρ.app (op W) m' →
        ∃! c : RingHom.ker (pullback.fst W.hom j).appTop.hom,
          ∃ b : (L.monoidSheaf.obj.obj (op W))ˣ,
            L.alpha.app (op W) b.val = 1 + c.val ∧ m' = m * b.val) ∧
    (∀ (W : T.Etale) (c : RingHom.ker (pullback.fst W.hom j).appTop.hom),
      ∃! b : (L.monoidSheaf.obj.obj (op W))ˣ,
        L.alpha.app (op W) b.val = 1 + c.val) ∧
    ∀ (W : T.Etale) (c d : RingHom.ker (pullback.fst W.hom j).appTop.hom),
      (1 + c.val) * (1 + d.val) = 1 + (c.val + d.val)

/-- Étale restriction identifies the associated log structures, including their
charts and structural maps. Source: ILO VI 1.1; Stacks Tags 00WK, 00Y0
(blueprint: lem-per-integral-chart-logification-thickening). -/
def IntegralChartEtaleRestriction {T : Scheme.{max u v}} {P : Type v} [CommMonoid P]
    (β : P →* Γ(T, ⊤)) (L : EtaleLogStructure T)
    (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj) : Prop :=
  ∀ U : T.Etale,
    ∃ (LU : EtaleLogStructure U.left)
      (ηU : associatedLogPresheaf (X := U.left) (associatedLogBeta β U) ⟶ LU.monoidSheaf.obj),
      IsAssociatedLogPresentation (associatedLogBeta β U) LU ηU ∧
      ∃ e : LU.monoidSheaf.obj ≅
          (MorphismProperty.Over.map ⊤ U.prop).op ⋙ L.monoidSheaf.obj,
        (∀ (W : U.left.Etale) (p : P) (b : Γ(W.left, ⊤)ˣ),
          e.hom.app (op W) (ηU.app (op W)
            ((divisorialChartCongruence (P := ULift.{u, v} P)
              (associatedLogBetaLift β
                ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
                  (ULift.up p, b))) =
            η.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
              ((divisorialChartCongruence (P := ULift.{u, v} P)
                (associatedLogBetaLift β
                  ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
                    (ULift.up p, b))) ∧
        ∀ (W : U.left.Etale) (m : LU.monoidSheaf.obj.obj (op W)),
          L.alpha.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
            (e.hom.app (op W) m) = LU.alpha.app (op W) m

/-- Integral finitely generated charts have an integral fine associated log structure on any
scheme, with its stalks, arbitrary-map universal property, étale restriction, and
strict first-order restriction with additive-ideal torsor fibres.

Source: ILO VI 1.1, p.69, and XVI 3.6.3, p.252, as conventions and motivation;
the general auxiliary construction and strict-thickening proof are those of this DAG node.
Proof (all thirteen steps, with their dependency nodes):
1. Work in a common enlarged universe and on small skeletons as in [def-weil-size-convention],
   so the monoid sheafification theorem applies. Write $Q(U)=P\oplus_{E_U}\mathcal O(U)^\times$.
   This is concretely the quotient of $P\times\mathcal O(U)^\times$ by the displayed generating
   relations. Restriction sends $E_U$ into $E_V$ and preserves those relations, so defines a
   presheaf of commutative monoids. The maps $[p,u]\mapsto\beta_U(p)u$ also preserve the
   relations and restrictions. Units form a sheaf: glue the units and their inverses separately
   in the structure ring sheaf. By [lem-trf-commutative-monoid-sheafification], $L=Q^\#$ is a
   monoid sheaf whose underlying set sheaf is the set sheafification, and the structural map
   extends uniquely. Set $\iota(p)=\eta([p,1])$ and $j(u)=\eta([1,u])$; thus $\alpha j(u)=u$.
   Uses: def-weil-size-convention, lem-trf-commutative-monoid-sheafification.
2. To verify the log axiom, let $l\in L(U)$ have unit image $a$. The local-representatives
   theorem [lem-weil-pbc-site-sheafification-sections-local] writes $l$ locally as
   $\eta([p,u])$. There $\beta(p)=a/u$ is a unit, so $p\in E$ and $[p,u]=[1,\beta(p)u]=[1,a]$.
   Therefore $l=j(a)$ locally and globally. Conversely $\alpha j(a)=a$ proves that $j$ is
   injective and identifies precisely the inverse image of the units. This is the log axiom in
   the stated inline definition, without any Noetherian assumption.
   Uses: lem-weil-pbc-site-sheafification-sections-local.
3. Fix a geometric point and put $A=\mathcal O_{T,\bar t}$. By [def-weil-pbc-geometric-stalks]
   this is the ring of germs of functions. The cofilteredness in [lem-weil-pbc-pointed-etale-
   neighbourhoods-cofiltered] implies that finitely many representatives and finitely many
   equalities of germs can be realized on one pointed refinement: a colimit equality is a finite
   chain of restriction relations, and a common source with equalized parallel maps realizes
   that chain. In particular a unit $a\in A^\times$ is represented by a unit on a neighbourhood:
   represent $a,a^{-1}$ together and refine until their product is $1$. Also $\beta_{\bar t}(e)$
   is a unit exactly when $e\in E_U$ on some pointed neighbourhood, by the same inverse-and-
   equation argument.
   Uses: def-weil-pbc-geometric-stalks, lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered.
4. Let $E=\beta_{\bar t}^{-1}(A^\times)$. The colimit of $Q(U)$ maps to $P\oplus_E A^\times$ by
   $[p,u]\mapsto[p,u_{\bar t}]$. Conversely represent a unit $a\in A^\times$ on a pointed
   neighbourhood and send $(p,a)$ to the germ of $[p,u]$. Step 3 makes this independent of the
   representative. For each relation $(pe,a)\sim(p,\beta(e)a)$ in the target refine until $e\in
   E_U$; the relation then already holds in $Q(U)$. Thus this inverse descends through the
   generated congruence, and both composites fix represented pairs. Products are computed on
   common refinements, so these maps are monoid maps. Finally [lem-weil-pbc-sets-sheafification-
   geometric-stalk] and the underlying-set clause of [lem-trf-commutative-monoid-sheafification]
   identify the colimit of $Q(U)$ with $L_{\bar t}$. This proves the stated canonical stalk
   formula, including its maps from $P$ and from $A^\times$.
   Uses: lem-weil-pbc-sets-sheafification-geometric-stalk, lem-trf-commutative-monoid-
   sheafification.
5. Apply [lem-per-integral-monoid-unit-pushout] to $P$, the submonoid $E$, the abelian group
   $A^\times$, and $f=\beta|_E$. Step 4 identifies its $M$ with $L_{\bar t}$; the embedding of
   $M$ in a group proves that every such stalk is integral. No injectivity of $\beta|_E$ is
   required. The global chart $\iota:P\to L(T)$ is the chart used to construct $L$, so it is a
   chart by the finitely generated integral monoid $P$ already on $T$. Consequently $L$ is fine
   in the stated definition.
   Uses: lem-per-integral-monoid-unit-pushout.
6. Let $a:S\to T$ and $v:P\to K(S)$ have $\alpha_Kv=a^\sharp\beta$. On an etale $U\to T$ put
   $S_U=S\times_TU$. For $u\in\mathcal O(U)^\times$ let $a_U^\sharp u$ be its unit pullback.
   Define $$Q(U)\longrightarrow K(S_U),\qquad [p,u]\longmapsto v(p)|_{S_U}\,j_K(a_U^\sharp u),$$
   where $j_K$ is the inverse of the units isomorphism in the log axiom. For $e\in E_U$,
   $\alpha_K(v(e)|_{S_U})=a_U^\sharp\beta_U(e)$ is a unit, so
   $v(e)|_{S_U}=j_K(a_U^\sharp\beta_U(e))$. This proves that the displayed formula respects
   every generating relation. It is natural in $U$ and gives a monoid-presheaf map $Q\to a_*K$.
   Direct image is a sheaf (the inverse-image/direct-image adjunction of [lem-weil-pbc-etale-
   inverse-image-algebraic-structures]); hence [lem-trf-commutative-monoid-sheafification]
   extends it uniquely to $L\to a_*K$.
   Uses: lem-weil-pbc-etale-inverse-image-algebraic-structures, lem-trf-commutative-monoid-
   sheafification.
7. The set-sheaf adjunction and finite-product preservation in [lem-weil-pbc-etale-inverse-
   image-algebraic-structures](1) lift to monoids: inverse image sends the multiplication and
   identity diagrams to those for $a^{-1}L$, and an adjoint map preserves these operations
   exactly when its transpose does, by naturality of the adjunction. Transpose Step 6 to obtain
   $a^{-1}L\to K$. The structural compatibility is checked on each $[p,u]$, where both sides
   equal $(a^\sharp\beta(p))a^\sharp u$, and extends by sheafification uniqueness. Conversely a
   structurally compatible map, transposed to $L\to a_*K$, determines $v$ on $\iota(P)$. Its
   value on $j(u)$ is forced to be $j_K(a^\sharp u)$ by the log axiom of $K$. As
   $\eta([p,u])=\iota(p)j(u)$, its restriction to $Q$ is precisely Step 6. Sheafification
   uniqueness proves that these constructions are inverse. This gives the asserted bijection and
   uniqueness of a chart-specified log map.
   Uses: lem-weil-pbc-etale-inverse-image-algebraic-structures, lem-trf-commutative-monoid-
   sheafification.
8. For etale $U\to T$, the small etale site of $U$ is the slice over $U$ of that of $T$:
   composition and cancellation are [lem-weil-pbc-etale-composition-cancellation], and coverings
   are the same jointly surjective families by [def-weil-pbc-etale-site]. The presheaf $Q_T$
   restricted to this slice is exactly $Q_U$, with identical functions and relations.
   Restriction of $L_T$ is a sheaf; $Q_U\to L_T|_U$ is locally surjective and locally injective
   by [lem-weil-pbc-site-sheafification-sections-local], since every refinement over an object
   of the slice still lies in the slice. By [lem-cbc-set-presheaf-sheafification-local-
   bijection] this identifies $L_T|_U$ with the set sheafification of $Q_U$. The underlying-set
   assertion of [lem-trf-commutative-monoid-sheafification] identifies this with $L_U$. The
   identification preserves multiplication, chart and structural map since it does so on all
   local pairs. This proves the claimed canonical restriction isomorphism.
   Uses: lem-weil-pbc-etale-composition-cancellation, def-weil-pbc-etale-site, lem-weil-pbc-
   site-sheafification-sections-local, lem-cbc-set-presheaf-sheafification-local-bijection, lem-
   trf-commutative-monoid-sheafification.
9. For $j:T_0\hookrightarrow T$, fix a corresponding geometric point. The affine pointed
   neighbourhoods compute the stalk by [lemma-weil-pbc-affine-neighbourhood-cofinal], so the
   ring $A$ is the strict-local ring colimit of [def-weil-pbc-strict-henselization-limit]. The
   quotient statement of [lem-trf-closed-immersion-strict-localization-cartesian] identifies the
   stalk ring of $T_0$ with $A/J$, where $J=\mathcal I_{\bar t}$. Indeed, on an affine chart
   with ideal $I$, the kernel is $IA$ by that node; germs of the ideal sheaf are exactly finite
   sums of elements of $I$ times germs of functions, so are $IA$. By [def-sbc-first-order-
   thickening], $I^2=0$ on affine charts and hence $J^2=0$. These results impose no Noetherian
   condition and keep the nilpotents of $T_0$.
   Uses: lemma-weil-pbc-affine-neighbourhood-cofinal, def-weil-pbc-strict-henselization-limit,
   lem-trf-closed-immersion-strict-localization-cartesian, def-sbc-first-order-thickening.
10. For any commutative ring $A$ and square-zero ideal $J$, reduction $A^\times\to(A/J)^\times$
   is surjective: lift $\bar a$ and $\bar a^{-1}$ to $a,b$, write $ab=1+c$ with $c\in J$, and
   use $a\,b(1-c)=1$. In particular an element of $A$ is a unit if and only if its reduction is.
   The kernel consists exactly of $1+c$, $c\in J$; each has inverse $1-c$. Moreover
   $(1+c)(1+d)=1+c+d$ since $cd=0$, and equality $1+c=1+d$ gives $c=d$. These calculations apply
   to Step 9 and show that the submonoid $E\subseteq P$ is identical before and after reduction.
11. The chart $P\to L_{T_0}(T_0)$ and Step 7 define the restriction log map. On stalks it sends
   $[p,u]\mapsto[p,\bar u]$, by its formula on charts and units. Step 4 on $T$ and on $T_0$,
   together with the equality of $E$ in Step 10, therefore gives $M=P\oplus_E A^\times$ and
   $M_0=P\oplus_E(A/J)^\times$. By [lem-weil-pbc-sets-etale-inverse-image-stalk-germ], the
   source of the sheaf pullback map has stalk $L_{T,\bar t}$, with these exact germs. The
   canonical identification $$M\oplus_{A^\times}(A/J)^\times\simeq M_0$$ is obtained by
   $[[p,u],b]\mapsto[p,\bar u b]$ with inverse $[p,b]\mapsto[[p,1],b]$. Both formulas respect
   the pushout relations, and their composites fix each represented pair. This proves the stated
   strictness and its compatibility with the structural maps.
   Uses: lem-weil-pbc-sets-etale-inverse-image-stalk-germ.
12. Every $[p,b]\in M_0$ lifts to $[p,u]\in M$, by the surjectivity on units in Step 10. If
   $m=[p,u]$ and $m'=[p',u']$ have the same image, apply the equality criterion of [lem-per-
   integral-monoid-unit-pushout] with $G=(A/J)^\times$. It gives $e,e'\in E$ with $pe'=p'e$ and
   $\bar u\,\overline{\beta(e)}=\bar u'\,\overline{\beta(e')}$. Put $c=\beta(e)$, $d=\beta(e')$,
   units in $A$. The defining relations give $m=[pe',u/d]$ and $m'=[p'e,u'/c]$, so $m'=mw$ for
   $w=u'd/(uc)$. The displayed reduced equality says $\bar w=1$, hence $w=1+v$ for a unique
   $v\in J$. The free unit action in the same cited node proves that no other $w$ can satisfy
   $m'=mw$, so this $v$ is unique. Thus each nonempty fiber is a torsor under $1+J$, and
   surjectivity shows that every fiber is nonempty.
   Uses: lem-per-integral-monoid-unit-pushout.
13. Use [sbc-lem-thickening-etale-site] to identify the small etale sites by $U\mapsto
   U_0=U\times_TT_0$. In this identification put $N(U)=L_{T_0}(U_0)$, a sheaf on
   $T_{\mathrm{Et}}$. Its stalk at $\bar t$ is $M_0$ of Step 11: the equivalence of pointed
   neighbourhoods identifies the colimits and their germ maps. Every germ of $N$ has a lift in
   $L_T$ by Step 12. Representing the lift and its equality with a given local section on a
   pointed neighbourhood gives local surjectivity, hence such neighbourhoods cover. Consider the
   map of sheaves $$(1+\mathcal I)\times L_T\longrightarrow
   L_T\times_NL_T,\qquad(w,m)\longmapsto(m,mw).$$ Its stalk maps are bijective by Step 12:
   finite tuples and their equations are represented on common pointed refinements as in Step 3.
   Apply [lem-weil-pbc-sets-etale-iso-on-geometric-stalks] to conclude this is an isomorphism.
   Thus any two lifts of the same local section differ by a unique local section of $1+\mathcal
   I$; the sheaf axiom glues the unique differences. Finally $(1+v)(1+w)=1+v+w$ on each object
   since $\mathcal I^2=0$, compatibly with restriction. This identifies $1+\mathcal I$ with the
   additive ideal sheaf. No surjectivity on global sections is asserted.
   Uses: sbc-lem-thickening-etale-site, lem-weil-pbc-sets-etale-iso-on-geometric-stalks.
(blueprint: lem-per-integral-chart-logification-thickening). -/
theorem integralChartLogificationThickening (T : Scheme.{max u v})
    (P : Type v) [CommMonoid P] (hfg : Monoid.FG P)
    (hint : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (β : P →* Γ(T, ⊤)) :
    ∃ (L : EtaleLogStructure T) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj),
      IsAssociatedLogPresentation β L η ∧
      (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        Function.Injective
          (Algebra.GrothendieckGroup.of (M := L.toEtalePrelogStructure.stalk t))) ∧
      L.IsFine ∧ L.IsChart (Scheme.Etale.mk (𝟙 T)) (associatedLogIota β L η) ∧
      IntegralChartStalkPresentation β L η ∧
      (∀ (S : Scheme.{max u v}) (a : S ⟶ T) (K : EtaleLogStructure S),
        Function.Injective (integralChartCompose β L η K a) ∧
        Set.range (integralChartCompose β L η K a) =
          {c | (K.alpha.app (op (Scheme.Etale.mk (𝟙 S)))).hom.comp c =
            associatedLogDownChart (a.appTop.hom.toMonoidHom.comp β)}) ∧
      IntegralChartEtaleRestriction β L η ∧
      ∀ (T₀ : Scheme.{max u v}) (j : T₀ ⟶ T), IsFirstOrderThickening j →
        ∃ (L₀ : EtaleLogStructure T₀)
          (η₀ : associatedLogPresheaf (j.appTop.hom.toMonoidHom.comp β) ⟶ L₀.monoidSheaf.obj)
          (H : L₀.HomAlong L j),
          IsAssociatedLogPresentation (j.appTop.hom.toMonoidHom.comp β) L₀ η₀ ∧
          integralChartCompose β L η L₀ j H =
            associatedLogIota (j.appTop.hom.toMonoidHom.comp β) L₀ η₀ ∧
          IntegralChartThickeningStalks j L L₀ H ∧ IntegralChartThickeningLocal j L L₀ H := by
  sorry

end AlgebraicGeometry
