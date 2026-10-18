module

public import Sheaf.TraceFormula.BigSmallEtaleExactRetraction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Evaluation and restriction of big étale extension

Source: Stacks Project, Étale Cohomology, Tag 09XN (lemma-describe-pullback),
and Sites, Tag 021I (lemma-morphism-big-small-etale)
(blueprint: lem-trf-big-small-etale-pullback-formula).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The inverse-image functor on abelian sheaves induced by a morphism of schemes.
Source: Sites, Tag 021I; (blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def smallEtalePullback {S T : Scheme.{u}} (a : T ⟶ S) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.upperStar AddCommGrpCat a

/-- Evaluation of a small étale abelian sheaf at the final étale object, i.e. global
sections. Source: Sites, Tag 01FT; (blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def smallEtaleSections (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} where
  obj F := F.obj.obj (op (Scheme.Etale.mk (𝟙 T)))
  map φ := φ.hom.app (op (Scheme.Etale.mk (𝟙 T)))

/-- Evaluation of a big étale sheaf on an object of the big site. Source: Sites,
Tag 021I; (blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def bigEtaleEvaluation {S T : Scheme.{u}} (a : T ⟶ S) :
    Sheaf (Scheme.etaleTopology.over S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} where
  obj H := H.obj.obj (op (Over.mk a))
  map φ := φ.hom.app (op (Over.mk a))

/-- Restriction of big étale sheaves along a morphism of bases. Source: Sites, Tag 021I;
(blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def bigEtaleRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.etaleTopology.over Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuous (Over.map f) AddCommGrpCat
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over Y)

/-- Pullback of global sections along the small étale morphism induced by `h`.
This is the actual inverse-image adjunction unit evaluated at `T/T`, followed by
restriction along the canonical inverse `T' → T ×_T T'` to the second projection.
Source: Stacks Sites, Tags 00WX and 021I(2), and the section map in step 7 of
(blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def smallEtaleSectionsPullback {T T' : Scheme.{u}} (h : T' ⟶ T)
    (K : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    K.obj.obj (op (Scheme.Etale.mk (𝟙 T))) ⟶
      ((smallEtalePullback h).obj K).obj.obj (op (Scheme.Etale.mk (𝟙 T'))) :=
  (((Etale.upperStarLowerStarAdjunction AddCommGrpCat h).unit.app K).hom.app
    (op (Scheme.Etale.mk (𝟙 T)))) ≫
    (((smallEtalePullback h).obj K).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift h (𝟙 T') (by simp)) (by simp)).op)

/-- Canonical restriction on small-site pullback sections over `S`: pull back sections
along `h`, then identify `h_s⁻¹ a_s⁻¹ F` with `a'_s⁻¹ F` by the unit-compatible
composition isomorphism `Etale.upperStarComp` for `ha`.
Source: Stacks Sites, Tags 021J and 03CB; Étale Cohomology, Tag 09XN
(blueprint: lem-trf-big-small-etale-pullback-formula). -/
noncomputable def smallEtaleRestrictionMap {S T T' : Scheme.{u}}
    (a : T ⟶ S) (a' : T' ⟶ S) (h : T' ⟶ T) (ha : h ≫ a = a')
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((smallEtalePullback a).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T))) ⟶
      ((smallEtalePullback a').obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T'))) :=
  smallEtaleSectionsPullback h ((smallEtalePullback a).obj F) ≫
    ((Etale.upperStarComp AddCommGrpCat h a a' ha.symm).inv.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 T')))

/-- Data expressing the evaluation formula, its functoriality in the sheaf and in the
object over the base, and the compatible big/small pullback square. The restriction
comparison uses the actual big-site sheaf map and the canonically constructed
`smallEtaleRestrictionMap`, rather than unspecified maps between these section groups.
Source: Stacks Tags 09XN and 021I
(blueprint: lem-trf-big-small-etale-pullback-formula). -/
structure BigSmallEtalePullbackFormulaData where
  retraction : ∀ S : Scheme.{u}, BigSmallEtaleRetractionData S
  evaluationIso : ∀ {S T : Scheme.{u}} (a : T ⟶ S),
    ((retraction S).morphism.inverse ⋙ bigEtaleEvaluation a) ≅
      (smallEtalePullback a ⋙ smallEtaleSections T)
  restriction_is_pullback : ∀ {S T T' : Scheme.{u}} (a : T ⟶ S) (a' : T' ⟶ S)
    (h : T' ⟶ T) (ha : h ≫ a = a')
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}),
    (((retraction S).morphism.inverse.obj F).obj.map (Over.homMk h ha).op) =
      ((evaluationIso a).hom.app F ≫ smallEtaleRestrictionMap a a' h ha F) ≫
        (evaluationIso a').inv.app F
  baseChangeIso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ((retraction Y).morphism.inverse ⋙ bigEtaleRestriction f) ≅
      (smallEtalePullback f ⋙ (retraction X).morphism.inverse)

/-- Evaluation and restriction of extension from the small to the big étale site.
For every `a : T ⟶ S` and abelian sheaf `F`, the component of `evaluationIso` is the
canonical additive-group isomorphism
`(π_S⁻¹ F)(T ⟶ S) ≅ Γ(T_et, a_s⁻¹ F)`. Naturality in `F` is the natural-isomorphism
field; `restriction_is_pullback` identifies the actual big-site sheaf restriction
with `smallEtaleRestrictionMap`, constructed from the small inverse-image unit and
its unit-compatible composition comparison. `baseChangeIso` gives the natural sheaf
isomorphism for every `f : X ⟶ Y`.
Source: Stacks Project, Étale Cohomology Tag 09XN and Sites Tag 021I
(blueprint: lem-trf-big-small-etale-pullback-formula).

Proof, following all eight steps of the node:

1. Use compatible small presentations (def-weil-size-convention). Identify `B_X`
with the localized site `B_Y/(X/Y)` (def-pur-localized-ringed-site): schemes over
`X` and the same jointly surjective étale covering families occur on both sides.
Let `u_f(V/X) = (V/Y)` and `v_f(W/Y) = (W ×_Y X/X)`, with fibre products from
 def-pc-fibre-product. Define `P_f G = G ∘ u_f` and `Q_f H = H ∘ v_f`, on both
objects and arrows. `P_f G` is a sheaf by localization. The site base-change axiom
(def-weil-pbc-sites-and-cohomology(1)) pulls every covering of `W` back to the
corresponding covering of `W ×_Y X`, and the fibre-product universal property
identifies all overlaps. Hence the sheaf equalizer for `Q_f H` is that for `H`.

2. Construct `P_f ⊣ Q_f` explicitly. Write `p_W : u_f v_f W → W` for projection
and `e_V : V → v_f u_f V` for the graph `(id_V, V → X)`. Send `α : P_f G → H`
to `λ(α)_W = α_(v_f W) ∘ G(p_W)`, and `γ : G → Q_f H` to
`μ(γ)_V = H(e_V) ∘ γ_(u_f V)`. Naturality of projections and graphs makes these
natural additive maps. Naturality of `α` gives
`μλ(α)_V = α_V ∘ G(p_(u_f V) ∘ u_f(e_V)) = α_V`; naturality of `γ` gives
`λμ(γ)_W = H(v_f(p_W) ∘ e_(v_f W)) ∘ γ_W = γ_W`. The two projection identities
follow from def-pc-fibre-product. These formulas commute with precomposition in
`G` and postcomposition in `H`, so lem-weil-pbc-adjunction-of-natural-bijection
supplies the adjunction. Taking `α = id` gives its unit `b_(f,G)(W) = G(p_W)`.
Thus `P_f = f_b⁻¹` is exactly restriction in the statement. Composition of the
`P_f` is composition of the structure maps.

3. Set `L_Z = π_Z⁻¹`, `R_Z = π_(Z,*)`, and let `e_Z : id → R_Z L_Z` be the unit.
The exact-retraction lemma (lem-trf-big-small-etale-exact-retraction) identifies
`R_Z` with restriction and makes `e_Z` invertible. On every étale `W/Y`,
`(R_Y Q_f H)(W/Y) = H(W ×_Y X/X) = (f_(s,*) R_X H)(W/Y)` by
 def-weil-pbc-direct-image. Both sides act on `W' → W` by the map induced on fibre
products and on sheaf morphisms by their components there. This supplies the
natural identification `δ_f : f_(s,*) R_X ≅ R_Y Q_f`, the identity with common
fibre-product choices, proving the direct-image square of Tag 021I(3).

4. Form the composite adjunctions `P_f L_Y ⊣ R_Y Q_f` and
`L_X f_s⁻¹ ⊣ f_(s,*) R_X` (def-weil-pbc-composite-adjunction); the small adjunction
is def-weil-pbc-sites-and-cohomology(3). Apply
 lem-weil-pbc-conjugate-iso-unit-equation to `δ_f` to obtain the canonical
`β_f : P_f L_Y ≅ L_X f_s⁻¹`, which is the final clause. Writing `s_f` for the
small adjunction unit, its characterizing equation, with `δ_f` understood, is
`R_Y Q_f(β_(f,F)) ∘ R_Y(b_(f,L_Y F)) ∘ e_(Y,F)
 = f_(s,*)(e_(X,f_s⁻¹ F)) ∘ s_(f,F)`. Call this equation (*).
It is an equality of abelian-sheaf morphisms, not just of underlying set maps.

5. For `a : T → S` and `h : T' → T`, write
`c_(a,h) : h_s⁻¹ a_s⁻¹ ≅ (ah)_s⁻¹` for the unit-compatible comparison of
 lem-weil-pbc-inverse-image-composition(2). The required composition identity is
`β_(ah,F) = L_T'(c_(a,h,F)) ∘ β_(h,a_s⁻¹ F) ∘ P_h(β_(a,F))`, called (**),
where `P_h P_a = P_(ah)`. Expand the composite unit using
 def-weil-pbc-composite-adjunction, substitute (*) for `h` and then for `a`, and
use the unit equation for `c_(a,h)`. The resulting right-adjoint comparison is
induced at `W/S` by `(W ×_S T) ×_T T' ≅ W ×_S T'`. Its projections to `W` and
`T'` agree with those for `ah` by def-pc-fibre-product. Thus both sides of (**)
satisfy the same characterizing unit equation, and uniqueness in
 lem-weil-pbc-conjugate-iso-unit-equation proves (**).

6. Put `K = a_s⁻¹ F`. Apply `R_T` to `β_(a,F) : P_a L_S F ≅ L_T K` and compose
with `e_(T,K)⁻¹`, invertible by lem-trf-big-small-etale-exact-retraction.
Evaluation at `T/T` gives `θ_(a,F) = e_(T,K)(T)⁻¹ ∘ β_(a,F)(T)` from
`(L_S F)(T/S)` to `K(T/T) = Γ(T_et, a_s⁻¹ F)`; restriction identifies the source
with `R_T P_a L_S F(T/T)`. Evaluation is
 def-weil-pbc-sites-and-cohomology(2). All components are homomorphisms, and
naturality in `F` follows from that of `β_a` and `e_T`. This is the first proof
paragraph of Tag 09XN: restriction along `T_et → B_S` is `R_T P_a`.

7. For an abelian sheaf `K` on `T_et`, evaluate (*) for `h : T' → T` at `T/T`.
By step 2, `b_(h,L_T K)(T)` is restriction along `h` after the canonical
identification `T ×_T T' ≅ T'` (def-pc-fibre-product); `δ_h` is the identity on
sections by step 3. Thus for `t ∈ K(T)`,
`β_(h,K)(T')((L_T K)(h)(e_(T,K)(T)t))
 = e_(T',h_s⁻¹ K)(T')(s_(h,K)(T)t)`, called (***).
Here `s_(h,K)(T)` is precisely the inverse-image adjunction unit evaluated at the
final object, with direct-image evaluation from def-weil-pbc-direct-image and
 def-weil-pbc-sites-and-cohomology(3). It is therefore the specific pullback of
global sections constructed by `smallEtaleSectionsPullback`, including its unit
normalization, rather than an unspecified homomorphism.

8. Finally set `G = L_S F`, `K = a_s⁻¹ F`, and `t = θ_(a,F)(s)` for `s ∈ G(T/S)`.
Then `β_(a,F)(T)s = e_(T,K)(T)t`. Naturality of the sheaf map `β_(a,F)` along
`h : T' → T`, viewed as an arrow of `B_T`, gives
`β_(a,F)(T')G(h)s = (L_T K)(h)e_(T,K)(T)t`. Apply `β_(h,K)(T')` and use (***),
then (**) and naturality of `e_T'` with respect to `c_(a,h,F)`. Cancel the
isomorphism `e_(T',(ah)_s⁻¹ F)(T')` to obtain
`θ_(ah,F)(G(h)s) = c_(a,h,F)(T')(s_(h,K)(T)t)`.
By lem-weil-pbc-inverse-image-composition this right side is pullback of `t`
along `h_s` followed by the canonical composition identification, exactly
`smallEtaleRestrictionMap`. This proves `restriction_is_pullback`, hence
naturality in every `T/S`, without assuming that `a` or `h` is étale. -/
theorem bigSmallEtalePullbackFormula :
    Nonempty BigSmallEtalePullbackFormulaData := by
  sorry

end AlgebraicGeometry
