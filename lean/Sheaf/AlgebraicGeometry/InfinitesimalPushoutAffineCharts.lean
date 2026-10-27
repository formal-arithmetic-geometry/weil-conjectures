module

public import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Affine charts of infinitesimal scheme pushouts

Source: Stacks Project, Tags 07RT and 07RV, `lemma-pushout-along-thickening` and
`lemma-equivalence-categories-schemes-over-pushout`
(blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Ring pullback and pushout universal properties below prescribe the canonical maps,
including their base algebra structures. In commutative rings a pushout is a tensor
product. Surjectivity together with the specified kernel prescribes the quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical comparison from sections to the ring fibre product, for compatible
opens in a commutative scheme square. This uses the actual section maps.
Source: Stacks, Tag 07RT (blueprint: lem-sfb-infinitesimal-pushout-affine-charts). -/
noncomputable def infinitesimalSectionPullback
    {K V K' W : Scheme.{u}} {a : K ⟶ V} {i : K ⟶ K'}
    {j : V ⟶ W} {b : K' ⟶ W} (h : CommSq a i j b)
    (OW : W.Opens) (OV : V.Opens) (OK' : K'.Opens) (OK : K.Opens)
    (ej : OV ≤ j ⁻¹ᵁ OW) (eb : OK' ≤ b ⁻¹ᵁ OW)
    (ea : OK ≤ a ⁻¹ᵁ OV) (ei : OK ≤ i ⁻¹ᵁ OK') :
    Γ(W, OW) ⟶ pullback (a.appLE OV OK ea) (i.appLE OK' OK ei) :=
  pullback.lift (j.appLE OW OV ej) (b.appLE OW OK' eb)
    (by simp only [Scheme.Hom.appLE_comp_appLE, h.w])

/-- The canonical tensor comparison on sections of a commutative scheme square.
Source: Stacks, Tag 07RV (blueprint: lem-sfb-infinitesimal-pushout-affine-charts). -/
noncomputable def infinitesimalSectionPushout
    {K V K' W : Scheme.{u}} {a : K ⟶ V} {i : K ⟶ K'}
    {j : V ⟶ W} {b : K' ⟶ W} (h : CommSq a i j b)
    (OW : W.Opens) (OV : V.Opens) (OK' : K'.Opens) (OK : K.Opens)
    (ej : OV ≤ j ⁻¹ᵁ OW) (eb : OK' ≤ b ⁻¹ᵁ OW)
    (ea : OK ≤ a ⁻¹ᵁ OV) (ei : OK ≤ i ⁻¹ᵁ OK') :
    pushout (j.appLE OW OV ej) (b.appLE OW OK' eb) ⟶ Γ(K, OK) :=
  pushout.desc (a.appLE OV OK ea) (i.appLE OK' OK ei)
    (by simp only [Scheme.Hom.appLE_comp_appLE, h.w])

/-- Recovery by the canonical maps. The common map `t` makes the overlap identification
an identification over T. The equations on `p` specify the unique induced map Z to P.
`IsPullback` says precisely that each canonical comparison is an isomorphism.
Source: Stacks, Tag 07RV (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: base change makes U to X affine and U to Y a thickening (node proof step 4).
Steps 1--3 construct the matching-sections sheaf and its affine charts, using
lem-sfb-ring-fibre-product-spectrum, lem-weil-pbc-thickening-affine-scheme,
lem-sfb-affine-closed-pinching-pushout and lem-weil-pbc-scheme-morphism-gluing.
Step 7 identifies C with D tensor_B A and C'/IC'. Step 8 applies
lem-sfb-patched-module-base-change to N = D and M' = C'; its canonical maps are
ring maps on pure tensors, hence algebra isomorphisms. The affine-spectrum
fibre-product identification turns them into the required local inverses.
Their uniqueness and scheme-morphism gluing give the two global inverses. -/
theorem infinitesimalPushout_recovery
    {T T' S P U X Y Z : Scheme.{u}}
    (i : T ⟶ T') (a : T ⟶ S) (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsThickening i) [IsAffineHom a] (hp : IsPushout a i j b)
    (uX : U ⟶ X) (uY : U ⟶ Y) (t : U ⟶ T) (x : X ⟶ S) (y : Y ⟶ T')
    (hX : IsPullback uX t x a) (hY : IsPullback uY t y i)
    (k : X ⟶ Z) (l : Y ⟶ Z) (hz : IsPushout uX uY k l)
    (p : Z ⟶ P) (hk : k ≫ p = x ≫ j) (hl : l ≫ p = y ≫ b) :
    IsPullback k x p j ∧ IsPullback l y p b := by
  sorry

/-- Every affine base open gives the canonical fibre-product ring chart.
The open equalities specify inverse images; the containment witnesses only type the
section maps and impose no further restriction. Nilpotence is elementwise.
Source: Stacks, Tag 07RT (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: node steps 1--3 construct the structure sheaf as matching pairs, using the
ring-fibre-product spectrum and localization lemma and affine pinching pushout.
Step 5 restricts this same construction to any open. In step 6, S0 is affine since
S to P is a closed immersion; T0 is affine since a is affine; T'0 is affine by
lem-weil-pbc-thickening-affine-scheme. The affine pinching pushout identifies R
with B times_A A' by its two actual projections. The closed immersion gives the
surjection, and the quotient-spectrum and radical lemmas give its nil kernel. -/
theorem infinitesimalPushout_base_affine_chart
    {T T' S P : Scheme.{u}}
    (i : T ⟶ T') (a : T ⟶ S) (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsThickening i) [IsAffineHom a] (hp : IsPushout a i j b)
    (P0 : P.Opens) (S0 : S.Opens) (T'0 : T'.Opens) (T0 : T.Opens)
    (hP0 : IsAffineOpen P0)
    (hS0 : S0 = j ⁻¹ᵁ P0) (hT'0 : T'0 = b ⁻¹ᵁ P0) (hT0 : T0 = a ⁻¹ᵁ S0)
    (ej : S0 ≤ j ⁻¹ᵁ P0) (eb : T'0 ≤ b ⁻¹ᵁ P0)
    (ea : T0 ≤ a ⁻¹ᵁ S0) (ei : T0 ≤ i ⁻¹ᵁ T'0) :
    IsAffineOpen S0 ∧ IsAffineOpen T'0 ∧ IsAffineOpen T0 ∧
      Function.Surjective (i.appLE T'0 T0 ei).hom ∧
      (∀ z ∈ RingHom.ker (i.appLE T'0 T0 ei).hom, IsNilpotent z) ∧
      IsIso (infinitesimalSectionPullback hp.toCommSq P0 S0 T'0 T0 ej eb ea ei) := by
  sorry

/-- Every affine total-space chart has the stated canonical algebra descriptions.
The two `IsPushout` squares giving C and the last two giving D and C' are tensor
identifications. The surjection and kernel equality give C = C'/IC'. The ring
pullback comparison gives E = D times_C C'. All arrows are the prescribed section
maps, so these are identifications over the indicated base rings.
Source: Stacks, Tag 07RV (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: steps 4--5 apply the matching-sections construction also to Z and restrict
it to Z0. Step 7 obtains affineness of X0, U0 and Y0 from the thickening, affine
map and affine-thickening lemma. The affine-spectrum fibre-product lemma gives
C = D tensor_B A and C = C' tensor_A' A. The latter is the quotient by IC':
the mutually inverse maps are multiplication modulo IC' and c' to c' tensor 1.
The affine pinching pushout gives E = D times_C C'. Step 8 applies
lem-sfb-patched-module-base-change to the underlying modules; multiplication on
pure tensors shows its bijections respect the algebra structures. This gives
E tensor_R B = D and E tensor_R A' = C'. -/
theorem infinitesimalPushout_total_affine_chart
    {T T' S P U X Y Z : Scheme.{u}}
    (i : T ⟶ T') (a : T ⟶ S) (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsThickening i) [IsAffineHom a] (hp : IsPushout a i j b)
    (uX : U ⟶ X) (uY : U ⟶ Y) (t : U ⟶ T) (x : X ⟶ S) (y : Y ⟶ T')
    (hX : IsPullback uX t x a) (hY : IsPullback uY t y i)
    (k : X ⟶ Z) (l : Y ⟶ Z) (hz : IsPushout uX uY k l)
    (p : Z ⟶ P) (hk : k ≫ p = x ≫ j) (hl : l ≫ p = y ≫ b)
    (P0 : P.Opens) (S0 : S.Opens) (T'0 : T'.Opens) (T0 : T.Opens)
    (Z0 : Z.Opens) (X0 : X.Opens) (Y0 : Y.Opens) (U0 : U.Opens)
    (hP0 : IsAffineOpen P0) (hZ0 : IsAffineOpen Z0) (hmap : Z0 ≤ p ⁻¹ᵁ P0)
    (hS0 : S0 = j ⁻¹ᵁ P0) (hT'0 : T'0 = b ⁻¹ᵁ P0) (hT0 : T0 = a ⁻¹ᵁ S0)
    (hX0 : X0 = k ⁻¹ᵁ Z0) (hY0 : Y0 = l ⁻¹ᵁ Z0) (hU0 : U0 = uX ⁻¹ᵁ X0)
    (ej : S0 ≤ j ⁻¹ᵁ P0) (eb : T'0 ≤ b ⁻¹ᵁ P0)
    (ea : T0 ≤ a ⁻¹ᵁ S0) (ei : T0 ≤ i ⁻¹ᵁ T'0)
    (ex : X0 ≤ x ⁻¹ᵁ S0) (ey : Y0 ≤ y ⁻¹ᵁ T'0) (et : U0 ≤ t ⁻¹ᵁ T0)
    (ek : X0 ≤ k ⁻¹ᵁ Z0) (el : Y0 ≤ l ⁻¹ᵁ Z0)
    (euX : U0 ≤ uX ⁻¹ᵁ X0) (euY : U0 ≤ uY ⁻¹ᵁ Y0) :
    IsAffineOpen X0 ∧ IsAffineOpen Y0 ∧ IsAffineOpen U0 ∧
      IsIso (infinitesimalSectionPushout hX.toCommSq S0 X0 T0 U0 ex ea euX et) ∧
      IsIso (infinitesimalSectionPushout hY.toCommSq T'0 Y0 T0 U0 ey ei euY et) ∧
      Function.Surjective (uY.appLE Y0 U0 euY).hom ∧
      RingHom.ker (uY.appLE Y0 U0 euY).hom =
        Ideal.map (y.appLE T'0 Y0 ey).hom (RingHom.ker (i.appLE T'0 T0 ei).hom) ∧
      IsIso (infinitesimalSectionPullback hz.toCommSq Z0 X0 Y0 U0 ek el euX euY) ∧
      IsPushout (p.appLE P0 Z0 hmap) (j.appLE P0 S0 ej)
        (k.appLE Z0 X0 ek) (x.appLE S0 X0 ex) ∧
      IsPushout (p.appLE P0 Z0 hmap) (b.appLE P0 T'0 eb)
        (l.appLE Z0 Y0 el) (y.appLE T'0 Y0 ey) := by
  sorry

/-- Arbitrary open restriction preserves the scheme pushout, including inverse images
of opens of any target H. It suffices to apply this to O = h inverse-image H0 for
any extension h of a compatible pair of maps into H.
Source: Stacks, Tag 07RT (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: node step 5 restricts the coordinatewise fibre-product sheaf of step 1 to
O. Steps 2--3 give its scheme charts and pushout universal property, using affine
pinching and scheme-morphism gluing. This works for arbitrary opens: intersections
of affine opens are covered by affines, never assumed affine themselves. -/
theorem infinitesimalPushout_open_restriction
    {T T' S P : Scheme.{u}}
    (i : T ⟶ T') (a : T ⟶ S) (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsThickening i) [IsAffineHom a] (hp : IsPushout a i j b)
    (O : P.Opens) (OS : S.Opens) (OT' : T'.Opens) (OT : T.Opens)
    (hOS : OS = j ⁻¹ᵁ O) (hOT' : OT' = b ⁻¹ᵁ O) (hOT : OT = a ⁻¹ᵁ OS)
    (ej : OS ≤ j ⁻¹ᵁ O) (eb : OT' ≤ b ⁻¹ᵁ O)
    (ea : OT ≤ a ⁻¹ᵁ OS) (ei : OT ≤ i ⁻¹ᵁ OT') :
    IsPushout (a.resLE OS OT ea) (i.resLE OT' OT ei)
      (j.resLE O OS ej) (b.resLE O OT' eb) := by
  sorry

/-- The fibre-product comparisons commute with every compatible restriction of opens.
This is the construction-level compatibility in the node; applying it to the base
and total pushout charts gives compatibility of both fibre-product identifications.
Source: Stacks, Tags 07RT and 07RV
(blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: node step 9. Each projection is an actual scheme section map. Restriction
commutes with it by the presheaf naturality axiom. The two composites therefore
have equal projections, hence are equal by the ring pullback universal property.
This works for all smaller opens, including ones not principal in the chart. -/
theorem infinitesimalSectionPullback_restriction
    {K V K' W : Scheme.{u}} {a : K ⟶ V} {i : K ⟶ K'}
    {j : V ⟶ W} {b : K' ⟶ W} (h : CommSq a i j b)
    (OW0 OW1 : W.Opens) (OV0 OV1 : V.Opens)
    (OK'0 OK'1 : K'.Opens) (OK0 OK1 : K.Opens)
    (ej0 : OV0 ≤ j ⁻¹ᵁ OW0) (eb0 : OK'0 ≤ b ⁻¹ᵁ OW0)
    (ea0 : OK0 ≤ a ⁻¹ᵁ OV0) (ei0 : OK0 ≤ i ⁻¹ᵁ OK'0)
    (ej1 : OV1 ≤ j ⁻¹ᵁ OW1) (eb1 : OK'1 ≤ b ⁻¹ᵁ OW1)
    (ea1 : OK1 ≤ a ⁻¹ᵁ OV1) (ei1 : OK1 ≤ i ⁻¹ᵁ OK'1)
    (rW : OW1 ≤ OW0) (rV : OV1 ≤ OV0) (rK' : OK'1 ≤ OK'0) (rK : OK1 ≤ OK0) :
    W.presheaf.map (homOfLE rW).op ≫
        infinitesimalSectionPullback h OW1 OV1 OK'1 OK1 ej1 eb1 ea1 ei1 =
      infinitesimalSectionPullback h OW0 OV0 OK'0 OK0 ej0 eb0 ea0 ei0 ≫
        pullback.map (a.appLE OV0 OK0 ea0) (i.appLE OK'0 OK0 ei0)
          (a.appLE OV1 OK1 ea1) (i.appLE OK'1 OK1 ei1)
          (V.presheaf.map (homOfLE rV).op) (K'.presheaf.map (homOfLE rK').op)
          (K.presheaf.map (homOfLE rK).op)
          (by simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE])
          (by simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]) := by
  sorry

/-- The tensor comparisons commute with every compatible restriction of opens.
Apply this to (uX,t,x,a), (uY,t,y,i), (k,x,p,j), and (l,y,p,b) for the four tensor
identifications of the affine chart. Here the last two squares commute by hk, hl.
Source: Stacks, Tag 07RV (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: node step 9. A tensor comparison sends e tensor b to the product of the
two images in the section ring. Each restriction is a ring map and commutes with
these two images. Thus the maps agree on pure tensors, or equivalently on the two
structure maps of the ring pushout. Their inverses commute too by uniqueness. -/
theorem infinitesimalSectionPushout_restriction
    {K V K' W : Scheme.{u}} {a : K ⟶ V} {i : K ⟶ K'}
    {j : V ⟶ W} {b : K' ⟶ W} (h : CommSq a i j b)
    (OW0 OW1 : W.Opens) (OV0 OV1 : V.Opens)
    (OK'0 OK'1 : K'.Opens) (OK0 OK1 : K.Opens)
    (ej0 : OV0 ≤ j ⁻¹ᵁ OW0) (eb0 : OK'0 ≤ b ⁻¹ᵁ OW0)
    (ea0 : OK0 ≤ a ⁻¹ᵁ OV0) (ei0 : OK0 ≤ i ⁻¹ᵁ OK'0)
    (ej1 : OV1 ≤ j ⁻¹ᵁ OW1) (eb1 : OK'1 ≤ b ⁻¹ᵁ OW1)
    (ea1 : OK1 ≤ a ⁻¹ᵁ OV1) (ei1 : OK1 ≤ i ⁻¹ᵁ OK'1)
    (rW : OW1 ≤ OW0) (rV : OV1 ≤ OV0) (rK' : OK'1 ≤ OK'0) (rK : OK1 ≤ OK0) :
    infinitesimalSectionPushout h OW0 OV0 OK'0 OK0 ej0 eb0 ea0 ei0 ≫
        K.presheaf.map (homOfLE rK).op =
      pushout.map (j.appLE OW0 OV0 ej0) (b.appLE OW0 OK'0 eb0)
        (j.appLE OW1 OV1 ej1) (b.appLE OW1 OK'1 eb1)
        (V.presheaf.map (homOfLE rV).op) (K'.presheaf.map (homOfLE rK').op)
        (W.presheaf.map (homOfLE rW).op)
        (by simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE])
        (by simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]) ≫
          infinitesimalSectionPushout h OW1 OV1 OK'1 OK1 ej1 eb1 ea1 ei1 := by
  sorry

/-- The quotient identifications commute with restriction. In the total chart take
f = uY; the preceding chart theorem identifies its kernel with the extended ideal IC'.
The containment witness `hker` simply types the induced map of these kernel quotients;
it follows from naturality of the section maps. No chosen isomorphism is substituted
for the canonical first-isomorphism-theorem comparison.
Source: Stacks, Tag 07RV (blueprint: lem-sfb-infinitesimal-pushout-affine-charts).

Proof: node step 9. Represent a quotient class by c'. Both routes send it to the
restriction of its image in C. These agree by naturality of the section map.
Quotient induction gives equality on every class. The kernel equality in the chart
theorem identifies these quotients with C'/IC', compatibly with their projections;
uniqueness of inverses gives compatibility of the inverse identifications as well. -/
theorem infinitesimalQuotient_restriction
    {K V : Scheme.{u}} (f : K ⟶ V)
    (OV0 OV1 : V.Opens) (OK0 OK1 : K.Opens)
    (e0 : OK0 ≤ f ⁻¹ᵁ OV0) (e1 : OK1 ≤ f ⁻¹ᵁ OV1)
    (rV : OV1 ≤ OV0) (rK : OK1 ≤ OK0)
    (hs0 : Function.Surjective (f.appLE OV0 OK0 e0).hom)
    (hs1 : Function.Surjective (f.appLE OV1 OK1 e1).hom)
    (hker : RingHom.ker (f.appLE OV0 OK0 e0).hom ≤
      Ideal.comap (V.presheaf.map (homOfLE rV).op).hom
        (RingHom.ker (f.appLE OV1 OK1 e1).hom)) :
    CommRingCat.ofHom
        ((f.appLE OV0 OK0 e0).hom.quotientKerEquivOfSurjective hs0).toRingHom ≫
        K.presheaf.map (homOfLE rK).op =
      CommRingCat.ofHom (Ideal.quotientMap (RingHom.ker (f.appLE OV1 OK1 e1).hom)
        (V.presheaf.map (homOfLE rV).op).hom hker) ≫
        CommRingCat.ofHom
          ((f.appLE OV1 OK1 e1).hom.quotientKerEquivOfSurjective hs1).toRingHom := by
  sorry

end AlgebraicGeometry
