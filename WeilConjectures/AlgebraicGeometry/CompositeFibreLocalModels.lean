/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FibreStalkQuotient

/-! # Local models of the fibres of a composite

Source: Stacks Project, Tags 0HA1, 01T3, 01T4, 01T6, 01U8, 02FX
(blueprint: lem-sbc-composite-fibre-local-models).
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem fibre_neighbourhood {Y T : Scheme.{u}} (g : Y ⟶ T)
    [LocallyOfFiniteType g] (y : Y) :
    ∃ V : (g.fiber (g y)).Opens, IsAffineOpen V ∧
      LocallyOfFiniteType (V.ι ≫ g.fiberToSpecResidueField (g y)) ∧
      QuasiCompact (V.ι ≫ g.fiberToSpecResidueField (g y)) ∧
      ∃ v : V, V.ι v = g.asFiber y ∧ IsIso (V.ι.stalkMap v) ∧
        IsIso (V.ι.residueFieldMap v) ∧
        IsIso ((g.fiberι (g y)).residueFieldMap (V.ι v)) ∧
        IsIso ((V.ι ≫ g.fiberι (g y)).residueFieldMap v) := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := g.asFiber y) (U := ⊤) trivial
  have : IsAffine V := hV
  have : LocallyOfFiniteType (g.fiberToSpecResidueField (g y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let v : V := ⟨g.asFiber y, hy⟩
  have hres : IsIso ((g.fiberι (g y)).residueFieldMap (V.ι v)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨RingHom.injective _, ?_⟩
    intro z
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨w, hw⟩ := (g.fiberι (g y)).stalkMap_surjective (V.ι v) z
    refine ⟨IsLocalRing.residue _ w, ?_⟩
    change IsLocalRing.residue _ ((g.fiberι (g y)).stalkMap (V.ι v) w) = _
    rw [hw]
  refine ⟨V, hV, inferInstance, inferInstance, v, rfl, inferInstance, inferInstance,
    hres, ?_⟩
  rw [Scheme.residueFieldMap_comp]
  infer_instance

private theorem residue_square {Y Z U X : Scheme.{u}} (b : Y ⟶ Z) (i : Y ⟶ U)
    (j : Z ⟶ X) (a : U ⟶ X) (h : b ≫ j = i ≫ a)
    (p : Y) (q : Z) (v : U) (hb : b p = q) (hi : i p = v) (hj : j q = a v) :
    (X.residueFieldCongr hj).inv ≫ j.residueFieldMap q ≫
      (Z.residueFieldCongr hb).inv ≫ b.residueFieldMap p =
      a.residueFieldMap v ≫ (U.residueFieldCongr hi).inv ≫ i.residueFieldMap p := by
  subst q v
  have hh := Scheme.Hom.residueFieldMap_congr h p
  simp only [Scheme.residueFieldMap_comp] at hh
  simpa using congrArg (fun k ↦ (X.residueFieldCongr hj).inv ≫ k) hh

private theorem stalk_square {Y Z U X : Scheme.{u}} (b : Y ⟶ Z) (i : Y ⟶ U)
    (j : Z ⟶ X) (a : U ⟶ X) (h : b ≫ j = i ≫ a)
    (p : Y) (q : Z) (v : U) (hb : b p = q) (hi : i p = v) (hj : j q = a v) :
    (X.presheaf.stalkCongr (.of_eq hj)).inv ≫ j.stalkMap q ≫
      (Z.presheaf.stalkCongr (.of_eq hb)).inv ≫ b.stalkMap p =
      a.stalkMap v ≫ (U.presheaf.stalkCongr (.of_eq hi)).inv ≫ i.stalkMap p := by
  subst q v
  have hh := Scheme.Hom.stalkMap_congr_hom _ _ h p
  simp only [Scheme.Hom.stalkMap_comp] at hh
  simpa using congrArg (fun k ↦ (X.presheaf.stalkCongr (.of_eq hj)).inv ≫ k) hh

private theorem quotient_common_source {E B C : Type u}
    [CommRing E] [CommRing B] [CommRing C]
    (ρ : E →+* B) (σ : E →+* C) (hρ : Function.Surjective ρ)
    (hσ : Function.Surjective σ) (J : Ideal B)
    (hk : RingHom.ker σ = J.comap ρ) :
    ∃ e : (B ⧸ J) ≃+* C, ∀ z, e (Ideal.Quotient.mk J (ρ z)) = σ z := by
  let τ := (Ideal.Quotient.mk J).comp ρ
  have hτ : Function.Surjective τ := Ideal.Quotient.mk_surjective.comp hρ
  have hk' : RingHom.ker τ = RingHom.ker σ := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hk]
  let e := (τ.quotientKerEquivOfSurjective hτ).symm.trans
    ((Ideal.quotEquivOfEq hk').trans (σ.quotientKerEquivOfSurjective hσ))
  refine ⟨e, ?_⟩
  intro z
  change e (τ z) = σ z
  simp [e]

private theorem surjective_square_pushout {D E A B : CommRingCat.{u}}
    (d : D ⟶ E) (π : D ⟶ A) (ρ : E ⟶ B) (φ : A ⟶ B)
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hw : π ≫ φ = d ≫ ρ) (hk : RingHom.ker ρ.hom = (RingHom.ker π.hom).map d.hom) :
    IsPushout d π ρ φ := by
  let s := PushoutCocone.mk ρ φ hw.symm
  apply IsPushout.of_isColimit (c := s)
  apply PushoutCocone.isColimitAux'
  intro t
  have hkill : RingHom.ker ρ.hom ≤ RingHom.ker t.inl.hom := by
    rw [hk, Ideal.map_le_iff_le_comap]
    intro z hz
    have he := congrArg (fun k ↦ k z) t.condition
    change t.inl.hom (d.hom z) = 0
    simpa [RingHom.mem_ker.mp hz] using he
  let l := ρ.hom.liftOfSurjective hρ ⟨t.inl.hom, hkill⟩
  have hl (z : E) : l (ρ z) = t.inl z := ρ.hom.liftOfSurjective_comp_apply hρ _ z
  refine ⟨CommRingCat.ofHom l, ?_, ?_, ?_⟩
  · ext z
    exact hl z
  · ext z
    obtain ⟨z, rfl⟩ := hπ z
    have he := congrArg (fun k ↦ k z) hw
    change l (φ (π z)) = t.inr (π z)
    rw [show φ (π z) = ρ (d z) from he, hl]
    exact congrArg (fun k ↦ k z) t.condition
  · intro m hm _
    ext z
    obtain ⟨z, rfl⟩ := hρ z
    change m.hom (ρ z) = l (ρ z)
    rw [hl]
    exact congrArg (fun k ↦ k z) hm

/-- Local models for the three pointed fibres, including their canonical maps.

Source: Stacks Project, Tags 0HA1, 01T3, 01T4, 01T6, 01U8, 02FX
(blueprint: lem-sbc-composite-fibre-local-models).

1. By clause (e) of [lem-weil-pbc-proper-fp-permanence], $f\circ a$ is locally of finite type.
Apply [lem-weil-pbc-lft-base-change] to $f$, $f\circ a$, and $a$, over
$\operatorname{Spec}\kappa(s)$, $\operatorname{Spec}\kappa(s)$, and
$\operatorname{Spec}\kappa(x)$ respectively. Thus $X_s,U_s,U_x$ are locally of finite type over
their indicated fields. The universal property in [def-pc-fibre-product] gives the map
$a_s:U_s\to X_s$: its projections are $a$ composed with the projection to $U$, and the
projection to $\operatorname{Spec}\kappa(s)$. Its point over $u$ maps to the point over $x$ by
[def-pc-scheme-fibre].

2. For each of these three field schemes, the defining affine cover in
[def-weil-finite-type-morphism] over the affine base $\operatorname{Spec}k$ supplies an affine
neighbourhood $V=\operatorname{Spec}E$ of the specified point. By
[lem-weil-pbc-lft-affine-pairs], $E$ is finitely generated over $k$. Hence
$V\to\operatorname{Spec}k$ is finite type: its one affine chart is a finite cover of the
preimage of the whole base. A field is Noetherian since each ideal is either zero or generated
by $1$. Apply [lem-weil-pbc-finite-type-algebra-noetherian] to get $E$ Noetherian. At the chosen
point, [lem-weil-pbc-affine-open-stalk-localization] gives the stalk as $E_{\mathfrak p}$, and
[lem-weil-pbc-localization-noetherian] makes it Noetherian. These are precisely $A,B,C$. They
are local because they are stalks of schemes [def-pc-scheme]. This argument never assumes
$S,X,U$ themselves Noetherian or globally of finite type.

3. We spell out the general stalk calculation used for each of the three fibres. For any scheme
morphism $g:Y\to T$ and $y\mapsto t$, [lem-weil-pbc-affine-opens-basis] supplies affine opens
$T_0=\operatorname{Spec}H$ containing $t$ and $Y_0=\operatorname{Spec}L$ containing $y$ inside
$g^{-1}(T_0)$. By [def-weil-affine-spectrum], the restricted map is $\operatorname{Spec}\varphi$
for its section map $\varphi:H\to L$. Write $\mathfrak p,\mathfrak q$ for the corresponding
primes, so $\varphi^{-1}(\mathfrak q)=\mathfrak p$. The germ-compatible isomorphism of
[lem-weil-pbc-affine-open-stalk-localization] identifies $H_{\mathfrak p}$ with $\mathcal
O_{T,t}$, $L_{\mathfrak q}$ with $\mathcal O_{Y,y}$, and their unique maximal ideals.
[lem-weil-pbc-spec-residue-field-identification] identifies $\kappa(t)$ with $\kappa(\mathfrak
p)$ and identifies the map into $T_0$ with $\operatorname{Spec}$ of $H\to H_{\mathfrak
p}\to\kappa(\mathfrak p)$. The map $\operatorname{Spec}\kappa(t)\to T$ factors through $T_0$
since its image is $t$; its restricted germs are the same. By [lem-weil-pbc-open-fibre-product],
$Y_0\times_{T_0}\operatorname{Spec}\kappa(t)$ is an open neighbourhood of $y$ in $Y_t$,
compatibly with the projection to $Y$. By [lem-weil-pbc-fibre-product-affine-spectra] it is
$\operatorname{Spec}F$ for $F=L\otimes_H\kappa(\mathfrak p)$, and the projection is
$\operatorname{Spec}j$, $j(l)=l\otimes1$. Let $\mathfrak Q$ be the prime corresponding to $y$ in
this open; the projection gives $j^{-1}(\mathfrak Q)=\mathfrak q$.
[lem-weil-pbc-spec-map-stalk-localization] identifies its stalk map with $L_{\mathfrak q}\to
F_{\mathfrak Q}$, $l/v\mapsto j(l)/j(v)$. By [lem-weil-pbc-fibre-ring-local-ring-natural-iso],
this map is surjective with kernel $\mathfrak p L_{\mathfrak q}$. Since $\mathfrak m_t=\mathfrak
pH_{\mathfrak p}$, that ideal is $\mathfrak m_t\mathcal O_{Y,y}$: denominators from
$H\setminus\mathfrak p$ are units in $L_{\mathfrak q}$. Consequently the actual fibre-projection
stalk map gives $\mathcal O_{Y,y}/\mathfrak m_t\mathcal O_{Y,y}\cong\mathcal O_{Y_t,y}$, sending
the class of every original germ to its image germ. The existing cited statements supply both
the stalk maps and their kernels; no compatibility of an unspecified isomorphism is assumed.

4. Put $R=\mathcal O_{S,s}$, $D=\mathcal O_{X,x}$, $E=\mathcal O_{U,u}$ and $I=\mathfrak m_R D$.
Apply step 3 to $f,f\circ a,a$. Its projection-compatible isomorphisms give $A=D/I$,
$B=E/\mathfrak m_R E$, and $C=E/\mathfrak m_D E$. Since $a_s$ is a scheme morphism,
[def-weil-locally-ringed-space-morphism] makes $A\to B$ local. More explicitly, the commuting
projection square identifies this map with $d\bmod I\mapsto a_u^\sharp(d)\bmod\mathfrak m_R E$:
both composites from $D$ are the same stalk map by the stated composition rule. Because $R\to D$
is local, $I\subseteq\mathfrak m_D$ and $\mathfrak m_A=\mathfrak m_D/I$. Thus $\mathfrak m_A B$
is generated by the classes of $a_u^\sharp(\mathfrak m_D)$, and $B/\mathfrak m_A B\to C$,
sending the class of $e$ to $e\bmod\mathfrak m_D E$, is an isomorphism: the map $E\to
B/\mathfrak m_A B$ is surjective and its kernel is exactly $\mathfrak m_D E$, since $\mathfrak
m_R E\subseteq\mathfrak m_D E$. This is the canonical closed-fibre identification.

5. If $a$ is flat at $u$, [def-weil-flat-morphism] says $E$ is a flat $D$-module. Apply
[lem-weil-pbc-flat-module-quotient-flat] with the ideal $I=\mathfrak m_R D$. It says $E/IE$ is
flat over $D/I$. The ideal $IE$ equals $\mathfrak m_R E$: its generators are the composites of
elements of $\mathfrak m_R$, and extending a generated ideal twice does not change its
generators. Hence the quotients from step 4 are $A=D/I$ and $B=E/IE$, with exactly the induced
scalar action $d\bmod I$ acting through $a_u^\sharp(d)$. Therefore $A\to B$ is flat. Only
flatness at the specified point was used; global flatness of $a$ was not substituted for it.

6. The fibre projections preserve the residue fields explicitly. For each application of step 3,
the ideal $\mathfrak m_tD$ lies in the maximal ideal $\mathfrak m_y$ of $D$ because the original
stalk map is local. The quotient $D/\mathfrak m_tD$ has maximal ideal $\mathfrak m_y/\mathfrak
m_tD$: elements outside it are classes of units of $D$, while the further quotient is the field
$D/\mathfrak m_y$. Its residue field is therefore canonically $D/\mathfrak m_y$ by
$[d]\mapsto[d]$. Apply this to the three fibres to obtain $\kappa(x),\kappa(u),\kappa(u)$. On
each chosen affine neighbourhood, [lem-weil-pbc-affine-open-stalk-localization] identifies the
same stalk through the germ map, so quotienting by its unique maximal ideal identifies the same
residue field. By [def-weil-residue-field] and the composition rule of
[def-weil-locally-ringed-space-morphism], the maps of residue fields are obtained by reducing
the actual stalk maps. Thus a germ $r\in R$ maps to the class of $f_x^\sharp(r)$ in $\kappa(x)$
and then to the class of $a_u^\sharp f_x^\sharp(r)$ in $\kappa(u)$; this is also its image
through the composite. The isomorphisms above send every germ to its own residue class, so
commute with these maps and give the asserted tower compatibility.

The map `b` is the unique map of fibres with the displayed projections, and `φ` is its
stalk map transported along `hb`. The equation for `e` specifies the closed-fibre
isomorphism on every original germ. The neighbourhood identifications are asserted for
the actual inclusion stalk and residue maps, and their composites with fibre projections.
-/
theorem composite_fibre_local_models
    {U X S : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType a] [LocallyOfFiniteType f]
    (u₀ : U) :
    IsNoetherianRing ((f.fiber (f (a u₀))).presheaf.stalk (f.asFiber (a u₀))) ∧
      IsNoetherianRing (((a ≫ f).fiber (f (a u₀))).presheaf.stalk ((a ≫ f).asFiber u₀)) ∧
      IsNoetherianRing ((a.fiber (a u₀)).presheaf.stalk (a.asFiber u₀)) ∧
      (∃ b : (a ≫ f).fiber (f (a u₀)) ⟶ f.fiber (f (a u₀)),
        b ≫ f.fiberι (f (a u₀)) = (a ≫ f).fiberι (f (a u₀)) ≫ a ∧
        b ≫ f.fiberToSpecResidueField (f (a u₀)) =
          (a ≫ f).fiberToSpecResidueField (f (a u₀)) ∧
        ∃ hb : b ((a ≫ f).asFiber u₀) = f.asFiber (a u₀),
        ∃ φ : (f.fiber (f (a u₀))).presheaf.stalk (f.asFiber (a u₀)) →+*
            ((a ≫ f).fiber (f (a u₀))).presheaf.stalk ((a ≫ f).asFiber u₀),
          φ = (((f.fiber (f (a u₀))).presheaf.stalkCongr (.of_eq hb)).inv ≫
            b.stalkMap ((a ≫ f).asFiber u₀)).hom ∧
          IsLocalHom φ ∧
          (∃ e : (((a ≫ f).fiber (f (a u₀))).presheaf.stalk ((a ≫ f).asFiber u₀) ⧸
              Ideal.map φ (IsLocalRing.maximalIdeal _)) ≃+*
              (a.fiber (a u₀)).presheaf.stalk (a.asFiber u₀),
            ∀ z : U.presheaf.stalk u₀,
              e (Ideal.Quotient.mk _
                (((U.presheaf.stalkCongr
                    (.of_eq ((a ≫ f).fiberι_asFiber u₀))).inv ≫
                  ((a ≫ f).fiberι (f (a u₀))).stalkMap ((a ≫ f).asFiber u₀)) z)) =
                ((U.presheaf.stalkCongr (.of_eq (a.fiberι_asFiber u₀))).inv ≫
                  (a.fiberι (a u₀)).stalkMap (a.asFiber u₀)) z) ∧
          ((X.residueFieldCongr (f.fiberι_asFiber (a u₀))).inv ≫
              (f.fiberι (f (a u₀))).residueFieldMap (f.asFiber (a u₀)) ≫
              ((f.fiber (f (a u₀))).residueFieldCongr hb).inv ≫
              b.residueFieldMap ((a ≫ f).asFiber u₀) =
            a.residueFieldMap u₀ ≫
              (U.residueFieldCongr ((a ≫ f).fiberι_asFiber u₀)).inv ≫
              ((a ≫ f).fiberι (f (a u₀))).residueFieldMap ((a ≫ f).asFiber u₀)) ∧
          (RingHom.Flat (a.stalkMap u₀).hom → RingHom.Flat φ)) ∧
      (∃ V : (f.fiber (f (a u₀))).Opens,
        IsAffineOpen V ∧
        LocallyOfFiniteType (V.ι ≫ f.fiberToSpecResidueField (f (a u₀))) ∧
        QuasiCompact (V.ι ≫ f.fiberToSpecResidueField (f (a u₀))) ∧
        ∃ v : V, V.ι v = f.asFiber (a u₀) ∧
          IsIso (V.ι.stalkMap v) ∧ IsIso (V.ι.residueFieldMap v) ∧
          IsIso ((f.fiberι (f (a u₀))).residueFieldMap (V.ι v)) ∧
          IsIso ((V.ι ≫ f.fiberι (f (a u₀))).residueFieldMap v)) ∧
      (∃ W : ((a ≫ f).fiber (f (a u₀))).Opens,
        IsAffineOpen W ∧
        LocallyOfFiniteType (W.ι ≫ (a ≫ f).fiberToSpecResidueField (f (a u₀))) ∧
        QuasiCompact (W.ι ≫ (a ≫ f).fiberToSpecResidueField (f (a u₀))) ∧
        ∃ v : W, W.ι v = (a ≫ f).asFiber u₀ ∧
          IsIso (W.ι.stalkMap v) ∧ IsIso (W.ι.residueFieldMap v) ∧
          IsIso (((a ≫ f).fiberι (f (a u₀))).residueFieldMap (W.ι v)) ∧
          IsIso ((W.ι ≫ (a ≫ f).fiberι (f (a u₀))).residueFieldMap v)) ∧
      (∃ T : (a.fiber (a u₀)).Opens,
        IsAffineOpen T ∧
        LocallyOfFiniteType (T.ι ≫ a.fiberToSpecResidueField (a u₀)) ∧
        QuasiCompact (T.ι ≫ a.fiberToSpecResidueField (a u₀)) ∧
        ∃ v : T, T.ι v = a.asFiber u₀ ∧
          IsIso (T.ι.stalkMap v) ∧ IsIso (T.ι.residueFieldMap v) ∧
          IsIso ((a.fiberι (a u₀)).residueFieldMap (T.ι v)) ∧
          IsIso ((T.ι ≫ a.fiberι (a u₀)).residueFieldMap v)) ∧
      (f.residueFieldMap (a u₀) ≫ a.residueFieldMap u₀ =
        (a ≫ f).residueFieldMap u₀) := by
  classical
  have hf : LocallyOfFiniteType (f.fiberToSpecResidueField (f (a u₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have haf : LocallyOfFiniteType ((a ≫ f).fiberToSpecResidueField (f (a u₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have ha : LocallyOfFiniteType (a.fiberToSpecResidueField (a u₀)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hfn := LocallyOfFiniteType.isLocallyNoetherian
    (f.fiberToSpecResidueField (f (a u₀)))
  have hafn := LocallyOfFiniteType.isLocallyNoetherian
    ((a ≫ f).fiberToSpecResidueField (f (a u₀)))
  have han := LocallyOfFiniteType.isLocallyNoetherian (a.fiberToSpecResidueField (a u₀))
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · let b : (a ≫ f).fiber (f (a u₀)) ⟶ f.fiber (f (a u₀)) :=
      pullback.lift ((a ≫ f).fiberι _ ≫ a)
        ((a ≫ f).fiberToSpecResidueField _) (by simp [Category.assoc, Scheme.Hom.fiber_fac])
    have hb₁ : b ≫ f.fiberι _ = (a ≫ f).fiberι _ ≫ a := pullback.lift_fst ..
    have hb₂ : b ≫ f.fiberToSpecResidueField _ =
        (a ≫ f).fiberToSpecResidueField _ := pullback.lift_snd ..
    have hb : b ((a ≫ f).asFiber u₀) = f.asFiber (a u₀) := by
      apply (f.fiberι _).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hb₁]
      change a ((a ≫ f).fiberι _ ((a ≫ f).asFiber u₀)) = _
      rw [Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]
    let φ := (((f.fiber (f (a u₀))).presheaf.stalkCongr (.of_eq hb)).inv ≫
      b.stalkMap ((a ≫ f).asFiber u₀)).hom
    let π := f.fiberStalkMap (a u₀)
    let ρ := (a ≫ f).fiberStalkMap u₀
    let σ := a.fiberStalkMap u₀
    obtain ⟨hπ, hkπ, -⟩ := f.fiberStalkMap_surjective_ker_quotientEquiv (a u₀)
    obtain ⟨hρ, hkρ, -⟩ := (a ≫ f).fiberStalkMap_surjective_ker_quotientEquiv u₀
    obtain ⟨hσ, hkσ, -⟩ := a.fiberStalkMap_surjective_ker_quotientEquiv u₀
    have hw : π ≫ CommRingCat.ofHom φ = a.stalkMap u₀ ≫ ρ := by
      exact stalk_square b ((a ≫ f).fiberι _) (f.fiberι _) a hb₁
        ((a ≫ f).asFiber u₀) (f.asFiber (a u₀)) u₀ hb
        ((a ≫ f).fiberι_asFiber u₀) (f.fiberι_asFiber (a u₀))
    have hw' : φ.comp π.hom = ρ.hom.comp (a.stalkMap u₀).hom :=
      congrArg CommRingCat.Hom.hom hw
    have hkρ' : RingHom.ker ρ.hom =
        (RingHom.ker π.hom).map (a.stalkMap u₀).hom := by
      rw [hkρ, hkπ, Ideal.map_map, Scheme.Hom.stalkMap_comp]
      rfl
    refine ⟨b, hb₁, hb₂, hb, φ, rfl, ?_, ?_, ?_, ?_⟩
    · dsimp [φ]
      infer_instance
    · let J := (IsLocalRing.maximalIdeal _).map φ
      have hJ : J = (RingHom.ker σ.hom).map ρ.hom := by
        dsimp only [J]
        rw [← IsLocalRing.map_maximalIdeal_of_surjective π.hom hπ,
          Ideal.map_map, hw', ← Ideal.map_map, hkσ]
      have hle : RingHom.ker ρ.hom ≤ RingHom.ker σ.hom := by
        rw [hkρ', hkσ]
        apply Ideal.map_mono
        exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π.hom)
      have hker : RingHom.ker σ.hom = J.comap ρ.hom := by
        rw [hJ, Ideal.comap_map_of_surjective _ hρ]
        exact (sup_eq_left.mpr hle).symm
      exact quotient_common_source ρ.hom σ.hom hρ hσ J hker
    · exact residue_square b ((a ≫ f).fiberι _) (f.fiberι _) a hb₁
        ((a ≫ f).asFiber u₀) (f.asFiber (a u₀)) u₀ hb
        ((a ≫ f).fiberι_asFiber u₀) (f.fiberι_asFiber (a u₀))
    · intro hflat
      exact MorphismProperty.of_isPushout
        (P := CommRingCat.flat)
        (surjective_square_pushout (a.stalkMap u₀) π ρ (CommRingCat.ofHom φ)
          hπ hρ hw hkρ').flip hflat
  · exact fibre_neighbourhood f (a u₀)
  · exact fibre_neighbourhood (a ≫ f) u₀
  · exact fibre_neighbourhood a u₀
  · exact (Scheme.residueFieldMap_comp a f u₀).symm

end AlgebraicGeometry
