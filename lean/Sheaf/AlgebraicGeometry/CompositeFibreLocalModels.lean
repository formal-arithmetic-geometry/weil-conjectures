/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.Topology.PresheafModuleStalkFunctor

import Sheaf.RingTheory.FibreLocalRingNaturalIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Local models of the fibres of a composite

Source: Stacks Project, Tags 0HA1, 01T3, 01T4, 01T6, 01U8, 02FX
(blueprint: lem-sbc-composite-fibre-local-models).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
