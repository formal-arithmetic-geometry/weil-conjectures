/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.Data.ZMod.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LocalModuleIso
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.CategoryTheory.SiteConstantModuleHom
import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm

/-!
# Frame scheme of a finite étale local system

Source: Stacks Project, Tags 03RV and 03Q1
(blueprint: lem-sfb-finite-local-system-frame-scheme).

The auxiliary declarations spell out frames, their canonical inverse-image restrictions,
base-changed universal frames and the geometric-stalk comparison. They contain real data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteLocalSystemFrame

/-- The finite coefficient ring at the sheaf universe, by the standard canonical lift.
Source: Stacks, Tag 03RV (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
abbrev Coeff (ell : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod ell)

/-- The finite free coefficient module before universe enlargement.
Source: Stacks, Tag 03RV (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
abbrev model (ell n : ℕ) : ModuleCat.{0} (ZMod ell) :=
  ModuleCat.of (ZMod ell) (Fin n → ZMod ell)

/-- The same free module in the universe of étale sheaf coefficients.
Source: Stacks, Tag 03RV (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
abbrev liftedModel (ell n : ℕ) : ModuleCat.{u + 1} (Coeff.{u} ell) :=
  ModuleCat.of (Coeff.{u} ell) (Fin n → Coeff.{u} ell)

/-- The constant finite free module sheaf.
Source: Stacks, Tags 03RV, 093T (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable abbrev constant (T : Scheme.{u}) (ell n : ℕ) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell))).obj
    (liftedModel.{u} ell n)

/-- Frames on an arbitrary test scheme, using the actual étale inverse image.
Source: Stacks, Tags 03RV, 03Q1 (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
abbrev Frame {T U : Scheme.{u}} (ell n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell))) (v : U ⟶ T) :=
  constant U ell n ≅ (Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H

/-- Restrict a frame by inverse image, then the canonical constant and composite comparisons.
Source: Stacks, Tags 03Q1, 03CB (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable def restrict {T : Scheme.{u}} (ell n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell)))
    {U V : Over T} (w : U ⟶ V) (e : Frame ell n H V.hom) : Frame ell n H U.hom :=
  ((Etale.constantSheafCompUpperStarIso (Coeff.{u} ell) w.left).app (liftedModel.{u} ell n)).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) w.left).mapIso e ≪≫
    ((Etale.upperStarComp (ModuleCat.{u + 1} (Coeff.{u} ell)) w.left V.hom
      U.hom (Over.w w).symm).app H).symm

/-- Pullback of a specified universal frame is the map from scheme morphisms to frames.
Source: Stacks, Tag 03RV (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable def evaluation {T P : Scheme.{u}} (ell n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell)))
    (p : P ⟶ T) (e : Frame ell n H p) (U : Over T) :
    (U ⟶ Over.mk p) → Frame ell n H U.hom :=
  fun a ↦ restrict ell n H a e

/-- The universal frame pulled back to the scheme-theoretic fibre product.
Source: Stacks, Tag 03Q1 (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable def baseFrame {T P U : Scheme.{u}} (ell n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell)))
    (p : P ⟶ T) (e : Frame ell n H p) (v : U ⟶ T) :
    Frame ell n ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H)
      (pullback.snd p v) :=
  restrict ell n H
      (U := Over.mk (pullback.snd p v ≫ v)) (V := Over.mk p)
      (Over.homMk (pullback.fst p v) (pullback.condition (f := p) (g := v))) e ≪≫
    (Etale.upperStarComp (ModuleCat.{u + 1} (Coeff.{u} ell)) (pullback.snd p v) v).app H

/-- Forget the second component of a map into a base-changed scheme.
Source: Stacks, Tag 03Q1 (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable def forgetBaseChange {T P U : Scheme.{u}} (p : P ⟶ T) (v : U ⟶ T)
    (W : Over U) (a : W ⟶ Over.mk (pullback.snd p v)) :
    Over.mk (W.hom ≫ v) ⟶ Over.mk p :=
  Over.homMk (a.left ≫ pullback.fst p v) (by
    change (a.left ≫ pullback.fst p v) ≫ p = W.hom ≫ v
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun k : W.left ⟶ U ↦ k ≫ v) (Over.w a))

/-- A frame after pullback to a geometric point induces a frame of the original stalk.
Source: Stacks, Tag 03Q1(3) (blueprint: lem-sfb-finite-local-system-frame-scheme). -/
noncomputable def stalkFrame {T : Scheme.{u}} (ell n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (e : Frame ell n H s) :
    liftedModel.{u} ell n ≅ ((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj H :=
  (((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiberConstantSheafIso
      (liftedModel.{u} ell n)).symm ≪≫
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber.mapIso e ≪≫
    (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} (Coeff.{u} ell)) s
      (𝟙 (Spec (.of Ω)))).app H ≪≫
    eqToIso (congrArg (fun t ↦ ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber.obj H)
      (Category.id_comp s))

/-- **Frame scheme of a finite étale local system.**

Source: Stacks Project, Tags 03RV and 03Q1
(blueprint: lem-sfb-finite-local-system-frame-scheme).

Proof:

1. Put $M=A^n$ and $G=\operatorname{Aut}_A(M)=\operatorname{GL}_n(A)$. This is a nonempty finite
set: it contains the identity and embeds in the set of all functions from the finite set $M$ to
itself. Define $F(V)=\operatorname{Isom}_{\underline A_V}(\underline M_V,H|_V)$ for etale $V\to
T$. By [lem-weil-pbc-etale-inverse-image-restriction] and
[lem-pe-constant-left-module-inverse-image], restriction is canonically the inverse image used in
the question, including the module structure; [lem-sfb-geometric-inverse-image-constant-module]
identifies the restricted constant source with $\underline M_V$. Thus
[lem-sf-local-module-isom-sheaf] makes $F$ a sheaf of sets, with exactly the question's
restriction maps. The slice $T_{\mathrm{et}}/V$ is $V_{\mathrm{et}}$: composition and cancellation
of etale morphisms give the identification [lem-weil-pbc-etale-composition-cancellation].

2. On any scheme $V$, the canonical map $\underline G_V\to\mathcal Aut_{\underline A_V}(\underline
M_V)$ sends $g$ to its constant module automorphism. It is an isomorphism as follows. Since $M$ is
finite free, [lem-pur-site-constant-module-hom] identifies the endomorphism sheaf with
$\underline{\operatorname{End}_A(M)}_V$, by the canonical constant-map comparison. Its underlying
set sheaf is the constant set sheaf, by [def-sf-site-constant-module-functor] and
[lem-pc-sites-sheafification-underlying-sets]. Given an automorphism and its inverse,
[lem-weil-pbc-finite-constant-set-sections-cover] makes both constant, say $a,b$, on a common
etale covering. On a nonempty member, injectivity of constant labels gives $ab=ba=1$, so $a\in G$;
empty members have unique sections and impose no condition. This proves local surjectivity of the
displayed map. The same injectivity on nonempty members proves local injectivity. Both sides are
sheaves, so [lem-galois-set-sheaf-local-bijection-isomorphism] gives the claimed isomorphism. Its
construction uses the same constant linear maps after restriction.

3. Choose the given etale cover $t_i:T_i\to T$ and trivializations $\tau_i:\underline
M_{T_i}\simeq t_i^{-1}H$. Composition $g\mapsto\tau_i\circ g$ and its inverse
$\lambda\mapsto\tau_i^{-1}\circ\lambda$ identify $F|_{T_i}$ with $\underline G_{T_i}$ by Step 2.
Hence $F$ is finite locally constant. Apply [lem-galois-flc-representable] to obtain a finite
etale $p:P\to T$ and a sheaf isomorphism $\theta:h_P\simeq F$. Because $P$ is itself an object of
$T_{\mathrm{et}}$, set $\lambda_P=\theta_P(\mathrm{id}_P)$. Naturality gives
$\theta_V(a)=a^{-1}\lambda_P$ for every etale $V\to T$ and $a:V\to P$ over $T$, using the
inverse-image comparisons of Step 1.

4. For a trivializing chart $T_i$, the fibre-product property identifies $h_{P\times_TT_i}$ on
$(T_i)_{\mathrm{et}}$ with $h_P|_{T_i}$. Under $\theta$ and $\tau_i$, this is $\underline
G_{T_i}$. By [lem-galois-constant-sheaf-sets-representable], the latter is represented by
$\coprod_{g\in G}T_i$. Both representing schemes are etale over $T_i$: for the first use
[lem-weil-pbc-etale-scheme-base-change], and for the second apply [lem-sc-etale-coproduct-etale]
to the finite family of identity maps (each identity is an open immersion, hence etale by
[lem-weil-pbc-etale-composition-cancellation]). Yoneda [lem-galois-yoneda-fully-faithful] gives an
isomorphism $P\times_TT_i\simeq\coprod_{g\in G}T_i$ under which the pulled-back universal frame on
component $g$ is $\tau_i\circ g$. Indeed, its pullback along the component section is the image of
that constant label under $\theta$. Since $1\in G$, this chart projection has a section. For every
$t\in T$ choose a point of a covering chart over $t$ and then its point on the identity component;
its image in $P$ lies over $t$. Thus $p$ is surjective.

5. Now let $v:U\to T$ be arbitrary, and put $P_U=P\times_TU$, $q:P_U\to U$. Pull $\lambda_P$ back
to $P_U$ and use the constant-module comparison [lem-sfb-geometric-inverse-image-constant-module]
and the composite inverse-image comparison [lem-pe-constant-left-module-inverse-image] to obtain
$\lambda_{P_U}:\underline M_{P_U}\simeq q^{-1}v^{-1}H$. Pullback of this frame defines a morphism
of sheaves on $U_{\mathrm{et}}$ from $h_{P_U}$ to the local isomorphism sheaf $F_{v^{-1}H}$: the
source is a sheaf by [lem-weil-pbc-small-etale-representable-presheaf-sheaf], the target by
[lem-sf-local-module-isom-sheaf]. Pull back the cover $\{T_i\to T\}$ to $U$: by
[lem-weil-pbc-etale-covering-base-change] the projections $U\times_TT_i\to U$ are etale and
jointly surjective, hence a covering family of $U_{\mathrm{et}}$ as defined in
[def-weil-pbc-etale-site]. On $U_i=U\times_TT_i$, Step 4 base changes to
$P_U\times_UU_i=\coprod_{g\in G}U_i$. This equality follows directly from the fibre-product
universal property: by [lem-weil-pbc-scheme-coproduct-family], the inverse images of the disjoint
open components partition the pullback and each is $U_i$. The frame on component $g$ is the
pulled-back $\tau_i$ followed by the SAME constant $g$, by naturality in linear maps of the
constant-module comparison. Thus the sheaf morphism is, on $U_i$, precisely the constant-$G$
isomorphism of Step 2 and [lem-galois-constant-sheaf-sets-representable]. It is locally injective
and locally surjective, hence an isomorphism by
[lem-galois-set-sheaf-local-bijection-isomorphism]. Evaluating at the final object $U$ gives
$\operatorname{Mor}_T(U,P)=\operatorname{Mor}_U(U,P_U)\cong\operatorname{Fr}_H(U)$.

6. For $w:U'\to U$, the frame assigned to $a\circ w:U'\to P$ is the inverse image under $w$ of the
frame assigned to $a:U\to P$, followed by the specified comparisons. This is the composition law
of [lem-weil-pbc-sets-etale-inverse-image-composition-units], lifted to constant module sheaves by
[lem-pe-constant-left-module-inverse-image]; constants carry the same linear maps by
[lem-sfb-geometric-inverse-image-constant-module]. Hence Step 5's bijections are natural on all
$T$-schemes. More generally, a map $W\to P_U$ over $U$ is exactly a map $W\to P$ over $T$ with its
prescribed map $W\to U$. Step 5 identifies these with frames of $(W\to T)^{-1}H$, equivalently
frames of $(W\to U)^{-1}v^{-1}H$. It sends the identity of $P_U$ to $\lambda_{P_U}$, proving the
base-change representability assertion with its specified universal frame. For $U'\to U\to T$,
both iterated base changes send a map from any $W$ to the inverse image of the SAME $\lambda_P$;
the associativity equation in the cited composition lemma equates the two sheaf comparisons. The
fibre-product associator equates the two maps of schemes. This proves compatibility with
composition, rather than merely existence of an unspecified isomorphism.

7. For a geometric point $\bar t:\operatorname{Spec}\Omega\to T$, Step 5 identifies the geometric
fibre's set of points $\operatorname{Mor}_T(\operatorname{Spec}\Omega,P)$ with frames of $\bar
t^{-1}H$. By [lem-weil-pbc-geometric-point-pullback-stalk], module sheaves on
$(\operatorname{Spec}\Omega)_{\mathrm{et}}$ are equivalent, via global sections, to modules, and
global sections of the pulled-back underlying abelian sheaf are $H_{\bar t}$. This identification
is $A$-linear: naturality in the scalar endomorphisms and the constant-scalar comparison of
[lem-pe-constant-left-module-inverse-image] identify each multiplication by $a\in A$. The constant
source has global sections $A^n$, since the constant-module comparison is the equivalence's
constant object. Thus these are exactly $\operatorname{Isom}_A(A^n,H_{\bar t})$, as claimed.

8. If $T$ is empty, any $T$-scheme is empty, any module sheaf on its small etale site is the
unique zero sheaf (apply its sheaf condition to the empty covering), and all frame sets are
singleton sets. The representing scheme $P$ is empty because it maps to $T$; surjectivity is
vacuous. If $n=0$, then $G=\{1\}$ and all the preceding steps still apply. There is exactly one
frame locally, and the sheaf condition makes $F$ terminal; the two representing etale objects $P$
and $T$ are isomorphic by Yoneda [lem-galois-yoneda-fully-faithful]. In particular no step used
$n>0$, a nonempty or connected base, a characteristic restriction on $T$, or a Noetherian
hypothesis.
-/
theorem exists_frameScheme
    (T : Scheme.{u}) (ell : ℕ) (hell : Nat.Prime ell) (n : ℕ)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} ell)))
    (hH : ∃ (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T),
      ∀ i : 𝒰.I₀, Nonempty (Frame ell n H (𝒰.f i))) :
    ∃ (P : Scheme.{u}) (p : P ⟶ T),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ frame : Frame ell n H p,
        (∀ U : Over T, Function.Bijective (evaluation ell n H p frame U)) ∧
        (∀ (U V : Over T) (w : U ⟶ V) (a : V ⟶ Over.mk p),
          evaluation ell n H p frame U (w ≫ a) =
            restrict ell n H w (evaluation ell n H p frame V a)) ∧
        (∀ (U V W : Over T) (w : U ⟶ V) (w' : W ⟶ U)
            (e : Frame ell n H V.hom),
          restrict ell n H (w' ≫ w) e =
            restrict ell n H w' (restrict ell n H w e)) ∧
        (∀ (U : Scheme.{u}) (v : U ⟶ T),
          (∀ W : Over U, Function.Bijective
            (evaluation ell n ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H)
              (pullback.snd p v) (baseFrame ell n H p frame v) W)) ∧
          (∀ (W : Over U) (a : W ⟶ Over.mk (pullback.snd p v)),
            evaluation ell n ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H)
                (pullback.snd p v) (baseFrame ell n H p frame v) W a ≪≫
                ((Etale.upperStarComp (ModuleCat.{u + 1} (Coeff.{u} ell)) W.hom v).app H).symm =
              evaluation ell n H p frame (Over.mk (W.hom ≫ v))
                (forgetBaseChange p v W a))) ∧
        (∀ (U V : Scheme.{u}) (v : U ⟶ T) (w : V ⟶ U)
            (W : Over V)
            (a : W ⟶ Over.mk (pullback.snd (pullback.snd p v) w)),
          evaluation ell n
              ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) w).obj
                ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H))
              (pullback.snd (pullback.snd p v) w)
              (baseFrame ell n
                ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H)
                (pullback.snd p v) (baseFrame ell n H p frame v) w) W a ≪≫
              ((Etale.upperStarComp (ModuleCat.{u + 1} (Coeff.{u} ell)) W.hom w).app
                ((Etale.upperStar (ModuleCat.{u + 1} (Coeff.{u} ell)) v).obj H)).symm ≪≫
              ((Etale.upperStarComp (ModuleCat.{u + 1} (Coeff.{u} ell))
                (W.hom ≫ w) v).app H).symm =
            evaluation ell n H p frame (Over.mk ((W.hom ≫ w) ≫ v))
              (forgetBaseChange p v (Over.mk (W.hom ≫ w))
                (forgetBaseChange (pullback.snd p v) w W a))) ∧
        (∀ (U : Scheme.{u}) (v : U ⟶ T), Etale v → Nonempty (Frame ell n H v) →
          ∃ e : pullback p v ≅ ∐ fun _ : model ell n ≅ model ell n ↦ U,
            e.hom ≫ Sigma.desc (fun _ : model ell n ≅ model ell n ↦ 𝟙 U) =
              pullback.snd p v) ∧
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T),
          Function.Bijective (fun a : Over.mk s ⟶ Over.mk p ↦
            stalkFrame ell n H s (evaluation ell n H p frame (Over.mk s) a))) := by
  sorry

end AlgebraicGeometry.FiniteLocalSystemFrame
