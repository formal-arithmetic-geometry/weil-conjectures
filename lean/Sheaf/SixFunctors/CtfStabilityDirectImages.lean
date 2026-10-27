/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.SixFunctors.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import all Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.Paper.ExceptionalInverseImageExistence
import Sheaf.Paper.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.SixFunctors.AdmissibleTensorConstructibility
import Sheaf.SixFunctors.AdmissibleDirectImage

/-!
# Pullback, tensor product and direct images on constructible finite-Tor objects

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
node det-thm-sf-ctf-stability-direct-images (blueprint: det-thm-sf-ctf-stability-direct-images).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Avoid expanding the coefficient pullback and the derived monoidal construction.
attribute [local irreducible] upperStarFromPoint derivedTensor

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- Elaborating the six derived-functor clauses needs a larger elaboration budget.
/-- Pullback, tensor product, direct images, and exceptional pullback preserve
constructible finite-Tor objects at every admissible coefficient stage.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
node det-thm-sf-ctf-stability-direct-images
(blueprint: det-thm-sf-ctf-stability-direct-images). The proof uses the recorded localizing,
constructibility, derived-functor, closed-immersion, lower-shriek, and tensor-projection
interfaces together with the direct-image and restriction results listed in the node.


Proof plan:
1. Use the admissible rings of [sk-def-localizing-closure], including every finite commutative
$\ell$-primary ring $A$, and the arbitrary characteristic-$p$ field setting of
[sk-def-sfb-dc-setting]. All schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian],
since a field is Noetherian. They are therefore qcqs, and every open subset is quasi-compact. By
[det-proper-base-change-unbounded-pullback], the exact inverse image $f^*$ preserves $\Dctf$ for
every admissible coefficient. This proves the pullback assertion. For integral and rational
coefficients, [det-def-localizing-closure-ctf-equals-bc] gives $\Dctf=\Dbc$; this equality will
never be used for an arbitrary finite ring $A$.

2. For finite $A$, descend $K,L\in\Dctf(X,A)$ to the étale site by
[det-pe-finite-tor-comparison-noetherian]; $A$ is Noetherian because every ideal is a finite set.
Choose ordered Tor intervals $[a,b]$, $[c,d]$. By [lem-sf-etale-flat-constructible], represent the
descended objects by bounded complexes $P,Q$ of flat constructible sheaves, zero outside these
intervals. Refine the finitely many stratifications of their terms by
[lem-weil-pbc-constructible-stratification-intersection]. On each stratum,
[lem-weil-pbc-locally-constant-tensor], applied to the flat terms in degree zero, shows that
$P^i\otimes_AQ^j$ is locally constant of finite type. Finite sums and the kernels and cokernels
computing cohomology are constructible by [thm-constructible-serre]. Each tensor term is flat:
tensoring with $P^i\otimes_AQ^j$ is the composite of two exact tensor functors; finite sums remain
exact. Thus $\operatorname{Tot}(P\otimes_AQ)$ is a bounded flat complex, supported in $[a+c,b+d]$.
It is K-flat by [lem-pc-bounded-above-flat-kflat-site], so it computes the derived tensor and has
this Tor interval against every module sheaf. The monoidal comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] identifies its exact pro-étale pullback with
$K\otimes_A^{\mathbf L}L$. The Tor comparison equivalence gives the finite-coefficient tensor
assertion of (1).

3. For $\mathcal O_E$, [det-lem-integral-models-operations](2) gives tensor closure of $\Dbc$. For
$E$ and $\overline{\mathbf Q}_\ell$, [det-thm-sf-pf-field-tensor](1) gives tensor closure of
$\Dbc$. Step 1 identifies these categories with $\Dctf$, proving the remaining tensor assertions
of (1). Taking $E=\mathbf Q_\ell$ includes $\mathbf Z_\ell$ and $\mathbf Q_\ell$.

4. Let $a:S\hookrightarrow X$ be a locally closed immersion. Since the schemes are Noetherian, it
is quasi-compact; [lem-pqf-qc-immersion-open-closed-factor] factors it as
$S\xrightarrow{u}T\xrightarrow{i}X$ with $u$ open and $i$ closed. The coefficient sheaves are
cartesian by [sk-prop-sfb-cartesian-coefficients]. Apply
[lem-weil-pbc-proetale-ringed-open-closed] to the pairs $(T,S)$ and $(X,X\setminus T)$: $u_!$ and
$i_*$ are exact, their restriction back to their support is the identity, and their restrictions
to the respective complements are zero. Hence $a_!=i_*u_!$ is exact and acts termwise on the
derived category by [lem-weil-pbc-exact-functor-derived-functor]. If $F$ is constructible on $S$,
take its finite stratification from [sk-def-sfb-constructible]. The stratum immersions composed
with $a$ are immersions by [lem-weil-pbc-proper-fp-permanence](e). Together with $T\setminus S$
and $X\setminus T$ these give a finite locally closed stratification of $X$; all its strata are
constructible because $X$ is Noetherian. On the source strata the restriction of $a_!F$ is the
given finite constant local model, and on the two complementary strata it is zero, by the
restriction identities just cited. Therefore $a_!F$ is constructible. For $K\in\Dctf(S,\Lambda)$,
exactness gives $H^n(a_!K)=a_!H^n(K)$, so $a_!K$ is bounded constructible. If $K$ has Tor interval
$[a_0,b_0]$, then for every target module sheaf $N$, [det-lem-int-tensor-projection] gives
$(a_!K)\otimes^{\mathbf L}_{\Lambda_X}N\simeq a_!(K\otimes^{\mathbf L}_{\Lambda_S}a^*N)$. The
pullback $a^*N$ is a sheaf by cartesian coefficients, and exact $a_!$ preserves vanishing outside
$[a_0,b_0]$. Thus $a_!K$ has the same Tor interval. This proves (2) uniformly for every admissible
coefficient, without replacing $K$ by its cohomology for the Tor test.

5. Let $j:U\hookrightarrow X$ be open and $A$ finite; $j$ is quasi-compact and quasi-separated
because the schemes are Noetherian (Step 1). Descend $K\in\Dctf(U,A)$ of Tor interval $[a,b]$ to a
bounded constructible etale complex $C$ of the same Tor interval by
[det-pe-finite-tor-comparison-noetherian]. Its etale direct image $B=Rj_*C$ is bounded
constructible by [cor-fin-deligne-open-finite-coefficients], since a power of $\ell$ kills $A$ and
is invertible in $k$. Put $d=\operatorname{cd}(j)<\infty$ by [lem-kun-0f10](1); clause (1) of
[det-geo-open-finiteness-ii-amplitude] states $R^qj_*F=0$ for every sheaf $F$ of $A$-modules and
every $q>d$. A finite $A$-module $M$ is finitely presented: it is a quotient of some $A^n$, and
the kernel is a finite set, hence finitely generated. Since $C$ is bounded,
[lem-sf-projection-finite-constant] with $N=d$ shows that the projection map $B\otimes_A^{\mathbf
L}\underline M_X\to Rj_*(C\otimes_A^{\mathbf L}\underline M_U)$ is an isomorphism for every finite
$A$-module $M$. These are exactly the hypotheses of [lem-sf-open-tor-bound-arbitrary-field] for
$L=C\in D^+(U_{\mathrm{\acute et}},A)$ and $e=d$, over the arbitrary standing field; it gives that
$B$ has Tor amplitude in $[a,b+d]$ against every $A_X$-module sheaf. Finally
[prop-weil-pbc-comparison-direct-image] identifies $\nu_X^*B$ with the pro-etale $Rj_*K$,
[lem-exc-comparison-tor-interval] keeps the interval $[a,b+d]$ against every pro-etale module
sheaf, and the equivalence of [det-pe-finite-tor-comparison-noetherian] places $\nu_X^*B$ in
$\Dctf(X,A)$. This proves the finite open direct-image case over the arbitrary standing field.

6. For $\mathcal O_E$ and a quasi-compact open immersion $j$, [det-thm-sf-pf-adic-open] gives
$Rj_*:\Dbc(U,\mathcal O_E)\to\Dbc(X,\mathcal O_E)$, including derived completeness and the
reduction comparison. Step 1 translates this to preservation of $\Dctf$.

7. Use the generators of [det-lem-integral-models-generators] and finite cones and shifts,
justified by [det-cor-coefficient-heart-ii-triangulated]. Write an $E$-generator as $M[1/\ell]$,
$M=a_!L_0\in\Dbc(U,\mathcal O_E)$. Apply [lem-weil-pbc-ring-sheaf-change-adjunction] to $j$:
cartesian coefficient isomorphisms are [sk-prop-sfb-cartesian-coefficients](1), and their
compatibility with each coefficient map is [sk-def-sfb-coefficient-change]. It gives exact
conservative scalar restriction and $\operatorname{Res}Rj_*^{\Lambda'}\simeq
Rj_*^\Lambda\operatorname{Res}$. By [sk-prop-sfb-qlbar-colimit-x], $M[1/\ell]$ is the degree-zero
filtered system $M\xrightarrow{\ell}M\xrightarrow{\ell}\cdots$. Bounded continuity
[det-pe-bounded-continuity-direct-image] and exact filtered colimits
[lem-pur-ringed-site-grothendieck-abelian] give $(Rj_*M)[1/\ell]\simeq Rj_*(M[1/\ell])$. Step 6
bounds $Rj_*M$ constructibly. Flat localization [det-prop-sfb-qlbar-colimit-x-invert-ell]
preserves its interval and finite constant local presentations [sk-def-sfb-constructible]. For a
$\Qlb$-generator take the filtered system over finite $F/E$ of $F_U\otimes_{E_U}M[1/\ell]$. Each
$F_T$ is finite free over $E_T$ [sk-prop-sfb-cartesian-coefficients], so a basis and additivity
give the direct-image comparison at $F$. Bounded continuity on this degree-zero system gives the
comparison at $\Qlb$ [sk-prop-sfb-qlbar-colimit-x]. Its tensor functor is a filtered colimit of
exact finite-free tensor functors, hence exact, and extends the same finite presentations. The
images are bounded constructible. Cones and shifts finish both rational cases; Step 1 gives
$\Dctf$.

8. For proper $p$, finite-coefficient preservation is [det-ctf-finite-proper-localizing](1), for
every finite $\ell$-primary ring $A$. For $\mathcal O_E$ it is the constructibility conclusion of
[det-thm-sfb-proper-base-change-integral](1); for $E$ and $\overline{\mathbf Q}_\ell$ it is
[det-thm-sfb-proper-base-change-rational](2). Step 1 translates the integral and rational $\Dbc$
conclusions to $\Dctf$. Thus proper direct image preserves $\Dctf$ at every coefficient stage.

9. Choose the compactification $f=pj$ supplied by [sk-def-sfb-dc-setting], whose intermediate
scheme is again in the standing setting. The derived direct-image composition isomorphism
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], applied to the cartesian coefficient
sheaves of [sk-prop-sfb-cartesian-coefficients], gives $Rf_*\simeq Rp_*Rj_*$. By
[sk-def-sfb-module-derived-lower-shriek], the specified compactly supported image is
$Rf_!=Rp_*D(j_!)$, where $j_!$ is exact. Steps 5--8 show that the first composite preserves
$\Dctf$, and Steps 4 and 8 show this for the second. This proves (3) for the specified ambient
derived functors and compactification.

10. For (4), apply the restriction assertion of [sk-prop-sf-rf-shriek-preservation] for every
finite admissible $A$, [sk-thm-int-restriction] for $\mathcal O_E$, and [sk-thm-restriction] for
$E$ and $\overline{\mathbf Q}_\ell$. Each statement explicitly sends $\Dctf(Y,\Lambda)$ into
$\Dctf(X,\Lambda)$ for the exceptional right adjoint; existence on a localizing closure alone is
not used as preservation. Taking $E=\mathbf Q_\ell$ covers $\mathbf Z_\ell$ and $\mathbf Q_\ell$.
These conclusions and Steps 1--9 give all four clauses.
-/
theorem constructibleFiniteTor_stability_direct_images
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (constantModelBoundedConstructible Λ Y K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ X ((L((f)^*⟦Λ⟧)).obj K) ∧
          DerivedCategory.finiteTorAmplitude _ ((L((f)^*⟦Λ⟧)).obj K)) ∧
    (∀ K M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible Λ X M ∧
          DerivedCategory.finiteTorAmplitude _ M) →
        constantModelBoundedConstructible Λ X
            (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M) ∧
          DerivedCategory.finiteTorAmplitude _ (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M)) ∧
    (∀ {S Sbar : Scheme.{u}}
        [S.Over (Spec (.of k))] [Sbar.Over (Spec (.of k))]
        [LocallyOfFiniteType (S ↘ Spec (.of k))]
        [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
        [LocallyOfFiniteType (Sbar ↘ Spec (.of k))]
        [QuasiCompact (Sbar ↘ Spec (.of k))] [IsSeparated (Sbar ↘ Spec (.of k))]
        (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X)
        (ha : a = u ≫ i) [a.IsOver (Spec (.of k))]
        [u.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
        [IsOpenImmersion u] [IsClosedImmersion i]
        (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))),
      (constantModelBoundedConstructible Λ S K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ X
            ((D((u)_!open⟦Λ⟧) ⋙ R((i)_*⟦Λ⟧)).obj K) ∧
          DerivedCategory.finiteTorAmplitude _
            ((D((u)_!open⟦Λ⟧) ⋙ R((i)_*⟦Λ⟧)).obj K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((R((f)_*⟦Λ⟧)).obj K) ∧
          DerivedCategory.finiteTorAmplitude _ ((R((f)_*⟦Λ⟧)).obj K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K) ∧
          DerivedCategory.finiteTorAmplitude _
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K)) ∧
    (∀ (h : ∀ K, localizingClosureProEtale Λ X K →
          localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K))
        (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ X).FullSubcategory)
        (_adj : (localizingLowerShriek Λ (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f)) h) ⊣ G),
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
        (hK : constantModelBoundedConstructible Λ Y K ∧
            DerivedCategory.finiteTorAmplitude _ K) →
          constantModelBoundedConstructible Λ X
            (G.obj ⟨K, fun P _hP hS ↦ hS K hK⟩).obj ∧
          DerivedCategory.finiteTorAmplitude _ (G.obj ⟨K, fun P _hP hS ↦ hS K hK⟩).obj)
  := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated
    (Y ↘ Spec (.of k))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact ⟨pullback_bounded_constructible Λ f (pullback_constructible Λ f) K hK.1,
      pullback_tor Λ f K hK.2⟩
  · intro K M hK hM
    refine ⟨?_, ?_⟩
    · exact constantModelBoundedConstructible_tensor_of_admissible ℓ k Λ _hΛ (X := X) K M hK hM
    · obtain ⟨a, b, hK⟩ := hK.2
      obtain ⟨c, d, hM⟩ := hM.2
      refine ⟨a + c, b + d, ?_⟩
      simpa only [derivedTensor, MonoidalCategory.curriedTensor] using
        DerivedCategory.torAmplitudeIn_tensor hK hM
  · intro S Sbar _ _ _ _ _ _ _ _ a j i ha _ _ _ _ _ K hK
    let c : Compactification a :=
      { Z := Sbar, g := i, i := j, comm := ha,
        isProper := inferInstance, isOpenImmersion := inferInstance }
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
      (S ↘ Spec (.of k))
    have : QuasiSeparatedSpace Sbar := quasiSeparatedSpace_of_quasiSeparated
      (Sbar ↘ Spec (.of k))
    have : QuasiCompact j := quasiCompact_of_compactSpace j
    have : IsSeparated a := by rw [ha]; infer_instance
    have : LocallyOfFiniteType a := by rw [ha]; infer_instance
    have : QuasiCompact a := by rw [ha]; infer_instance
    let c' : Compactification.BoundaryCompactification a := ⟨⟨c, inferInstance⟩⟩
    exact (compactification_localizing Λ ℓ k a c' _hΛ).2.2.2 K hK
  · intro K hK
    exact constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ _hΛ
      (X := X) (Y := Y) f K hK
  · intro K hK
    let c := @HasCompactification.compactification X Y f
      (HasCompactification.of_isOver (S := Spec (.of k)) f)
    have : QuasiCompact c.i :=
      (Compactification.quasiCompact_openImmersion_iff c).mpr inferInstance
    let c' : Compactification.BoundaryCompactification f := ⟨⟨c, inferInstance⟩⟩
    exact (compactification_localizing Λ ℓ k f c' _hΛ).2.2.2 K hK
  · intro h G adj K hK
    let X' := Over.mk (X ↘ Spec (.of k))
    let Y' := Over.mk (Y ↘ Spec (.of k))
    let f' : X' ⟶ Y' := f.asOver (Spec (.of k))
    have : LocallyOfFiniteType X'.hom := inferInstanceAs
      (LocallyOfFiniteType (X ↘ Spec (.of k)))
    have : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
    have : IsSeparated X'.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
    have : LocallyOfFiniteType Y'.hom := inferInstanceAs
      (LocallyOfFiniteType (Y ↘ Spec (.of k)))
    have : QuasiCompact Y'.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
    have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
    obtain ⟨hX, hY, hSX, hSY, h', sX, sY, hex⟩ :=
      exceptionalInverseImage_exists Λ ℓ k f' _hΛ
    obtain ⟨_, _, _, _, _, _, ⟨G', _, _, ⟨adj'⟩, hG'⟩, _⟩ := hex
    have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
    have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.1
    let e := adj'.rightAdjointUniq adj
    exact (constantModelBoundedConstructible Λ X ⊓
      DerivedCategory.finiteTorAmplitude
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))).prop_of_iso
        ((localizingClosureProEtale Λ X).ι.mapIso (e.app ⟨K, fun P _ hS ↦ hS K hK⟩))
        (hG' _ hK)

end AlgebraicGeometry.ProEtale.CondensedRing
