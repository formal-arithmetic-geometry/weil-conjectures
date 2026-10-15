/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.SitePullbackAbelianExact

/-!
# Ringed-site Čech comparison and refinement

Source: Stacks Project, Cohomology on Sites, Tags 03AX, 03FC, 08J6;
Cohomology, Tag 01FD (blueprint: lem-weil-pbc-ringed-site-cech-refinement-square).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

attribute [instance] Functor.additive_of_preserves_binary_products

/-- The tuple formula defines a unique additive cochain map. Normalized edges and the
resolved-direct-image cohomology map exist uniquely, for all degrees, and commute with it.
The roof normalization is quantified over every pair of resolutions and every replacement,
not an extra acyclicity assumption. `IsNormalizedEdge` uses Čech degree first and its
actual alpha/beta augmentations, hence fixes the sign convention and resolution comparison.

Source: Stacks 03AX, 03FC, 08J6 and the ringed-site version of 01FD
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square).

Proof (the DAG proof, including the integer-coefficient specialization):
1. Use additive section complexes throughout. Evaluation $P\mapsto P(U)$ in modules is left exact:
  kernels are sectionwise, and evaluation preserves finite products because their sectionwise
  product is again a sheaf. Since $u$ preserves the final object, $\Gamma_{\mathcal
  C}(f_*P)=\Gamma_{\mathcal D}(P)$. Continuity, in the covering-family sense of the site definition,
  makes $u\mathcal U$ a covering; preservation of fibre products identifies its tuple intersections
  with $u(U_{\mathbf i})$. For a tuple $\mathbf j$ and each omitted coordinate $k$, the two maps
  from $V_{\mathbf j}$ to $u(U_{r(\mathbf j\widehat k)})$ obtained by first taking $a_{\mathbf j}$
  or first omitting coordinate $k$ agree: both have projections $a_{j_l}\mathrm{pr}_l$ for $l\ne k$.
  Naturality of $h$ and of restriction therefore gives $d_C\gamma=\gamma d_C$ term by term, with the
  same signs $(-1)^k$, including repeated indices of $r$.
Uses: def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category,
  def-weil-pbc-site-cech-complex.

2. Choose nonnegative injective resolutions $\varepsilon_M:M\to I^\bullet$ and $\varepsilon_N:N\to
  J^\bullet$. Put $P^\bullet=f_*J^\bullet$. By the complex injective-resolution monomorphism lemma,
  applied with lower bound $0$, choose a termwise monic quasi-isomorphism $\lambda:P^\bullet\to
  Q^\bullet$, with $Q$ nonnegative and termwise injective. Apply the strict lifting lemma to the
  termwise monic quasi-isomorphism $M[0]\to I^\bullet$ and the map
  $M[0]\xrightarrow{h}f_*N[0]\xrightarrow{f_*\varepsilon_N}P^\bullet\xrightarrow{\lambda}Q^\bullet$.
  It gives $b:I^\bullet\to Q^\bullet$ with $b\varepsilon_M=\lambda f_*\varepsilon_N h$ as maps of
  complexes. Neither $P$ nor $f_*N$ is asserted to be injective.
Uses: def-sp-injective-resolutions, lem-weil-pbc-complex-injective-resolution-mono,
  lem-weil-pbc-lift-along-injective-quasi-iso.

3. Write $A=\operatorname{Tot}\check C(\mathcal V,J)$, $B=\operatorname{Tot}\check C(\mathcal U,I)$,
  $B'=\operatorname{Tot}\check C(\mathcal U,Q)$ and $B''=\operatorname{Tot}\check C(\mathcal U,P)$.
  Each augmented Cech row for an injective term of $I,Q,J$ is a resolution of its global sections:
  positive Cech cohomology vanishes by the general ringed-site injective-module lemma, and degree
  zero is the sheaf equalizer. For $P^n$, its row is the row of $J^n$ on $u\mathcal U$ by step 1,
  hence is also such a resolution. Apply the first-quadrant augmentation lemma, exchanging the two
  indices, to obtain quasi-isomorphisms $\alpha_I,\alpha_Q,\alpha_J,\alpha_P$ from the respective
  global section complexes. With the exchanged indices the canonical sign isomorphism has component
  $(-1)^{t n}$ on Cech degree $t$ and resolution degree $n$: it intertwines the exchanged total
  differential and $d_C+(-1)^t d_I$, and is identity on the augmentation axis $t=0$. Thus these are
  exactly the alphas prescribed in the statement, not unspecified edge isomorphisms. The common
  universe permits the general ringed-site lemma's coefficient and index convention (enlarge all
  small data together); the sheafification hypotheses there hold for the usual site sheafification.
Uses: lem-weil-pbc-ringed-site-injective-module-cech-acyclic, def-weil-pbc-sites-and-cohomology,
  lem-sc-first-quadrant-column-augmentation, def-sp-double-complex-total.

4. Every $P^n=f_*J^n$ is acyclic for $\Gamma_{\mathcal C}$ by the direct-image injective evaluation
  lemma at $1_{\mathcal C}$. Every $Q^n$ is acyclic for this functor by injective derived-functor
  vanishing. Apply Leray acyclicity for quasi-isomorphisms to $\lambda:P\to Q$, with bound $0$, to
  get a quasi-isomorphism $\ell=\Gamma_{\mathcal C}(\lambda):\Gamma_{\mathcal
  D}(J)\to\Gamma_{\mathcal C}(Q)$. All its hypotheses hold: the source module category is abelian
  with enough injectives, evaluation is additive and left exact by step 1, both complexes are
  nonnegative, and both have acyclic terms. Consequently the canonical map specified in the item is
  $h_H=H^q(\ell)^{-1}H^q(\Gamma_{\mathcal C}(b))$.
Uses: lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic,
  lem-weil-pbc-derived-functor-injective-vanishing, lem-weil-pbc-leray-acyclicity-quasi-iso.

5. Coefficient maps $b$ and $\lambda$ give total maps $L:B\to B'$ and $S:B''\to B'$. For each
  bidegree define $T:B''\to A$ by $T(x)_{\mathbf j}=J^n(a_{\mathbf j})(x_{r(\mathbf j)})$. The
  omitted-coordinate identities of step 1 show commutation with $d_C$; naturality of $d_J$ shows
  commutation with $d_I$. Since $T$ preserves Cech degree, it also commutes with $(-1)^t d_I$, and
  therefore totalizes. Define $\delta:\check C(\mathcal U,M)\to B''$ using
  $M\xrightarrow{h}f_*N\xrightarrow{f_*\varepsilon_N}P^0$ into resolution degree zero. It is a chain
  map because that augmentation is killed by $d_P^0$. Coefficient functoriality and the strict lift
  identity of step 2 give the pentagon $L\beta_M=S\delta$. In coordinates, the other upper identity
  is $T\delta=\beta_N\gamma$: both send $s_{r(\mathbf j)}$ to $\varepsilon_N\bigl(N(a_{\mathbf
  j})h(s_{r(\mathbf j)})\bigr)$.
Uses: def-weil-pbc-site-cech-complex, def-sp-double-complex-total.

6. The lower squares satisfy $L\alpha_I=\alpha_Q\Gamma(b)$ and $S\alpha_P=\alpha_Q\ell$ since
  coefficient maps commute with restriction. The right square is $T\alpha_P=\alpha_J$, after
  identifying the two global section complexes of $P$ and $J$: its component at $j$ restricts a
  global $J^n$ section first to $u(U_{r(j)})$, then to $V_j$, which is exactly restriction to $V_j$.
  On cohomology put $a_I=H^q(\alpha_I)$, and similarly $a_Q,a_P,a_J$. These are invertible by step
  3, and $\ell_q=H^q(\ell)$ is invertible by step 4; therefore $S_q=a_Q\ell_q a_P^{-1}$ is
  invertible, even though no termwise acyclicity of a pulled-back coefficient sheaf was assumed.
  Using the four displayed squares and the pentagon, cancellation gives
$$\ell_q^{-1}H^q(\Gamma(b))a_I^{-1}H^q(\beta_M)=a_P^{-1}S_q^{-1}L_qH^q(\beta_M)=a_P^{-1}H^q(\delta)=
a_J^{-1}T_qH^q(\delta)=a_J^{-1}H^q(\beta_N)H^q(\gamma).$$
This is the required equality with both edges equal to the displayed inverse-alpha followed by beta.
Uses: def-weil-pbc-site-cech-complex.

7. For two nonnegative injective resolutions of a coefficient sheaf, apply the strict lifting lemma
  to their augmentations to get comparisons in both directions over the identity. The
  uniqueness-up-to-homotopy lemma applied to the coefficient augmentation shows that the composites
  are homotopic to the identities, so the comparisons are homotopy equivalences. A coefficient chain
  homotopy $k$ induces the total Cech homotopy with component $(-1)^t\check C^t(k)$: its horizontal
  cross terms cancel and its vertical terms give $\check C^t(dk+kd)$. The alphas commute with these
  comparisons, and the betas commute because the comparisons are strict over the coefficient. Their
  induced homology diagrams prove independence of $a^{-1}H^q(\beta)$ under the canonical
  global-section identifications. This applies without acyclicity of the coefficient sheaf.
Uses: lem-weil-pbc-lift-along-injective-quasi-iso,
  lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, def-weil-pbc-site-cech-complex,
  def-sp-double-complex-total.

8. For a second replacement $\lambda':P\to Q'$, lift $\lambda'$ strictly along the termwise monic
  quasi-isomorphism $\lambda$ to $c:Q\to Q'$. Then $c\lambda=\lambda'$; uniqueness up to homotopy
  applied to $M[0]\to I$ gives $cb\simeq b'$. On global cohomology, $H(\Gamma c)\ell_q=\ell'_q$, and
  both $\ell_q,\ell'_q$ are invertible by step 4; cancellation shows that the roof defining $h_H$ is
  unchanged. For another resolution $J'$ of $N$, take a comparison $v:J\to J'$ strict over $N$ from
  step 7 and put $P'=f_*J'$. Its direct image $w=f_*v:P\to P'$ is a homotopy equivalence: applying
  the additive direct image to the inverse and the two chain homotopies preserves their equations.
  Choose $\lambda':P'\to Q'$ and $b':I\to Q'$ as in step 2. Lift $\lambda'w$ along $\lambda$ to
  $c:Q\to Q'$ with $c\lambda=\lambda'w$. Since $v\varepsilon_N=\varepsilon_{N'}$, the maps $cb$ and
  $b'$ agree after $\varepsilon_M$, hence are homotopic by the uniqueness lemma. Write
  $g=H^q(\Gamma_{\mathcal D}v)$. The equality $c\lambda=\lambda'w$ gives $H^q(\Gamma
  c)\ell_q=\ell'_q g$. Consequently $g\ell_q^{-1}H^q(\Gamma b)=(\ell'_q)^{-1}H^q(\Gamma c)H^q(\Gamma
  b)=(\ell'_q)^{-1}H^q(\Gamma b')$, the desired canonical target identification. For another source
  resolution $I'$ choose $z:I\to I'$ strict over $M$, and let $b':I'\to Q$ be its lift. The maps
  $b'z$ and $b$ agree after $\varepsilon_M$, so are homotopic. Writing $k=H^q(\Gamma z)$, which is
  the canonical source identification by step 7, gives $\ell_q^{-1}H^q(\Gamma
  b')k=\ell_q^{-1}H^q(\Gamma b)$. These equations establish independence of every resolution choice.
Uses: lem-weil-pbc-lift-along-injective-quasi-iso,
  lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, def-weil-pbc-sites-and-cohomology.

9. For integer coefficients a sheaf of modules is exactly an abelian sheaf: multiplication by an
  integer is repeated addition, so the two section complexes agree. Let $\bar h:f^{-1}M\to N$ be
  adjoint to $h$. The abelian site-pullback exactness lemma gives a resolution $f^{-1}M\to f^{-1}I$.
  Lift $\bar h$ followed by $\varepsilon_N$ along this termwise monic quasi-isomorphism to
  $v:f^{-1}I\to J$. Its adjoint $b_0:I\to f_*J=P$ is a cochain map strictly extending $h$. Taking
  $b=\lambda b_0$ in step 4 cancels $\ell_q$, so $h_H=H^q(\Gamma b_0)$. The degreewise adjunction
  says $\Gamma b_0$ is the inverse-image unit on sections followed by $\Gamma v$. For comparison
  with pullback followed by $H(\bar h)$, choose an injective resolution $E$ of $f^{-1}M$, lift
  $f^{-1}I\to E$ over its augmentation and $E\to J$ over $\bar h$. Their composite and $v$ agree up
  to homotopy by the uniqueness lemma applied to $f^{-1}M[0]\to f^{-1}I$. Thus their section
  cohomology maps agree. This is the asserted inverse-image cohomology pullback followed by the
  adjoint coefficient map.
Uses: def-weil-sheaf-of-modules-category, def-weil-pbc-sites-and-cohomology,
  lem-weil-pbc-lift-along-injective-quasi-iso, lem-weil-pbc-lift-to-injective-unique-up-to-homotopy,
  lem-weil-pbc-site-pullback-abelian-exact.
-/
theorem ringedSite_cech_refinement_square
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k)) :
    ∃! γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf,
      (∀ (p : ℕ) (s : S.cochains M.val.presheaf p) (j : Fin (p + 1) → I₁),
        (γ.f p s) j = N.val.presheaf.map (aTuple p j).op
          ((h.val.app (op (S.W p (r ∘ j)))) (s (r ∘ j)))) ∧
      ∀ q : ℕ,
        ∃! eM : (S.cohomologyFunctor q).obj M.val.presheaf ⟶ (((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
          X)).rightDerived q).obj M,
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM ∧
          ∃! eN : (T.cohomologyFunctor q).obj N.val.presheaf ⟶ (((SheafOfModules.forget R' ⋙
            PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj
            X))).rightDerived q).obj N,
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj) q eN
              ∧
            ∃! hH : (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation
              Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ (((SheafOfModules.forget R'
              ⋙ PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
              (u.obj X))).rightDerived q).obj N,
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
                ∃ (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                  (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                    ℕ)).obj IN.cocomplex ⟶ L)
                  (b : IM.cocomplex ⟶ L),
                  (∀ n : ℕ, Injective (L.X n)) ∧
                  (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
                  IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f
                    0) ∧
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
                (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                  ℕ)).obj IN.cocomplex ⟶ L)
                (b : IM.cocomplex ⟶ L),
                (∀ n : ℕ, Injective (L.X n)) →
                (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
                IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0 →
                IsIso (HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                  PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                  X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q) ∧
                hH ≫ (IN.isoRightDerivedObj ((SheafOfModules.forget R' ⋙
                  PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
                  (u.obj X))) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q =
                (IM.isoRightDerivedObj ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf
                  R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q) ∧
              eM ≫ hH = HomologicalComplex.homologyMap γ q ≫ eN := by
  sorry

/-- For abelian sheaves (the constant-integer-ring specialization), the same
resolved-direct-image roof equals inverse-image cohomology pullback followed by
the adjoint coefficient morphism. The pullback is computed by any strict lift of
the adjunction unit into the direct image of a resolution of the inverse image.
Under adjunction this is precisely a lift of the pulled-back resolution.

Source: Stacks 01FB, 03AX and 08J6
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square).

Proof: Apply the exact abelian inverse image to a source injective resolution.
Lift its augmentation into an injective resolution of the inverse image, then
compose with a resolution lift of the adjoint coefficient map. Adjunction gives
a strict map into the direct image of the target resolution. Composing with
its monic injective replacement cancels that replacement on global cohomology.
Uniqueness up to homotopy makes the answer independent of both lifts and all
three resolutions. The adjunction unit followed by its adjoint coefficient map
is h, so the resulting map is exactly the roof in steps 2, 4, 8 and 9 above.
-/
theorem ringedSite_cech_refinement_square_abelian
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (M : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (N : Sheaf K.toGrothendieck AddCommGrpCat.{u})
    (h : M ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj
      N)
    (q : ℕ)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X)) :
    ∃! hH : ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
      AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ ((sheafToPresheaf K.toGrothendieck
      AddCommGrpCat.{u} ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))).rightDerived q).obj
      N,
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
        ∃ (L : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℕ)
          (lam : ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj IN.cocomplex ⟶ L) (b :
            IM.cocomplex ⟶ L),
          (∀ n : ℕ, Injective (L.X n)) ∧ (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
          IM.ι.f 0 ≫ b.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).map (IN.ι.f 0) ≫ lam.f 0) ∧
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
        (L : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℕ)
        (lam : ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj IN.cocomplex ⟶ L) (b :
          IM.cocomplex ⟶ L),
        (∀ n : ℕ, Injective (L.X n)) → (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
        IM.ι.f 0 ≫ b.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).map (IN.ι.f 0) ≫ lam.f 0 →
        IsIso (HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
          ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
          ℕ)).map lam) q) ∧
        hH ≫ (IN.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map lam) q =
        (IM.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
          AddCommGrpCat.{u}).obj (op X)) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map b) q) ∧
      (∀ (IM : InjectiveResolution M) (E : InjectiveResolution ((sheafPullback u AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).obj M)),
        ∃ z : IM.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.cocomplex,
          IM.ι.f 0 ≫ z.f 0 = (sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).unit.app M ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).map (E.ι.f 0)) ∧
      (∀ (IM : InjectiveResolution M) (E : InjectiveResolution ((sheafPullback u AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).obj M))
        (z : IM.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.cocomplex),
        IM.ι.f 0 ≫ z.f 0 = (sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).unit.app M ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck).map (E.ι.f 0) →
        hH = (IM.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map z) q ≫
          (E.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation
            Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))) q).inv ≫
          ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Dᵒᵖ
            AddCommGrpCat.{u}).obj (op (u.obj X))).rightDerived q).map (((sheafAdjunctionContinuous
            u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).homEquiv M N).symm h)) := by
  sorry

end CategoryTheory
