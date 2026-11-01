/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiDerivedData

import WeilConjectures.AlgebraicGeometry.ContextExistence
import WeilConjectures.AlgebraicGeometry.DerivedReflection
import WeilConjectures.AlgebraicGeometry.FrobeniusTransport
import WeilConjectures.AlgebraicGeometry.FrobeniusCube

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

open RelativeEtaleZariskiDerivedData

abbrev relativeModuleDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u+1} (SheafOfModules.{u} T.ringCatSheaf) :=
  RelativeEtaleZariskiDerivedData.relativeModuleDerived T
abbrev relativeSchemeDerived (T : Scheme.{u}) : HasDerivedCategory.{u+1} T.Modules :=
  RelativeEtaleZariskiDerivedData.relativeSchemeDerived T
abbrev relativeModuleInjectives (T : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} T.ringCatSheaf) :=
  RelativeEtaleZariskiDerivedData.relativeModuleInjectives T
abbrev relativeSchemeInjectives (T : Scheme.{u}) : EnoughInjectives T.Modules :=
  RelativeEtaleZariskiDerivedData.relativeSchemeInjectives T
abbrev relativeZariskiRestrictScalars (T : Scheme.{u})
    (sigma : T.ringCatSheaf ⟶ T.ringCatSheaf) :=
  RelativeEtaleZariskiDerivedData.relativeZariskiRestrictScalars T sigma
instance relativeRestrictScalarsAdditive (T : Scheme.{u})
    (sigma : T.ringCatSheaf ⟶ T.ringCatSheaf) :
    (relativeZariskiRestrictScalars T sigma).Additive :=
  RelativeEtaleZariskiDerivedData.relativeRestrictScalarsAdditive T sigma
abbrev RelativeEtaleAbelianSheaves (T : Scheme.{u}) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleAbelianSheaves T
abbrev relativeEtaleForgetModules (T : Scheme.{u}) :=
  RelativeEtaleZariskiDerivedData.relativeEtaleForgetModules T
abbrev RelativeEtaleZariskiContext {X S : Scheme.{u}} (f : X ⟶ S) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f
abbrev RelativeEtaleZariskiContext.sourceDerived {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.sourceDerived c
abbrev RelativeEtaleZariskiContext.targetDerived {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.targetDerived c
abbrev RelativeEtaleZariskiContext.comparison {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.comparison c
abbrev RelativeEtaleZariskiContext.sourceSingle {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) (M : X.Modules) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.sourceSingle c M
abbrev RelativeEtaleZariskiContext.arrow {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) (M : X.Modules) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c M
abbrev RelativeEtaleZariskiFrobeniusTransport {T : Scheme.{u}}
    (c : ZariskiEtaleModuleContext T) (p : ℕ) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport c p
abbrev RelativeEtaleZariskiFrobeniusTransport.resDerived {T : Scheme.{u}}
    {c : ZariskiEtaleModuleContext T} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusTransport c p) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport.resDerived t
abbrev relativeEtaleZariskiResDerivedComparison {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) {p : ℕ}
    (x : RelativeEtaleZariskiFrobeniusTransport c.source p)
    (s : RelativeEtaleZariskiFrobeniusTransport c.target p)
    (r : pushforward f ⋙ relativeZariskiRestrictScalars S s.sigma ≅
      relativeZariskiRestrictScalars X x.sigma ⋙ pushforward f) :=
  RelativeEtaleZariskiDerivedData.relativeEtaleZariskiResDerivedComparison c x s r
abbrev RelativeEtaleZariskiFrobeniusSquare {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) (p : ℕ) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare c p
abbrev RelativeEtaleZariskiContext.targetTwist {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusTransport c.target p) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.targetTwist c t
abbrev RelativeEtaleZariskiFrobeniusSquare.sourceAction {X S : Scheme.{u}} {f : X ⟶ S}
    {c : RelativeEtaleZariskiContext f} {p : ℕ} (t : RelativeEtaleZariskiFrobeniusSquare c p) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare.sourceAction t
abbrev RelativeEtaleZariskiFrobeniusSquare.targetAction {X S : Scheme.{u}} {f : X ⟶ S}
    {c : RelativeEtaleZariskiContext f} {p : ℕ} (t : RelativeEtaleZariskiFrobeniusSquare c p) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare.targetAction t
abbrev RelativeEtaleZariskiContext.homologyIdentification {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiContext f) (M : X.Modules) (q : ℕ) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.homologyIdentification c M q
def RelativeEtaleZariskiFrobeniusSquare.homologyAction {X S : Scheme.{u}} {f : X ⟶ S}
    {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) (q : ℕ) :
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj
      (((pushforward f).rightDerived q).obj (SheafOfModules.unit X.ringCatSheaf)) ⟶
    (c.target.extension ⋙ relativeEtaleForgetModules S).obj
      (((pushforward f).rightDerived q).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (c.homologyIdentification (SheafOfModules.unit X.ringCatSheaf) q).hom ≫
    (DerivedCategory.Plus.homologyFunctor (RelativeEtaleAbelianSheaves S) q).map t.sourceAction ≫
      (c.homologyIdentification (SheafOfModules.unit X.ringCatSheaf) q).inv
abbrev RelativeEtaleZariskiFrobeniusSquare.sectionAction {X S : Scheme.{u}} {f : X ⟶ S}
    {c : RelativeEtaleZariskiContext f} {p : ℕ}
    (t : RelativeEtaleZariskiFrobeniusSquare c p) (q : ℕ) (V : S.Etale)
    (e : (c.target.extension.obj (((pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)) :=
  RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare.sectionAction t q V e

/-- Relative quasi-coherent derived étale/Zariski comparison, natural in all O_X-linear maps F → G,
with additive Frobenius compatibility in characteristic p and its semilinearity on every étale
object's local sections. The existential context supplies only canonical presented constructions
and their normalizations; the comparison itself is the explicitly defined arrow above.

Source: Stacks 071N, 03P2, 0736 and 0EBS (blueprint:
lem-fd-qcoherent-relative-etale-zariski-derived).

Proof: 1. Apply [lem-fd-etale-zariski-ringed-pullback-flat] for \(T=X,S\). It gives exactness on
all modules, not merely on the quasi-coherent subcategory, and the canonical identifications
\(\epsilon_X^*\mathcal F=\mathcal F_{\mathrm{Et}}\). Put \(K=Rf_{\mathrm{Zar},*}(\mathcal
F[0])\) and \(L=Rf_{\mathrm{Et},*}^{\mathrm{Mod}}(\mathcal F_{\mathrm{Et}}[0])\). By
[lem-pc-sections-higher-direct-image-quasi-coherent], every \(\mathcal H^qK\) is quasi-coherent.
Exact pullback commutes with cohomology by [lem-weil-pbc-exact-functor-bounded-below], so
\(\epsilon_S^*K\) lies in the étale \(D^+_{\mathrm{QC}}\). Choose the small skeleta and common
module universe of [def-weil-size-convention]; [prop-pur-kinjective-resolutions-exist] supplies
module resolutions.

2. Using the sectionwise direct image of [def-weil-pbc-direct-image], the square of small ringed
topoi with top edge \(\epsilon_X\), bottom edge \(\epsilon_S\), and vertical edges
\(f_{\mathrm{Et}},f_{\mathrm{Zar}}\) commutes: restricting étale direct image to an open
\(W\subset S\) evaluates on \(X\times_SW=f^{-1}W\), with the same structural ring maps. Its
horizontal edges are flat by [lem-fd-etale-zariski-ringed-pullback-flat]. Thus
[lem-fd-flat-ringed-square-derived-mate] defines the canonical module comparison
\(\beta:\epsilon_S^*K\to L\). This also fixes its meaning, rather than choosing arbitrary
isomorphisms on cohomology groups.

3. Show \(L\in D^+_{\mathrm{QC}}\). By [lem-pur-ringed-coefficient-restriction-counit] with
constant coefficient ring \(\mathbf Z\), forgetting modules identifies its derived direct image
with the abelian one. By [lem-weil-pbc-higher-direct-image-sheafified-presheaf], its
degree-\(q\) cohomology is the sheafification of \(V\mapsto H^q_{\mathrm{Et}}(X_V,\mathcal
F_V)\), where \(V\to S\) is étale, \(X_V=X\times_SV\), and \(\mathcal F_V\) is the pulled-back
quasi-coherent module. The base change is an étale object by
[lem-weil-pbc-etale-base-change-finite-limits]. The cohomology-over-an-object is the cohomology
on the small site of \(X_V\), by [lem-weil-pbc-cohomology-over-object-localization] and
[lem-weil-pbc-etale-site-localization-open]. Pullback preserves quasi-coherence by
[lem-weil-pbc-module-pullback-quasi-coherent]. Module and abelian evaluations agree by
[lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison]. The absolute derived unit
comparison [lem-fd-etale-zariski-qcoherent-derived-unit] identifies this presheaf canonically
with \(V\mapsto H^q_{\mathrm{Zar}}(X_V,\mathcal F_V)\), compatibly with the restriction maps and
scalar actions.

4. For an affine étale \(v:V\to S\), flatness follows from [def-weil-etale-morphism], and flat
base change [lem-pc-flat-base-change-cohom] gives \(v^*R^qf_{\mathrm{Zar},*}\mathcal F\cong
R^q(f_V)_*\mathcal F_V\). The latter has quasi-coherent cohomology by
[lem-pc-sections-higher-direct-image-quasi-coherent], since [lem-pc-quasi-compact-base-change]
applies to \(f\) and its quasi-compact diagonal; the diagonal of \(f_V\) is the base change of
that diagonal, so it too is quasi-compact, as required by [def-weil-quasi-separated-morphism].
Affine vanishing [lem-pc-affine-vanishing] and the cocycle-normalized edge isomorphism
[lem-pc-leray-degenerate-sections] give \(H^q(X_V,\mathcal F_V)\cong\Gamma(V,R^q(f_V)_*\mathcal
F_V)\). These are the canonical edge and base-change maps, so their restrictions along an affine
étale \(V'\to V\) agree: both send a restricted cocycle to its class in the pulled-back
cohomology sheaf. Thus on the affine basis the presheaf in Step 3 is canonically
\(V\mapsto\Gamma(V,v^*R^qf_*\mathcal F)\). Its sheafification is \((R^qf_*\mathcal
F)_{\mathrm{Et}}\) by [def-sc-etale-qcoherent-module]. This proves the required quasi-coherence
of \(\mathcal H^qL\); negative cohomology vanishes by right-derived bounded-below construction.
Affine objects suffice: cover any étale object by affine opens, whose inclusions are étale by
[lem-weil-pbc-open-immersion-etale]; refine overlaps by affine opens again. The
restriction-compatible affine identifications therefore glue uniquely after sheafification by
the sheaf axiom.

5. Apply \(R\epsilon_{S,*}\) to \(\beta\). Under the derived composition isomorphisms
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], its adjoint is the composite
\(K\xrightarrow{Rf_{\mathrm{Zar},*}\eta_X}Rf_{\mathrm{Zar},*}R\epsilon_{X,*}\epsilon_X^*\mathcal
F\cong R\epsilon_{S,*}L\). The unit formula of [lem-fd-flat-ringed-square-derived-mate] says
precisely \(R\epsilon_{S,*}(\beta)\circ\eta_{S,K}=Rf_{\mathrm{Zar},*}(\eta_{X,\mathcal F})\).
Both units are isomorphisms by [lem-fd-etale-zariski-qcoherent-derived-unit]; for \(K\) use its
quasi-coherent cohomology from Step 1. Hence \(R\epsilon_{S,*}\beta\) is invertible. Since both
ends of \(\beta\) are in \(D^+_{\mathrm{QC}}\) by Steps 1 and 4, the same absolute equivalence
reflects isomorphisms and proves \(\beta\) invertible. This proves the chosen derived map is an
isomorphism, not only existence of per-degree identifications.

6. Use [lem-pur-ringed-coefficient-restriction-counit] for \(f_{\mathrm{Et}}\) and \(A=\mathbf
Z\) to compose \(U_S\beta\) with its canonical isomorphism \(U_SL\cong
Rf_{\mathrm{Et},*}^{\mathrm{Ab}}U_X\mathcal F_{\mathrm{Et}}\). Its normalization by derived
composition identifies this with the canonical relative comparison in the statement. Forgetting
is exact because kernels are sectionwise and cokernels are sheafified cokernels in
[def-weil-sheaf-of-modules-category]. Naturality follows from the naturality in the argument of
[lem-fd-flat-ringed-square-derived-mate] and of the coefficient comparison.

7. Assume \(p\mathcal O_S=0\). It implies \(p\mathcal O_X=0\) by the structural map. Write
\(\sigma_T\) for the ring-sheaf map \(a\mapsto a^p\) on either small site and
\(\operatorname{Res}_{\sigma_T}\) for [def-pc-sheaf-restrict-scalars]. The latter is exact,
since it leaves underlying groups, kernels and sheafified cokernels unchanged. There is an
exact-functor isomorphism \(\epsilon_T^*\operatorname{Res}_{\sigma_{T,\mathrm{Zar}}}\cong\operat
orname{Res}_{\sigma_{T,\mathrm{Et}}}\epsilon_T^*\): on affine étale
\(\operatorname{Spec}B\to\operatorname{Spec}A\) it sends \(b\otimes m\mapsto b^p\otimes m\).
Indeed, since \(\operatorname{Spec}B\to\operatorname{Spec}A\) is étale and \(p=0\) in \(A\),
[lem-fd-etale-relative-frobenius-iso] says that \(B\otimes_{A,F_A}A\to B\), \(b\otimes a\mapsto
b^pa\), is invertible. Tensor its inverse over the second \(A\) with the module: the source is
\(B\otimes_A\operatorname{Res}_{F_A}M\) after \((b\otimes a)\otimes m\mapsto b\otimes am\). This
proves the displayed isomorphism for every module, without perfection or Frobenius-flatness. Its
formula commutes with localization, so the sheafification model of
[lem-fd-etale-zariski-ringed-pullback-flat] glues it.

8. For either topology, direct image commutes with \(\operatorname{Res}_{\sigma}\): at each
object it is the same additive sections functor with scalars acting by their \(p\)-th powers.
The underived tensor-adjunction exchange square commutes with these restrictions and the
isomorphisms of Step 7. On a tensor generator \(b\otimes s\), the two routes are restriction of
\(b^p\otimes s\); the equality uses \((bs)^p=b^ps^p\) when the coefficient map is Frobenius.
Thus the underived cube hypothesis of [lem-weil-pbc-right-derived-plus-cube] holds, with its
four vertical functors the exact scalar restrictions and its horizontal exact functors the two
\(\epsilon^*\)'s. The coefficient-restriction comparisons for the vertical direct images are
invertible: after forgetting to abelian sheaves they are the identity comparison, by the
compatible-ring-map naturality of [lem-pur-ringed-coefficient-restriction-counit]. The cube node
gives the cube equality for the chosen bounded-below derived exchange maps (their normalization
is [lem-fd-flat-ringed-square-derived-mate]). Apply its naturality to the linear arrow
\(\mathcal O_X\to\operatorname{Res}_{\sigma_X}\mathcal O_X\), \(s\mapsto s^p\). After forgetting
scalars, this is precisely additive Frobenius on both sides of Step 6; the
coefficient-restriction comparison is natural in compatible ring-sheaf homomorphisms by
[lem-pur-ringed-coefficient-restriction-counit]. Hence the isomorphism intertwines Frobenius in
the derived category. The target of the linear Frobenius arrow has scalar action \(a\cdot
e=a^pe\), so on cohomology it gives \(F(ae)=a^pF(e)\); exact pullback commutes with cohomology
by [lem-weil-pbc-exact-functor-bounded-below].
-/
theorem relativeEtaleZariskiDerivedComparison
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ∃ c : RelativeEtaleZariskiContext f,
      IsIso (c.arrow F) ∧
      (∀ (G : X.Modules) [G.IsQuasicoherent] (g : F ⟶ G),
        c.targetDerived.map ((pushforward f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g)) ≫ c.arrow G =
        c.arrow F ≫ (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (RelativeEtaleAbelianSheaves X) 0).map
            ((c.source.extension ⋙ relativeEtaleForgetModules X).map g))) ∧
      (∀ (p : ℕ), p.Prime → (p : S.ringCatSheaf.obj.obj (op ⊤)) = 0 →
        F = SheafOfModules.unit X.ringCatSheaf →
        ∃ t : RelativeEtaleZariskiFrobeniusSquare c p,
          t.sourceAction ≫ c.arrow (SheafOfModules.unit X.ringCatSheaf) =
            c.arrow (SheafOfModules.unit X.ringCatSheaf) ≫ t.targetAction ∧
          ∀ (q : ℕ) (V : S.Etale) (a : (smallEtaleModuleRing S).obj.obj (op V))
            (e : (c.target.extension.obj
              (((pushforward f).rightDerived q).obj
                (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)),
            t.sectionAction q V (a • e) = a ^ p • t.sectionAction q V e) := by
  obtain ⟨c, _⟩ := canonical_relative_context_exists f
  have hi := relative_derived_comparison_isIso c F
  letI := hi
  refine ⟨c, hi, ?_, ?_⟩
  · intro G hG g
    exact relative_derived_comparison_natural c F G g
  · intro p hp hchar hF
    subst F
    obtain ⟨x, s, r, hrs⟩ := relative_frobenius_transport_data c p hp hchar
    letI := relative_frobenius_cube_isIso c p x s r
    let t : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare c p :=
      { source := x
        target := s
        ordinary := r
        ordinary_sections := hrs
        derived_iso := inferInstance }
    refine ⟨t, ?_, ?_⟩
    · exact relative_frobenius_cube_commutes c p t
    · intro q V a e
      exact relative_frobenius_section_semilinear c p t q V a e

end AlgebraicGeometry.Scheme.Modules
