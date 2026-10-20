/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.Compactification.NagataCompactification

import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.SpDirectImageEtaleMate
import Sheaf.Paper.DirectImageChangeRingTranspose
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation

/-!
# Compact support and finite coefficient extension

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.md (blueprint: det-sp-reduction-direct-image).

The comparison uses the specified counit mate and the unit-normalized open tensor
comparison. All categories are ordinary uncompleted module derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical coefficient comparison is an isomorphism in the full subcategory
of bounded intrinsically constructible complexes of finite Tor amplitude. Membership
is written out for both endpoints, so no etale-origin hypothesis replaces intrinsic
constructibility. No flatness or finite-projective-dimension condition is imposed.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.md
(blueprint: det-sp-reduction-direct-image).

Proof plan (the node's steps):

1. Put $p=\bar f$, and let $T_T^{A,B}$ denote scalar extension on a scheme $T$. Pullback carries
constant $B$ to constant $B$ by [prop-weil-pbc-proetale-constant-ring-map]. Its derived tensor
compatibility [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] gives a canonical identification
$p_B^*T_Y^{A,B}\simeq T_{\bar X}^{A,B}p_A^*$; this is $B$-linear, since on tensor representatives
its map preserves the right $B$-factor. For $N\in D(\bar X_{\mathrm{proét}},A)$ define
$$\gamma_N^{A,B}:T_Y^{A,B}Rp_*^A N\longrightarrow Rp_*^B T_{\bar X}^{A,B}N$$ by the adjunction of
[def-weil-pbc-proetale-operations], with transpose $$p_B^*T_Y^{A,B}Rp_*^A N\simeq T_{\bar
X}^{A,B}p_A^*Rp_*^A N\xrightarrow{T^{A,B}(\varepsilon_N^A)}T_{\bar X}^{A,B}N.$$ Thus, under this
pullback identification, its defining identity is
$\varepsilon^B_{TN}\,p_B^*(\gamma_N^{A,B})=T^{A,B}(\varepsilon_N^A)$. This constructs an actual
$B$-linear map, without an assumption on the Tor dimension of $B/A$.

2. First construct the coefficient comparison as a morphism of $B$-complexes. Choose a K-flat
resolution $P\to M$ with flat terms by [lem-pc-kflat-resolution]. The ordinary sheaf identity of
[lem-weil-pbc-ringed-slice-extension-tensor], for the open object $X$ of $\bar X_{\mathrm{proét}}$
(whose localized-site identification is part of [def-weil-extension-by-zero] and clause (1) of
[lem-weil-proetale-weakly-etale-localization]), gives $(j_!G)\otimes Q\simeq j_!(G\otimes j^*Q)$.
It extends to total tensor complexes: $j_!$ preserves direct sums because it is a left adjoint
[lem-cbc-proetale-extension-zero]. For any acyclic complex $Q$, $j^*Q$ is acyclic by exact
pullback [def-weil-pbc-proetale-operations], then $P\otimes j^*Q$ is acyclic by K-flatness, and
$j_!(P\otimes j^*Q)$ is acyclic by exactness of $j_!$. Hence $j_!P$ is K-flat. The same identity
on sheaves shows each $j_!P^i$ is flat, since both $j^*$ and $j_!$ are exact. Thus scalar
extension on the two sides is computed by $j_!P\otimes_A B$ and $j_!^B(P\otimes_A B)$. Their
termwise tensor comparison is $B$-linear (it preserves multiplication on the right $B$-factor),
and is an isomorphism by the cited ordinary identity. It yields the canonical $$e_M^{A,B}:T_{\bar
X}^{A,B}j_!^A M\xrightarrow{\sim}j_!^B T_X^{A,B}M.$$ After restriction of scalars, this is the
derived open tensor comparison [lem-trf-open-tensor]; compatibility of $j_!$ with restriction of
scalars is included in [lem-cbc-proetale-extension-zero]. Its restriction to $X$ is the tensor
identity. Define $$b_{A,B}(M)=Rp_*^B(e_M^{A,B})\circ\gamma_{j_!^AM}^{A,B}.$$ These canonical
derived comparisons are natural in $M$, without making a functorial choice of the resolution.

3. The arbitrary-finite-ring equivalence [lem-weil-pbc-finite-ring-constructible-derived-origin]
supplies a bounded constructible etale $A$-complex $L$ with $\nu_X^*L\simeq M$. Let
$K=j_!^{\mathrm{et},A}L$. Exactness [lem-weil-pbc-extension-by-zero-exact] makes $K$ bounded. The
sheaf comparison [lem-cbc-proetale-extension-zero-comparison] extends termwise to complexes: both
extension-by-zero functors and $\nu^*$ are exact, so the sheaf isomorphism gives a complex
isomorphism and survives localization at quasi-isomorphisms. Hence $\nu_{\bar X}^*K\simeq N:=j_!^A
M$. By [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], this also identifies $\nu_{\bar
X}^*(K\otimes_A^L B_{\bar X,\mathrm{et}})$ with $N\otimes_A^L B_{\bar X}$. The latter is bounded:
Step 2 identifies its underlying $A$-complex with that of $j_!^B M_B$, and $M_B$ is bounded by
[det-sp-scalar-extension-functor]. Exactness and the sheaf unit in
[prop-weil-pbc-site-comparison-finite-level] reflect vanishing of every cohomology sheaf:
$H^i(\nu^*E)=\nu^*H^i(E)$ and $H^i(E)\simeq\nu_*\nu^*H^i(E)$. Thus $K\otimes_A^L B_{\bar
X,\mathrm{et}}$ is bounded as well. Both etale arguments needed below therefore lie in $D^+$; no
fully faithful comparison is applied to an unbounded-below tensor.

4. The schemes $\bar X,Y$ and $p$ satisfy the finite-type-over-a-field hypotheses of
[lem-kun-0f10]. By its clause (1) and [def-kun-cd] there is one $c\geq0$ killing $R^qp_*$ on every
torsion abelian etale sheaf for $q>c$. This is also a uniform bound for etale $A$-module sheaves,
as follows. Resolve such a sheaf $F$ by injective $A$-module sheaves, using
[lem-weil-pbc-module-sheaves-enough-injectives], which also gives enough injectives for the
abelian sheaf category. Forgetting the action preserves exactness, and every term is $p_*$-acyclic
as an abelian sheaf by [lem-weil-pbc-injective-module-direct-image-acyclic]. The
acyclic-resolution criterion, clause (2) of [lemma-weil-pbc-leray-acyclicity], identifies the
underlying abelian sheaf of $R^qp_*^A F$ with $R^qp_*F$. The latter vanishes for $q>c$, since $F$
is killed by a power of $\ell$. Forgetting a module action reflects the zero object, proving the
required module-sheaf bound for all $F$.

5. A finite commutative ring $A$ is Noetherian: its ideals form a finite set, so an ascending
chain stabilizes. The finite set underlying $B$ generates it as an $A$-module, giving a finite
free surjection $A^r\twoheadrightarrow B$; its kernel is a finite set because $A^r$ is finite, so
it too has a finite generating set. This is a finite presentation of $B$ over $A$. Apply
[lem-sf-projection-finite-constant] to the etale map $p$, coefficient ring $A$, the uniform bound
$c$ from Step 4, bounded-above complex $K$ from Step 3, and constant finitely presented $A$-module
$B$. It gives invertibility of the specified counit projection $$\pi_K:Rp_{\mathrm{et},*}^A
K\otimes_A^L B_{Y,\mathrm{et}}\longrightarrow Rp_{\mathrm{et},*}^A(K\otimes_A^L B_{\bar
X,\mathrm{et}}).$$ This is precisely the finite-free-resolution/finite-window tool of the
blueprint's Steps 2–3. Its statement imposes neither finite projective dimension of $B$ nor a
bounded constructible flat model for $K$.

6. Let $d:r_YRp_{*,B}\xrightarrow{\sim}Rp_{*,A}r_{\bar X}$ be the restriction/direct-image
comparison of [lem-weil-pbc-ring-sheaf-change-adjunction]. By
[lem-sp-direct-image-change-ring-transpose], for every $N\in D(\bar X_{\mathrm{proét}},A)$ the
$A$-linear map $d\circ r_Y(\gamma_N^{A,B}):Rp_{*,A}N\otimes^{\mathbf L}_AB_Y\to
Rp_{*,A}(N\otimes^{\mathbf L}_AB_{\bar X})$ is the pro-étale projection morphism, i.e. its adjoint
transpose under $p_A^*\dashv Rp_{*,A}$, after the tensor-pullback identification, is
$\varepsilon^A_N\otimes^{\mathbf L}1_{B_{\bar X}}$. We use this at $N=j_!^AM$.

7. Take the bounded etale $A$-complex $K$ of Step 3 with $\nu_{\bar X}^*K\simeq N=j_!^AM$; Step 3
also shows $H=K\otimes^{\mathbf L}_AB_{\bar X,\mathrm{et}}$ is bounded, so $K,H\in D^+$ as
required by [lem-sp-direct-image-etale-mate-isomorphism]. That node gives the map
$t=\beta_H\,\nu_Y^*(\pi_K)\,(\beta_K^{-1}\otimes1)$ whose adjoint transpose is
$\varepsilon^p_N\otimes1$, and $t$ is an isomorphism because $\pi_K$ is invertible by Step 5. The
map of Step 6 has the same source, target and adjoint transpose (transported along $\nu^*K\simeq
N$ by naturality of both transposes), so by injectivity of the adjunction bijection of
[def-weil-pbc-proetale-operations] it equals $t$. Hence $d\circ r_Y(\gamma_N^{A,B})$ is an
isomorphism.

8. The comparison $d$ is an isomorphism by [lem-weil-pbc-ring-sheaf-change-adjunction], so Step 7
makes $r_Y(\gamma_N^{A,B})$ invertible. Restriction of scalars reflects isomorphisms by the same
statement; hence $\gamma_N^{A,B}$ is an isomorphism in the $B$-linear pro-étale derived category.
With $N=j_!^AM$, Step 2's definition $b=Rp_*^B(e_M)\circ\gamma_{j_!M}^{A,B}$ is a composite of
isomorphisms, hence an isomorphism.

9. Both objects of $b$ have the claimed category membership. The restricted adjunction stated in
[sk-prop-sf-rf-shriek-preservation] gives $Rf_{!,A}M\in\Dctf(Y,A)$ and $Rf_{!,B}M_B\in\Dctf(Y,B)$;
its finite-commutative-coefficient hypotheses apply to $A$ and $B$. By
[det-sp-scalar-extension-functor], $(Rf_{!,A}M)_B$ also belongs to $\Dctf(Y,B)$. This is a full
subcategory, so the isomorphism already obtained is an isomorphism there. Naturality follows from
the explicit counit transpose, tensor comparison, and extension-by-zero maps of Steps 1–2: for
$u:M\to M'$ their defining adjuncts agree by naturality of the counit, and hence the corresponding
square for $b$ commutes by injectivity of the adjunction bijection.

10. We now prove the coefficient cocycle on the named proper maps. Suppress the pullback/scalar
identifications, and identify $T^{B,C}T^{A,B}$ with $T^{A,C}$ by $\alpha$ of
[det-sp-scalar-extension-functor]. Consider $$d_N=\gamma^{B,C}_{T^{A,B}N}\circ
T_Y^{B,C}(\gamma_N^{A,B}).$$ Its $C$-adjoint transpose, using the defining identity in Step 1
first for $B\to C$ and then for $A\to B$, is $$\begin{aligned} \varepsilon^C\,p_C^*(d_N)
&=T^{B,C}(\varepsilon^B_{T^{A,B}N})\,T^{B,C}(p_B^*\gamma_N^{A,B})\\
&=T^{B,C}\bigl(T^{A,B}(\varepsilon_N^A)\bigr)  =T^{A,C}(\varepsilon_N^A). \end{aligned}$$
Naturality of the pullback tensor comparison justifies the first line; its associativity with
$\alpha$ is the balancing equality $((x\otimes b)\otimes c)\mapsto x\otimes\varphi(b)c$ on K-flat
tensor representatives, so the displayed identifications do not change this transpose. The last
expression is the defining transpose of $\gamma_N^{A,C}$. Injectivity of the adjunction bijection
[def-weil-pbc-proetale-operations] therefore gives the proper-map cocycle, including the indicated
$\alpha$'s. This calculation takes place for all $N$, so it can be used at $N=j_!M$.

11. The open tensor maps satisfy the same cocycle. After restriction to $X$, both composites from
$T^{B,C}T^{A,B}j_!^AM$ to $j_!^C T^{A,C}M$ give $((m\otimes b)\otimes c)\mapsto
m\otimes\varphi(b)c$. The domain is canonically $j_!^C(T^{B,C}T^{A,B}M)$ by Step 2, and
$j_!^C\dashv j^{-1}$ by [lem-cbc-proetale-extension-zero]. The unit $F\to j^{-1}j_!^CF$ is the
identity: in the presheaf construction [def-weil-extension-by-zero], by clause (4) of
[lem-weil-proetale-weakly-etale-localization] an object $V\to X$ and every object covering it
already factor through $X$, so the presheaf and its sheafification restrict to $F$ on
$X_{\mathrm{proét}}$. This holds degreewise and hence in the derived categories, since both
functors are exact. For $Z=T^{B,C}T^{A,B}M$ the adjunction now identifies
$\operatorname{Hom}(j_!^CZ,j_!^CT^{A,C}M)$ with $\operatorname{Hom}(Z,T^{A,C}M)$, and sends a map
to its restriction. Thus equality after restriction proves equality of the two maps in question.
This proves, under $\alpha$, $e_M^{A,C}=e_{T^{A,B}M}^{B,C}\circ T^{B,C}(e_M^{A,B})$.  Finally
expand $b=Rp_*(e)\gamma$. Naturality of $\gamma^{B,C}$ with respect to $e_M^{A,B}$ gives, after
suppressing the same $\alpha$'s, $$\begin{aligned} b_{B,C}(M_B)\,T_Y^{B,C}(b_{A,B}(M))
&=Rp_*^C(e_{M_B}^{B,C})\,\gamma^{B,C}_{j_!^BM_B}\,T_Y^{B,C}(Rp_*^B
e_M^{A,B})\,T_Y^{B,C}(\gamma^{A,B}_{j_!^AM})\\ &=Rp_*^C(e_{M_B}^{B,C})\,Rp_*^C(T_{\bar
X}^{B,C}e_M^{A,B})\,\gamma^{B,C}_{T^{A,B}j_!^AM}\,T_Y^{B,C}(\gamma^{A,B}_{j_!^AM})\\
&=Rp_*^C(e_M^{A,C})\,\gamma^{A,C}_{j_!^AM}=b_{A,C}(M). \end{aligned}$$ The second equality uses
naturality, and the third uses the open cocycle and Step 8. Reinsert $\alpha$ using its naturality
from [det-sp-scalar-extension-functor]; the result is exactly the equation in the statement.
-/
theorem reductionDirectImage_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    IsIso ((reductionDirectImageComparison φ j p).app M) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)) := by
  sorry

/-- The coefficient cocycle for these very comparisons, with both canonical alpha maps.
Source: blueprint statement's last equation and proof Steps 10-11
(blueprint: det-sp-reduction-direct-image).
Proof: transpose the two proper composites under the C-linear adjunction. Both become
extension of the A-counit by balanced tensor associativity. The injective adjunction
bijection identifies them. On the open, both maps restrict to the same balanced tensor
map ((m tensor b) tensor c) to m tensor psi(b)c. The unit of extension/restriction is
the identity, so its adjunction detects equality of these maps between extensions.
Expand b = Rp_*(e) gamma, use naturality of gamma at e, and substitute the two cocycles.
Naturality of the canonical alpha reinserts the two displayed associativity maps. -/
theorem reductionDirectImage_cocycle
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((reductionCompactSupport A j p).obj M) ≫
      (reductionDirectImageComparison (ψ.comp φ) j p).app M =
    (scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j p).app M) ≫
      (reductionDirectImageComparison ψ j p).app ((scalarExtensionFunctor φ X).obj M) ≫
        (reductionCompactSupport C j p).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale
