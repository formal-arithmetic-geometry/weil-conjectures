/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.EtaleSumTensorTotalization
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence

/-!
# Tensor compatibility for étale sum extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
thm-asd-smooth-tensor.md, proof paragraph 3 (blueprint: lem-asd-etale-sum-extension-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The canonical tensor comparison for exact, termwise derived inverse image. Transport
`leftDerivedUpperStarTensorIso` through `leftDerivedUpperStarIsoMapDerivedCategory` in both
arguments and in the value. Source: Stacks, Tag 0G7E and the tensor comparison in
lem-weil-pbc-ringed-topoi-derived-tensor-pullback
(blueprint: lem-asd-etale-sum-extension-tensor). -/
noncomputable def etaleSumExtensionTensorPullbackIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (v : V ⟶ T)
    (B C : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≅
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj C) :=
  ((derivedTensor (ModuleCat.{u + 1} A) V).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app B).symm).app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app C).symm ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v B C).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _

/-- The canonical comparison `v_!(v^*B ⊗ᴸ M) ⟶ B ⊗ᴸ v_!M`. It is the adjoint transpose
of `1 ⊗ unit`, followed by the canonical tensor-pullback comparison. On sum-extension
sections its inverse sends `b ⊗ (s,m)` to `(s,s^*b ⊗ m)`.
Source: Stacks Project, Tag 0GKF (blueprint: lem-asd-etale-sum-extension-tensor). -/
noncomputable def etaleSumExtensionTensorComparison
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (B : DerivedCategoryModule A T) (M : DerivedCategoryModule A V) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).obj M) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj M) :=
  (((etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).homEquiv _ _).symm
    (((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).map
        (((etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).unit.app M) ≫
      (etaleSumExtensionTensorPullbackIso A v B
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj M)).hom)

/-- Sum extension commutes with arbitrary unbounded derived tensor products, compatibly
with the fold counit. Source: blueprint thm-asd-smooth-tensor, proof paragraph 3;
Stacks Tag 0GKF (blueprint: lem-asd-etale-sum-extension-tensor).

Proof:
1. Both $v_!$ and $v^*$ are additive exact functors on constant-$A$ module sheaves: use
[lem-weil-pbc-etale-restriction-injectives] for sum extension and
[prop-weil-pbc-inverse-image-modules-exact] for inverse image, including its identification with
ringed-topos module pullback. By [lem-weil-pbc-exact-functor-derived-factorization], applying
either functor degreewise represents its functor on the entire unbounded derived category and
preserves quasi-isomorphisms. In particular the $v_!$ in this proof is sum extension, not a
compactification-dependent candidate for compact supports.
2. Represent $B$ and $M$ by complexes and choose quasi-isomorphisms $P\to B$ and $Q\to M$ with
$P,Q$ K-flat and with flat terms, by [lem-pc-kflat-resolution] on the two constant ringed sites.
Here and below an arrow to a derived object abbreviates an arrow to its chosen complex
representative. The preservation clause in [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]
gives that $v^*P$ is K-flat with flat terms; exactness in step 1 identifies its derived pullback
with $v^*B$. By [lem-pur-etale-sum-flat-kflat], $v_!Q$ is also K-flat with flat terms. All
hypotheses hold: $v$ is separated etale of finite type and the coefficient sheaves are constant;
the cited results impose no boundedness or constructibility condition.
3. Write $\beta$ for signed tensor symmetry: in bidegree $(p,q)$ it sends $b\otimes m$ to
$(-1)^{pq}m\otimes b$. From the differential of [def-pc-tensor-complex-sheaves], its two
differential terms have signs $(-1)^{(p+1)q}$ and $(-1)^{p+p(q+1)}=(-1)^{pq}$, respectively,
agreeing with the differential after symmetry; hence it is a chain isomorphism. Apply
[lem-pur-etale-sum-tensor-totalization] to $(Q,P)$. The composite
$$v_!\operatorname{Tot}(v^*P\otimes Q)\xrightarrow{v_!\beta}v_!\operatorname{Tot}(Q\otimes
v^*P)\xrightarrow{\Psi_{Q,P}^{-1}}\operatorname{Tot}(v_!Q\otimes
P)\xrightarrow{\beta}\operatorname{Tot}(P\otimes v_!Q)$$ is a natural chain isomorphism
$\pi_{P,Q}$. The two symmetry signs are both $(-1)^{pq}$ and cancel. Consequently its inverse
sends the lift-indexed generator $b\otimes(s,m)$ to $(s,s^*b\otimes m)$, with no sign. This
follows directly from the component formula for $\Psi$ in the cited statement. It uses direct-sum
totalizations even in an unbounded total degree.
4. The model comparison in [lem-weil-pbc-site-derived-tensor-descent], together with step 2,
identifies the two localizations in step 3 with $v_!(v^*B\otimes_A^L M)$ and $B\otimes_A^L v_!M$.
This is the derived tensor of [def-kun-derived-tensor]. Thus $\pi_{P,Q}$ represents the comparison
specified in the item: its inverse is exactly the termwise sum-extension pure-tensor map, with the
tensor factors in the stated order. Its naturality on homotopy categories is supplied by the
totalization statement in step 3. To descend in both variables, use separately the equivalence
from the localization of flat-term K-flat complexes to $D(T_{\mathrm{et}},A)$ and to
$D(V_{\mathrm{et}},A)$ in [lem-weil-pbc-site-derived-tensor-descent]. For each fixed first
variable, clause (2) of [lem-weil-pbc-localization-universal-property] descends the natural
transformation in the second variable. Descend its naturality in the first variable by the same
clause; uniqueness, clause (3), preserves these naturality equations. Apply the same process to
$\pi^{-1}$; the inverse equations descend by clause (3). This gives the specified natural
isomorphism $P_{B,M}$, independently of resolutions, on the two entire derived categories.
5. Here is the counit normalization needed for the equality. By
[lem-weil-pbc-etale-inverse-image-restriction], an etale test object $(W,s)$ over $V$ identifies
$(v^*H)(W,s)$ with $H(W)$; the comparison is $A$-linear because
[prop-weil-pbc-inverse-image-modules-exact] transports the action through the constant-ring
comparison. On the presheaf defining $v_!v^*H$ in [def-weil-pbc-etale-sum-extension], send the
summand element $(s,h)$ to $h\in H(W)$ and add over finitely supported summands. This is
compatible with restrictions and $A$-linear, so factors uniquely through sheafification
[def-weil-pbc-sheafification]. This fold is the counit: maps from the sum presheaf to $H$ are
precisely restriction-compatible families of maps into $H(W)$, hence maps into $v^*H$; the
displayed fold corresponds to $1_{v^*H}$. This identifies the adjunction of
[lem-weil-pbc-etale-restriction-injectives]. By [lem-weil-pbc-termwise-adjunction-homotopy] its
complex counit is degreewise this fold, and [lem-weil-pbc-localization-universal-property]
descends it with its triangle identities. It is therefore the fold counit $\epsilon$ of the
termwise adjunction in the item.
6. Choose flat-term K-flat representatives $P,R$ of $B,C$ as in step 2. By
[lem-pur-kflat-total-tensor-model], $\operatorname{Tot}(P\otimes R)$ is itself flat-term K-flat.
The current statement of [lem-pur-cochain-pullback-tensor-coherence] includes the ordinary
comparison, its pure-tensor formula and inverse, together with coefficient-change and
quotient-transition equations; the ordinary clause gives the chain map sending $s^*b\otimes s^*c$
to $s^*(b\otimes c)$. On these K-flat models it represents the canonical $\theta$ of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. We check the required identity before
localization, after precomposing with $\pi_{P,v^*R}^{-1}$. On the $(p,q)$ summand, take $b\in
P^p(W)$ and $c\in R^q(W)$ in the summand indexed by a lift $s:W\to V$. By steps 3 and 5, the left
composite sends $b\otimes(s,c)$ to $b\otimes c$. The right composite sends it successively to
$(s,s^*b\otimes s^*c)$, then to $(s,s^*(b\otimes c))$ under $v_!\theta$, and finally to $b\otimes
c$ under the fold. There are no signs: no tensor factors are permuted in these composites.
Equality on these generators gives equality of sheaf maps by the tensor universal property
[lem-pc-sites-sheaf-tensor-bilinear-universal] and the uniqueness in
[def-weil-pbc-sheafification]. Equality on every summand gives equality in each total degree; the
direct-sum compatibility in [lem-pur-etale-sum-tensor-totalization] identifies those degree maps
with the displayed complex composites. Since $\pi^{-1}$ is invertible, this proves the desired
equality of chain maps on these representatives.
7. Localize the equality of step 6. Steps 4 and 5 identify its terms with $P_{B,v^*C}$ and the
specified derived counits, while the pullback comparison in step 6 is the canonical
$\theta_{B,C}$. Therefore it reads $$(1_B\otimes\epsilon_C)\circ
P_{B,v^*C}=\epsilon_{B\otimes_A^LC}\circ v_!(\theta_{B,C}).$$ Every $B,C$ has the flat-term K-flat
representatives used above by [lem-pc-kflat-resolution]. The bifunctorial descent and detection
clause of [lem-weil-pbc-site-derived-tensor-descent] makes this equality independent of
representatives and valid for arbitrary derived morphisms. No boundedness or finite Tor amplitude
was used, so both the isomorphism and its counit compatibility hold for all unbounded $B,M,C$.
-/
theorem isIso_etaleSumExtensionTensorComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsNoetherian V] [IsNoetherian T]
    (B : DerivedCategoryModule A T) (M : DerivedCategoryModule A V) :
    IsIso (etaleSumExtensionTensorComparison A v B M) ∧
      ∀ C : DerivedCategoryModule A T,
        etaleSumExtensionTensorComparison A v B
            ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≫
            ((derivedTensor (ModuleCat.{u + 1} A) T).obj B).map
              (((etaleLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).counit.app C) =
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
            (etaleSumExtensionTensorPullbackIso A v B C).hom ≫
            ((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).counit.app
              (((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj C) := by
  sorry

end AlgebraicGeometry.Etale
