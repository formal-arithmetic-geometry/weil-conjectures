module

public import Sheaf.AlgebraicGeometry.FormalModuliQuotient
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.AffineActionQuotientStack
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.AlgebraicGeometry.ActionGroupoidQuotientCriterion

/-! # Finite representable pullbacks of formal quotient charts

Source: Stacks Project, spaces-groupoids.tex, Tags 04M9 and 044W, algebraic.tex,
Tags 04T4 and 04T5, and algebra.tex, Tags 00MA and 07N9; the formal argument
in Pikaart--de Jong Proposition 2.3.6
(blueprint: lem-sfb-finite-formal-quotient-pullback).

Formal quotients use supported atlas arrows and arbitrary étale local trivializations.
The last compatibility equation identifies the lifted arrows with the original ones
through the specified pullback square. It is the equivalence over the base quotient,
including its descent arrows, rather than an unspecified equivalence of stacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Coherent atlas arrows restricted to test maps with image in the formal support.
Naturality includes arbitrary changes of test scheme. Source: Stacks 04M9, 044W;
Pikaart--de Jong Section 2.3.6 (blueprint: lem-sfb-finite-formal-quotient-pullback). -/
structure SupportedModuliAtlasAction {S : Scheme.{u}} {Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} {H : Type u} [Group H]
    (ρ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F)
    (Z : Set Q.left) where
  stable : ∀ (h : H) (z : Q.left), z ∈ Z → (ρ h).hom.left z ∈ Z
  arrow : ∀ (T : Over S) (a : T ⟶ Q) (_ : ∀ t : T.left, a.left t ∈ Z) (h : H),
    ModuliTwoIso (moduliChartMap (a ≫ (ρ h).hom) f) (moduliChartMap a f)
  naturality : ∀ (T W : Over S) (a : T ⟶ Q) (ha : ∀ t : T.left, a.left t ∈ Z)
      (c : W ⟶ T) (h : H),
    HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map c)).toFunctor
      (arrow T a ha h).val.hom)
      (arrow W (c ≫ a) (fun t ↦ ha (c.left t)) h).val.hom
  one : ∀ (T : Over S) (a : T ⟶ Q) (ha : ∀ t : T.left, a.left t ∈ Z),
    HEq (arrow T a ha 1).val.hom (𝟙 (moduliChartMap a f).toFunctor)
  mul : ∀ (T : Over S) (a : T ⟶ Q) (ha : ∀ t : T.left, a.left t ∈ Z) (h k : H),
    HEq (arrow T a ha (h * k)).val.hom
      ((arrow T (a ≫ (ρ k).hom) (fun t ↦ stable k (a.left t) (ha t)) h).val.hom ≫
        (arrow T a ha k).val.hom)

/-- The atlas-and-arrows characterization of the torsor quotient on a formal support.
The object lifts and arrow labels are étale local; only uniqueness is tested globally
on nonempty schemes. This retains locally constant labels and nontrivial torsors.
Source: Stacks 04M9, 044W; Pikaart--de Jong Section 2.3.6
(blueprint: lem-sfb-finite-formal-quotient-pullback). -/
def IsSupportedFormalModuliQuotient {S : Scheme.{u}} {Q : Over S}
    {F : BasedCategory.{v, w} (Over S)} {H : Type u} [Group H]
    (ρ : H →* Aut Q) (f : BasedFunctor (discreteModuli (yoneda.obj Q)) F)
    (Z : Set Q.left) (θ : SupportedModuliAtlasAction ρ f Z)
    (P : ∀ (T : Over S), BasedFunctor (discreteModuli (yoneda.obj T)) F → Prop) : Prop :=
  (∀ (T : Over S) (a : T ⟶ Q), (∀ t : T.left, a.left t ∈ Z) →
    P T (moduliChartMap a f)) ∧
  (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F), P T t →
    ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
      ∀ (W : Over S) (c : W ⟶ T), R c →
        ∃ (a : W ⟶ Q) (_ : ∀ z : W.left, a.left z ∈ Z),
          Nonempty (ModuliTwoIso (moduliChartMap a f) (moduliChartMap c t))) ∧
  (∀ (T : Over S) (a b : T ⟶ Q) (ha : ∀ t : T.left, a.left t ∈ Z)
      (_ : ∀ t : T.left, b.left t ∈ Z),
    ∀ η : ModuliTwoIso (moduliChartMap a f) (moduliChartMap b f),
      ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
        ∀ (W : Over S) (c : W ⟶ T), R c →
          ∃ h : H, (c ≫ a) ≫ (ρ h).hom = c ≫ b ∧
            HEq (Functor.whiskerLeft (discreteModuliMap (yoneda.map c)).toFunctor η.val.hom)
              (θ.arrow W (c ≫ a) (fun t ↦ ha (c.left t)) h).val.inv) ∧
  (∀ (T : Over S) (_ : Nonempty T.left) (a : T ⟶ Q)
      (ha : ∀ t : T.left, a.left t ∈ Z) (h k : H),
    a ≫ (ρ h).hom = a ≫ (ρ k).hom →
      HEq (θ.arrow T a ha h).val.inv (θ.arrow T a ha k).val.inv → h = k)


/-- The affine map induced by a homomorphism of base algebras.
Source: Stacks 04M9 (blueprint: lem-sfb-finite-formal-quotient-pullback). -/
def formalAffineMap {Ω A B : Type u} [Field Ω] [CommRing A] [CommRing B]
    [Algebra Ω A] [Algebra Ω B] (φ : A →ₐ[Ω] B) :
    affineActionScheme Ω B ⟶ affineActionScheme Ω A :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r)

/-- The closed-point map into the affine chart with the literal identity base.
Source: Stacks 04M9 (blueprint: lem-sfb-finite-formal-quotient-pullback). -/
def formalResidueMap {Ω R : Type u} [Field Ω] [CommRing R] [Algebra Ω R]
    [IsLocalRing R] (res : IsLocalRing.ResidueField R ≃ₐ[Ω] Ω) :
    Over.mk (𝟙 (Spec (.of Ω))) ⟶ affineActionScheme Ω R :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (res.toAlgHom.comp (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R))).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω) using 1
    congr 1
    ext r
    exact (res.toAlgHom.comp
      (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R))).commutes r)

/-- Descent-arrow compatibility of a finite formal pullback presentation.
The equation is stated at every object of every represented test groupoid. The equality
δ only identifies the two source objects via the equivariance of the scheme projection.
Source: Stacks 04M9, proof by triples (blueprint: lem-sfb-finite-formal-quotient-pullback). -/
def FormalQuotientPullbackArrows
    {Ω R C H : Type u} [Field Ω] [CommRing R] [CommRing C]
    [Algebra Ω R] [Algebra Ω C] [IsLocalRing R] [Group H]
    {X : BasedCategory.{v₁, w₁} (Over (Spec (.of Ω)))}
    {Y : BasedCategory.{v₂, w₂} (Over (Spec (.of Ω)))}
    (φ : R →ₐ[Ω] C) (p : BasedFunctor Y X)
    (ρ : H →* Aut (affineActionScheme Ω R))
    (ρC : H →* Aut (affineActionScheme Ω C))
    (f : BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme Ω R))) X)
    (g : BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme Ω C))) Y)
    (η : g.comp p ≅ (discreteModuliMap (yoneda.map (formalAffineMap φ))).comp f)
    (θ : SupportedModuliAtlasAction ρ f
      (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R)))
    (ψ : SupportedModuliAtlasAction ρC g
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal R).map φ.toRingHom))) : Prop :=
  (∀ h : H, (ρC h).hom ≫ formalAffineMap φ = formalAffineMap φ ≫ (ρ h).hom) ∧
  ∀ (T : Over (Spec (.of Ω))) (a : T ⟶ affineActionScheme Ω C)
    (ha : ∀ z : T.left,
      a.left z ∈ PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal R).map φ.toRingHom))
    (h : H) (z : (discreteModuli (yoneda.obj T)).obj),
    ∃ δ :
      (((discreteModuliMap (yoneda.map (formalAffineMap φ))).comp f).obj
        ((discreteModuliMap (yoneda.map (a ≫ (ρC h).hom))).obj z)) =
        (moduliChartMap ((a ≫ formalAffineMap φ) ≫ (ρ h).hom) f).obj z,
      HEq
        (p.toFunctor.map ((ψ.arrow T a ha h).val.hom.app z) ≫
          η.hom.toNatTrans.app ((discreteModuliMap (yoneda.map a)).obj z))
        (η.hom.toNatTrans.app
            ((discreteModuliMap (yoneda.map (a ≫ (ρC h).hom))).obj z) ≫
          eqToHom δ ≫
          (θ.arrow T (a ≫ formalAffineMap φ)
            (fun t _r hr ↦ ha t (Ideal.mem_map_of_mem φ.toRingHom hr)) h).val.hom.app z)

/-- Finite pullbacks of a formal quotient chart.
Source: Stacks 04M9, 04T4, 04T5 and 00MA; Pikaart--de Jong Proposition 2.3.6
(blueprint: lem-sfb-finite-formal-quotient-pullback).

Proof:
1. Apply the scheme-test definition of $p$ to $\operatorname{Spec}R$. Its pullback is an affine
scheme $\operatorname{Spec}C$ finite over $\operatorname{Spec}R$, so $C$ is a finite $R$-module by
[def-weil-finite-integral-morphism]. Apply
[lem-weil-pbc-finite-module-complete-over-complete-noetherian] with $J=\mathfrak m$ and $N=C$: $R$
is Noetherian and $\mathfrak m$-adically complete by hypothesis. Thus the canonical map
$C\to\varprojlim_{n\geq1}C/\mathfrak m^nC$ is bijective. It is a ring homomorphism because
operations on the limit are componentwise; consequently it is a ring isomorphism.

2. Write $R_n=R/\mathfrak m^n$, $C_n=C/\mathfrak m^nC$, $U_n=\operatorname{Spec}R_n$, and let
$\mathcal X_n$ be the $n$th neighbourhood of the gerbe. The specified formal chart identifies
$\mathcal X_n$ with $[U_n/H]$ and its atlas with the restriction of $f$. Put $\mathcal
Y_n=\mathcal Y\times_{\mathcal X}\mathcal X_n$. Associating the triples in a 2-fibre product gives
$$\mathcal Y_n\times_{\mathcal X_n}U_n\simeq\mathcal Y\times_{\mathcal
X}U_n\simeq\operatorname{Spec}C_n=:V_n.$$ For the last identification, a homomorphism $C\to A$
whose restricted map $R\to A$ kills $\mathfrak m^n$ factors uniquely through $C_n$; this proves
the affine pullback assertion directly. All these identifications commute with reduction from
$n+1$ to $n$.

3. For a test scheme $T$, represent a point of $V_n$ by $(u,y,\beta)$, with $u:T\to U_n$,
$y\in\mathcal Y_n(T)$ and $\beta:p(y)\simeq a_n(u)$. An arrow from $u$ to $hu$ in $[U_n/H]$ is the
corresponding equivariant isomorphism of trivial torsors; its composites are given by
multiplication in $H$. Compose $\beta$ with that arrow, leaving $y$ fixed. This defines an
automorphism $\widetilde h_n$ of $V_n$ covering $h$ on $U_n$. Although triples are taken up to
isomorphism, $V_n$ is a scheme, so natural isomorphisms give equal maps on its represented sheaf.
Hence $\widetilde g_n\widetilde h_n=\widetilde{gh}_n$ and $\widetilde1_n=1$. These maps commute
with reduction, since composition of the same arrows commutes with restriction.

4. Use contravariance of affine spectra to put $\rho_{h,n}=(\widetilde {h^{-1}}_n)^*:C_n\to C_n$.
These are compatible ring automorphisms, satisfy $\rho_{gh,n}=\rho_{g,n}\rho_{h,n}$, and are
semilinear for the given ring action on $R_n$ (the scheme action associated to a ring action uses
inverse pullback). Via the canonical ring isomorphism of step 1 define
$$\rho_h((c_n)_n)=(\rho_{h,n}(c_n))_n.$$ The identities $\rho_{gh}=\rho_g\rho_h$, $\rho_1=1$ and
$\rho_h(rc)=h(r)\rho_h(c)$ hold in every coordinate, hence in $C$. Each $\rho_h$ preserves
$\mathfrak m^nC$: its quotient at level $n$ is $\rho_{h,n}$. It is therefore continuous for the
$\mathfrak m C$-adic topology, as is its inverse $\rho_{h^{-1}}$. This is the required continuous
semilinear action extending the action on $R$.

5. Check the presentation criterion [lem-sfb-action-groupoid-quotient-criterion] over
$S=\operatorname{Spec}\Omega$ for $b:V_n\to\mathcal Y_n$, $(u,y,\beta)\mapsto y$. Every
$y\in\mathcal Y_n(T)$ lifts etale locally to $V_n$: under $\mathcal X_n\simeq[U_n/H]$, $p(y)$ is
an $H_T$-torsor $P\to T$ with an equivariant map $e:P\to U_n$, and $P$ is trivial on a jointly
surjective etale family $T_i\to T$ (torsors as in [lem-sfb-action-groupoid-quotient-criterion]).
The identity section of $P|_{T_i}\simeq H_{T_i}$ composed with $e$ gives $u_i:T_i\to U_n$ and
$\beta_i:p(y)|_{T_i}\simeq a_n(u_i)$; then $(u_i,y|_{T_i},\beta_i)\in V_n(T_i)$ lifts $y|_{T_i}$.
The structure isomorphisms are $\alpha_{h,v}=1_y$, since $\widetilde h_n$ leaves $y$ fixed; their
cocycle identities are trivial. Its arrow space is $$V_n\times_{\mathcal Y_n}V_n\simeq
H_\Omega\times_\Omega V_n$$ on $T$-valued points. For $v=(u,y,\beta)$ and $v'=(u',y',\beta')$ an
arrow over $\mathcal Y_n$ is $\gamma:y\simeq y'$; put
$\alpha=\beta'p(\gamma)\beta^{-1}:a_n(u)\simeq a_n(u')$, so $\alpha\beta=\beta'p(\gamma)$. An
equivariant isomorphism of the trivial left torsors is right translation by $h^{-1}$ for a unique
locally constant $h:T\to H$, with $u'=hu$. The displayed equation then identifies $v'$ with
$\widetilde h_n(v)$ via $\gamma$. Conversely $(h,v)$ gives $(v,\widetilde h_n(v),1_y)$. These
constructions are inverse, functorial in $T$, and identify composition with multiplication,
including when points have nontrivial stabilizers. The criterion gives the equivalence
$F_n:[V_n/H]\to\mathcal Y_n$ whose atlas map is $b$ and whose arrows are the ones just computed.

6. The equivalences in step 5 use exactly the object map $V_n\to\mathcal Y_n$ and the arrows
computed in step 3. Restricting these maps to level $n$ from level $n+1$ gives those same maps at
level $n$. The uniqueness clause of [lem-sfb-action-groupoid-quotient-criterion] supplies the
compatible 2-isomorphisms of the equivalences; their cocycle holds by the same uniqueness. The
level-$n$ identification of step 5 lies over $[U_n/H]\simeq\mathcal X_n$: on the atlas the two
composites $V_n\to\mathcal X_n$ send $v=(u,y,\beta)$ to $p(y)$ and to $a_n(u)$, and $\beta$ is an
isomorphism between them compatible with the arrows, because $\widetilde h_n$ composes $\beta$
with the arrow $u\to hu$ (the equation $\alpha\beta=\beta'p(\gamma)$ of step 5). Since every
object of $[V_n/H]$ comes etale locally from $V_n$ and isomorphisms in $\mathcal X_n$ form etale
sheaves [def-sfb-stable-pointed-moduli-groupoids], these $\beta$ glue uniquely to a 2-isomorphism
of the two composites $[V_n/H]\to\mathcal X_n$; it is compatible with reduction in $n$ because the
triple components $\beta$ restrict unchanged, so the 2-isomorphisms of the equivalences also
respect the maps to $[U_n/H]$. The ideal defining $\mathcal Y_n$ is the extension to $\mathcal Y$
of the $n$th power of the gerbe ideal, which equals the $n$th power of its extended ideal: both
are generated by products of $n$ local generators. Thus $(\mathcal Y_n)_n$ is precisely the
completion along $p^{-1}\mathcal G_x$. On its atlas the ideals are $\mathfrak m^nC=(\mathfrak m
C)^n$, so $(V_n)_n$ is $\operatorname{Spf}C$. Taking the compatible system gives the asserted
canonical equivalence over $[\operatorname{Spf}R/H]$.
-/
theorem finite_formal_quotient_pullback
    (Ω R : Type u) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (res : IsLocalRing.ResidueField R ≃ₐ[Ω] Ω)
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of Ω))))
    (hX : IsDeligneMumfordModuliStack X)
    (hnoeth : ∃ (U : Over (Spec (.of Ω)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) X),
      IsLocallyNoetherian U.left ∧
        ∀ (T : Over (Spec (.of Ω))) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
          ∃ (Z : AlgebraicSpace (Spec (.of Ω))) (q : Z.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange a T t Z q ∧ SpaceMapIsEtale Z T q ∧ SpaceMapIsSurjective Z T q)
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of Ω)))))) X)
    (H : Type u) [Group H] [Finite H]
    (α : H →* (R ≃ₐ[Ω] R))
    (ρ : H →* Aut (affineActionScheme Ω R))
    (hρ : ∀ h : H, (ρ h).hom.left = Spec.map (CommRingCat.ofHom (α h).symm.toRingHom))
    (hcont : ∀ h : H, @Continuous R R
      (IsLocalRing.maximalIdeal R).adicTopology (IsLocalRing.maximalIdeal R).adicTopology
      (α h))
    (f : BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme Ω R))) X)
    (hx : Nonempty (ModuliTwoIso
      (moduliChartMap (formalResidueMap res) f) x))
    (θ : SupportedModuliAtlasAction ρ f
      (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R)))
    (hchart : IsSupportedFormalModuliQuotient ρ f
      (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R)) θ
      (fun _ t ↦ ModuliCompletionAt x t))
    (Y : BasedCategory.{v₂, w₂} (Over (Spec (.of Ω)))) (hY : IsModuliStack Y)
    (p : BasedFunctor Y X) (hp : IsRepresentableFiniteModuliMap p) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra Ω C) (φ : R →ₐ[Ω] C),
      @Module.Finite R C _ _ φ.toRingHom.toAlgebra.toModule ∧
      @IsAdicComplete R _ (IsLocalRing.maximalIdeal R) C _ φ.toRingHom.toAlgebra.toModule ∧
      ∃ (σ : H →* (C ≃ₐ[Ω] C)),
        (∀ (h : H) (r : R), σ h (φ r) = φ (α h r)) ∧
        (∀ h : H, @Continuous C C
          ((IsLocalRing.maximalIdeal R).map φ.toRingHom).adicTopology
          ((IsLocalRing.maximalIdeal R).map φ.toRingHom).adicTopology (σ h)) ∧
        ∃ (ρC : H →* Aut (affineActionScheme Ω C))
          (g : BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme Ω C))) Y)
          (η : g.comp p ≅ (discreteModuliMap (yoneda.map (formalAffineMap φ))).comp f),
          (∀ h : H, (ρC h).hom.left =
            Spec.map (CommRingCat.ofHom (σ h).symm.toRingHom)) ∧
          (moduliTwoFiberLift
            (discreteModuliMap (yoneda.map (formalAffineMap φ))) g η.symm).toFunctor.IsEquivalence ∧
          ∃ ψ : SupportedModuliAtlasAction ρC g
              (PrimeSpectrum.zeroLocus
                (↑(Ideal.map φ.toRingHom (IsLocalRing.maximalIdeal R)) : Set C)),
            IsSupportedFormalModuliQuotient ρC g
              (PrimeSpectrum.zeroLocus
                (↑(Ideal.map φ.toRingHom (IsLocalRing.maximalIdeal R)) : Set C)) ψ
              (fun _ t ↦ ModuliCompletionAt x (t.comp p)) ∧
              FormalQuotientPullbackArrows φ p ρ ρC f g η θ ψ := by
  sorry

end CategoryTheory
