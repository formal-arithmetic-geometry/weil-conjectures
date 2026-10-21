/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.RadicialDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Internal Hom preserves constructibility and finite Tor amplitude

Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-rem-sf-matrix,
node det-rem-sf-matrix-hom-devissage (blueprint: det-rem-sf-matrix-hom-devissage).

The ordinary ambient etale internal Hom is the existing `Etale.derivedHom`, obtained
by right deriving the sheaf Hom complex with K-injective resolutions. The constant-ring
module presentation in `derivedInternalHomOfUniverses` gives the same ringed-site operation.
Bounded constructibility uses the recorded finite-value constructibility predicate.
Finite Tor amplitude tests every module sheaf, not merely constant sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

private theorem devissage_ctf_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X) :
    (DerivedCategory.isBoundedConstructible A X K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K) ↔
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨⟨hc, ⟨a, b, -, hz⟩⟩, ⟨c, d, -, ht⟩⟩
    exact ⟨⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
        (fun q hq ↦ hz q (.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
        (fun q hq ↦ hz q (.inr hq))⟩⟩,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (hc q)⟩, c, d, torAmplitudeIn_of_hasTorAmplitudeIn A ht⟩
  · rintro ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, c, d, ht⟩
    refine ⟨⟨fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc q),
      ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩⟩,
      ⟨min c d, max c d, min_le_max,
        hasTorAmplitudeIn_of_torAmplitudeIn
          (DerivedCategory.torAmplitudeIn.mono (min_le_left c d) (le_max_right c d) ht)⟩⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha q
        (hq.trans_le (min_le_left a b))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb q
        ((le_max_right a b).trans_lt hq)

-- Keep coefficients abstract here, as in the source's Point comparison lemma:
-- specializing the derived monoidal structures before this comparison is expensive.
private theorem devissage_hom_equivalence
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsUniversalHomeomorphism f]
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (let : (upperStar C f).IsEquivalence := isEquivalence_upperStar C f
    Nonempty ((((derivedHom C X).obj (op K)).obj L) ≅
      (upperStar C f).inv.mapDerivedCategory.obj
        (((derivedHom C Y).obj (op ((upperStar C f).mapDerivedCategory.obj K))).obj
          ((upperStar C f).mapDerivedCategory.obj L)))) := by
  let F := upperStar C f
  let : F.IsEquivalence := isEquivalence_upperStar _ f
  let : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  let E := F.asEquivalence.mapDerivedCategory
  let H := ((derivedHom C Y).obj (op (E.functor.obj K))).obj (E.functor.obj L)
  let Q := E.inverse.obj H
  let eK : K ≅ E.inverse.obj (E.functor.obj K) := E.unitIso.app K
  let eL : L ≅ E.inverse.obj (E.functor.obj L) := E.unitIso.app L
  have e₁ : (((derivedHom C X).obj (op K)).obj L) ≅
      (((derivedHom C X).obj
        (op (E.inverse.obj (E.functor.obj K)))).obj L) :=
    ((derivedHom C X).mapIso eK.symm.op).app L
  have e₂ : (((derivedHom C X).obj
        (op (E.inverse.obj (E.functor.obj K)))).obj L) ≅
      (((derivedHom C X).obj
        (op (E.inverse.obj (E.functor.obj K)))).obj
          (E.inverse.obj (E.functor.obj L))) :=
    ((derivedHom C X).obj
      (op (E.inverse.obj (E.functor.obj K)))).mapIso eL
  have e₃ : Q ≅ (((derivedHom C X).obj
      (op (E.inverse.obj (E.functor.obj K)))).obj
        (E.inverse.obj (E.functor.obj L))) :=
    (_root_.DerivedCategory.ihomCompMapDerivedCategoryInvIso F
      (E.functor.obj K)).app (E.functor.obj L)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃.symm⟩

private theorem devissage_hom_descends
    (A : Type (u + 1)) [CommRing A] [Finite A] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsUniversalHomeomorphism f]
    (K L : DerivedCategoryModule A X)
    (h : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj
        (op ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K))).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj L))) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) := by
  let F := upperStar (ModuleCat.{u + 1} A) f
  let : F.IsEquivalence := isEquivalence_upperStar _ f
  let : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  let E := F.asEquivalence.mapDerivedCategory
  let H := ((derivedHom (ModuleCat.{u + 1} A) Y).obj (op (E.functor.obj K))).obj
    (E.functor.obj L)
  let Q := E.inverse.obj H
  have hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X Q := by
    have hp : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y
        (E.functor.obj Q) :=
      (DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso
        (E.counitIso.app H).symm h
    obtain ⟨hc, a, b, ht⟩ := hp
    exact ⟨boundedConstructible_of_upperStar_of_isUniversalHomeomorphism f hc,
      a, b, _root_.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory F Q ht⟩
  obtain ⟨e⟩ := devissage_hom_equivalence (ModuleCat.{u + 1} A) f K L
  exact (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso e.symm hQ

/-- Internal Hom of two bounded constructible finite-Tor complexes is again such a complex.
Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-rem-sf-matrix,
node det-rem-sf-matrix-hom-devissage (blueprint: det-rem-sf-matrix-hom-devissage).
The finite ell-primary condition is expressed by a power of ell vanishing in A.
No separatedness or coefficient presentation is required.

Proof plan (the numbered steps are the DAG node's proof):

1. We prove the assertion simultaneously for all pairs of objects on each finite-type
$k$-scheme, by Noetherian induction on reduced closed subsets of a fixed $X$. The field spectrum
is Noetherian (a field has only two ideals); hence $X$ is Noetherian by [lem-weil-pbc-finite-
type-over-noetherian]. The minimal-closed-subset principle [lem-weil-pbc-noetherian-scheme-
closed-subsets-minimal] justifies induction on proper closed subsets. Give each such subset its
reduced induced closed structure using [lem-weil-pbc-reduced-induced-closed-subscheme]; it is
still finite type over $k$, since affine coordinate rings are quotients of finite-type
$k$-algebras. Use the original, possibly nonreduced $X$ for the top case and the reduced induced
closed schemes for its strict descendants. A closed subset of a descendant is closed in $X$, and
the two reduced induced structures agree by the uniqueness in [lem-weil-pbc-reduced-induced-
closed-subscheme]. The inductive hypothesis is the conclusion for every pair in
$\Dctf(Z_{\mathrm{ét}},A)$ for every such proper closed subscheme $Z$. On the empty scheme all
module sheaves are zero, so the conclusion holds.

2. We record the closure and inverse-image facts used throughout the induction. Clause (3) of
[det-sf-flat-model-generation], with its explicit ordinary étale constant-$A$ convention, says
that $\Dctf$ is closed under shifts, cones, retracts and isomorphisms; in particular it has the
two-out-of-three property in distinguished triangles. For every scheme considered here, [thm-
constructible-serre] supplies closure of constructible $A$-module sheaves under kernels,
cokernels and extensions; zero and isomorphism invariance follow from the definition. Thus the
explicit weak-Serre hypothesis of the main-20261015 statement of [prop-constructible-derived-
subcategory] holds throughout the proof. Finite direct sums are constructible by the split exact
sequences, and retracts are constructible as kernels of $1-e$ for an idempotent $e$. For every
morphism between the Noetherian schemes at issue, inverse image preserves $\Dctf$: choose a
bounded flat constructible representative by [lem-sf-etale-flat-constructible], apply the exact
inverse image of constant-$A$ modules [prop-weil-pbc-inverse-image-modules-exact] termwise, and
use [lem-weil-pbc-ringed-topos-flat-module-pullback] for flatness and [lem-weil-pbc-
constructible-etale-set-pullback] for constructibility of the underlying sheaf of sets. They are
constructible as $A$-module sheaves: on each pulled-back stratum, after trivializing the finite
set sheaf, the finitely many addition and scalar maps are locally constant, so a finite
refinement of the covering makes the restriction constant as an $A$-module sheaf (as in Step 4).
The resulting complex is bounded in the same degrees. Its bounded constructible cohomology
follows by the stupid filtration and [prop-constructible-derived-subcategory], and the converse
direction of [lem-sf-etale-flat-constructible] gives the Tor bound. In particular this applies
to $j^*$ and $i^*$ below.

3. For a closed immersion $i:Z\hookrightarrow X$, direct image also preserves $\Dctf$ in this
setting. Indeed [lemma-openclosed-stalk-lowerstar] identifies $(i_*F)_{\bar x}$ with $F_{\bar
z}$ at a point on $Z$; outside $Z$ it is zero by [lem-kun-04ca]. These formulas, exactness of
geometric stalks [prop-weil-pbc-geometric-stalks-exact], and their conservativity [lemma-weil-
pbc-geometric-stalk-conservative] show that $i_*$ on module sheaves is exact. They also show it
preserves flatness: by [lem-pod-etale-stalk-tensor-scalar], tensoring a short exact sequence
with $i_*F$ has stalkwise the tensor sequence with the flat $A$-module $F_{\bar z}$ on $Z$, and
the zero sequence off $Z$. Here flatness of $F_{\bar z}$ follows from [lem-weil-pbc-ringed-
topos-flat-module-pullback] applied to the geometric point of the topos, whose inverse image is
the stalk. Exactness is detected by applying the exact conservative stalks to kernels and
cokernels. By [lem-fin-closed-immersion] $i_*$ preserves constructibility. Applying $i_*$
termwise to a bounded flat constructible model therefore gives another such model; [prop-
constructible-derived-subcategory] and [lem-sf-etale-flat-constructible] put its derived object
in $\Dctf(X_{\mathrm{ét}},A)$.

4. Assume $X$ is nonempty. Choose bounded flat constructible models $P^\bullet,Q^\bullet$ for
$K,L$ using [lem-sf-etale-flat-constructible], with supports $[c,e]$ and $[a,b]$. Apply [prop-
constructible-generic-constancy] to each of the finitely many nonzero $P^q$, and intersect the
resulting dense opens. This gives a dense open $j:U\hookrightarrow X$ on which all $P^q$ are
finite locally constant. The local trivializations can be chosen $A$-linear: after trivializing
the finite underlying set sheaf, the finitely many addition and scalar-action maps are locally
constant, so refine finitely many times. Clause (1) of [det-sf-flat-model-generation] says the
stalks of each flat constructible $P^q$ are finite projective $A$-modules. Thus étale locally on
$U$ each of the finitely many $P^q$ is a direct summand of a finite free constant-$A$ sheaf,
simultaneously on the covering family of finite fibre products over $U$ of members of the
individual trivializing covers; the family covers because each geometric point lifts through
each of the finitely many covers. The complement has the reduced structure $i:Z\hookrightarrow
X$ from Step 1 and is a proper closed subset. Every open of a Noetherian scheme is Noetherian
[lem-weil-pbc-noetherian-open-subscheme-noetherian]; thus $U$ is quasi-compact and finite type
over $k$ (on affine charts the quasi-compact open is covered by finitely many principal opens).

5. On $U$, form the ordinary sheaf Hom complex $H^\bullet=\mathcal
Hom_A^\bullet(P^\bullet|_U,Q^\bullet|_U)$ and its canonical map to the Hom complex into a
K-injective resolution of $Q^\bullet|_U$. On each member $V$ of the étale covering of Step 4 on
which the finitely many $P^q$ are direct summands of finite free constant sheaves, [lem-weil-
pbc-ringed-site-bounded-free-rhom-model] identifies the restriction of that map with the
canonical quasi-isomorphism computing derived internal Hom on the slice; the lower bound on $Q$
and upper bound on $P$ are exactly its hypotheses. Derived internal Hom commutes with these
slice restrictions by [lem-weil-pbc-ringed-internal-hom-exact-restriction], so the map is a
quasi-isomorphism globally: the cohomology sheaves of its cone vanish on a covering, hence
vanish. For each degree pair $(q,r)$, apply [lem-sfb-lisse-split-hom-flat-constructible] on the
Noetherian scheme $U$ (Step 4) with $E=P^q|_U$, which is a direct summand of a finite free
constant sheaf on each member of the covering of Step 4, and $G=Q^r|_U$, which is flat and
constructible as the inverse image of a flat constructible sheaf along the open immersion $j$
(Step 2): $\mathcal Hom_A(P^q|_U,Q^r|_U)$ is flat and constructible. Finite direct sums of flat
constructible sheaves are constructible by Step 2 and flat since tensor product distributes over
finite sums. Thus $H^n=\bigoplus_q\mathcal Hom(P^q,Q^{q+n})$ (a finite sum) is flat
constructible, and it is zero unless some $q$ satisfies $c\leq q\leq e$ and $a\leq q+n\leq b$,
i.e. outside $[a-e,b-c]$. Bounded constructibility of the cohomology follows from [prop-
constructible-derived-subcategory] by the finite stupid filtration, and the flat-model
equivalence [lem-sf-etale-flat-constructible] (interval $[a-e,b-c]$, nonempty since $a\leq b$,
$c\leq e$) yields $R\mathcal Hom_A(j^*K,j^*L)\in\Dctf(U_{\mathrm{ét}},A)$.

6. The functor $Rj_*$ sends every $C\in\Dctf(U_{\mathrm{ét}},A)$ into
$\Dctf(X_{\mathrm{ét}},A)$. Constructibility and boundedness follow from [cor-fin-deligne-open-
finite-coefficients]: the finite ring $A$ is killed by a power of $\ell$, an integer invertible
in $k$. By [lem-kun-0f10] choose a finite integer $d\geq\operatorname{cd}(j)$. Clause (2) of
[det-cor-sf-direct-image-ctf-open-tor] then takes any Tor interval $[v,w]$ for $C$ to $[v,w+d]$
for $Rj_*C$, against all étale module sheaves. The fields, coefficients and finite-type
hypotheses in that statement agree with ours; no separatedness of $X$ is required. We use only
its étale clause (2).

7. Apply [lem-weil-stratum-ambient-hom] to the open immersion $s=j$, for which the factorization
is the identity closed immersion followed by $j$ and hence $Rs^!=j^*$. It gives $R\mathcal
Hom_A(j_!j^*K,L)\cong Rj_*R\mathcal Hom_A(j^*K,j^*L)$. The inner object is in
$\Dctf(U_{\mathrm{ét}},A)$ by Step 5 and its direct image is in $\Dctf(X_{\mathrm{ét}},A)$ by
Step 6. This proves the open outer term needed for gluing, without an internal-Hom pullback
assertion for a closed immersion.

8. The ambient support triangle [lem-exc-closed-support-triangle] gives $i_*Ri^!L\to L\to
Rj_*j^*L\to$. Here $j^*L\in\Dctf(U_{\mathrm{ét}},A)$ by Step 2, so $Rj_*j^*L$ is in $\Dctf$ by
Step 6. Two-out-of-three from Step 2 gives $i_*Ri^!L\in\Dctf(X_{\mathrm{ét}},A)$. Applying $i^*$
and using $i^*i_*\cong\mathrm{id}$ from [prop-openclosed-lowerstar-fully-faithful] gives
$Ri^!L\in\Dctf(Z_{\mathrm{ét}},A)$. This counit extends degreewise to the derived categories
because both inverse image and closed direct image are exact, as established in Steps 2 and 3.
Also $i^*K\in\Dctf(Z_{\mathrm{ét}},A)$ by Step 2.

9. Apply [lem-weil-stratum-ambient-hom] to $s=i$, with identity open factor. The isomorphism is
$R\mathcal Hom_A(i_*i^*K,L)\cong i_*R\mathcal Hom_A(i^*K,Ri^!L)$; ordinary $i_*$ agrees with its
derived functor by Step 3. The two inputs on $Z$ are in $\Dctf$ by Step 8. Since $Z$ is a proper
reduced closed subscheme, the inductive hypothesis applies and puts their internal Hom in
$\Dctf(Z_{\mathrm{ét}},A)$. Step 3 puts its direct image in $\Dctf(X_{\mathrm{ét}},A)$. This
proves the closed outer term; it uses no preservation theorem for $Ri^!$ beyond what Step 8 just
proved.

10. Use [lem-cbc-open-closed-recollement] on the bounded object $K$ to obtain $j_!j^*K\to K\to
i_*i^*K\to$. By [lem-sf-hom-triangulated], applying $R\mathcal Hom_A(-,L)$ gives the
distinguished triangle $R\mathcal Hom_A(i_*i^*K,L)\to R\mathcal Hom_A(K,L)\to R\mathcal
Hom_A(j_!j^*K,L)\to$. Its first and third terms are in $\Dctf$ by Steps 9 and 7. The two-out-of-
three property established in Step 2 gives the desired conclusion for the middle term,
completing the induction.
-/
theorem isBoundedConstructible_finiteTor_derivedHom_by_devissage
    (k : Type u) [Field k] [IsSepClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (K L : DerivedCategoryModule A X)
    (_hKc : DerivedCategory.isBoundedConstructible A X K)
    (_hKt : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K)
    (_hLc : DerivedCategory.isBoundedConstructible A X L)
    (_hLt : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b L) :
    DerivedCategory.isBoundedConstructible A X
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) := by
  -- Reuse algebraically closed preservation and descend along the purely inseparable
  -- algebraic-closure base change, rather than replaying the original plan above.
  have hK := (devissage_ctf_iff A X K).mp ⟨_hKc, _hKt⟩
  have hL := (devissage_ctf_iff A X L).mp ⟨_hLc, _hLt⟩
  apply (devissage_ctf_iff A X _).mpr
  let Ω := AlgebraicClosure k
  let g : Spec (.of Ω) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let Y := Limits.pullback (X ↘ Spec (.of k)) g
  let f : Y ⟶ X := Limits.pullback.fst _ _
  let aY : Y ⟶ Spec (.of Ω) := Limits.pullback.snd _ _
  let : IsPurelyInseparable k Ω :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure k Ω).mp inferInstance
  let : IsUniversalHomeomorphism g := inferInstance
  let : IsUniversalHomeomorphism f := inferInstance
  have : LocallyOfFiniteType aY := inferInstance
  have : QuasiCompact aY := inferInstance
  obtain ⟨n, hn⟩ := _hA
  have : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos n, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hn
    · simpa only [map_pow, map_natCast, Nat.cast_pow] using
        ((_hℓ.isUnit.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom)
  have : HasInvertibleExponent A Y := .of_hom (f ≫ X ↘ Spec (.of k))
  apply devissage_hom_descends A f K L
  have hK' := constructibleFiniteTor_mapDerivedCategory_upperStar A f hK
  have hL' := constructibleFiniteTor_mapDerivedCategory_upperStar A f hL
  obtain ⟨hcK, a, b, htK⟩ := hK'
  obtain ⟨hcL, c, d, htL⟩ := hL'
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_le aY
  exact ⟨boundedConstructible_derivedHom A aY a b c d hcK htK hcL htL,
    _, _, torAmplitudeIn_derivedHom A aY m hm a b c d hcK htK hcL htL⟩


end AlgebraicGeometry.Etale
