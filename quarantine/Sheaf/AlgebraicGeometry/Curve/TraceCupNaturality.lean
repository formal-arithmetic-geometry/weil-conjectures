/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.SecondKummerDivisors
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Naturality of finite curve trace-cup pairings

Source: Milne, Lectures on Étale Cohomology, Propositions 14.2, 14.5,
Remark 14.6, Theorem 14.7, Example 14.8 and §22; Stacks 0H9A and 0FPJ
(blueprint: lem-wf-curve-trace-cup-naturality).

## Main definitions

- `curvePointKummerClass`: the Kummer class of the divisor line bundle O(P).
- `curveConstantReduction`: reduction of the constant coefficient sheaf.
- `curveRootsReduction`: the power map on roots of unity.
- `curveRootsPullback`: the canonical pullback comparison for roots of unity.
- `curveTraceCup`: cup followed by trace, with total degree two.

## Main statements

- `curve_trace_cup_naturality`: coefficient reduction and semilinear invariance.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- Kummer class of O(P), where P is a closed point. Smoothness and the curve condition
supply relative dimension one; this is not an additional hypothesis.
Source: Milne 14.2 and 14.6 (blueprint: lem-wf-curve-trace-cup-naturality). -/
noncomputable def curvePointKummerClass
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (g : X ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g]
    (N : ℕ) (hN : IsUnit (N : Γ(X, ⊤))) (P : closedPoints X) :
    Sheaf.H (X.rootsOfUnitySheaf N) 2 :=
  letI : X.Over (Spec (.of k)) := ⟨g⟩
  letI : IsIntegral X := (X.smooth_connected_curve_local_rings k g).choose
  letI : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := g))
  X.kummerδ₁ N hN (Scheme.Pic.toCohomologicalPicardGroup X (Scheme.Pic.ofClosedPoint k P))

/-- Reduction of locally constant residue classes. Source: Milne §22
(blueprint: lem-wf-curve-trace-cup-naturality). -/
noncomputable def curveConstantReduction (X : Scheme.{u}) (ell n m : ℕ) (hmn : m ≤ n) :
    X.constantZMod (ell ^ n) ⟶ X.constantZMod (ell ^ m) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    ((AddCommGrpCat.uliftFunctor.{u + 1, 0}).map
      (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ell hmn) (ZMod (ell ^ m))).toAddMonoidHom))

/-- The power map z ↦ z^(ell^(n-m)), defined by the kernel universal property.
Source: the Kummer coefficient ladder, Milne 14.2
(blueprint: lem-wf-curve-trace-cup-naturality). -/
noncomputable def curveRootsReduction (X : Scheme.{u}) (ell n m : ℕ) (hmn : m ≤ n) :
    X.rootsOfUnitySheaf (ell ^ n) ⟶ X.rootsOfUnitySheaf (ell ^ m) :=
  kernel.lift (ell ^ m • 𝟙 X.gmSheaf)
    (kernel.ι (ell ^ n • 𝟙 X.gmSheaf) ≫ (ell ^ (n - m) • 𝟙 X.gmSheaf)) (by
      have hpow : ell ^ m * ell ^ (n - m) = ell ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hmn]
      simpa only [Category.assoc, Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        Category.comp_id, smul_smul, hpow] using
          kernel.condition (ell ^ n • 𝟙 X.gmSheaf))

/-- Restrict the canonical pullback-of-units map to the kernels of N-th powers.
Source: Stacks 0H9A and the Kummer sequence
(blueprint: lem-wf-curve-trace-cup-naturality). -/
noncomputable def curveRootsPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (N : ℕ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj (X.rootsOfUnitySheaf N) ⟶
      Y.rootsOfUnitySheaf N :=
  let U := Etale.upperStar AddCommGrpCat.{u + 1} f
  let c := Scheme.upperStarGmSheafToGmSheaf f
  kernel.lift (N • 𝟙 Y.gmSheaf) (U.map (kernel.ι (N • 𝟙 X.gmSheaf)) ≫ c) (by
    have hg : U.map (N • 𝟙 X.gmSheaf) ≫ c = c ≫ (N • 𝟙 Y.gmSheaf) := by
      simp [U]
    rw [Category.assoc, ← hg, ← Category.assoc, ← U.map_comp,
      kernel.condition, U.map_zero, zero_comp])

/-- The pairing in total degree two. The equality witness merely reindexes the output;
the condition i+j=2 is exactly the three cases (0,2), (1,1), (2,0).
Source: Milne 14.7 and 14.8 (blueprint: lem-wf-curve-trace-cup-naturality). -/
noncomputable def curveTraceCup (X : Scheme.{u}) (N : ℕ)
    (tr : Sheaf.H (X.rootsOfUnitySheaf N) 2 →+ ZMod N)
    (cup : ∀ i j : ℕ, Sheaf.H (X.constantZMod N) i →
      Sheaf.H (X.rootsOfUnitySheaf N) j → Sheaf.H (X.rootsOfUnitySheaf N) (i + j))
    (i j : ℕ) (hij : i + j = 2)
    (x : Sheaf.H (X.constantZMod N) i) (y : Sheaf.H (X.rootsOfUnitySheaf N) j) : ZMod N :=
  tr (hij ▸ cup i j x y)

/-- The degree-normalized trace-cup pairings commute with reduction and pullback along
any scheme isomorphism covering an automorphism of the algebraically closed ground field.
Trace is specified by its defining closed-point normalization. Cup is specified by
`IsFiniteEtaleCup`, the derived coefficient-action product in its Yoneda model.
Source: Milne 14.2, 14.5, 14.6, 14.7, 14.8 and §22; Stacks 0H9A/0FPJ
(blueprint: lem-wf-curve-trace-cup-naturality).


Proof plan from the node:
1. For either curve $T=C,D$ and every $rgeq1$, write $delta_{T,r}:operatorname{Pic}(T)to
H^2(T,mu_{ell^r})$ for the Kummer boundary. By [lem-sc-second-kummer-divisors] this map is
surjective. By [lem-sc-divisor-class-curve], every line-bundle class is the class of $mathcal
O_T(E)$ for a divisor $E$. Since [def-sc-divisor] makes the divisor group free on closed points
and the divisor-class map is additive, the elements $delta_{T,r}(mathcal O_T(P))$ generate
$H^2(T,mu_{ell^r})$ as an abelian group. Thus two additive maps out of this group agree if they
agree on these point classes.
2. On each of the two small etale sites, the category of abelian sheaves is Grothendieck by
[lem-weil-pbc-abelian-etale-sheaves-grothendieck], hence has enough injectives by [lem-sp-
grothendieck-enough-injectives]. Global sections is additive and left exact: the sectionwise
kernel of a sheaf morphism is a sheaf (compatible sections glue in the source and remain in the
kernel), and its global sections are the kernel of the map on global sections. Consequently
[lem-weil-pbc-right-derived-universal-delta-functor], applied to global sections and the
cohomology of [def-weil-pbc-etale-cohomology], says that a morphism $(a,b,c)$ of short exact
sequences commutes with connecting maps: $H^{q+1}(a)delta=delta'H^q(c)$. These $delta$-functor
connecting maps are the ones used everywhere below: by [lem-sc-p1-right-derived-triangle-
connecting], under the canonical identification $R^qGamma(F)cong H^q(RGamma(T_{Et},F[0]))$,
which is the cohomology of [def-weil-pbc-etale-cohomology], they are the homology connecting
maps of the distinguished triangle $A[0]to B[0]to C[0]to A[0][1]$ of the short exact sequence
after applying $RGamma$. These are the connecting maps of [lem-weil-pbc-pullback-cohomology-
long-exact-ladder] and the Kummer coboundaries of [lem-sc-second-kummer-divisors] and of the
item's trace normalization. We will use precisely this coefficient naturality, in addition to
the change-of-site naturality below.
3. Put $d=ell^{n-m}$. Both Kummer sequences are short exact by [lem-sc-kummer-exact], since
$ell$ is invertible in $k$. There is a morphism from the level-$n$ sequence to the level-$m$
sequence whose three nonzero vertical maps, in order, are
$$mu_{ell^n}xrightarrow{zmapsto z^d}mu_{ell^m},qquad mathbf G_mxrightarrow{umapsto u^d}mathbf
G_m,qquad mathbf G_mxrightarrow{mathrm{id}}mathbf G_m.$$
The first square commutes by inclusion, and the second because $(u^d)^{ell^m}=u^{ell^n}$.
Connecting-map naturality of [lem-weil-pbc-right-derived-universal-delta-functor], as applied in
Step 2, gives
$$s_{n,m}delta_{C,n}(L)=delta_{C,m}(L)$$
for every $Linoperatorname{Pic}(C)$, using the Kummer/Picard boundary of [lem-sc-second-kummer-
divisors]. In particular there is no extra factor $d$ on the line-bundle input: that input
belongs to the final, identity-mapped copy of $mathbf G_m$.
4. Let $rho:A_nto A_m$ be reduction. On a point generator from Step 1, Step 3 and the given
degree normalization give
$$operatorname{tr}_{C,m}(s_{n,m}delta_{C,n}(mathcal
O_C(P)))=1=rho(operatorname{tr}_{C,n}(delta_{C,n}(mathcal O_C(P)))).$$
Both sides are additive, so generation proves $operatorname{tr}_{C,m}circ
s_{n,m}=rhocircoperatorname{tr}_{C,n}$ on all of $H^2(C,mu_{ell^n})$.
5. The evaluation square for $A_n,mu_{ell^n},mu_{ell^n}$ and $A_m,mu_{ell^m},mu_{ell^m}$
commutes. Indeed for an integer representative $a$ and $z^{ell^n}=1$,
$(z^a)^d=(z^d)^a=(z^d)^{abmodell^m}$, since $z^d$ has order dividing $ell^m$. Apply [lem-wf-
etale-cup-functoriality] with $f=mathrm{id}_C$, coefficient maps $(rho,s_{n,m},s_{n,m})$ and
these evaluations. For $p=i$, $q=2-i$ this gives
$$s_{n,m}(xsmile y)=r_{n,m}xsmile s_{n,m}y.$$
All these sheaves are abelian sheaves, and evaluation is the indicated bilinear pairing over
$mathbf Z$.
6. For the scheme isomorphism $f:Dto C$, pullback of units gives $c_f:f^{-1}mathbf
G_{m,C}tomathbf G_{m,D}$, restricting to the canonical map on $mu_{ell^n}$. These maps give a
morphism from the inverse image of the Kummer sequence on $C$ to the Kummer sequence on $D$:
inclusion commutes, and $c_f(u^{ell^n})=c_f(u)^{ell^n}$. The sequences are short exact by [lem-
sc-kummer-exact]. Apply [lem-weil-pbc-pullback-cohomology-long-exact-ladder] first to the
inverse-image sequence and then coefficient naturality of [lem-weil-pbc-right-derived-universal-
delta-functor] to this comparison morphism. The result is $f^*delta_{C,n}(L)=delta_{D,n}(f^*L)$,
where [lem-sc-h1-gm-pic-pullback] identifies the induced map on $H^1(mathbf G_m)$ with pullback
of invertible modules. These statements apply to arbitrary scheme morphisms between the curves;
no $k$-linearity of $f$ is required.
7. If $P$ is a closed point of $C$, the isomorphism $f$ has a unique closed inverse image $Q$.
Its isomorphism of local rings preserves normalized valuations: for a nonzero regular element
$h$ and $jgeq0$, the condition $v_P(h)geq j$ is membership in the $j$th power of the maximal
ideal. The local-ring isomorphism preserves these powers, hence valuations on regular elements
and then on rational functions by taking quotients. Applying the valuation-bounded description
of $mathcal O(E)$ in [def-sc-divisor] on corresponding opens therefore gives $f^*mathcal
O_C(P)congmathcal O_D(Q)$. Step 6 sends the Kummer point class at $P$ to the Kummer point class
at $Q$. Both have trace $1$ by hypothesis. Additivity and the generation proved in Step 1 give
$operatorname{tr}_{D,n}circ f^*=operatorname{tr}_{C,n}$. This argument uses the scheme
isomorphism and point classes, so it also covers a nontrivial automorphism of the base field.
8. The canonical pullback identifications of the constant sheaf and roots-of-unity sheaf
preserve evaluation: pullback of units respects $zmapsto z^a$ for every integer $a$, and
pullback of a constant integer residue class is that same residue class. Apply [lem-wf-etale-
cup-functoriality] with the three canonical coefficient maps along $f$. It gives
$$f^*(xsmile y)=f^*xsmile f^*y.$$
The lemma is about small etale sites and arbitrary scheme morphisms; the coefficient square just
checked therefore also applies to this semilinear scheme isomorphism.
9. For $i=0,1,2$, the degrees $i$ and $2-i$ are nonnegative. Apply $operatorname{tr}_{C,m}$ to
the cup equality of Step 5 and use Step 4 to obtain
$P^i_{C,m}(r_{n,m}x,s_{n,m}y)=rho(P^i_{C,n}(x,y))$. Apply $operatorname{tr}_{D,n}$ to Step 8 and
use Step 7 to obtain $P^i_{D,n}(f^*x,f^*y)=P^i_{C,n}(x,y)$. These are the two asserted
equalities.
-/
theorem curve_trace_cup_naturality
    (k : Type u) [Field k] [IsAlgClosed k]
    (C D : Scheme.{u})
    (fC : C ⟶ Spec (.of k)) [IsConnectedCurve fC] [Smooth fC] [IsProper fC]
    (fD : D ⟶ Spec (.of k)) [IsConnectedCurve fD] [Smooth fD] [IsProper fD]
    (ell c : ℕ) [Fact ell.Prime] [CharP k c] (hell : ell ≠ c)
    (trC : ∀ n : ℕ, Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 2 →+ ZMod (ell ^ n))
    (trD : ∀ n : ℕ, Sheaf.H (D.rootsOfUnitySheaf (ell ^ n)) 2 →+ ZMod (ell ^ n))
    (htrC : ∀ n : ℕ, 1 ≤ n → ∀ (hn : IsUnit ((ell ^ n : ℕ) : Γ(C, ⊤))) (P : closedPoints C),
      trC n (curvePointKummerClass k C fC (ell ^ n) hn P) = 1)
    (htrD : ∀ n : ℕ, 1 ≤ n → ∀ (hn : IsUnit ((ell ^ n : ℕ) : Γ(D, ⊤))) (P : closedPoints D),
      trD n (curvePointKummerClass k D fD (ell ^ n) hn P) = 1)
    (cupC : ∀ n i j : ℕ, Sheaf.H (C.constantZMod (ell ^ n)) i →
      Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) j →
        Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) (i + j))
    (cupD : ∀ n i j : ℕ, Sheaf.H (D.constantZMod (ell ^ n)) i →
      Sheaf.H (D.rootsOfUnitySheaf (ell ^ n)) j →
        Sheaf.H (D.rootsOfUnitySheaf (ell ^ n)) (i + j))
    (hcupC : ∀ n : ℕ, 1 ≤ n →
      IsFiniteEtaleCup C (ell ^ n) (C.rootsOfUnitySheaf (ell ^ n)) (cupC n))
    (hcupD : ∀ n : ℕ, 1 ≤ n →
      IsFiniteEtaleCup D (ell ^ n) (D.rootsOfUnitySheaf (ell ^ n)) (cupD n))
    (σ : k ≃+* k) (f : D ⟶ C) [IsIso f]
    (hσ : f ≫ fC = fD ≫ Spec.map (CommRingCat.ofHom σ)) :
    (∀ n m : ℕ, 1 ≤ m → (hmn : m ≤ n) → ∀ i j : ℕ, (hij : i + j = 2) →
      ∀ (x : Sheaf.H (C.constantZMod (ell ^ n)) i)
        (y : Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) j),
      curveTraceCup C (ell ^ m) (trC m) (cupC m) i j hij
        (Sheaf.H.map (curveConstantReduction C ell n m hmn) i x)
        (Sheaf.H.map (curveRootsReduction C ell n m hmn) j y) =
      ZMod.castHom (pow_dvd_pow ell hmn) (ZMod (ell ^ m))
        (curveTraceCup C (ell ^ n) (trC n) (cupC n) i j hij x y)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ i j : ℕ, (hij : i + j = 2) →
      ∀ (x : Sheaf.H (C.constantZMod (ell ^ n)) i)
        (y : Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) j),
      curveTraceCup D (ell ^ n) (trD n) (cupD n) i j hij
        (Sheaf.H.map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ell ^ n))))) i
          (Etale.cohomologyMap f (C.constantZMod (ell ^ n)) i x))
        (Sheaf.H.map (curveRootsPullback f (ell ^ n)) j
          (Etale.cohomologyMap f (C.rootsOfUnitySheaf (ell ^ n)) j y)) =
      curveTraceCup C (ell ^ n) (trC n) (cupC n) i j hij x y) := by
  sorry

end AlgebraicGeometry
end
