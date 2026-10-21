/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
import Sheaf.Paper.CoefficientTowerSectionCoordinates
import Sheaf.Paper.CoefficientTowerGeometricComposition
import Sheaf.Paper.CoefficientTowerTransitionCompatibility
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.Compactification.Over

/-! # Compact support on strict varying-coefficient towers

The existing interfaces are reexported unchanged; the proof assembles section
coordinates, geometric composition and actual coefficient-transition compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finite_direct_ring_map {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y (SpTowerShriek.R l E n))
      (proEtaleConstantRing X (SpTowerShriek.R l E n))
      (proEtaleConstantRingComparison f (SpTowerShriek.R l E n)) =
    proEtaleCoefficientDirectImageMap.{u} f (SpTowerShriek.R l E n) := by
  exact proEtaleConstantModulePullback_ring_direct f (SpTowerShriek.R l E n)

private def finite_direct_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f ≅
      proEtaleConstantModuleDirectImage f (SpTowerShriek.R l E n) :=
  SheafOfModules.pushforwardCongr (congrArg
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
    (finite_direct_ring_map l E f n))

/-- The identity on direct-image sections gives the finite coordinates.
Source: Stacks 03D2, the inverse-image/direct-image Hom bijection.
The coefficient map is the adjunct of the specified inverse-image map, so the
pushforward congruence fixes every underlying section.
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
theorem finite_coordinates_exists : Nonempty (FiniteCoordinates l E) := by
  exact ⟨{ direct := fun f n ↦ finite_direct_iso l E f n
           sections := fun _ _ _ _ _ ↦ HEq.rfl }⟩


private theorem reduction_naturality_aux (b : SpTowerShriek.Base l E)
    (q : Coordinates l E b) (T : Scheme.{u}) {m n : ℕ} (a : m ≤ n)
    {K L : spDerivedCoefficientTowers l E T (q.abelian T)} (f : K ⟶ L) :
    (scalarExtensionFunctor (quotient l E a) T).map
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).map f) ≫
      reduction l E T (q.abelian T) a (q.scalar T a) L =
    reduction l E T (q.abelian T) a (q.scalar T a) K ≫
      (spDerivedCoefficientEvaluation l E T (q.abelian T) m).map f := by
  let t : spDerivedCoefficientEvaluation l E T (q.abelian T) n ⋙
      scalarExtensionFunctor (quotient l E a) T ⟶
        spDerivedCoefficientEvaluation l E T (q.abelian T) m :=
    Functor.whiskerLeft _ (q.scalar T a).scalar.inv ≫ (q.abelian T).reduction a
  exact t.naturality f

private theorem reduction_identity_aux (b : SpTowerShriek.Base l E)
    (q : Coordinates l E b) (T : Scheme.{u}) (n : ℕ)
    (K : spDerivedCoefficientTowers l E T (q.abelian T)) :
    reduction l E T (q.abelian T) (Nat.le_refl n) (q.scalar T (Nat.le_refl n)) K =
      (scalarUnit l E b q T n).hom.app
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K) := by
  dsimp only [reduction]
  rw [(q.abelian T).reduction_identity]
  rfl

private theorem reduction_composition_aux (b : SpTowerShriek.Base l E)
    (q : Coordinates l E b) (T : Scheme.{u}) {r m n : ℕ} (a : r ≤ m) (c : m ≤ n)
    (K : spDerivedCoefficientTowers l E T (q.abelian T)) :
    (scalarExtensionFunctor (quotient l E a) T).map
        (reduction l E T (q.abelian T) c (q.scalar T c) K) ≫
      reduction l E T (q.abelian T) a (q.scalar T a) K =
    (scalarAssoc l E b q T a c).hom.app
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K) ≫
      reduction l E T (q.abelian T) (a.trans c) (q.scalar T (a.trans c)) K := by
  dsimp only [reduction, scalarAssoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [(q.scalar T a).scalar.inv.naturality_assoc]
  erw [(q.abelian T).reduction_comp]
  simp only [Iso.hom_inv_id_app_assoc]
  unfold spDerivedCoefficientEvaluation
  rfl


private theorem ell_torsion (n : ℕ) :
    ∃ a : ℕ, ∀ x : SpTowerShriek.R l E n, (l ^ a) • x = 0 := by
  refine ⟨n + 1, fun x ↦ ?_⟩
  have h : ((l ^ (n + 1) : ℕ) : SpTowerShriek.R l E n) = 0 := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (I := spEllIdeal l E)
        (Ideal.subset_span (Set.mem_singleton (l : Padic.coefficientExtensionIntegers l E)))
        (n + 1)))
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
  rw [nsmul_eq_mul, h, zero_mul]
private theorem reduction_comparison_isIso_aux
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (_o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) :
∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : C l E b q X) {m n : ℕ} (v : m ≤ n),
    IsIso ((reductionDirectImageComparison (quotient l E v) c.i c.g).app
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj)) := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c K m n v
  have hK := K.property.1 n
  obtain ⟨a, d, _, hv⟩ := hK.1
  have hb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n))) i).obj
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj))} := by
    apply (Set.finite_Icc a d).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
  exact (reductionDirectImage_isIso l pchar hp hne k f c.i c.g c.comm.symm
    (ell_torsion l E n) (ell_torsion l E m) (quotient l E v)
    ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj)
    hb hK.2.1 hK.2.2).1

/-- Compact support composition, etale sum adjunction and actual semilinear reduction.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus).

Proof:
1. Use the actual strict semilinear section model of [lem-coef-semilinear-derived-sections] with
  ring system $A_{n,T}$: its ordinary homotopy category is $D(\operatorname{Tow}(T,\mathcal
  O_E))$, and it supplies inverse image, separately derived direct image, open extension, their
  units/counits, and the comparisons built from them. It does not identify a derived morphism with
  an arbitrary family of its evaluations. Every level of an object of $\mathcal C_T$ has bounded
  constructible etale origin by [lem-weil-pbc-finite-ring-constructible-derived-origin]. These
  representatives have the same Tor intervals by [det-pe-finite-tor-comparison-noetherian]: the
  schemes are qcqs and $A_n$ is finite, hence discrete Noetherian. Consequently the finite
  comparisons in [lem-sp-et-proet-coefficient-compatibility] apply over the arbitrary field $k$ in
  the statement; no global finite-field datum is needed. We will use [det-sp-tower-shriek-levels]
  to identify evaluations and detect invertibility only after constructing maps in the section
  model.

2. Construct proper/open comparisons before evaluation. For a commutative square $pk=ir$ with
  $p,r$ proper and $i,k$ open, put $W'=W\times_T S$ and $s=(k,r):V\to W'$. The geometric clause of
  [lem-cbc-strict-tower-proper-open-calculus] makes $s$ clopen. The sheafified presheaf of
  [def-weil-extension-by-zero-presheaf] gives the open base-change map $\beta:p^*i_!\simeq
  b_!q^*$. Exactness is [lem-pur-site-restriction-module-adjunction-exact]. The termwise clopen
  projection defines $\alpha_Q$ and its proper-adjunction mate $\gamma_Q$. Apply
  [lem-sp-varying-ring-proper-open-pasting]: the projection is ring-linear and commutes with
  semilinear transitions, so the maps are actual tower transformations; the section model of
  [lem-coef-semilinear-derived-sections] realizes them simultaneously, and its horizontal and
  vertical identities hold before evaluation by [lem-weil-pbc-mate-pasting]. Evaluation is the
  finite normalized mate from [lem-cbc-proper-open-interchange-coherence], hence is invertible on
  the constructible finite-ring origins supplied in step 1 by
  [lem-sp-et-proet-coefficient-compatibility] and detected by [det-sp-tower-shriek-levels].

3. For $T\xrightarrow hB\xrightarrow gC$, choose a compatible compactification tower using
  [lem-cbc-compactifiable-compatible-tower]. Write $i:B\hookrightarrow\overline B$, $q:\overline
  B\to C$, $a:T\hookrightarrow\overline T$, $p:\overline T\to\overline B$, and $U=\overline
  T\times_{\overline B}B$, with $a=bj$ and $r:U\to B$ proper. The comparison applies the
  proper/open mate from step 2, followed by the inverse of the canonical direct-image compositor
  [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] and the open compositor
  [def-weil-extension-by-zero-presheaf]. The direct-image compositors are conjugates of the
  coherent inverse-image compositors, so [lem-weil-pbc-mate-pasting] supplies their identity and
  associativity laws. Its independence from the chosen tower and its equality for common
  refinements are exactly [lem-sp-compactification-refinement-coherence], using
  [lem-cbc-compactifiable-cofiltered]; the latter also equalizes parallel refinement arrows. Thus
  $\alpha_{g,h}$ is well-defined. Applying the same lemma to a three-map staircase gives
  associativity, while identity towers give identities. Evaluation is the finite construction of
  [lem-amb-etale-compact-comparisons] with the site normalization
  [lem-sp-et-proet-coefficient-compatibility] and is invertible by [det-sp-tower-shriek-levels].
  If $u:U\hookrightarrow T$ is open, use $(ju,p)$; [lem-cbc-extension-zero-composition] gives
  $F_{hu}=F_hu_!$ and the canonical open counits. The preservation assumption in the statement
  applies to each proper or open map used here, so these operations restrict to the chosen
  categories.

4. For etale $e:U\to T$, [lem-weil-proetale-weakly-etale-localization] identifies
  $U_{\mathrm{proet}}$ with $T_{\mathrm{proet}}/U$. At each $n$ define $e_!M_n$ by sheafifying
$$V\longmapsto\bigoplus_{t:V\to U\,/T}M_n(V,t),$$
with transition maps induced on each summand by those of $M$. The scalar action factors through
  $A_n$, so this is an actual functor on varying-coefficient towers.
  [lem-pur-site-restriction-module-adjunction-exact] makes $e_!$ and $e^*$ exact; exactness on
  towers follows from [det-sp-coefficient-towers-abelian]. The unit places a section in the
  summand of its structural lift; the counit sums the evaluations of all lifts. Both commute with
  the quotient transitions summand by summand. The adjunction bijection is a bijection on
  compatible families because these unit/counit formulas are natural in the level maps. Apply
  [lem-weil-pbc-termwise-adjunction-homotopy] on complexes and then
  [lem-weil-pbc-localization-universal-property]: exactness lets both functors descend, and the
  two triangle identities descend with them. This proves $e_{!,\bullet}\dashv e_\bullet^*$ on the
  ordinary unbounded derived categories themselves, not by levelwise conservativity. For an open
  immersion there is at most one lift, giving extension by zero.

5. Identify the exact sum-extension functor with the compactification candidate by constructing
  the comparison. For a pro-etale test object $V\to T$, each lift $t:V\to U$ has a graph in
  $\overline U\times_TV$, closed because $p$ is separated and open because the etale diagonal is
  open. [lem-sp-varying-ring-graph-summand] constructs the graph section extended by zero, proves
  its $A_n$-linearity and transition compatibility, and assembles the natural tower map
  $\theta:e_{!,\bullet}\to F_e$. The localized-site morphism
  [lem-weil-pbc-localize-ringed-site-morphism] identifies the right adjoints of the etale and
  pro-etale sum-extension functors, so the site comparison is an isomorphism and preserves units
  and counits. On each finite etale-origin level, [lem-pur-etale-support-map-compatibility]
  identifies $\theta_n$ with the inverse finite normalization;
  [lem-sp-et-proet-coefficient-compatibility] gives the coefficient comparison. Hence $\theta$ is
  invertible by [det-sp-tower-shriek-levels]. The finite counit is the fibre sum by
  [lem-amb-etale-sum-stalks], and the open case is the unique-lift inclusion. Its coefficient
  compatibility follows from the graph construction and the last sum-extension identity of
  [lem-sp-et-proet-coefficient-compatibility].

6. Exactness of $e_!$ and $e^*$ gives $H^q(e_!M_n)=e_!H^q(M_n)$ and $H^q(e^*N_n)=e^*H^q(N_n)$, so
  each cohomological interval is preserved without shifting, uniformly in $n$. For every
  degree-zero module sheaf $N$ on $T$, [lem-weil-pbc-ringed-slice-extension-tensor] gives
  $e_!P\otimes N\cong e_!(P\otimes e^*N)$. It also shows that $e_!$ preserves flat sheaves: tensor
  an injection with a flat sheaf on $U$, then apply exact $e_!$. Thus applying this identity to
  K-flat resolutions gives
$$(e_!M_n)\otimes^LN\simeq e_!(M_n\otimes^Le^*N).$$
This preserves every Tor interval. For an arbitrary module sheaf $Q$ on $U$ the structural summand
  makes $Q$ a direct summand of $e^*e_!Q$: the complementary lifts are the complement of the
  clopen diagonal of separated $e$. For $L_n$ on $T$ with Tor interval $[a,b]$, $e^*L_n\otimes^LQ$
  is a direct summand of
$$e^*(L_n\otimes^Le_!Q),$$
using derived tensor/pullback [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The latter has
  the required interval by the Tor bound on $L_n$ and exactness of $e^*$, which proves it for $Q$.
  Constructibility for $e^*$ follows by pulling back the finite partition and the local constant
  finite presentations. Constructibility for $e_!$ on $\mathcal C_U$ follows from step 5 and the
  assumed preservation by $F_e$. The ambient adjunction therefore restricts to $\mathcal
  C_U,\mathcal C_T$ with precisely the same units and counits.

7. Write the transition in restriction-of-scalars form as
  $t^C_{n,m}:C_n\to\operatorname{Res}_{n,m}C_m$. The semilinear section model
  [lem-coef-semilinear-derived-sections] and the restriction comparison
  [lem-sf-compact-support-restriction-of-scalars] give the actual transition $F_{h,n}(t^C_{n,m})$
  followed by $d_h$. Apply [lem-sp-restriction-transition-transpose] to its scalar-adjunction
  transpose: it is precisely $F_{h,m}(r^C_{n,m})\circ b_h(C_n)$, with no flatness assumption. For
  $n\ge m\ge r$, the same node gives the composite law by naturality and the
  coefficient-composition equation in [det-sp-reduction-direct-image], together with
  $r^C_{m,r}(r^C_{n,m}\otimes^LA_r)=r^C_{n,r}$ from [det-sp-coefficient-towers-abelian].
  Naturality in $C$ follows from naturality of these transformations, and $m=n$ gives identities.

The operations are those of the recorded shriek-level theorem: the same `b`, `o` and open
exchange `x` satisfy its `Laws`, so this calculus, the projection and exchange isomorphisms
and conservativity of [det-sp-tower-shriek-levels] all concern one functor F_h.
-/
theorem coefficient_tower_shriek_calculus
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar] :
    ∃ b : SpTowerShriek.Base l E, ∃ o : SpTowerShriek.Operations l E b,
    ∃ x : SpTowerShriek.OpenExchange l E b o, SpTowerShriek.Laws l E b o x ∧
    ∃ q : Coordinates l E b, ∃ z : FiniteCoordinates l E,
    ∀ h : Preservation l E k b o q, Nonempty (Calculus l E k b o q z h) := by
  obtain ⟨b, o, x, laws⟩ := SpTowerShriek.tower_shriek_levels l E
  obtain ⟨q⟩ := coordinates_realization l E b
  obtain ⟨z⟩ := finite_coordinates_exists l E
  obtain ⟨fd, ops, hc⟩ := geometric_calculus l E pchar hp hne k b o x laws q z
  refine ⟨b, o, x, laws, q, z, fun h ↦ ?_⟩
  obtain ⟨et, ⟨coh⟩, hn⟩ := hc h
  exact ⟨{ finite := fd
           composition := ops
           coherence := coh
           etale := et
           reduction :=
             { reduction_formula :=
                 reduction_transition_compatibility l E pchar hp hne k b o q z fd
               reduction_comparison_isIso :=
                 reduction_comparison_isIso_aux l E pchar hp hne k b o q
               reduction_identity := reduction_identity_aux l E b q
               reduction_composition := reduction_composition_aux l E b q
               reduction_naturality := reduction_naturality_aux l E b q }
           open_normalization := hn }⟩

end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
