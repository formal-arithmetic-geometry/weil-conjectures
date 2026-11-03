/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage

/-! # Finite-level exceptional data for the smooth purity tower

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, *Levels*: the finite exceptional adjunctions
$f^!_{\mathcal O_E/\ell^n}$ and the coefficient comparisons $c_{n,m}$ of
[det-sp-reduction-exceptional] (blueprint: lem-route-tower-finite-level-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

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

/-- The compact-support coefficient comparison is invertible on every finite ctf object.
Source: [det-sp-reduction-direct-image] (blueprint: lem-route-tower-finite-level-data). -/
private theorem direct_isIso
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))] [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    {m n : ℕ} (h : m ≤ n) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)) :
    IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      M.obj) := by
  obtain ⟨⟨a, d, _, hv⟩, hc, ht⟩ := M.property
  have hb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n))) i).obj
        M.obj)} := by
    apply (Set.finite_Icc a d).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
  exact (reductionDirectImage_isIso l pchar hp hne k f c.i c.g c.comm.symm
    (ell_torsion l E n) (ell_torsion l E m) (SpTowerCalculus.quotient l E h)
    M.obj hb hc ht).1

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The finite fields of `Levels`, with the tower comparisons and coherence removed.
The statement is strictly lower than `Levels`: it only records finite compact-support
preservation, finite exceptional adjunctions, their realizations, and scalar mates.
Source: blueprint det-sp-tower-gluing, *Levels* (blueprint: lem-route-tower-finite-level-data).
-/
structure FiniteLevelData {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)) where
  finite_closed : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
      ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj)
  right : ∀ n : ℕ, spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
    spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)
  adjunction : ∀ n : ℕ,
    reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (finite_closed n) ⊣ right n
  realization : ∀ n : ℕ,
    ReductionExceptionalRealization (SpTowerShriek.R l E n) c.i c.g
      (finite_closed n) (right n) (adjunction n)
  scalarX : ∀ (m n : ℕ) (h : m ≤ n)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor X (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj)
  scalarY : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj)
  direct_image_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
      ((right n).obj K).obj)
  coefficient_iso : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso (coefficientMate l E b c m n h (finite_closed n) (finite_closed m)
      (scalarX m n h) (scalarY m n h) (right n) (right m)
      (adjunction n) (adjunction m) K (direct_image_iso m n h K))

/-- Finite exceptional data for an arbitrary compactification over the base field.
Source: [det-sp-reduction-exceptional] and its chart and conservativity steps
(blueprint: lem-route-tower-finite-level-data). -/
private theorem finiteLevelData_of_compactification
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))] [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj)) :
    Nonempty (FiniteLevelData l E b o q c hF) := by
  classical
  have hclosed (n : ℕ) : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
        ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj) := by
    obtain ⟨hFA, -⟩ := reductionExceptional_isIso l pchar hp hne k f d c.i c.g c.comm.symm
      (ell_torsion l E n) (ell_torsion l E n) (RingHom.id _)
    exact hFA
  have hscalar (m n : ℕ) (h : m ≤ n) :
      (∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
        spFiniteConstructibleTor X (SpTowerShriek.R l E m)
          ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj M.obj)) ∧
      (∀ K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n),
        spFiniteConstructibleTor Y (SpTowerShriek.R l E m)
          ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj K.obj)) := by
    obtain ⟨-, -, hSX, hSY, -⟩ := reductionExceptional_isIso l pchar hp hne k f d c.i c.g
      c.comm.symm (ell_torsion l E n) (ell_torsion l E m) (SpTowerCalculus.quotient l E h)
    exact ⟨hSX, hSY⟩
  choose G adj hR using fun n : ℕ ↦ reductionExceptionalRealization_exists l pchar hp hne k
    f c.i c.g c.comm.symm (SpTowerShriek.R l E n) (ell_torsion l E n) (hclosed n)
  have hcoeff (m n : ℕ) (h : m ≤ n)
      (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
      IsIso (coefficientMate l E b c m n h (hclosed n) (hclosed m)
        (hscalar m n h).1 (hscalar m n h).2 (G n) (G m) (adj n) (adj m) K
        (direct_isIso l E pchar hp hne k f c h ((G n).obj K))) := by
    let φ := SpTowerCalculus.quotient l E h
    let SX := reductionCtfScalar φ X (hscalar m n h).1
    let SY := reductionCtfScalar φ Y (hscalar m n h).2
    let beta : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (hclosed n) ⋙ SY ≅
        SX ⋙ reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g (hclosed m) :=
      NatIso.ofComponents
        (fun M ↦ by
          have := direct_isIso l E pchar hp hne k f c h M
          exact (spFiniteConstructibleTor Y (SpTowerShriek.R l E m)).fullyFaithfulι.preimageIso
            (asIso ((reductionDirectImageComparison φ c.i c.g).app M.obj)))
        (by
          intro M N g
          apply ObjectProperty.hom_ext
          exact (reductionDirectImageComparison φ c.i c.g).naturality g.hom)
    let cc := (mateEquiv (adj n) (adj m)
      (TwoSquare.mk SX (reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (hclosed n))
        (reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g (hclosed m)) SY
        beta.inv)).natTrans
    have hcc (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :=
      mateEquiv_counit (adj n) (adj m)
        (TwoSquare.mk SX (reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (hclosed n))
          (reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g (hclosed m)) SY
          beta.inv) K
    have hc' (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
        (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map (cc.app K).hom ≫
            ((adj m).counit.app (SY.obj K)).hom =
          @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app ((G n).obj K).obj)
              (direct_isIso l E pchar hp hne k f c h ((G n).obj K)) ≫
            (scalarExtensionFunctor φ Y).map ((adj n).counit.app K).hom :=
      congrArg (fun v ↦ v.hom) (hcc K)
    have hchart := reductionExceptional_chartEquation l pchar hp hne k f d c.i c.g c.comm.symm
      (ell_torsion l E n) (ell_torsion l E m) φ (hclosed n) (hclosed m)
      (hscalar m n h).1 (hscalar m n h).2 (G n) (G m) (adj n) (adj m)
      (hR n).some (hR m).some cc
      (fun K ↦ direct_isIso l E pchar hp hne k f c h ((G n).obj K)) hc'
    have hiso := reductionExceptional_components_isIso l pchar hp hne k f d c.i c.g
      c.comm.symm (ell_torsion l E n) (ell_torsion l E m) φ (hclosed n) (hclosed m)
      (hscalar m n h).1 (hscalar m n h).2 (G n) (G m) (adj n) (adj m)
      (hR n).some (hR m).some cc hchart K
    have he : coefficientMate l E b c m n h (hclosed n) (hclosed m)
        (hscalar m n h).1 (hscalar m n h).2 (G n) (G m) (adj n) (adj m) K
        (direct_isIso l E pchar hp hne k f c h ((G n).obj K)) = cc.app K := by
      apply ((adj m).homEquiv _ _).symm.injective
      rw [coefficientMate, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      apply ObjectProperty.hom_ext
      exact (hc' K).symm
    rw [he]
    exact hiso
  exact ⟨{
    finite_closed := hclosed
    right := G
    adjunction := adj
    realization := fun n ↦ (hR n).some
    scalarX := fun m n h ↦ (hscalar m n h).1
    scalarY := fun m n h ↦ (hscalar m n h).2
    direct_image_iso := fun m n h K ↦ direct_isIso l E pchar hp hne k f c h ((G n).obj K)
    coefficient_iso := hcoeff }⟩

/-- Finite exceptional data exists under the hypotheses of the chart-level theorem.
Source: blueprint det-sp-tower-gluing, *Levels*; [det-sp-reduction-exceptional],
[det-sp-reduction-direct-image] (blueprint: lem-route-tower-finite-level-data).

Proof:
1. Make `X.left`, `Y.left`, `f.left` schemes over `Spec k` from the `Over` structure. The fixed
compactification $X\xrightarrow{i}Z\xrightarrow{g}Y$ is over `Spec k` through $g$; $Z$ is of
finite type, quasi-compact and separated over $k$ because $g$ is proper and $Y$ is.
2. For every level $n$ the ring $A_n=\mathcal O_E/\ell^{n+1}$ is finite and killed by
$\ell^{n+1}$. [det-sp-reduction-exceptional] (with the identity map) gives that the compact
support $Rf_{!,A_n}=Rg_*i_!$ preserves finite ctf objects, and (with the quotient map
$A_n\to A_m$) that scalar extension preserves them on $X$ and $Y$.
3. [lem-sp-reduction-exceptional-realization] gives at every level a right adjoint, its
adjunction and its realization; choose one for every $n$.
4. For $m\le n$, [det-sp-reduction-direct-image] makes the compact-support coefficient
comparison $b$ invertible on every finite ctf object, in particular on the values of the chosen
right adjoint. With $b$ as a natural isomorphism of the restricted functors, the mate $c$ of
$b^{-1}$ under the two chosen adjunctions has the counit equation
$\varepsilon_{m}\circ F_m(c_K)=b^{-1}\circ S_Y(\varepsilon_{n,K})$.
[lem-sp-reduction-exceptional-chart] turns this equation into the chart equation and
[lem-sp-reduction-exceptional-components-isIso] makes every $c_K$ invertible.
5. `coefficientMate` is by definition the $F_m\dashv G_m$ transpose of the same composite
$b^{-1}\circ S_Y(\varepsilon_{n,K})$; transposition is injective, so it equals $c_K$ and is
invertible. Bundle the data. -/
theorem finiteLevelData_exists
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj))
    : Nonempty (FiniteLevelData l E b o q
      (CondensedRing.compactificationOverField f) hF) := by
  classical
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  generalize CondensedRing.compactificationOverField f = c at hF ⊢
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ (Y.left ↘ Spec (.of k))⟩
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y.left ↘ Spec (.of k))))
  let : QuasiCompact (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (Y.left ↘ Spec (.of k))))
  let : IsSeparated (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (c.g ≫ (Y.left ↘ Spec (.of k))))
  let : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : c.i.IsOver (Spec (.of k)) := (Scheme.Hom.isOver_iff (Spec (.of k))).mpr (by
    change c.i ≫ c.g ≫ (Y.left ↘ Spec (.of k)) = X.left ↘ Spec (.of k)
    rw [← Category.assoc, ← c.comm]
    exact f.w)
  exact finiteLevelData_of_compactification l E b o q pchar (Fact.out : pchar.Prime).pos hne k
    f.left d c hF

end AlgebraicGeometry.ProEtale.SpTowerGluing
