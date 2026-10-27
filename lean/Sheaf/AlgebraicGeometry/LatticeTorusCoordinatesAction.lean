/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.GroupTheory.Finiteness
import Sheaf.AlgebraicGeometry.CanonicalTorusCoactionUnit
import Sheaf.AlgebraicGeometry.CanonicalTorusCoactionAssociativity
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Lattice torus coordinates, actions and Laurent base change

Source: ILO, Travaux de Gabber, Exposé VIII, Proposition 3.2.2, 3.2.4--3.2.5,
printed p.103, and the Laurent-chart input to Lemma 3.2.12(i), printed p.104
(blueprint: lem-trf-lattice-torus-coordinates-action).

Lattices are written multiplicatively to use the recorded monoscheme interface.
A basis is encoded by its coordinate equivalence `b`; `b.symm` sends the standard
integer vectors to the chosen basis. The Laurent algebra is the monoid algebra on
integer vectors, namely finite sums of Laurent monomials. No rank is required positive.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Basis coordinates identify the canonical Hopf group scheme with the coordinate torus.
The coordinate Hopf structure sends each Laurent monomial to its tensor square, to one,
and to its inverse, so its operations on tuples of units are coordinatewise.

Source: ILO VIII 3.2.4, p.103 (blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Steps 1--3 of the node. Send a basis monomial to its coordinate monomial and
use the inverse coordinate equivalence to construct the inverse algebra map. Products
are preserved because coordinates add. On monomials, comultiplication, counit and
antipode are respectively the tensor square, one, and negation of the exponent.
Consequently both maps preserve all three Hopf operations. Contravariance of Spec
and the affine tensor-product formula give the indicated group-scheme isomorphism
(`def-weil-affine-spectrum`, `def-sc-group-scheme`,
`lem-weil-pbc-fibre-product-affine-spectra`). -/
theorem latticeTorus_coordinates (k : Type u) [Field k] (L : Type u) [CommGroup L]
    (r : ℕ) (b : L ≃* Multiplicative (Fin r → ℤ)) :
    ∃ e : MonoidAlgebra k L ≃ₐ[k] MonoidAlgebra k (Multiplicative (Fin r → ℤ)),
      (∀ l : L, e (MonoidAlgebra.single l 1) = MonoidAlgebra.single (b l) 1) ∧
      (∀ n : Multiplicative (Fin r → ℤ),
        e.symm (MonoidAlgebra.single n 1) = MonoidAlgebra.single (b.symm n) 1) ∧
      (∀ x : MonoidAlgebra k L,
        (Algebra.TensorProduct.map e.toAlgHom e.toAlgHom) (Coalgebra.comul x) =
          Coalgebra.comul (e x)) ∧
      (∀ x : MonoidAlgebra k L, Coalgebra.counit (e x) = (Coalgebra.counit x : k)) ∧
      (∀ x : MonoidAlgebra k L,
        e (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (e x)) ∧
      ∃ i : Grp.mk ((Spec (.of (MonoidAlgebra k L))).asOver (Spec (.of k))) ≅
          Grp.mk ((Spec (.of (MonoidAlgebra k (Multiplicative (Fin r → ℤ))))).asOver
            (Spec (.of k))),
        i.hom.hom.hom.left = Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  let e := MonoidAlgebra.domCongr k k b
  let d := MonoidAlgebra.domCongrBialgEquiv k k b
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    exact MonoidAlgebra.domCongr_single b l 1
  · intro n
    exact MonoidAlgebra.domCongr_single b.symm n 1
  · intro x
    exact DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom d.toBialgHom) x
  · intro x
    exact MonoidAlgebra.counit_domCongr b x
  · intro x
    induction x using MonoidAlgebra.induction_linear <;> simp_all [e]
  · refine ⟨(hopfSpec (.of k)).mapIso (CommHopfAlgCat.isoMk d.symm).op, ?_⟩
    rfl

private theorem componentChart_fac (k : Type u) [Field k] {M : Monoscheme.Fine.{u}}
    (C : Monoscheme.ToricComponent M) (U : Monoscheme.ComponentAffineOpens C) :
    Monoscheme.componentChart k C U ≫ Monoscheme.componentι k C =
      Monoscheme.realizationι k M U.1 := by
  exact IsOpenImmersion.lift_fac _ _ _

private theorem componentChart_open (k : Type u) [Field k] {M : Monoscheme.Fine.{u}}
    (C : Monoscheme.ToricComponent M) (U : Monoscheme.ComponentAffineOpens C) :
    IsOpenImmersion (Monoscheme.componentChart k C U) := by
  have : IsOpenImmersion (Monoscheme.componentChart k C U ≫ Monoscheme.componentι k C) := by
    rw [componentChart_fac]
    infer_instance
  have : IsOpenImmersion (Monoscheme.componentι k C) := by
    change IsOpenImmersion (Monoscheme.componentOpen k C).ι
    infer_instance
  exact .of_comp _ (Monoscheme.componentι k C)

private noncomputable def componentCover (k : Type u) [Field k] {M : Monoscheme.Fine.{u}}
    (C : Monoscheme.ToricComponent M) : (Monoscheme.componentRealization k C).OpenCover where
  I₀ := Monoscheme.ComponentAffineOpens C
  X U := (Monoscheme.realizationDiagram k M).obj U.1
  f U := Monoscheme.componentChart k C U
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun U ↦ componentChart_open k C U⟩
    intro x
    have hx : (Monoscheme.componentι k C) x ∈ Monoscheme.componentOpen k C := x.property
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
    obtain ⟨y, hy⟩ := hU
    refine ⟨U, y, ?_⟩
    apply (Monoscheme.componentOpen k C).ι.isOpenEmbedding.injective
    change (Monoscheme.componentι k C) ((Monoscheme.componentChart k C U) y) =
      (Monoscheme.componentι k C) x
    rw [← Scheme.Hom.comp_apply, componentChart_fac]
    exact hy

private theorem connected_component_iso (k : Type u) [Field k] (M : Monoscheme.Fine.{u})
    [ConnectedSpace M.space] (C : Monoscheme.ToricComponent M) :
    IsIso (Monoscheme.componentι k C) := by
  classical
  have htop : Monoscheme.componentOpen k C = ⊤ := by
    apply top_le_iff.mp
    intro x _hx
    let : ∀ {U V : Monoscheme.AffineOpens M} (f : U ⟶ V),
        IsOpenImmersion ((Monoscheme.realizationDiagram k M).map f) :=
      Monoscheme.realizationDiagram_open k M
    let := Monoscheme.realizationDiagram_locallyDirected k M
    obtain ⟨U, y, hy⟩ :=
      Scheme.IsLocallyDirected.ι_jointly_surjective (F := Monoscheme.realizationDiagram k M) x
    let V : Monoscheme.ComponentAffineOpens C := ⟨U, fun _ _ ↦ Subsingleton.elim _ _⟩
    apply Opens.mem_iSup.mpr
    exact ⟨V, y, hy⟩
  have : IsOpenImmersion (Monoscheme.componentι k C) := by
    change IsOpenImmersion (Monoscheme.componentOpen k C).ι
    infer_instance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  simpa only [Monoscheme.componentι, Scheme.Opens.opensRange_ι] using htop

private theorem canonical_over (k : Type u) [Field k] {M : Monoscheme.Fine.{u}}
    (C : Monoscheme.ToricComponent M) :
    Monoscheme.torusAction k C ≫ Monoscheme.componentToBase k C =
      pullback.fst _ _ ≫ Monoscheme.torusToBase k C := by
  let cov := (componentCover k C).pullback₁
    (pullback.snd (Monoscheme.torusToBase k C) (Monoscheme.componentToBase k C))
  apply Scheme.Cover.hom_ext cov
  intro U
  let e := pullbackLeftPullbackSndIso (Monoscheme.torusToBase k C)
    (Monoscheme.componentToBase k C) (Monoscheme.componentChart k C U) ≪≫
      pullback.congrHom rfl (Monoscheme.componentChart_over k C U)
  have hcf : cov.f U = pullback.fst _ _ := rfl
  have he : cov.f U = e.hom ≫ Monoscheme.chartProductMap k C U := by
    rw [hcf]
    apply pullback.hom_ext
    · simp [componentCover, e, Monoscheme.chartProductMap, Category.assoc,
        pullback.congrHom_hom, pullback.map]
    · simpa [componentCover, e, Monoscheme.chartProductMap, Category.assoc,
        pullback.congrHom_hom, pullback.map] using
        (pullback.condition (f := pullback.snd (Monoscheme.torusToBase k C)
          (Monoscheme.componentToBase k C)) (g := Monoscheme.componentChart k C U))
  rw [he]
  simp only [Category.assoc]
  have hc : Monoscheme.IsCanonicalTorusAction k C (Monoscheme.torusAction k C) :=
    Classical.choose_spec (Monoscheme.existsUnique_torusAction k C).exists
  rw [← Category.assoc _ (Monoscheme.torusAction k C), hc U,
    Category.assoc, Category.assoc, Monoscheme.componentChart_over]
  have hh : Spec.map (CommRingCat.ofHom (Monoscheme.coaction k C U).toRingHom) ≫
      (Monoscheme.baseCocone k M).ι.app U.1 =
        Spec.map (CommRingCat.ofHom (algebraMap k
          (MonoidAlgebra k C.lattice ⊗[k]
            MonoidAlgebra k (M.space.presheaf.obj (op U.1.1))))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (Monoscheme.coaction k C U).comp_algebraMap
  rw [hh]
  simp [Monoscheme.chartProductMap, Monoscheme.torusToBase, Monoscheme.baseCocone]

/-- The recorded glued chart coaction is an associative unital action of the canonical
Hopf group scheme. On a connected monoscheme its component realization is the whole
realization, via the recorded component inclusion.

Source: ILO VIII 3.2.2 and 3.2.4, p.103
(blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Steps 4--6 of the node. The chart coaction is multiplicative and unital.
Its iterates send a monomial to the same triple tensor and its unit composite fixes
that monomial. Localizing at a monomial localizes both the chart and its coaction,
since the generic-lattice factor is a unit. In two intersecting charts, the smallest
neighbourhood of a monoidal point is a basic open in both charts: sum the generators
of the complementary face. The monoid sheaf identifies these localizations compatibly
with the generic stalk (`def-trf-fine-fan-blowup`). Thus the coactions agree there.
Product chart opens cover the product (`lem-weil-pbc-open-fibre-product`), so glue by
`lem-weil-pbc-scheme-morphism-gluing`. Uniqueness of gluing proves the action identities.
Connectedness makes the component open the whole realization. -/
theorem latticeTorus_action (k : Type u) [Field k] (L : Type u) [CommGroup L]
    (M : Monoscheme.Fine.{u}) [ConnectedSpace M.space]
    (hM : Monoscheme.Fine.IsTorsionFree M) (C : Monoscheme.ToricComponent M)
    (j : C.lattice ≃* L) :
    IsIso (Monoscheme.componentι k C) ∧
      Monoscheme.IsCanonicalTorusAction k C (Monoscheme.torusAction k C) ∧
      ∃ action : ModObj
          ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))
          (Over.mk (Monoscheme.componentToBase k C)),
        action.smul.left = Monoscheme.torusAction k C := by
  have _torsionFree := hM
  have _latticeCoordinates := j
  have hc : Monoscheme.IsCanonicalTorusAction k C (Monoscheme.torusAction k C) :=
    Classical.choose_spec (Monoscheme.existsUnique_torusAction k C).exists
  let a : ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k))) ⊗
      Over.mk (Monoscheme.componentToBase k C) ⟶
        Over.mk (Monoscheme.componentToBase k C) :=
    Over.homMk (Monoscheme.torusAction k C) (canonical_over k C)
  refine ⟨connected_component_iso k M C, hc, ?_⟩
  refine ⟨{ smul := a
            one_smul := Monoscheme.canonicalTorusCoaction_unit k C a hc
            mul_smul := Monoscheme.canonicalTorusCoaction_associativity k C a hc }, rfl⟩

/-- Base change has the specified Laurent coordinates, natural for every coefficient map.
The monomial formula determines the equivalences uniquely, including over the zero ring.

Source: ILO VIII 3.2.2--3.2.4, p.103
(blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Step 8 of the node. The coefficient base-change map sends c tensor e^l to
c e^l; its inverse sends a finite sum to the sum of its coefficient tensors. Tensor
balancing makes these mutually inverse. Compose with the basis-coordinate map of
Step 1. For a coefficient map f, both composites send c tensor e^l to f(c)t^b(l),
so they agree. In particular the formula commutes with every affine restriction map,
without a principal-open restriction. -/
theorem latticeTorus_baseChange (k : Type u) [Field k] (L : Type u) [CommGroup L]
    (r : ℕ) (b : L ≃* Multiplicative (Fin r → ℤ)) :
    ∃ e : ∀ R : CommAlgCat.{u} k,
        R ⊗[k] MonoidAlgebra k L ≃ₐ[R] MonoidAlgebra R (Multiplicative (Fin r → ℤ)),
      (∀ (R : CommAlgCat.{u} k) (c : R) (l : L),
        e R (c ⊗ₜ[k] MonoidAlgebra.single l 1) = MonoidAlgebra.single (b l) c) ∧
      (∀ (R S : CommAlgCat.{u} k) (f : R ⟶ S) (x : R ⊗[k] MonoidAlgebra k L),
        e S ((Algebra.TensorProduct.map f.hom (AlgHom.id k (MonoidAlgebra k L))) x) =
          MonoidAlgebra.mapAlgHom (Multiplicative (Fin r → ℤ)) f.hom (e R x)) := by
  let e (R : CommAlgCat.{u} k) :=
    (MonoidAlgebra.scalarTensorEquiv k R).trans (MonoidAlgebra.domCongr R R b)
  refine ⟨e, ?_, ?_⟩
  · intro R c l
    simp [e]
  · intro R S f x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul c x =>
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
      | single l a => simp [e, Algebra.smul_def, mul_comm]

/-- The Laurent algebra has the displayed finite polynomial quotient presentation.
The two copies of `Fin r` index the variables t_i and u_i; their images are inverse
Laurent monomials. This specifies the isomorphism as an algebra isomorphism.

Source: ILO VIII, Laurent-chart input to Lemma 3.2.12(i), p.104
(blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Step 9 of the node. Send t_i to the positive standard monomial and u_i to
its inverse. Conversely split every integer exponent into its positive and negative
parts and multiply the corresponding residue classes. The relations t_i*u_i=1 cancel
opposite pairs, so this inverse is multiplicative. The composites fix all Laurent
monomials and all polynomial generators, proving that they are inverse. The argument
also applies to rank zero and the zero coefficient ring. -/
theorem latticeTorus_presentation (k : Type u) [Field k] (r : ℕ)
    (R : CommAlgCat.{u} k) :
    ∃ q : (MvPolynomial (Fin r ⊕ Fin r) R ⧸
        Ideal.span (Set.range (fun i : Fin r ↦
          MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i) - 1))) ≃ₐ[R]
        MonoidAlgebra R (Multiplicative (Fin r → ℤ)),
      (∀ i : Fin r,
        q (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i))) =
          MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) 1) ∧
      (∀ i : Fin r,
        q (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr i))) =
          MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (-1 : ℤ))) 1) := by
  classical
  let I : Ideal (MvPolynomial (Fin r ⊕ Fin r) R) :=
    Ideal.span (Set.range (fun i : Fin r ↦
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i) - 1))
  let Q := MvPolynomial (Fin r ⊕ Fin r) R ⧸ I
  let π := Ideal.Quotient.mkₐ R I
  let t (i : Fin r) : Q := π (MvPolynomial.X (Sum.inl i))
  let u (i : Fin r) : Q := π (MvPolynomial.X (Sum.inr i))
  have htu (i : Fin r) : t i * u i = 1 := by
    apply sub_eq_zero.mp
    change π (MvPolynomial.X (Sum.inl i)) * π (MvPolynomial.X (Sum.inr i)) - 1 = 0
    rw [← map_mul, ← map_one π, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  let v (i : Fin r) : Qˣ := Units.mkOfMulEqOne (t i) (u i) (htu i)
  let powers : Multiplicative (Fin r → ℤ) →* Qˣ :=
    { toFun := fun n ↦ ∏ i, v i ^ n.toAdd i
      map_one' := by simp
      map_mul' := fun n m ↦ by simp [zpow_add, Finset.prod_mul_distrib] }
  let g := (Units.coeHom Q).comp powers
  let back := MonoidAlgebra.lift R Q _ g
  let pos (i : Fin r) : MonoidAlgebra R (Multiplicative (Fin r → ℤ)) :=
    MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) 1
  let neg (i : Fin r) : MonoidAlgebra R (Multiplicative (Fin r → ℤ)) :=
    MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (-1 : ℤ))) 1
  let f : MvPolynomial (Fin r ⊕ Fin r) R →ₐ[R]
      MonoidAlgebra R (Multiplicative (Fin r → ℤ)) :=
    MvPolynomial.aeval (Sum.elim pos neg)
  have hf : I ≤ RingHom.ker f.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [f, pos, neg, MonoidAlgebra.single_mul_single,
      ← ofAdd_add, ← Pi.single_add, MonoidAlgebra.one_def]
  let forward : Q →ₐ[R] MonoidAlgebra R (Multiplicative (Fin r → ℤ)) :=
    Ideal.Quotient.liftₐ I f (fun a ha ↦ hf ha)
  have hfX (s : Fin r ⊕ Fin r) : forward (π (MvPolynomial.X s)) = Sum.elim pos neg s := by
    change (forward.comp π) (MvPolynomial.X s) = _
    rw [show forward.comp π = f from Ideal.Quotient.liftₐ_comp I f _]
    exact MvPolynomial.aeval_X _ _
  have hpos (i : Fin r) : back (pos i) = t i := by
    simp [back, pos, g, powers, v, Pi.single_apply, apply_ite]
  have hneg (i : Fin r) : back (neg i) = u i := by
    simp [back, neg, g, powers, v, Pi.single_apply, apply_ite]
    rfl
  have hbf : back.comp forward = AlgHom.id R Q := by
    apply Ideal.Quotient.algHom_ext
    change back.comp (forward.comp π) = (AlgHom.id R Q).comp π
    rw [show forward.comp π = f from Ideal.Quotient.liftₐ_comp I f _, AlgHom.id_comp]
    ext s
    cases s with
    | inl i => simpa only [AlgHom.comp_apply, f, MvPolynomial.aeval_X, Sum.elim_inl, t] using hpos i
    | inr i => simpa only [AlgHom.comp_apply, f, MvPolynomial.aeval_X, Sum.elim_inr, u] using hneg i
  have hfb : forward.comp back = AlgHom.id R _ := by
    apply MonoidAlgebra.algHom_ext
    · intro n
      simp only [AlgHom.comp_apply, AlgHom.id_apply, back,
        MonoidAlgebra.lift_single, one_smul]
      let w := (MonoidAlgebra.of R (Multiplicative (Fin r → ℤ))).toHomUnits
      have hv (i : Fin r) : Units.map forward.toMonoidHom (v i) =
          w (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) := by
        apply Units.ext
        change forward (t i) = pos i
        exact hfX (Sum.inl i)
      have hn : n = ∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ)) ^ n.toAdd i := by
        apply Multiplicative.toAdd.injective
        simpa only [toAdd_prod, toAdd_zpow,
          toAdd_ofAdd] using pi_eq_sum_univ' n.toAdd
      change ((Units.map forward.toMonoidHom) (powers n) :
        MonoidAlgebra R (Multiplicative (Fin r → ℤ))) = _
      change ((Units.map forward.toMonoidHom) (∏ i, v i ^ n.toAdd i) :
        MonoidAlgebra R (Multiplicative (Fin r → ℤ))) = _
      rw [map_prod]
      simp_rw [map_zpow, hv, ← map_zpow, ← map_prod, ← hn]
      rfl
    · ext
  refine ⟨AlgEquiv.ofAlgHom forward back hfb hbf, ?_, ?_⟩
  · intro i
    exact hfX (Sum.inl i)
  · intro i
    exact hfX (Sum.inr i)

/-- Every affine open base chart pulls back to the canonical tensor-product chart.
Both projection equations specify the comparison, so these comparisons commute with
restriction; combined with `latticeTorus_baseChange` and `latticeTorus_presentation`
they give exactly the stated Laurent and polynomial-quotient charts.

Source: ILO VIII 3.2.2--3.2.4, p.103; Stacks 01I4, 01JR
(blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Step 7 of the node. The open fibre-product formula identifies the inverse image
of Spec R with T times Spec R. The affine fibre-product formula identifies this with
Spec of k[L] tensor R. Exchange the factors to obtain R tensor k[L]. The projection
formulas are the scalar inclusions. Uniqueness in the fibre-product universal property
makes these comparisons commute with every change of affine chart. -/
theorem latticeTorus_affineCharts (k : Type u) [Field k] (L : Type u) [CommGroup L]
    (Y : Over (Spec (.of k))) (R : CommAlgCat.{u} k)
    (j : (Spec (.of R)).asOver (Spec (.of k)) ⟶ Y) [IsOpenImmersion j.left] :
    ∃ c : pullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L))))
          Y.hom) j.left ≅ Spec (.of (R ⊗[k] MonoidAlgebra k L)),
      c.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] MonoidAlgebra k L).toRingHom) =
        pullback.snd _ _ ∧
      c.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          MonoidAlgebra k L →ₐ[k] R ⊗[k] MonoidAlgebra k L).toRingHom) =
        pullback.fst _ _ ≫ pullback.fst _ _ := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L)))
  have hj : j.left ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) := j.w
  let p := pullbackLeftPullbackSndIso f Y.hom j.left
  let q := pullback.congrHom (rfl : f = f) hj
  let c := p ≪≫ q ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso k R (MonoidAlgebra k L)
  refine ⟨c, ?_, ?_⟩
  · change c.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k))) = _
    simp [c, p, q, f, Category.assoc, pullback.congrHom_hom, pullback.map]
  · simp [c, p, q, f, Category.assoc, pullback.congrHom_hom, pullback.map]

/-- The projection is locally finitely presented for any base; finite type is preserved
when the base is finite type. In particular the lattice torus itself is finite type.

Source: ILO VIII, Laurent-chart input to Lemma 3.2.12(i), p.104
(blueprint: lem-trf-lattice-torus-coordinates-action).
Proof: Step 10 of the node. Use the affine charts of Step 7 and the Laurent polynomial
presentation of Steps 8--9. It is a finite presentation over each affine base, which
is precisely local finite presentation (`def-sbc-locally-finite-presentation`). For
a finite-type base, take a finite affine cover and adjoin the finitely many Laurent
variables and their inverses to each finite generating set. This gives a finite affine
cover by finite-type algebras (`def-weil-finite-type-morphism`). Take Y=Spec k for the
last clause. Rank zero gives R itself, and empty Y uses the empty cover. -/
theorem latticeTorus_finiteType (k : Type u) [Field k] (L : Type u) [CommGroup L]
    (r : ℕ) (b : L ≃* Multiplicative (Fin r → ℤ)) :
    (∀ Y : Over (Spec (.of k)),
      LocallyOfFinitePresentation
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L))))
          Y.hom) ∧
      (LocallyOfFiniteType Y.hom → QuasiCompact Y.hom →
        LocallyOfFiniteType
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L))))
            Y.hom ≫ Y.hom) ∧
        QuasiCompact
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L))))
            Y.hom ≫ Y.hom))) ∧
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L)))) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L)))) := by
  have : Group.FG L := Group.fg_of_surjective (f := b.symm.toMonoidHom) b.symm.surjective
  have : Algebra.FiniteType k (MonoidAlgebra k L) := inferInstance
  have : Algebra.FinitePresentation k (MonoidAlgebra k L) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k L)))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact (RingHom.finitePresentation_algebraMap).mpr inferInstance
  refine ⟨?_, inferInstance, inferInstance⟩
  intro Y
  refine ⟨inferInstance, ?_⟩
  intro hft hqc
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
