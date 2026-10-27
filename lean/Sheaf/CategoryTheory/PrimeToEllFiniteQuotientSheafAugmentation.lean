/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.CategoryTheory.PrimeToEllCochainFiniteQuotientDescent
public import Sheaf.Analysis.ScalarCochainAveragingPrimitives
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Topology.Algebra.ClopenNhdofOne
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The scalar augmentation of finite-quotient cochain sheaves

Source: latest six-functors direct-images proof, paragraph (3), agent-formulated
finite-quotient sheaf argument; exact external reference WANTED
(blueprint: lem-sfb-prime-to-ell-finite-quotient-sheaf-augmentation).

The coordinate presentation below specifies the presheaf, its sheafification, scalar
multiplication, and the actual augmentation. It is a proposition, not a choice of an
object from an existence theorem. The objects are determined up to compatible isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures

namespace Profinite.ContinuousScalarCochains

/-- Section-coordinate presentation of the finite-quotient complex and its scalar
augmentation, including the local representatives, their simultaneous quotient refinement,
and signed finite primitives. `e` is injective with exactly the finite-quotient image.
The maps `eta` are the actual sheafification units transported along `a`. The scalar
identity on these local generators specifies the internal module action. `z` identifies
degree zero with the regular scalar module, and fixes the degree-zero part of `uL`.
Extension along `embeddingUpNat` gives zero terms in all negative degrees.

Source: latest direct-images proof, paragraph (3), agent finite-quotient sheaf argument
(blueprint: lem-sfb-prime-to-ell-finite-quotient-sheaf-augmentation).
The local clause uses an arbitrary initial subgroup `U0`; intersection allows the
representative and its cocycle equation to use one refining quotient. The finite sum
is written as `tsum` on a finite quotient, without choosing a `Fintype` enumeration.
-/
def HasFiniteQuotientSheafAugmentation (F K : Type u) [NormedField F] [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] : Prop := by
  let A := Profinite.continuousMapRingObjOfUniverse.{u, u} F
  letI : MonObj A := Profinite.continuousMapRingObjOfUniverseMonObj F
  letI : IsCommMonObj A := Profinite.isCommMonObj_continuousMapRingObjOfUniverse F
  let M := Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) A
  let V : M ⥤ Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} := Mod.forget A
  let T := presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}
  letI : HasDerivedCategory.{u + 2} M := HasDerivedCategory.standard M
  exact ∃ (P : CochainComplex (Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ)
    (e : ∀ (n : ℕ) (S : Profinite.{u}),
      (P.X n).obj (op S) →+ C(S × (Fin n → K), F)),
    (∀ (n : ℕ) (S : Profinite.{u}), Function.Injective (e n S)) ∧
    (∀ (n : ℕ) (S : Profinite.{u}) (c : C(S × (Fin n → K), F)),
      (∃ p : (P.X n).obj (op S), e n S p = c) ↔ FactorsThroughFiniteQuotient c) ∧
    (∀ (n : ℕ) (S S' : Profinite.{u}) (f : S' ⟶ S)
      (p : (P.X n).obj (op S)) (s : S') (g : Fin n → K),
      e n S' ((P.X n).map f.op p) (s, g) = e n S p (f s, g)) ∧
    (∀ (n : ℕ) (S : Profinite.{u}) (p : (P.X n).obj (op S))
      (s : S) (g : Fin (n + 1) → K),
      e (n + 1) S (((P.d n (n + 1)).app (op S)) p) (s, g) =
        scalarCochainDifferential n (e n S p) s g) ∧
    ∃ (L : CochainComplex M ℕ)
      (a : (T.mapHomologicalComplex (.up ℕ)).obj P ≅
        (V.mapHomologicalComplex (.up ℕ)).obj L)
      (eta : ∀ n : ℕ, P.X n ⟶ (L.X n).X.obj),
      (∀ n : ℕ, eta n = toSheafify (coherentTopology Profinite.{u}) (P.X n) ≫
        (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}).map
          (a.hom.f n)) ∧
      (∀ (n : ℕ) (S : Profinite.{u})
        (r : (InternalAbelianSheafModule.sectionRings
          (coherentTopology Profinite.{u}) A).obj (op S))
        (p q : (P.X n).obj (op S)),
        (∀ (s : S) (g : Fin n → K), e n S q (s, g) = r.down s * e n S p (s, g)) →
        (eta n).app (op S) q = r •
          (@id (((InternalAbelianSheafModule.sectionModuleFunctor
            (coherentTopology Profinite.{u}) A).obj (L.X n)).val.obj (op S))
              ((eta n).app (op S) p))) ∧
      ∃ (z : Mod.regular A ≅ L.X 0)
        (uL : (CochainComplex.single₀ M).obj (Mod.regular A) ⟶ L),
        (∀ (S : Profinite.{u}) (p : (P.X 0).obj (op S))
          (s : S) (g : Fin 0 → K),
          e 0 S p (s, g) =
            ((z.inv.hom.hom.app (op S)) ((eta 0).app (op S) p)).down s) ∧
        L.d 0 1 = 0 ∧ uL.f 0 = z.hom ∧
        (∀ n : ℕ, uL.f (n + 1) = 0) ∧
        IsIso (DerivedCategory.Q.{u + 2}.map
          (HomologicalComplex.extendMap uL ComplexShape.embeddingUpNat)) ∧
        (∀ n : ℕ, L.ExactAt (n + 1)) ∧
        (∀ (n : ℕ) (S : Profinite.{u}) (x : (L.X (n + 1)).X.obj.obj (op S)),
          ((L.d (n + 1) (n + 2)).hom.hom.app (op S)) x = 0 →
          ∀ U0 : OpenNormalSubgroup K,
          ∃ R : Sieve S, R ∈ (coherentTopology Profinite.{u}) S ∧
            ∀ (S' : Profinite.{u}) (f : S' ⟶ S), R f →
            ∃ (p : (P.X (n + 1)).obj (op S'))
              (U : OpenNormalSubgroup K)
              (cbar : C(S' × (Fin (n + 1) → K ⧸ U.toSubgroup), F)),
              U ≤ U0 ∧
              (eta (n + 1)).app (op S') p =
                (L.X (n + 1)).X.obj.map f.op x ∧
              (∀ (s : S') (g : Fin (n + 1) → K),
                e (n + 1) S' p (s, g) =
                  cbar (s, fun j ↦ QuotientGroup.mk' U.toSubgroup (g j))) ∧
              (∀ (s : S') (g : Fin (n + 2) → K ⧸ U.toSubgroup),
                scalarCochainDifferential (n + 1) cbar s g = 0)) ∧
        (∀ (n : ℕ) (S : Profinite.{u}) (U : OpenNormalSubgroup K)
          (cbar : C(S × (Fin (n + 1) → K ⧸ U.toSubgroup), F)),
          (∀ (s : S) (g : Fin (n + 2) → K ⧸ U.toSubgroup),
            scalarCochainDifferential (n + 1) cbar s g = 0) →
          ∃ (bbar : C(S × (Fin n → K ⧸ U.toSubgroup), F))
            (b : (P.X n).obj (op S)),
            (∀ (s : S) (g : Fin n → K ⧸ U.toSubgroup),
              bbar (s, g) = (-1 : F) ^ (n + 1) *
                (Nat.card (K ⧸ U.toSubgroup) : F)⁻¹ *
                  ∑' h, cbar (s, Fin.snoc g h)) ∧
            (∀ (s : S) (g : Fin n → K),
              e n S b (s, g) = bbar (s, fun j ↦ QuotientGroup.mk' U.toSubgroup (g j))) ∧
            (∀ (s : S) (g : Fin (n + 1) → K ⧸ U.toSubgroup),
              scalarCochainDifferential n bbar s g = cbar (s, g)) ∧
            (n = 0 → cbar = 0))

set_option backward.isDefEq.respectTransparency false

private lemma differential_zero {F K : Type u} [NormedField F] [Group K]
    {S : Type u} (c : S × (Fin 0 → K) → F) (s : S) (g : Fin 1 → K) :
    scalarCochainDifferential 0 c s g = 0 := by
  simp [scalarCochainDifferential, Subsingleton.elim (fun j ↦ g j.succ)
    (Fin.contractNth (0 : Fin 1) (· * ·) g)]

private lemma differential_pullback {F K Q : Type u} [NormedField F] [Group K]
    [Group Q] {S : Type u} (q : K →* Q) (n : ℕ)
    (c : S × (Fin n → Q) → F) (s : S) (g : Fin (n + 1) → K) :
    scalarCochainDifferential n (fun x ↦ c (x.1, fun j ↦ q (x.2 j))) s g =
      scalarCochainDifferential n c s (fun j ↦ q (g j)) := by
  simp only [scalarCochainDifferential]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact congrArg (fun h ↦ (s, h))
    (Fin.comp_contractNth (· * ·) (· * ·) q.map_mul j g)

private lemma refine_quotient {F K : Type u} [NormedField F] [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {S : Profinite.{u}} {n : ℕ} {c : C(S × (Fin n → K), F)}
    (hc : FactorsThroughFiniteQuotient c) (U0 : OpenNormalSubgroup K) :
    ∃ (U : OpenNormalSubgroup K) (b : C(S × (Fin n → K ⧸ U.toSubgroup), F)),
      U ≤ U0 ∧ ∀ (s : S) (g : Fin n → K),
        c (s, g) = b (s, fun j ↦ QuotientGroup.mk' U.toSubgroup (g j)) := by
  obtain ⟨U, b, hb⟩ := hc
  let W := U ⊓ U0
  let q : K ⧸ W.toSubgroup →* K ⧸ U.toSubgroup :=
    QuotientGroup.map W.toSubgroup U.toSubgroup (MonoidHom.id K) inf_le_left
  let b' : C(S × (Fin n → K ⧸ W.toSubgroup), F) :=
    b.comp ⟨fun x ↦ (x.1, fun j ↦ q (x.2 j)),
      continuous_fst.prodMk (continuous_pi fun j ↦
        (continuous_of_discreteTopology : Continuous q).comp
          ((continuous_apply j).comp continuous_snd))⟩
  exact ⟨W, b', inf_le_right, hb⟩

private lemma finite_primitives (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ell] F]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ∀ (Q : Type u) [Group Q] [Fintype Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (q : K →ₜ* Q), Function.Surjective q → Nat.Coprime (Nat.card Q) ell)
    (n : ℕ) (S : Profinite.{u}) (U : OpenNormalSubgroup K)
    (cbar : C(S × (Fin (n + 1) → K ⧸ U.toSubgroup), F))
    (hcbar : ∀ s g, scalarCochainDifferential (n + 1) cbar s g = 0) :
    ∃ bbar : C(S × (Fin n → K ⧸ U.toSubgroup), F),
      (∀ s g, bbar (s, g) = (-1 : F) ^ (n + 1) *
        (Nat.card (K ⧸ U.toSubgroup) : F)⁻¹ * ∑' h, cbar (s, Fin.snoc g h)) ∧
      (∀ s g, scalarCochainDifferential n bbar s g = cbar (s, g)) ∧
      (n = 0 → cbar = 0) := by
  classical
  let : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra ℚ_[ell]
  let c : C(S × (Fin (n + 1) → K), F) :=
    cbar.comp ⟨fun x ↦ (x.1, fun j ↦ QuotientGroup.mk' U.toSubgroup (x.2 j)),
      continuous_fst.prodMk (continuous_pi fun j ↦
        (QuotientGroup.continuous_mk).comp ((continuous_apply j).comp continuous_snd))⟩
  have hprime (W : OpenNormalSubgroup K) :
      Nat.Coprime (Nat.card (K ⧸ W.toSubgroup)) ell := by
    let : Fintype (K ⧸ W.toSubgroup) := Fintype.ofFinite _
    exact hK _ ⟨QuotientGroup.mk' W.toSubgroup, QuotientGroup.continuous_mk⟩
      Quotient.mk_surjective
  obtain ⟨b, bbar, hbbar, hb, hd, _⟩ :=
    (scalar_cochain_averaging_primitives ell F (algebraMap ℚ_[ell] F)
      (algebraMap_isometry ℚ_[ell] F) IsUltrametricDist.norm_add_le_max K
      (fun _ hW h1 ↦ ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1)
      hprime).1 n S c U cbar (fun _ _ ↦ rfl) (by
        intro s g
        rw [show scalarCochainDifferential (n + 1) c s g =
          scalarCochainDifferential (n + 1) cbar s
            (fun j ↦ QuotientGroup.mk' U.toSubgroup (g j)) from
          differential_pullback (QuotientGroup.mk' U.toSubgroup) (n + 1) cbar s g]
        exact hcbar _ _)
  have hdbar (s : S) (g : Fin (n + 1) → K ⧸ U.toSubgroup) :
      scalarCochainDifferential n bbar s g = cbar (s, g) := by
    obtain ⟨g', rfl⟩ := (Function.Surjective.piMap
      (fun _ ↦ Quotient.mk_surjective) :
        Function.Surjective (fun g : Fin (n + 1) → K ↦
          fun j ↦ QuotientGroup.mk' U.toSubgroup (g j))) g
    have heq : (b : S × (Fin n → K) → F) =
        fun x ↦ bbar (x.1, fun j ↦ QuotientGroup.mk' U.toSubgroup (x.2 j)) := by
      funext x
      exact hb x.1 x.2
    have h := hd s g'
    rw [heq, differential_pullback] at h
    exact h
  refine ⟨bbar, hbbar, hdbar, ?_⟩
  intro hn
  subst n
  ext ⟨s, g⟩
  exact (hdbar s g).symm.trans (differential_zero bbar s g)

private theorem augmentation_of_comparison (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ell] F]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ∀ (Q : Type u) [Group Q] [Fintype Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (q : K →ₜ* Q), Function.Surjective q → Nat.Coprime (Nat.card Q) ell)
    (hcomp : HasFiniteQuotientComparison F K) : HasFiniteQuotientSheafAugmentation F K := by
  classical
  let A := Profinite.continuousMapRingObjOfUniverse.{u, u} F
  let : MonObj A := Profinite.continuousMapRingObjOfUniverseMonObj F
  let : IsCommMonObj A := Profinite.isCommMonObj_continuousMapRingObjOfUniverse F
  let M := Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) A
  let : HasDerivedCategory.{u + 2} M := HasDerivedCategory.standard M
  let J := coherentTopology Profinite.{u}
  let V : M ⥤ Sheaf J AddCommGrpCat.{u + 1} := Mod.forget A
  let T := presheafToSheaf J AddCommGrpCat.{u + 1}
  rcases hcomp with ⟨C, L, e, hres, hsmul, hd, P, i, hi, hrange, a, iota, hiota, _⟩
  let e' (n : ℕ) (S : Profinite.{u}) :=
    (e n S).toAddMonoidHom.comp ((i.f n).app (op S)).hom
  let eta (n : ℕ) : P.X n ⟶ (L.X n).X.obj :=
    toSheafify J (P.X n) ≫ (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (a.hom.f n)
  -- The counit formula identifies the actual sheafification unit with the inclusion.
  have heta (n : ℕ) :
      eta n ≫ (iota.f n).hom.hom = i.f n := by
    dsimp only [eta]
    erw [Category.assoc, ← Functor.map_comp]
    change toSheafify J (P.X n) ≫ (sheafToPresheaf J AddCommGrpCat.{u + 1}).map
      (a.hom.f n ≫ V.map (iota.f n)) = _
    erw [hiota]
    have ha : a.hom.f n ≫ a.inv.f n = 𝟙 _ :=
      congrArg (fun f ↦ f.f n) a.hom_inv_id
    erw [← Category.assoc (a.hom.f n) (a.inv.f n), ha, Category.id_comp]
    change toSheafify J (P.X n) ≫
      (sheafToPresheaf J AddCommGrpCat.{u + 1}).map
        (T.map (i.f n) ≫ (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app _) = _
    erw [Functor.map_comp, ← Category.assoc, ← toSheafify_naturality]
    erw [Category.assoc,
      (sheafificationAdjunction J AddCommGrpCat.{u + 1}).right_triangle_components]
    exact Category.comp_id _
  have hmono (n : ℕ) : Mono ((iota.f n).hom) := by
    have : ∀ S, Mono ((i.f n).app S) := fun S ↦
      (AddCommGrpCat.mono_iff_injective _).2 (hi n S.unop)
    have : Mono (i.f n) := NatTrans.mono_of_mono_app _
    change Mono (V.map (iota.f n))
    rw [hiota]
    infer_instance
  have hetainj (n : ℕ) (S : Profinite.{u}) :
      Function.Injective ((eta n).app (op S)) := by
    intro p q hpq
    apply hi n S
    have hh := congrArg (fun x ↦ ((iota.f n).hom.hom.app (op S)) x) hpq
    simp only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, heta] at hh
    exact hh
  have hdiff (n : ℕ) (S : Profinite.{u}) (p : (P.X n).obj (op S))
      (s : S) (g : Fin (n + 1) → K) :
      e' (n + 1) S (((P.d n (n + 1)).app (op S)) p) (s, g) =
        scalarCochainDifferential n (e' n S p) s g := by
      dsimp only [e', AddMonoidHom.comp_apply]
      have hh := congrArg (fun f ↦ f.app (op S)) (i.comm n (n + 1))
      have hx := (ConcreteCategory.congr_hom hh p).symm
      change (i.f (n + 1)).app (op S) (((P.d n (n + 1)).app (op S)) p) =
        ((C.d n (n + 1)).hom.hom.app (op S)) (((i.f n).app (op S)) p) at hx
      erw [hx, hd]
      simp only [scalarCochainDifferential, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one]
      rfl
  have heta_comm (n : ℕ) :
      eta n ≫ (L.d n (n + 1)).hom.hom = P.d n (n + 1) ≫ eta (n + 1) := by
    dsimp only [eta]
    erw [Category.assoc, ← Functor.map_comp]
    have hh := a.hom.comm n (n + 1)
    change a.hom.f n ≫ V.map (L.d n (n + 1)) =
      T.map (P.d n (n + 1)) ≫ a.hom.f (n + 1) at hh
    erw [hh, Functor.map_comp, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫
      (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (a.hom.f (n + 1)))
        (toSheafify_naturality J (P.d n (n + 1))).symm
  have hprimitive (n : ℕ) (S : Profinite.{u}) (W : OpenNormalSubgroup K)
      (cbar : C(S × (Fin (n + 1) → K ⧸ W.toSubgroup), F))
      (hc : ∀ s g, scalarCochainDifferential (n + 1) cbar s g = 0) :
      ∃ (bbar : C(S × (Fin n → K ⧸ W.toSubgroup), F))
        (b : (P.X n).obj (op S)),
        (∀ s g, bbar (s, g) = (-1 : F) ^ (n + 1) *
          (Nat.card (K ⧸ W.toSubgroup) : F)⁻¹ * ∑' h, cbar (s, Fin.snoc g h)) ∧
        (∀ s g, e' n S b (s, g) =
          bbar (s, fun j ↦ QuotientGroup.mk' W.toSubgroup (g j))) ∧
        (∀ s g, scalarCochainDifferential n bbar s g = cbar (s, g)) ∧
        (n = 0 → cbar = 0) := by
    obtain ⟨bbar, hformula, hdb, hz⟩ := finite_primitives ell F K hK n S W cbar hc
    let b : C(S × (Fin n → K), F) :=
      bbar.comp ⟨fun x ↦ (x.1, fun j ↦ QuotientGroup.mk' W.toSubgroup (x.2 j)),
        continuous_fst.prodMk (continuous_pi fun j ↦
          QuotientGroup.continuous_mk.comp ((continuous_apply j).comp continuous_snd))⟩
    obtain ⟨p, hp⟩ := (hrange n S b).2 ⟨W, bbar, fun _ _ ↦ rfl⟩
    exact ⟨bbar, p, hformula, fun s g ↦ congrArg (fun c ↦ c (s, g)) hp, hdb, hz⟩
  -- Injectivity of eta makes a second cover for the cocycle equation unnecessary.
  have hlocal (n : ℕ) (S : Profinite.{u}) (x : (L.X (n + 1)).X.obj.obj (op S))
      (hx : ((L.d (n + 1) (n + 2)).hom.hom.app (op S)) x = 0)
      (U0 : OpenNormalSubgroup K) :
      ∃ R : Sieve S, R ∈ J S ∧ ∀ (S' : Profinite.{u}) (f : S' ⟶ S), R f →
        ∃ (p : (P.X (n + 1)).obj (op S')) (W : OpenNormalSubgroup K)
          (cbar : C(S' × (Fin (n + 1) → K ⧸ W.toSubgroup), F)),
          W ≤ U0 ∧ (eta (n + 1)).app (op S') p = (L.X (n + 1)).X.obj.map f.op x ∧
          (∀ s g, e' (n + 1) S' p (s, g) =
            cbar (s, fun j ↦ QuotientGroup.mk' W.toSubgroup (g j))) ∧
          ∀ s g, scalarCochainDifferential (n + 1) cbar s g = 0 := by
    have : Presheaf.IsLocallySurjective J (eta (n + 1)) := by
      dsimp only [eta]
      infer_instance
    refine ⟨Presheaf.imageSieve (eta (n + 1)) x,
      Presheaf.imageSieve_mem J _ x, ?_⟩
    rintro S' f ⟨p, hp⟩
    have hdp : ((P.d (n + 1) (n + 2)).app (op S')) p = 0 := by
      apply hetainj (n + 2) S'
      rw [map_zero]
      have hh := ConcreteCategory.congr_hom
        (NatTrans.congr_app (heta_comm (n + 1)) (op S')) p
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hh
      rw [← hh, hp, NatTrans.naturality_apply, hx, map_zero]
    obtain ⟨W, cbar, hW, hcbar⟩ := refine_quotient ((hrange (n + 1) S' _).1
      ⟨p, rfl⟩) U0
    refine ⟨p, W, cbar, hW, hp, hcbar, ?_⟩
    intro s g
    obtain ⟨g', rfl⟩ := (Function.Surjective.piMap
      (fun _ ↦ Quotient.mk_surjective) :
        Function.Surjective (fun g : Fin (n + 2) → K ↦
          fun j ↦ QuotientGroup.mk' W.toSubgroup (g j))) g
    have heq : (e' (n + 1) S' p : S' × (Fin (n + 1) → K) → F) =
        fun x ↦ cbar (x.1, fun j ↦ QuotientGroup.mk' W.toSubgroup (x.2 j)) := by
      funext x
      exact hcbar x.1 x.2
    have hh := hdiff (n + 1) S' p s g'
    rw [hdp, map_zero, ContinuousMap.zero_apply, heq, differential_pullback] at hh
    exact hh.symm
  have hp_exact (n : ℕ) (S : Profinite.{u})
      (p : (P.X (n + 1)).obj (op S))
      (hp : ((P.d (n + 1) (n + 2)).app (op S)) p = 0) :
      ∃ b : (P.X n).obj (op S), ((P.d n (n + 1)).app (op S)) b = p := by
    obtain ⟨W, cbar, hcbar⟩ := (hrange (n + 1) S _).1 ⟨p, rfl⟩
    have heq : (e' (n + 1) S p : S × (Fin (n + 1) → K) → F) =
        fun x ↦ cbar (x.1, fun j ↦ QuotientGroup.mk' W.toSubgroup (x.2 j)) := by
      funext x
      exact hcbar x.1 x.2
    have hdc (s : S) (g : Fin (n + 2) → K ⧸ W.toSubgroup) :
        scalarCochainDifferential (n + 1) cbar s g = 0 := by
      obtain ⟨g', rfl⟩ := (Function.Surjective.piMap
        (fun _ ↦ Quotient.mk_surjective) :
          Function.Surjective (fun g : Fin (n + 2) → K ↦
            fun j ↦ QuotientGroup.mk' W.toSubgroup (g j))) g
      have hh := hdiff (n + 1) S p s g'
      rw [hp, map_zero, ContinuousMap.zero_apply, heq, differential_pullback] at hh
      exact hh.symm
    obtain ⟨bbar, b, _, hb, hdb, _⟩ := hprimitive n S W cbar hdc
    refine ⟨b, ?_⟩
    apply hi (n + 1) S
    apply (e (n + 1) S).injective
    ext ⟨s, g⟩
    change e' (n + 1) S (((P.d n (n + 1)).app (op S)) b) (s, g) =
      e' (n + 1) S p (s, g)
    rw [hdiff]
    have heb : (e' n S b : S × (Fin n → K) → F) =
        fun x ↦ bbar (x.1, fun j ↦ QuotientGroup.mk' W.toSubgroup (x.2 j)) := by
      funext x
      exact hb x.1 x.2
    rw [heb, differential_pullback, hdb]
    exact (hcbar s g).symm
  -- Sheafify objectwise exactness, then reflect it through the faithful forgetful functor.
  have hLexact (n : ℕ) : L.ExactAt (n + 1) := by
    let sc := P.sc' n (n + 1) (n + 2)
    have hex : sc.Exact := by
      rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
      apply NatTrans.ext
      funext S
      let ev := (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj S
      have heval : (sc.map ev).Exact := by
        rw [ShortComplex.ab_exact_iff]
        exact hp_exact n S.unop
      have hz := (ShortComplex.exact_iff_isZero_homology _).1 heval
      have hz' : IsZero (ev.obj sc.homology) :=
        IsZero.of_iso hz (sc.mapHomologyIso ev).symm
      exact hz'.eq_of_src _ _
    have hexT : ((T.mapHomologicalComplex (.up ℕ)).obj P).ExactAt (n + 1) := by
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      exact hex.map T
    have hexV := hexT.of_iso a
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hexV ⊢
    exact ((L.sc' n (n + 1) (n + 2)).exact_map_iff_of_faithful V).1 hexV
  -- Construct the degree-zero identification as an actual internal module isomorphism.
  let B := InternalAbelianSheafModule.sectionModuleFunctor J A
  have hregular (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings J A).obj (op S))
      (x : (B.obj (Mod.regular A)).val.obj (op S)) :
      (r • x).down = r.down * x.down := by
    change (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1}) A A ≫
      (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (MonObj.mul (X := A))).app
        (op S)).hom (r ⊗ₜ[ℤ] x)).down = _
    erw [Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose J
      (Profinite.continuousMapRingSheafOfUniverse F)]
    rfl
  let eval0 (S : Profinite.{u}) : (B.obj (C.X 0)).val.obj (op S) →+
      (B.obj (Mod.regular A)).val.obj (op S) :=
    { toFun := fun x ↦ ULift.up ((e 0 S x).comp
        ⟨fun s ↦ (s, Fin.elim0), continuous_id.prodMk continuous_const⟩)
      map_zero' := by
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        simp
      map_add' := by
        intro x y
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        change e 0 S (x + y) (s, Fin.elim0) =
          e 0 S x (s, Fin.elim0) + e 0 S y (s, Fin.elim0)
        simp }
  let theta : C.X 0 ⟶ Mod.regular A :=
    (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful J A).preimage
      ⟨PresheafOfModules.homMk
        { app Z := AddCommGrpCat.ofHom (eval0 Z.unop)
          naturality Z Z' f := by
            apply ConcreteCategory.hom_ext
            intro x
            apply ULift.ext
            apply ContinuousMap.ext
            intro s
            exact hres 0 Z.unop Z'.unop f.unop x s Fin.elim0 }
        (by
          intro Z r x
          apply ULift.ext
          ext s
          exact (hsmul 0 Z.unop r x s Fin.elim0).trans
            (congrArg (fun f : C(Z.unop, F) ↦ f s) (hregular Z.unop r (eval0 Z.unop x))).symm)⟩
  have htheta (S : Profinite.{u}) (x : (C.X 0).X.obj.obj (op S)) :
      theta.hom.hom.app (op S) x = eval0 S x := rfl
  have htheta_iso : IsIso theta := by
    have hbij (S : Profinite.{u}) : Function.Bijective (theta.hom.hom.app (op S)) := by
      constructor
      · intro x y hxy
        apply (e 0 S).injective
        ext ⟨s, g⟩
        have h := congrArg (fun x ↦ x.down s) hxy
        simpa only [htheta, eval0, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          ContinuousMap.comp_apply, ContinuousMap.coe_mk,
          Subsingleton.elim g Fin.elim0] using h
      · intro r
        let c : C(S × (Fin 0 → K), F) := r.down.comp ContinuousMap.fst
        refine ⟨(e 0 S).symm c, ?_⟩
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        simp [htheta, eval0, c]
    have : ∀ S, IsIso (theta.hom.hom.app S) := fun S ↦
      (ConcreteCategory.isIso_iff_bijective _).2 (hbij S.unop)
    have : IsIso theta.hom.hom := NatIso.isIso_of_isIso_app _
    have : IsIso ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map theta.hom) := by
      change IsIso theta.hom.hom
      infer_instance
    have : IsIso theta.hom := isIso_of_reflects_iso _
      (sheafToPresheaf J AddCommGrpCat.{u + 1})
    have : IsIso (V.map theta) := by change IsIso theta.hom; infer_instance
    exact isIso_of_reflects_iso _ V
  have hi0 : IsIso (i.f 0) := by
    have : ∀ S, IsIso ((i.f 0).app S) := by
      intro S
      apply (ConcreteCategory.isIso_iff_bijective _).2
      refine ⟨hi 0 S.unop, ?_⟩
      intro x
      obtain ⟨p, hp⟩ := (hrange 0 S.unop (e 0 S.unop x)).2
        ⟨⟨⊤, by change (⊤ : Subgroup K).Normal; infer_instance⟩,
          ⟨fun y ↦ e 0 S.unop x (y.1, Fin.elim0),
          (e 0 S.unop x).continuous.comp (continuous_fst.prodMk continuous_const)⟩,
          fun s g ↦ congrArg (fun g ↦ e 0 S.unop x (s, g)) (Subsingleton.elim _ _)⟩
      exact ⟨p, (e 0 S.unop).injective hp⟩
    exact NatIso.isIso_of_isIso_app _
  have hiota0 : IsIso (iota.f 0) := by
    have : IsIso (V.map (iota.f 0)) := by rw [hiota]; infer_instance
    exact isIso_of_reflects_iso _ V
  let z : Mod.regular A ≅ L.X 0 := (asIso (iota.f 0) ≪≫ asIso theta).symm
  have hd0 : L.d 0 1 = 0 := by
    apply V.map_injective
    apply (cancel_mono (iota.f 1).hom).1
    have hC : C.d 0 1 = 0 := by
      apply V.map_injective
      ext S x
      apply (e 1 S.unop).injective
      ext ⟨s, g⟩
      change e 1 S.unop (((C.d 0 1).hom.hom.app S) x) (s, g) = _
      simpa [scalarCochainDifferential, zsmul_eq_mul,
        Subsingleton.elim (fun j ↦ g j.succ) (Fin.contractNth (0 : Fin 1) (· * ·) g)]
        using hd 0 S.unop x s g
    change (L.d 0 1).hom ≫ (iota.f 1).hom = (0 : L.X 0 ⟶ L.X 1).hom ≫ _
    rw [show (L.d 0 1).hom ≫ (iota.f 1).hom =
      (iota.f 0).hom ≫ (C.d 0 1).hom from congrArg Mod.Hom.hom (iota.comm 0 1).symm]
    rw [hC]
    simp
  let uL : (CochainComplex.single₀ M).obj (Mod.regular A) ⟶ L :=
    (CochainComplex.fromSingle₀Equiv L _).symm ⟨z.hom, by rw [hd0, comp_zero]⟩
  refine ⟨P, e', fun n S ↦ (e n S).injective.comp (hi n S), hrange, ?_, ?_,
    L, a, eta, fun _ ↦ rfl, ?_, ?_⟩
  · intro n S S' f p s g
    change e n S' (((i.f n).app (op S')) (((P.X n).map f.op) p)) (s, g) = _
    rw [← ConcreteCategory.comp_apply, (i.f n).naturality]
    exact hres n S S' f _ s g
  · exact hdiff
  · intro n S r p q heq
    have : Mono ((iota.f n).hom.hom.app (op S)) := by
      have := hmono n
      infer_instance
    apply (AddCommGrpCat.mono_iff_injective _).1 this
    have hscalar := (((InternalAbelianSheafModule.sectionModuleFunctor J A).map
      (iota.f n)).val.app (op S)).hom.map_smul r ((eta n).app (op S) p)
    change ((iota.f n).hom.hom.app (op S)) ((eta n).app (op S) q) =
      (((InternalAbelianSheafModule.sectionModuleFunctor J A).map
        (iota.f n)).val.app (op S)).hom
          (r • (@id (((InternalAbelianSheafModule.sectionModuleFunctor J A).obj
            (L.X n)).val.obj (op S)) ((eta n).app (op S) p)))
    dsimp only [id]
    erw [hscalar]
    have hp (t : (P.X n).obj (op S)) :
        ((iota.f n).hom.hom.app (op S)) ((eta n).app (op S) t) =
          (i.f n).app (op S) t :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (heta n) (op S)) t
    apply (e n S).injective
    ext ⟨s, g⟩
    rw [hsmul]
    change e n S (((iota.f n).hom.hom.app (op S)) ((eta n).app (op S) q)) (s, g) =
      r.down s * e n S
        (((iota.f n).hom.hom.app (op S)) ((eta n).app (op S) p)) (s, g)
    erw [hp, hp]
    exact heq s g
  · refine ⟨z, uL, ?_, hd0, ?_, ?_, ?_, ?_, hlocal, hprimitive⟩
    · intro S p s g
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app (heta 0) (op S)) p
      change e 0 S ((i.f 0).app (op S) p) (s, g) = _
      change _ = (theta.hom.hom.app (op S)
        ((iota.f 0).hom.hom.app (op S) ((eta 0).app (op S) p))).down s
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hh
      rw [hh, htheta]
      exact congrArg (fun g ↦ e 0 S ((i.f 0).app (op S) p) (s, g))
        (Subsingleton.elim _ _)
    · exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    · intro n
      apply IsZero.eq_of_src
      exact HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (Mod.regular A) (n + 1)
        (by omega)
    · -- Check the actual augmentation before applying derived localization.
      let : QuasiIso uL := by
        rw [quasiIso_iff]
        intro n
        cases n with
        | zero =>
          rw [quasiIsoAt_iff' uL 0 0 1 (by simp) (by simp)]
          have h0 : uL.f 0 = z.hom :=
            CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
          let phi := (HomologicalComplex.shortComplexFunctor' M (.up ℕ) 0 0 1).map uL
          have : IsIso phi.τ₂ := by change IsIso (uL.f 0); rw [h0]; infer_instance
          have : Mono phi.τ₃ := by
            change Mono (uL.f 1)
            exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0
              (Mod.regular A) 1 (by omega)).mono _
          have : Epi phi.τ₁ := by change Epi (uL.f 0); rw [h0]; infer_instance
          exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono phi
        | succ n =>
          rw [quasiIsoAt_iff_exactAt uL (n + 1)
            (HomologicalComplex.ExactAt.of_isZero
              (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)))]
          exact hLexact n
      have : QuasiIso (HomologicalComplex.extendMap uL ComplexShape.embeddingUpNat) := by
        rw [HomologicalComplex.quasiIso_extendMap_iff]
        infer_instance
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso M
        (HomologicalComplex.extendMap uL ComplexShape.embeddingUpNat)).2 inferInstance
    · exact hLexact

set_option backward.isDefEq.respectTransparency true

/-- The actual scalar augmentation of the sheafified finite-quotient complex is
invertible in the ordinary unbounded derived category, for both finite E and Omega.
The latter retains its norm topology and has no completeness hypothesis.
Source: latest direct-images proof, paragraph (3), agent finite-quotient sheaf argument
(blueprint: lem-sfb-prime-to-ell-finite-quotient-sheaf-augmentation).

Proof plan:
1. The inhomogeneous faces preserve finite-quotient functions and scalar multiplication.
   Their identities give a presheaf complex; degree zero is A and its differential is zero.
2. Use lem-pc-sites-module-sheafification-interface and
   lem-pc-sites-sheafification-underlying-sets. The unit is locally surjective; use
   lem-weil-pbc-site-sheafification-sections-local also on its differential to refine
   the cover until the cocycle equation holds in the presheaf. Intersect the finitely
   many open normal subgroups, also with U0, to obtain a simultaneous finite quotient.
3. Apply lem-sfb-scalar-cochain-averaging-primitives to each finite quotient. The signed
   last-variable sum has differential cbar. In degree one averaging the cocycle identity
   gives cbar=0. Every sum is finite and continuous, including for empty test objects.
4. These primitives give exactness of the presheaf in positive degrees. Apply
   lem-weil-pbc-ringed-site-module-sheafification-exact. Transport through
   def-weil-pbc-internal-abelian-sheaf-module-equivalence, which retains sections,
   restrictions, kernels and images. This gives ExactAt in internal modules.
5. Degree zero sheafifies to A by def-sfb-continuous-map-condensed-ring. The actual
   augmentation is the identity there and zero elsewhere; all negative terms vanish.
   It is a quasi-isomorphism and Q inverts it by def-weil-abstract-derived-category.
   Empty S and K=1 satisfy the same formulas, without an infinite average or completion.
-/
theorem prime_to_ell_finite_quotient_sheaf_augmentation (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ∀ (Q : Type u) [Group Q] [Fintype Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (q : K →ₜ* Q), Function.Surjective q → Nat.Coprime (Nat.card Q) ell) :
    HasFiniteQuotientSheafAugmentation E K ∧ HasFiniteQuotientSheafAugmentation Ω K := by
  obtain ⟨hE, hΩ⟩ := prime_to_ell_cochain_finite_quotient_descent ell Ω E K hK
  exact ⟨augmentation_of_comparison ell E K hK hE,
    augmentation_of_comparison ell Ω K hK hΩ⟩

end Profinite.ContinuousScalarCochains
