/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.ConstructibleApproximation
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FiniteSections
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Hypercohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso

/-!
# Deligne's finiteness criterion at closed points

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`p : X ⟶ Spec k` proper. Let `hᵢ : Wᵢ ⟶ X` be finitely many morphisms from Noetherian schemes
whose images contain all the non-closed points of `X`. A bounded below complex `G` of étale
sheaves of `Λ`-modules on `X` is bounded constructible as soon as its pullbacks `Lhᵢ^* G` and its
cohomology `Rp_* G` are bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper`).

This is the form of Deligne's argument (SGA 4½, [Th. finitude], proof of 3.2) used for the
finiteness of nearby cycles, the `hᵢ` being the geometric generic fibres of the coordinates of
the charts of the special fibre of `ℙⁿ`.

## Proof

Let `F = ℋ^q(G)`. By Deligne's approximation
(`AlgebraicGeometry.Etale.exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel`) it has a
constructible subsheaf `F₀` with `F / F₀` supported at closed points; for `q` larger than the
amplitudes of the `Lhᵢ^* G`, `F` itself is supported at closed points.
* By induction on `q` from below, `τ^{≤ q} G` is bounded constructible: if `τ^{< q} G` is, so is
  its cohomology (`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`),
  hence `H^q(X, τ^{≥ q} G) = Γ(X, F)` is finite
  (`AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE`);
  then `Γ(X, F / F₀)` is finite, as `H¹(X, F₀)` is, so `F / F₀` is constructible
  (`AlgebraicGeometry.Etale.isConstructibleSheaf_of_isZero_sheafFiber_of_finite`), and so is `F`.
* For `N` beyond the amplitudes, `τ^{≥ N} G` has cohomology sheaves supported at closed points,
  which are acyclic
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber`), so
  `H^q(X, τ^{≥ N} G) = Γ(X, ℋ^q(G))` vanishes for large `q`, and `ℋ^q(G) = 0` for large `q`
  (`AlgebraicGeometry.Etale.isZero_of_isZero_sheafFiber_of_subsingleton`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)

section Auxiliary

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- In an exact sequence of modules over a finite ring, the middle term is finite as soon as the
outer terms are. -/
lemma finite_X₂_of_exact {S : ShortComplex (ModuleCat.{u + 1} Λ)} (hS : S.Exact)
    (h₁ : Finite S.X₁) (h₃ : Finite S.X₃) : Finite S.X₂ := by
  have := isNoetherian_of_range_eq_ker S.f.hom S.g.hom hS.moduleCat_range_eq_ker
  exact Module.finite_of_finite Λ

variable {k : Type u} [Field k] [IsSepClosed k]

omit [Finite Λ] in
/-- Over a separably closed field `k`, the derived global sections `RΓ(Spec k, M)` of a bounded
constructible complex `M` are bounded with finite cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_isSepClosed
    {M : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) M) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj M) :=
  (_root_.DerivedCategory.boundedFiniteCohomology Λ).prop_of_iso
    ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app M).symm
    ((boundedConstructible_iff_boundedFiniteCohomology M).1 hM)

omit [Finite Λ] in
/-- If the derived direct image `Rp_* K` to a separably closed point is bounded constructible,
then the derived global sections `RΓ(X, K) = RΓ(Spec k, Rp_* K)` are bounded with finite
cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K)) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) :=
  (_root_.DerivedCategory.boundedFiniteCohomology Λ).prop_of_iso
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) p).app K)
    (boundedFiniteCohomology_rightDerivedGlobalSections_of_isSepClosed hK)

/-- For `X` proper over a separably closed field, the derived global sections `RΓ(X, K)` of a
bounded constructible complex `K` are bounded with finite cohomology. -/
lemma boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    _root_.DerivedCategory.boundedFiniteCohomology Λ
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) :=
  boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p
    (boundedConstructible_rightDerivedLowerStar_of_isProper (𝟙 _) p hK)

omit [Finite Λ] in
/-- The stalk of a sheaf `F` at the geometric point over `h w` vanishes as soon as the stalk of
the pullback `h^* F` at the geometric point over `w` does: the geometric point of `W` over `w`,
followed by `h`, factors through the geometric point of `X` over `h w`. -/
lemma isZero_sheafFiber_algClosurePoint_apply_of_isZero_sheafFiber_upperStar {X W : Scheme.{u}}
    (h : W ⟶ X) (w : W) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsZero ((pointSmallEtale (W.algClosurePoint w)).sheafFiber.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj F))) :
    IsZero ((pointSmallEtale (X.algClosurePoint (h w))).sheafFiber.obj F) := by
  let φ := h.residueFieldMap w
  let : Algebra (X.residueField (h w)) (AlgebraicClosure (W.residueField w)) :=
    (φ ≫ CommRingCat.ofHom (algebraMap (W.residueField w) _)).hom.toAlgebra
  let j : AlgebraicClosure (X.residueField (h w)) →ₐ[X.residueField (h w)]
      AlgebraicClosure (W.residueField w) := IsAlgClosed.lift
  let a : Spec (.of (AlgebraicClosure (W.residueField w))) ⟶
      Spec (.of (AlgebraicClosure (X.residueField (h w)))) :=
    Spec.map (CommRingCat.ofHom j.toRingHom)
  have ha : a ≫ X.algClosurePoint (h w) = W.algClosurePoint w ≫ h := by
    change a ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (h w)) _)) ≫
        X.fromSpecResidueField (h w) =
      (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField w) _)) ≫
        W.fromSpecResidueField w) ≫ h
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext x
    exact j.commutes x
  refine IsZero.of_iso ?_ ((Scheme.sheafFiberPrecompIso _ a (ModuleCat.{u + 1} Λ)).app F)
  rw [ha]
  exact hF.of_iso ((Etale.upperStarCompSheafFiberIso _ h _).app F).symm

omit [Finite Λ] in
/-- If `G ∈ D^{≥ m}` has constructible cohomology sheaves in degrees `< q`, then its truncation
`τ^{< q} G` is bounded constructible. -/
lemma boundedConstructible_truncLT_of_isGE {X : Scheme.{u}}
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m q : ℤ)
    [G.IsGE m]
    (hG : ∀ j < q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ j).obj G)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ((t.truncLT q).obj G) := by
  have e (j : ℤ) (hj : j < q) :=
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncLTι_app G q j hj
    asIso ((_root_.DerivedCategory.homologyFunctor _ j).map ((t.truncLTι q).app G))
  have hz (j : ℤ) (hj : q ≤ j) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj ((t.truncLT q).obj G)) :=
    _root_.DerivedCategory.isZero_of_isLE _ (q - 1) j (by lia)
  refine ⟨⟨⟨m, ?_⟩, ⟨q - 1, inferInstance⟩⟩, fun j ↦ ?_⟩
  · refine (_root_.DerivedCategory.isGE_iff _ m).2 fun j hj ↦ ?_
    rcases lt_or_ge j q with hjq | hjq
    · exact (_root_.DerivedCategory.isZero_of_isGE G m j hj).of_iso (e j hjq)
    · exact hz j hjq
  · rcases lt_or_ge j q with hjq | hjq
    · have := hG j hjq
      exact IsConstructibleSheaf.of_iso
        (F := (_root_.DerivedCategory.homologyFunctor _ j).obj G) (e j hjq).symm
    · exact IsConstructibleSheaf.of_isZero (hz j hjq)

end Auxiliary

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The induction step of Deligne's finiteness criterion: if the cohomology sheaves of `G` in
degrees `< q` are constructible, so is `ℋ^q(G)`. -/
theorem isConstructibleSheaf_homology_of_forall_lt {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m q : ℤ)
    [G.IsGE m]
    (hpull : ∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj G)))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G))
    (hlt : ∀ j < q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ j).obj G)) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let F := (_root_.DerivedCategory.homologyFunctor _ q).obj G
  have hfin {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hK : _root_.DerivedCategory.boundedFiniteCohomology Λ (RΓ.obj K)) (n : ℤ) :
      Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj (RΓ.obj K)) :=
    ((_root_.DerivedCategory.boundedFiniteCohomology_iff_finite _).1 hK).2 n
  -- `Γ(X, F)` is finite
  have hΓF : Finite (Γ.obj F) := by
    have hT := RΓ.map_distinguished _ (t.triangleLTGE_distinguished q G)
    have h₃ := finite_X₂_of_exact
      (_root_.DerivedCategory.HomologySequence.exact₃ _ hT q (q + 1))
      (hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p hΓ) q)
      (hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
        (boundedConstructible_truncLT_of_isGE G m q hlt)) (q + 1))
    obtain ⟨e⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((t.truncGE q).obj G) q
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app G q q le_rfl
    exact @Finite.of_equiv _ _ h₃ (e ≪≫ Γ.mapIso (asIso
      ((_root_.DerivedCategory.homologyFunctor _ q).map
        ((t.truncGEπ q).app G))).symm).toLinearEquiv.toEquiv
  -- Deligne's approximation `F₀ ⊆ F`
  obtain ⟨F₀, a, ha, hF₀, hcok⟩ := exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel F h
    hpull
  let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel a) }
  have hQ : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj (cokernel a)) := by
    intro x hx
    obtain ⟨i, w, rfl⟩ := hcov x hx
    exact hcok i w
  -- `Γ(X, F / F₀)` is finite, as `Γ(X, F)` and `H¹(X, F₀)` are
  have hΓQ : Finite ((cokernel a).obj.obj (op (etaleTerminal X))) := by
    have hT := RΓ.map_distinguished _ hS.singleTriangle_distinguished
    obtain ⟨e₂⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0
    obtain ⟨e₃⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (cokernel a)) 0
    have h₂ : Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).obj
        (RΓ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
      @Finite.of_equiv _ _ hΓF (e₂ ≪≫ Γ.mapIso
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          F)).symm.toLinearEquiv.toEquiv
    have h₁ : Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 1).obj
        (RΓ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F₀))) :=
      hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
        (DerivedCategory.boundedConstructible_singleFunctor_obj F₀ 0)) 1
    have h₃ := finite_X₂_of_exact
      (_root_.DerivedCategory.HomologySequence.exact₃ _ hT 0 1) h₂ h₁
    exact @Finite.of_equiv _ _ h₃ (e₃ ≪≫ Γ.mapIso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (cokernel a)) ≪≫
      (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal X)).app _).toLinearEquiv.toEquiv
  have : IsConstructibleSheaf S.X₁ := hF₀
  have : IsConstructibleSheaf S.X₃ :=
    isConstructibleSheaf_of_isZero_sheafFiber_of_finite p (cokernel a) hQ hΓQ
  exact IsConstructibleSheaf.of_shortExact hS

/-- **Deligne's finiteness criterion at closed points** (SGA 4½, [Th. finitude], proof of 3.2).
Over a separably closed field `k`, let `p : X ⟶ Spec k` be proper and `hᵢ : Wᵢ ⟶ X` finitely many
morphisms from Noetherian schemes whose images contain the non-closed points of `X`. A bounded
below complex `G` of étale sheaves of modules over a finite ring with invertible exponent is
bounded constructible as soon as the pullbacks `Lhᵢ^* G` and the direct image `Rp_* G` are. -/
theorem boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ)
    [G.IsGE m]
    (hG : ∀ i, Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (W i)
      ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G)) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  -- the pullbacks of the cohomology sheaves are the cohomology sheaves of the pullbacks
  let e (i : ι) (q : ℤ) := ((Etale.upperStar (ModuleCat.{u + 1} Λ)
    (h i)).leftDerivedFunctorHomologyFunctorIso q).app G
  -- a bound `N` for the amplitudes of the `Lhᵢ^* G`
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i q, N < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G)) := by
    choose b hb using fun i ↦ (hG i).1.2
    obtain ⟨N, hN⟩ := (Set.finite_range b).bddAbove
    refine ⟨N, fun i q hq ↦ ?_⟩
    have := hb i
    exact _root_.DerivedCategory.isZero_of_isLE _ (b i) q (lt_of_le_of_lt (hN ⟨i, rfl⟩) hq)
  -- above `N`, the cohomology sheaves of `G` are supported at closed points
  have hstalk (q : ℤ) (hq : N < q) (x : X) (hx : x ∉ closedPoints X) :
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj G)) := by
    obtain ⟨i, w, rfl⟩ := hcov x hx
    exact isZero_sheafFiber_algClosurePoint_apply_of_isZero_sheafFiber_upperStar (h i) w _
      ((pointSmallEtale _).sheafFiber.map_isZero ((hN i q hq).of_iso (e i q)))
  -- all the cohomology sheaves of `G` are constructible
  have hc (q : ℤ) : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) := by
    suffices H : ∀ n : ℕ, ∀ q, q < m + n →
        IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) from
      H (q - m + 1).toNat q (by lia)
    intro n
    induction n with
    | zero =>
      intro q hq
      exact IsConstructibleSheaf.of_isZero
        (_root_.DerivedCategory.isZero_of_isGE G m q (by simpa using hq))
    | succ n ih =>
      intro q hq
      rcases lt_or_eq_of_le (show q ≤ m + n by push_cast at hq; lia) with hq' | rfl
      · exact ih q hq'
      · refine isConstructibleSheaf_homology_of_forall_lt p h hcov G m _ (fun i ↦ ?_) hΓ
          (fun j hj ↦ ih j hj)
        have := (hG i).2 (m + n)
        exact IsConstructibleSheaf.of_iso
          (F := (_root_.DerivedCategory.homologyFunctor _ (m + n)).obj
            ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G)) (e i (m + n)).symm
  -- the truncation `τ^{≥ N + 1} G` has cohomology sheaves supported at closed points
  let B := (t.truncGE (N + 1)).obj G
  have eB (q : ℤ) (hq : N + 1 ≤ q) :=
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app G (N + 1) q hq
    asIso ((_root_.DerivedCategory.homologyFunctor _ q).map ((t.truncGEπ (N + 1)).app G))
  have hBstalk (q : ℤ) (x : X) (hx : x ∉ closedPoints X) :
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj B)) := by
    rcases lt_or_ge q (N + 1) with hq | hq
    · exact (pointSmallEtale _).sheafFiber.map_isZero
        (_root_.DerivedCategory.isZero_of_isGE B (N + 1) q hq)
    · exact (hstalk q (by lia) x hx).of_iso ((pointSmallEtale _).sheafFiber.mapIso (eB q hq)).symm
  -- so `H^q(X, τ^{≥ N + 1} G) = Γ(X, ℋ^q(τ^{≥ N + 1} G))`
  have hB (q : ℤ) := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_acyclic Λ X B (N + 1)
    (fun q r hr ↦ isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber Λ p _
      (hBstalk q) hr.ne') q
  -- vanishing of `H^q(X, G)` and of `H^{q + 1}(X, τ^{< N + 1} G)` for large `q`
  obtain ⟨b₁, hb₁⟩ :=
    (boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p hΓ).1.2
  obtain ⟨b₂, hb₂⟩ := (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
    (boundedConstructible_truncLT_of_isGE G m (N + 1) fun j _ ↦ hc j)).1.2
  have hT := RΓ.map_distinguished _ (t.triangleLTGE_distinguished (N + 1) G)
  have hz (q : ℤ) (hq : max (max b₁ b₂) (N + 1) < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj G) := by
    have hS := _root_.DerivedCategory.HomologySequence.exact₃ _ hT q (q + 1)
    have h₁ : IsZero
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj (RΓ.obj G)) :=
      _root_.DerivedCategory.isZero_of_isLE _ b₁ q (by lia)
    have h₃ : IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q + 1)).obj
        (RΓ.obj ((t.truncLT (N + 1)).obj G))) :=
      _root_.DerivedCategory.isZero_of_isLE _ b₂ (q + 1) (by lia)
    have h₂ := hS.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
    obtain ⟨e'⟩ := hB q
    refine IsZero.of_iso ?_ (eB q (by lia))
    refine isZero_of_isZero_sheafFiber_of_subsingleton _ p (hBstalk q) ?_
    exact ModuleCat.isZero_iff_subsingleton.1 ((h₂.of_iso e'.symm).of_iso
      ((Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal X)).app _).symm)
  exact ⟨⟨⟨m, ‹_›⟩, ⟨max (max b₁ b₂) (N + 1),
    (_root_.DerivedCategory.isLE_iff G _).2 fun q hq ↦ hz q hq⟩⟩, hc⟩

end Etale

end AlgebraicGeometry
