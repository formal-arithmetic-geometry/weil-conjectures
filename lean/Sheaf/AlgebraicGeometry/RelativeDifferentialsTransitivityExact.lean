/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit
public import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityAffineStalk
import Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityOpen
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The canonical transitivity sequence of differential sheaves

Source: Stacks Project, Morphisms, Tags 01UX, 01UV, 01UT and 01US
(blueprint: lem-a1-differential-sheaf-transitivity-exact).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

private theorem transitivity_zero_of_formula {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
    g.relativeDifferentialsPullbackMap h ≫ q = 0 := by
  obtain ⟨adj, hadj⟩ := Modules.exists_tensorPullbackAdjunction h
  apply (adj.homEquiv g.relativeDifferentials h.relativeDifferentials).injective
  apply (g.relativeDifferentialsHomEquiv _).injective
  ext V b
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  simp only [PresheafOfModules.Derivation.postcomp_d_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change q.val.app (op (h ⁻¹ᵁ V.unop))
    ((g.relativeDifferentialsPullbackMap h).val.app (op (h ⁻¹ᵁ V.unop))
      ((adj.unit.app g.relativeDifferentials).val.app V
        (g.relativeDifferentialsDerivation.d b))) = 0
  have hη : (adj.unit.app g.relativeDifferentials).val.app V
      (g.relativeDifferentialsDerivation.d b) =
        g.relativeDifferentialsPullbackGenerator h V.unop b := by
    rw [hadj]
    rfl
  rw [hη]
  have hfirst : (g.relativeDifferentialsPullbackMap h).val.app (op (h ⁻¹ᵁ V.unop))
      (g.relativeDifferentialsPullbackGenerator h V.unop b) =
        (h ≫ g).relativeDifferentialsDerivation.d (h.app V.unop b) :=
    (Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap g h)).1 V.unop b
  exact (congrArg (q.val.app (op (h ⁻¹ᵁ V.unop))) hfirst).trans
    ((hq (h ⁻¹ᵁ V.unop) (h.app V.unop b)).trans
      (h.relativeDifferentialsDerivation.d_app_app V.unop b))

private theorem transitivity_exact_epi_of_stalk {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a)
    (hz : g.relativeDifferentialsPullbackMap h ≫ q = 0)
    (hs : ∀ x : X,
      Function.Exact
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
          (g.relativeDifferentialsPullbackMap h))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) ∧
      Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q)) :
    (ShortComplex.mk (g.relativeDifferentialsPullbackMap h) q hz).Exact ∧ Epi q := by
  constructor
  · apply ((RingedSpace.module_stalk_exact X.toRingedSpace
      (g.relativeDifferentialsPullbackMap h)).2.2.2.2 _ _ _ hz).mpr
    intro x
    exact ModuleCat.shortComplex_exact _ (hs x).1
  · constructor
    intro M a b hab
    apply (h.relativeDifferentialsHomEquiv M).injective
    ext U x
    change a.val.app U (h.relativeDifferentialsDerivation.d x) =
      b.val.app U (h.relativeDifferentialsDerivation.d x)
    exact (congrArg (a.val.app U) (hq U.unop x).symm).trans
      ((congrArg (fun m ↦ m.val.app U
        ((h ≫ g).relativeDifferentialsDerivation.d x)) hab).trans
        (congrArg (b.val.app U) (hq U.unop x)))

private theorem differentialCongr_hom_d {X S : Scheme.{u}}
    (f f' : X ⟶ S) (hf : f = f') (O : X.Opens) (a : Γ(X, O)) :
    (relativeDifferentialsCongr f hf).hom.app O
      (f.relativeDifferentialsDerivation.d (X := op O) a) =
        f'.relativeDifferentialsDerivation.d (X := op O) a := by
  subst f'
  rfl

/-- The canonical sequence `h* Ω(Y/S) → Ω(X/S) → Ω(X/Y) → 0` is right exact.
Its affine comparisons are isomorphisms of sheaves, hence commute with restriction
on principal opens, where `tilde.toOpen` is the standard module localization.
The first comparison is normalized on actual pulled-back differential sections.
The two affine arrows are specified on the generating tensors and differentials;
the diagrams identify the sheaf arrows with their associated module arrows.
The last clause identifies the sequence on every source open with its restriction,
including the normalization of the first-term comparison on pulled-back sections.

Source: Stacks Project, Morphisms, Tag 01UX (`lemma-triangle-differentials`),
Tag 01UV (`lemma-functoriality-differentials`), affine description Tag 01UT and
source-open restriction Tag 01US
(blueprint: lem-a1-differential-sheaf-transitivity-exact).

Proof:
1. The universal derivation for h is also relative to h ≫ g, since it kills
   h-sharp(g-sharp a). Its universal property constructs q, with q(da)=da.
2. Pass the composite of the first arrow and q through the normalized tensor
   adjunction and the universal property for g. On db it is d(h-sharp b) over h,
   hence zero. Both Hom equivalences are injective, so the composite vanishes.
3. `relativeDifferentials_transitivity_affine_stalk` supplies the affine comparison
   and stalk assertions. The stalk criterion gives sheaf exactness. The formula
   q(da)=da and the universal property for h show that q is an epimorphism.
4. `relativeDifferentials_transitivity_open` supplies normalized restriction
   comparisons and qO(da)=da. Apply the same affine/stalk argument to O.ι ≫ h and g,
   after transporting qO by the associativity congruence. An isomorphism of short
   complexes transports exactness and the epimorphism back to the displayed
   source-open sequence. No smoothness, flatness or finiteness is used. -/
theorem relativeDifferentials_transitivity_exact {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) :
    ∃ q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials,
      (∀ (O : X.Opens) (a : Γ(X, O)),
        q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
          h.relativeDifferentialsDerivation.d (X := op O) a) ∧
      (∃ z : g.relativeDifferentialsPullbackMap h ≫ q = 0,
        (ShortComplex.mk (g.relativeDifferentialsPullbackMap h) q z).Exact) ∧
      Epi q ∧
      (∀ x : X,
        Function.Exact
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
            (g.relativeDifferentialsPullbackMap h))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) ∧
        Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q)) ∧
      (∀ (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
          (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1),
        ∃ θ : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict U.2.fromSpec ≅
            tilde ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
              (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))),
          (∀ b : Γ(Y, V.1),
            θ.hom.app ⊤
              ((Modules.sectionsRestrictFromSpecLinearEquiv
                ((Modules.tensorPullback h).obj g.relativeDifferentials) U.2).symm
                (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                  (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b))) =
              tilde.toOpen ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))) ⊤
                  ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                    (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                      (CommRingCat.KaehlerDifferential.d b))) ∧
          ∃ (uA : (ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)) ⟶
              CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
            (vA : CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) ⟶
              CommRingCat.KaehlerDifferential (h.appLE V.1 U.1 hUV)),
            (∀ (a : Γ(X, U.1)) (b : Γ(Y, V.1)),
              uA (a • @id
                ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)))
                ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                    (CommRingCat.KaehlerDifferential.d b))) =
                a • CommRingCat.KaehlerDifferential.d (h.appLE V.1 U.1 hUV b)) ∧
            (∀ a : Γ(X, U.1), vA (CommRingCat.KaehlerDifferential.d a) =
              CommRingCat.KaehlerDifferential.d a) ∧
            Function.Exact uA vA ∧ Function.Surjective vA ∧
            (Modules.restrictFunctor U.2.fromSpec).map
                (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom =
              θ.hom ≫ (tilde.functor Γ(X, U.1)).map uA ∧
            (Modules.restrictFunctor U.2.fromSpec).map q ≫
                (h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).hom =
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom ≫ (tilde.functor Γ(X, U.1)).map vA) ∧
      (∀ O : X.Opens,
        ∃ (e : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict O.ι ≅
              (Modules.tensorPullback (O.ι ≫ h)).obj g.relativeDifferentials)
          (qO : (O.ι ≫ (h ≫ g)).relativeDifferentials ⟶ (O.ι ≫ h).relativeDifferentials),
          (∀ (V : Y.Opens) (b : Γ(Y, V)),
            e.hom.app (O.ι ⁻¹ᵁ (h ⁻¹ᵁ V))
              (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                (homOfLE (O.ι.image_preimage_le (h ⁻¹ᵁ V))).op
                  (g.relativeDifferentialsPullbackGenerator h V b)) =
              g.relativeDifferentialsPullbackGenerator (O.ι ≫ h) V b) ∧
          (Modules.restrictFunctor O.ι).map (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom =
            e.hom ≫ g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫
              (relativeDifferentialsCongr _ (Category.assoc O.ι h g)).hom ∧
          (Modules.restrictFunctor O.ι).map q ≫
              (h.relativeDifferentialsRestrictIso O.ι).hom =
            ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom ≫ qO ∧
          (∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
            qO.app T ((O.ι ≫ (h ≫ g)).relativeDifferentialsDerivation.d (X := op T) a) =
              (O.ι ≫ h).relativeDifferentialsDerivation.d (X := op T) a) ∧
          (∃ z : (g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫
                (relativeDifferentialsCongr _ (Category.assoc O.ι h g)).hom) ≫ qO = 0,
            (ShortComplex.mk (g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫
              (relativeDifferentialsCongr _ (Category.assoc O.ι h g)).hom) qO z).Exact) ∧
          Epi qO) := by
  let D : h.relativeDifferentials.val.Derivation' (h ≫ g).pullbackPresheafToPresheaf :=
    (h ≫ g).derivationMk
      h.relativeDifferentialsDerivation.d
      (fun {U} a b ↦ h.relativeDifferentialsDerivation.d_mul a b)
      (fun {U V} i x ↦ h.relativeDifferentialsDerivation.d_map i x)
      (by
        intro V a
        change h.relativeDifferentialsDerivation.d
          (h.app (g ⁻¹ᵁ V) (g.app V a)) = 0
        exact h.relativeDifferentialsDerivation.d_app_app (g ⁻¹ᵁ V) (g.app V a))
  let q := ((h ≫ g).relativeDifferentialsHomEquiv _).symm D
  have hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a := by
    intro O a
    exact (h ≫ g).relativeDifferentialsHomEquiv_symm_app_d D a
  obtain ⟨hstalk, haffine⟩ := relativeDifferentials_transitivity_affine_stalk h g q hq
  have hz := transitivity_zero_of_formula h g q hq
  obtain ⟨hexact, hepi⟩ := transitivity_exact_epi_of_stalk h g q hq hz hstalk
  refine ⟨q, hq, ⟨hz, hexact⟩, hepi, hstalk, haffine, ?_⟩
  intro O
  obtain ⟨e, qO, he, hfirst, hsecond, hqO⟩ :=
    relativeDifferentials_transitivity_open h g q hq O
  let c := relativeDifferentialsCongr ((O.ι ≫ h) ≫ g) (Category.assoc O.ι h g)
  let q' := c.hom ≫ qO
  have hq' : ∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
      q'.app T (((O.ι ≫ h) ≫ g).relativeDifferentialsDerivation.d (X := op T) a) =
        (O.ι ≫ h).relativeDifferentialsDerivation.d (X := op T) a := by
    intro T a
    change qO.app T (c.hom.app T
      (((O.ι ≫ h) ≫ g).relativeDifferentialsDerivation.d (X := op T) a)) = _
    rw [differentialCongr_hom_d]
    exact hqO T a
  obtain ⟨hs', _⟩ := relativeDifferentials_transitivity_affine_stalk (O.ι ≫ h) g q' hq'
  have hz' := transitivity_zero_of_formula (O.ι ≫ h) g q' hq'
  obtain ⟨hexact', hepi'⟩ := transitivity_exact_epi_of_stalk (O.ι ≫ h) g q' hq' hz' hs'
  have hzO : (g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫ c.hom) ≫ qO = 0 := by
    simpa only [Category.assoc] using hz'
  let C₁ := ShortComplex.mk (g.relativeDifferentialsPullbackMap (O.ι ≫ h)) q' hz'
  let C₂ := ShortComplex.mk (g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫ c.hom) qO hzO
  let eC : C₁ ≅ C₂ := ShortComplex.isoMk (Iso.refl _) c (Iso.refl _)
    (by simp [C₁, C₂]) (by simp [C₁, C₂, q'])
  obtain ⟨hexactO, hepiO⟩ :=
    (ShortComplex.exact_and_epi_g_iff_of_iso eC).mp ⟨hexact', hepi'⟩
  exact ⟨e, qO, he, hfirst, hsecond, hqO, ⟨hzO, hexactO⟩, hepiO⟩

end AlgebraicGeometry.Scheme.Hom
