/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsTransitivityAffineStalk
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsTransitivityOpen

/-!
# The canonical transitivity exact sequence of differential sheaves

Source: Stacks Project, Morphisms, Tags 01UX (`lemma-triangle-differentials`)
and 01UV (`lemma-functoriality-differentials`)
(blueprint: lem-a1-differential-sheaf-transitivity-exact).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- The congruence of differential sheaves sends the universal derivation to the universal
derivation. Proof: by equality induction on the two morphisms. -/
private theorem congr_hom_app_d {X S : Scheme.{u}} {f f' : X ⟶ S} (e : f = f')
    (T : X.Opens) (a : Γ(X, T)) :
    (relativeDifferentialsCongr f e).hom.app T
        (f.relativeDifferentialsDerivation.d (X := op T) a) =
      f'.relativeDifferentialsDerivation.d (X := op T) a := by
  subst e
  rfl

/-- The section formula identifies the quotient map and makes the stalk exactness
criterion applicable. Source: Stacks Project, Tag 01UX. -/
private theorem transitivity_exact_of_formula
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
    ∃ z : g.relativeDifferentialsPullbackMap h ≫ q = 0,
      (ShortComplex.mk (g.relativeDifferentialsPullbackMap h) q z).Exact ∧ Epi q := by
  have hz : g.relativeDifferentialsPullbackMap h ≫ q = 0 := by
    obtain ⟨adj, hadj⟩ := Modules.exists_tensorPullbackAdjunction h
    let e := adj.homEquiv g.relativeDifferentials h.relativeDifferentials
    apply e.injective
    apply (g.relativeDifferentialsHomEquiv _).injective
    ext U a
    rw [Adjunction.homEquiv_unit]
    change q.val.app (op (h ⁻¹ᵁ U.unop))
      ((g.relativeDifferentialsPullbackMap h).val.app (op (h ⁻¹ᵁ U.unop))
        ((adj.unit.app g.relativeDifferentials).val.app U
          (g.relativeDifferentialsDerivation.d a))) = 0
    rw [hadj]
    change q.app (h ⁻¹ᵁ U.unop)
      ((g.relativeDifferentialsPullbackMap h).app (h ⁻¹ᵁ U.unop)
        (relativeDifferentialsPullbackGenerator g h U.unop a)) = 0
    have hu := (existsUnique_relativeDifferentialsPullbackMap g h).choose_spec.1 U.unop a
    change (g.relativeDifferentialsPullbackMap h).app (h ⁻¹ᵁ U.unop)
      (relativeDifferentialsPullbackGenerator g h U.unop a) = _ at hu
    rw [hu, hq]
    exact h.relativeDifferentialsDerivation.d_app_app U.unop a
  obtain ⟨hstk, _⟩ := relativeDifferentials_transitivity_affine_stalk h g q hq
  refine ⟨hz, ?_, ?_⟩
  · apply ((RingedSpace.module_stalk_exact X.toRingedSpace
      (g.relativeDifferentialsPullbackMap h)).2.2.2.2 _ _ _ hz).mpr
    intro x
    exact ModuleCat.shortComplex_exact _ (hstk x).1
  · apply Modules.epi_of_surjective_stalk q
    intro x
    exact (hstk x).2

/-- The canonical right exact transitivity sequence, with normalized affine comparisons,
stalk exactness, and compatibility with every source open subscheme.
Source: Stacks Project, Morphisms, Tags 01UX and 01UV
(blueprint: lem-a1-differential-sheaf-transitivity-exact).

Proof:
1. Regard the h-relative universal derivation as an h≫g-relative derivation, since it
   kills every section coming from Y, hence from S. The universal Hom equivalence
   constructs q and gives q(da)=da on every open.
2. The composite with the canonical first arrow is zero. Apply the normalized tensor
   adjunction and the universal Hom equivalence on Y; on db this composite is the
   h-relative differential of h-sharp(b), which is zero.
3. Apply the normalized affine/stalk comparison to q and its section formula. On each
   affine triple the first map is a tensor db ↦ a d(h-sharp(b)), and the second is
   da ↦ da. The algebraic differential sequence is exact and its second map surjective.
   The comparison isomorphisms are sheaf morphisms, so commute with restriction,
   including principal localization. Localization gives exactness on every stalk.
   Clause (5) of module_stalk_exact gives sheaf exactness. If two maps agree after q,
   their values on every da agree; the universal Hom equivalence gives their equality,
   proving that q is an epimorphism.
4. For a source open j:O→X, the normalized open comparison gives e and qO with the
   two commuting squares and qO(da)=da. Apply the preceding construction to j≫h,g.
   The associativity congruence identifies its middle differential sheaf with that of
   j≫(h≫g), and carries da to da by equality induction. The resulting short complexes
   are isomorphic, so exactness and the epimorphism transport to qO. -/
theorem relativeDifferentials_transitivity_exact
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) :
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
  let D : h.relativeDifferentials.val.Derivation'
      (h ≫ g).pullbackPresheafToPresheaf :=
    (h ≫ g).derivationMk
      (fun {U} ↦ h.relativeDifferentialsDerivation.d)
      (by
        intro U a b
        exact h.relativeDifferentialsDerivation.d_mul a b)
      (by
        intro U V i a
        exact h.relativeDifferentialsDerivation.d_map i a)
      (by
        intro V a
        change h.relativeDifferentialsDerivation.d
          (h.app (g ⁻¹ᵁ V) (g.app V a)) = 0
        apply h.relativeDifferentialsDerivation.d_app_app)
  let q := ((h ≫ g).relativeDifferentialsHomEquiv _).symm D
  have hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a := by
    intro O a
    exact (h ≫ g).relativeDifferentialsHomEquiv_symm_app_d D a
  obtain ⟨hstk, haff⟩ := relativeDifferentials_transitivity_affine_stalk h g q hq
  obtain ⟨z, hex, hepi⟩ := transitivity_exact_of_formula h g q hq
  refine ⟨q, hq, ⟨z, hex⟩, hepi, hstk, haff, ?_⟩
  intro O
  obtain ⟨e, qO, he, hsq1, hsq2, hqO⟩ := relativeDifferentials_transitivity_open h g q hq O
  let c := relativeDifferentialsCongr _ (Category.assoc O.ι h g)
  have hq' : ∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
      (c.hom ≫ qO).app T (((O.ι ≫ h) ≫ g).relativeDifferentialsDerivation.d (X := op T) a) =
        (O.ι ≫ h).relativeDifferentialsDerivation.d (X := op T) a := by
    intro T a
    rw [Modules.Hom.comp_app, ConcreteCategory.comp_apply, congr_hom_app_d, hqO]
  obtain ⟨z', hex', hepi'⟩ := transitivity_exact_of_formula (O.ι ≫ h) g (c.hom ≫ qO) hq'
  have z'' : (g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫ c.hom) ≫ qO = 0 := by
    rw [Category.assoc]
    exact z'
  refine ⟨e, qO, he, hsq1, hsq2, hqO, ⟨z'', ?_⟩, epi_of_epi c.hom qO⟩
  refine (ShortComplex.exact_iff_of_iso ?_).mp hex'
  exact ShortComplex.isoMk (Iso.refl _) c (Iso.refl _) (by simp [c]) (by simp [c])

end AlgebraicGeometry.Scheme.Hom
