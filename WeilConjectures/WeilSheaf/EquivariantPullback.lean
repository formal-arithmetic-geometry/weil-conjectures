/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.ConstantExtension
public import WeilConjectures.WeilSheaf.FrobeniusTwist
public import WeilConjectures.WeilSheaf.UpperStarExact

/-!
# Pulling Weil sheaves back to a scheme over a finite extension

Let `k₀ ⊆ L` be finite fields, `[L : k₀] = N`, let `X₀` be a `k₀`-scheme with geometric fiber `X̄`
and geometric Galois Frobenius `Fr`, and let `Y` be an `L`-scheme with geometric fiber `Ȳ` and
geometric Galois Frobenius `Fr_Y`. A morphism `j : Ȳ ⟶ X̄` with `j ≫ Fr^N = Fr_Y ≫ j` (for
instance the base change of an `L`-scheme `Y ⊆ X₀ ⊗ L`, such as a curve defined over `L`) carries
a Weil sheaf `F` on `X₀`, through the iterated Weil structure `φ_N : (Fr^N)^* F̄ ≅ F̄`, to a Weil
sheaf on `Y` over `L` with underlying sheaf `j^* F̄`
(`AlgebraicGeometry.WeilSheaf.curvePullback`). The same applies to a subsheaf `P ⊆ F̄` which is
only defined over `L`, i.e. fixed by the `N`-th iterate of the Frobenius twist
(`AlgebraicGeometry.WeilSheaf.curvePullbackSub`).

This is how the blueprint restricts a Weil sheaf and its geometric constituents to a curve which is
only defined over a finite constant extension (`thm-zl-real-mixed-by-curves`,
`lem-zl-curve-testing-irreducibility`). The stalks of the pullback at a geometric point `s'` of
`Ȳ` are those of `F` at the corresponding geometric point `s` of `X̄`, with the Frobenius relative
to `𝔽_{q^{N n}}` (`AlgebraicGeometry.WeilSheaf.exists_equiv_stalkAt_curvePullback`).

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.equivariantPullback`: the pullback along `j` of sheaves
  with a structure `g^* A ≅ A` for an automorphism `g` with `j ≫ g = Fr_Y ≫ j`.
- `AlgebraicGeometry.WeilSheaf.curvePullback`: the pullback `WeilSheaf k₀ l X₀ ⥤ WeilSheaf L l Y`.
- `AlgebraicGeometry.WeilSheaf.curvePullbackSub`: the pullback of a subsheaf defined over `L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime]

section Equivariant

variable {L : Type u} [Field L] [Finite L] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))]
  {Z : Scheme.{u}} (g : Aut Z) (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ Z)
  (hj : j ≫ g.hom = (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.hom ≫ j)

/-- The exchange isomorphism `j^* ∘ Fr_Y^* ≅ g^* ∘ j^*` of pullbacks of `ℓ`-adic sheaves, from
`Fr_Y ≫ j = j ≫ g`, with the pullbacks along automorphisms realized as pushforwards along their
inverses. -/
noncomputable def adicUpperStarCompFrobeniusIsoOfComm :
    (j)^*ᵃ[l] ⋙ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.inv)_*ᵃ[l] ≅
      (g.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _
      (adicUpperStarIsoLowerStarInv l (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l hj.symm ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g) _

/-- The pullback along `j : Ȳ ⟶ Z` of `ℓ`-adic sheaves `A` on `Z` with a structure
`g^* A ≅ A`, for an automorphism `g` of `Z` with `j ≫ g = Fr_Y ≫ j`: the sheaf `j^* A` with the
Weil structure `Fr_Y^* j^* A ≅ j^* g^* A ≅ j^* A`. -/
noncomputable def ProEtaleWeilSheaf.equivariantPullback :
    IsoAlgebra ((g.inv)_*ᵃ[l]) ⥤ ProEtaleWeilSheaf L l Y :=
  IsoAlgebra.mapOfNatIso (adicUpperStarCompFrobeniusIsoOfComm g j hj)

end Equivariant

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))] {N : ℕ}
  (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
    (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.hom ≫ j)

/-- The pullback of Weil sheaves along `j : Ȳ ⟶ X̄` with `j ≫ Fr^N = Fr_Y ≫ j`: the pullback
`j^* F̄` with the Weil structure induced by the iterated Weil structure `φ_N` of `F`. -/
noncomputable def curvePullback : WeilSheaf k₀ l X ⥤ WeilSheaf L l Y where
  obj F := ⟨(ProEtaleWeilSheaf.equivariantPullback _ j hj).obj (F.powIsoAlgebra N),
    F.isAdicConstructibleSheaf_carrier.upperStar j⟩
  map φ := ObjectProperty.homMk ((ProEtaleWeilSheaf.equivariantPullback _ j hj).map
    (ObjectProperty.homMk ⟨φ.hom.hom.f, frobeniusPowIso_hom_naturality φ N⟩))
  map_id _ := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((j)^*ᵃ[l].map_id _)))
  map_comp _ _ := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((j)^*ᵃ[l].map_comp _ _)))

@[simp]
lemma curvePullback_obj_obj_carrier (F : WeilSheaf k₀ l X) :
    ((curvePullback j hj).obj F).obj.carrier = (j)^*ᵃ[l].obj F.obj.carrier :=
  rfl

variable (k₀ l X N) in
/-- The underlying sheaves of Weil sheaves with their iterated Weil structures `φ_N`, as algebras
for the `N`-th Frobenius pullback. -/
noncomputable def powIsoAlgebraFunctor :
    WeilSheaf k₀ l X ⥤
      IsoAlgebra ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).inv)_*ᵃ[l]) where
  obj F := F.powIsoAlgebra N
  map {F G} φ := ObjectProperty.homMk ⟨φ.hom.hom.f, frobeniusPowIso_hom_naturality φ N⟩

/-- The curve pullback, viewed in pro-étale Weil sheaves, is the iterated Weil structure followed
by the equivariant pullback. -/
noncomputable def curvePullbackCompιIso :
    curvePullback (l := l) j hj ⋙ (WeilSheaf.objectProperty L l Y).ι ≅
      powIsoAlgebraFunctor l k₀ X N ⋙ ProEtaleWeilSheaf.equivariantPullback _ j hj :=
  NatIso.ofComponents (fun F ↦ Iso.refl ((ProEtaleWeilSheaf.equivariantPullback _ j hj).obj
    (F.powIsoAlgebra N))) fun _ ↦
    sorry

/-- The underlying sheaf of the iterated Weil structure is the underlying sheaf. -/
noncomputable def powIsoAlgebraFunctorCompForgetIso :
    powIsoAlgebraFunctor l k₀ X N ⋙ IsoAlgebra.forget _ ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ IsoAlgebra.forget _ :=
  Iso.refl _

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (powIsoAlgebraFunctor l k₀ X N) := by
  have : PreservesFiniteLimits (powIsoAlgebraFunctor l k₀ X N ⋙ IsoAlgebra.forget _) :=
    preservesFiniteLimits_of_natIso (powIsoAlgebraFunctorCompForgetIso (N := N)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteColimits (powIsoAlgebraFunctor l k₀ X N) := by
  have : PreservesFiniteColimits (powIsoAlgebraFunctor l k₀ X N ⋙ IsoAlgebra.forget _) :=
    preservesFiniteColimits_of_natIso (powIsoAlgebraFunctorCompForgetIso (N := N)).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

instance : (curvePullback (l := l) j hj).Additive where
  map_add := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((j)^*ᵃ[l].map_add)))

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (curvePullback (l := l) j hj) := by
  have : PreservesFiniteLimits (curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) :=
    preservesFiniteLimits_of_natIso (curvePullbackCompιIso j hj).symm
  have : ReflectsLimitsOfSize.{0, 0} (WeilSheaf.objectProperty L l Y).ι := inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty L l Y).ι

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteColimits (curvePullback (l := l) j hj) := by
  have : PreservesFiniteColimits (curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) :=
    preservesFiniteColimits_of_natIso (curvePullbackCompιIso j hj).symm
  have : ReflectsColimitsOfSize.{0, 0} (WeilSheaf.objectProperty L l Y).ι := inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty L l Y).ι

/-- The pullback of a lisse Weil sheaf is lisse. -/
theorem IsLisse.curvePullback {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    ((WeilSheaf.curvePullback j hj).obj F).IsLisse :=
  IsAdicLisseSheaf.upperStar j hF

/-- The pullback along `j` of a lisse subsheaf `P ⊆ F̄` fixed by the `N`-th iterate of the
Frobenius twist: a lisse Weil sheaf on `Y` over `L`, with underlying sheaf `j^* P`. -/
noncomputable def curvePullbackSub (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    WeilSheaf L l Y :=
  ⟨(ProEtaleWeilSheaf.equivariantPullback _ j hj).obj (F.stableIsoAlgebra P hP),
    hPl.isAdicConstructibleSheaf.upperStar j⟩

/-- The inclusion `j^* P ⟶ j^* F̄` of the pullback of a subsheaf defined over `L`. -/
noncomputable def curvePullbackSubι (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    curvePullbackSub j hj F P hP hPl ⟶ (curvePullback j hj).obj F :=
  ObjectProperty.homMk ((ProEtaleWeilSheaf.equivariantPullback _ j hj).map
    (F.stableIsoAlgebraι P hP))

instance (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    Mono (curvePullbackSubι j hj F P hP hPl) := by
  sorry

/-- The pullback of a subsheaf defined over `L` is lisse. -/
theorem isLisse_curvePullbackSub (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    (curvePullbackSub j hj F P hP hPl).IsLisse :=
  IsAdicLisseSheaf.upperStar j hPl

/-- If the pullback `j^* P` is an irreducible local system, then the Weil sheaf
`curvePullbackSub j hj F P` is irreducible lisse. -/
theorem isIrreducibleLisse_curvePullbackSub (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P))
    (hirr : IsIrreducibleAdicLocalSystem ((j)^*ᵃ[l].obj (Subobject.underlying.obj P))) :
    (curvePullbackSub j hj F P hP hPl).IsIrreducibleLisse := by
  sorry

/-- If finitely many subsheaves defined over `L` span `F̄` and the pullback of each is punctually
`ι`-pure of weight `w`, so is the pullback of `F`: it is a quotient of their direct sum. -/
theorem isPunctuallyPureOfWeight_curvePullback_of_iSup_eq_top
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))] (F : WeilSheaf k₀ l X) {M : ℕ}
    (Q : Fin M → Subobject F.obj.carrier) (hQ : (Finset.univ : Finset (Fin M)).sup Q = ⊤)
    (hQN : ∀ n, (⇑F.frobeniusTwist)^[N] (Q n) = Q n)
    (hQl : ∀ n, IsAdicLisseSheaf (Subobject.underlying.obj (Q n))) {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (hpure : ∀ n, (curvePullbackSub j hj F (Q n) (hQN n) (hQl n)).IsPunctuallyPureOfWeight ι w) :
    ((curvePullback j hj).obj F).IsPunctuallyPureOfWeight ι w := by
  sorry

variable [Algebra k₀ L] (hN : N = Module.finrank k₀ L)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L)

include hN in
/-- **Stalks of the pullback.** Let `s'` be a geometric point of `Ȳ` fixed by `Fr_Yⁿ` up to
reparametrisation, lying over the geometric point `s` of `X̄` through `j` and the identification
`Spec θ : Spec k̄_L ≅ Spec k̄₀`. Then `s` is fixed by `Fr^{N n}` up to reparametrisation, and the
stalk of `curvePullback j hj F` at `s'`, with its Frobenius relative to `L_n`, is the stalk of `F`
at `s` with its Frobenius relative to `𝔽_{q^{N n}}`; the isomorphism carries the stalk of the
pullback of a subsheaf `P` defined over `L` onto the stalk `P_s`. -/
theorem exists_equiv_stalkAt_curvePullback (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hss' : s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫ s) {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius L ^ n).hom ≫ s') :
    ∃ (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * n)).hom =
        (specGeometricFrobenius k₀ ^ (N * n)).hom ≫ s)
      (e : (((curvePullback j hj).obj F).stalkAt s' n hs').Equiv (F.stalkAt s (N * n) hs)),
      ∀ (P : Subobject F.obj.carrier) (hP : (⇑F.frobeniusTwist)^[N] P = P)
        (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)),
        (LinearMap.range (stalkAtMap s' n hs' (curvePullbackSubι j hj F P hP hPl))).map
            e.toLinearEquiv.toLinearMap =
          F.stalkSubspace s P := by
  sorry

include hN in
/-- The pullback of an `ι`-real Weil sheaf is `ι`-real: at a closed point of `Y` of degree `n`
over `L`, the local Frobenius of the pullback is, up to conjugation, a power of the local
Frobenius of `F` at the image point. -/
theorem IsReal.curvePullback [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))] {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    ((WeilSheaf.curvePullback j hj).obj F).IsReal ι := by
  sorry

end WeilSheaf

end AlgebraicGeometry
