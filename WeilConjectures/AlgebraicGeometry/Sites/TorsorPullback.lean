/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta

/-!
# Pullback of torsors and of their classes in `H¹`

Let `g : X ⟶ Y` be a morphism of schemes, `G` an abelian sheaf on the small étale site of `Y`,
`G'` one on the small étale site of `X` and `φ : G ⟶ g_* G'` a morphism, with transpose
`φ^♭ : g^* G ⟶ G'`. Let `P` be a `G`-torsor and `P'` a `G'`-torsor, and suppose given maps
`σ : P(V) → P'(V ×_Y X)`, natural in the étale `Y`-scheme `V` and equivariant along `φ`. Then the
class of `P'` in `H¹(X, G')` is the image of the class of `P` under the pullback map

`H¹(Y, G) ⟶ H¹(X, g^* G) ⟶ H¹(X, G')`

(`AlgebraicGeometry.Etale.classH1_eq_map_cohomologyMap_of_equivariant`). In other words `P'` is
the torsor obtained from `P` by pullback along `g` and extension of the structure group along
`φ^♭`.

Writing `P` and `P'` as torsors of local lifts of global sections `s` and `s'` for injective
resolutions `0 → G → I → Q → 0` and `0 → G' → I' → Q' → 0`, the pullback map sends the class
`δ(s)` to `δ'(ψ(g^* s))` for a morphism of short exact sequences
`(φ^♭, χ, ψ) : g^* (0 → G → I → Q → 0) ⟶ (0 → G' → I' → Q' → 0)`. The local differences
`b'(σ x) - χ(g^* (b x))` of the lifts of `σ x` and of `x` are invariant, hence glue to a global
section `c` of `I'` with `d' c = s' - ψ(g^* s)`.

We also record that the classes of torsors, the connecting homomorphisms and the degree-zero
identification `H⁰(G) ≅ G(T)` do not depend on the choice of the terminal object `T` of the site.

## Main statements

- `CategoryTheory.Sheaf.Torsor.classH1_congr`: the class of a torsor does not depend on the
  terminal object.
- `AlgebraicGeometry.Etale.equiv₀_cohomologyMap`: in degree zero the pullback map is the
  pullback of global sections along the unit of `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.classH1_eq_map_cohomologyMap_of_equivariant`: compatibility of the
  pullback map on `H¹` with the pullback of torsors.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The unit of the constant sheaf adjunction at a terminal object `T`, evaluated at `1`, is
compatible with the restriction to any other terminal object `T'`. -/
lemma constantHomEquiv_id_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') :
    constantHomEquiv hT' _ (𝟙 ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ)))) =
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))).obj.map
        (hT.from T').op (constantHomEquiv hT _ (𝟙 _)) := by
  simp only [constantHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    Adjunction.homEquiv_unit, Functor.map_id, Category.comp_id]
  simp only [constantSheafAdj, Adjunction.comp_unit_app]
  sorry

/-- Morphisms out of the constant sheaf `ℤ` are global sections, compatibly with the change of
the terminal object. -/
lemma constantHomEquiv_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w})
    (f : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    constantHomEquiv hT' F f = F.obj.map (hT.from T').op (constantHomEquiv hT F f) := by
  rw [← constantHomEquiv_naturality hT f, ← constantHomEquiv_id_congr hT hT',
    ← constantHomEquiv_comp, Category.id_comp]

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The identification `H⁰(F) ≅ F(T)` is compatible with the change of the terminal object. -/
lemma H.equiv₀_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w}) (x : H F 0) :
    H.equiv₀ F hT' x = F.obj.map (hT.from T').op (H.equiv₀ F hT x) :=
  constantHomEquiv_congr hT hT' F (Ext.addEquiv₀ x)

/-- The connecting homomorphism `Γ(Q) → H¹(G)` is compatible with the change of the terminal
object. -/
lemma H.δ_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (s : S.X₃.obj.obj (op T)) :
    H.δ hS hT' (S.X₃.obj.map (hT.from T').op s) = H.δ hS hT s := by
  obtain ⟨x, rfl⟩ := (H.equiv₀ S.X₃ hT).surjective s
  rw [← H.equiv₀_congr hT hT', ← H.δSucc_zero, ← H.δSucc_zero]

namespace Torsor

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] {G : Sheaf J AddCommGrpCat.{w}}

/-- The lifting torsor of a global section does not depend on the terminal object. -/
lemma lifts_equiv_lifts_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    {I Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0}
    (hS : (ShortComplex.mk ι d w).ShortExact) (s : Q.obj.obj (op T)) :
    lifts hT hS s ≈ lifts hT' hS (Q.obj.map (hT.from T').op s) := by
  refine ⟨Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun x ↦ ⟨x.1, ?_⟩
      naturality U V f := rfl }) fun U a x ↦ rfl⟩
  change d.hom.app U x.1 = Q.obj.map (hT'.from U.unop).op (Q.obj.map (hT.from T').op s)
  rw [lifts_val hT hS x, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp]
  exact congrArg (fun f ↦ Q.obj.map f.op s) (hT.hom_ext _ _)

/-- **The class of a torsor does not depend on the terminal object.** -/
theorem classH1_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (P : Torsor G) :
    classH1 G hT' ⟦P⟧ = classH1 G hT ⟦P⟧ := by
  have hS := injectiveSequence_shortExact G
  obtain ⟨s, hs⟩ := exists_equiv_lifts hT hS P
  rw [_root_.Quotient.sound hs, classH1_lifts,
    _root_.Quotient.sound (lifts_equiv_lifts_congr hT hT' hS s), classH1_lifts]
  exact H.δ_congr hT hT' hS s

end Torsor

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Etale

open Scheme Sheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **Pullback in degree zero.** Under the identifications `H⁰(F) ≅ F(Y)` and
`H⁰(g^* F) ≅ (g^* F)(X)`, the pullback map on `H⁰` is the pullback of global sections along
the unit `F ⟶ g_* g^* F`, followed by the restriction along any morphism `X ⟶ Y ×_Y X` of
étale `X`-schemes. -/
lemma equiv₀_cohomologyMap (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : H F 0) (e : MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @Etale X) ⟶
      g.Etale.obj (MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem @Etale Y))) :
    H.equiv₀ _ (isTerminalEtale X) (cohomologyMap g F 0 x) =
      ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map e.op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app
          (op (MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem @Etale Y))) (H.equiv₀ F (isTerminalEtale Y) x)) := by
  sorry

variable {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **Pullback of torsors.** Let `g : X ⟶ Y`, `φ : G ⟶ g_* G'` a morphism of abelian sheaves,
`P` a `G`-torsor on `Y_ét` and `P'` a `G'`-torsor on `X_ét`, and let `σ : P(V) → P'(V ×_Y X)`
be maps, natural in the étale `Y`-scheme `V`, with `σ(a • x) = φ(a) • σ(x)`. Then the class of
`P'` in `H¹(X, G')` is the image of the class of `P` under the pullback map
`H¹(Y, G) ⟶ H¹(X, g^* G) ⟶ H¹(X, G')`, the second map being induced by the transpose
`g^* G ⟶ G'` of `φ`. -/
theorem classH1_eq_map_cohomologyMap_of_equivariant
    (φ : G ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj G') (P : Torsor G) (P' : Torsor G')
    (σ : ∀ U : Y.Etaleᵒᵖ, P.sheaf.obj.obj U →
      P'.sheaf.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U.unop)))
    (hσ : ∀ ⦃U V : Y.Etaleᵒᵖ⦄ (f : U ⟶ V) (x : P.sheaf.obj.obj U),
      P'.sheaf.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ g).map f.unop).op (σ U x) =
        σ V (P.sheaf.obj.map f x))
    (hσ₁ : ∀ (U : Y.Etaleᵒᵖ) (a : G.obj.obj U) (x : P.sheaf.obj.obj U),
      σ U (P.vadd U a x) = P'.vadd _ (φ.hom.app U a) (σ U x)) :
    Torsor.classH1 G' (isTerminalEtale X) ⟦P'⟧ =
      H.map (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).symm φ) 1
        (cohomologyMap g G 1 (Torsor.classH1 G (isTerminalEtale Y) ⟦P⟧)) := by
  sorry

end AlgebraicGeometry.Etale
