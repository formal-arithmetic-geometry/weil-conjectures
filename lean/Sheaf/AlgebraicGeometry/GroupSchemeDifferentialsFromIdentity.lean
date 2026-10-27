module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-! # Group-scheme differentials from the identity

Source: Stacks Project, groupoids.tex, Tag 047I,
`lemma-group-scheme-module-differentials`
(blueprint: lem-sfb-group-scheme-differentials-from-identity).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Opposite
open CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The section `(e f, id)` used to restrict the shearing comparison.
Source: Stacks, Tag 047I (blueprint: lem-sfb-group-scheme-differentials-from-identity). -/
noncomputable def groupDifferentialsIdentitySection {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G] :
    G.left ⟶ (G ⊗ G).left :=
  (lift (toUnit G ≫ MonObj.one (X := G)) (𝟙 G)).left

/-- Pull a specified comparison `m*Ω ≅ p₀*Ω` back along `(e f, id)`.
All coherence maps are the section-normalized ordinary tensor-pullback comparisons.
Source: Stacks, Tag 047I (blueprint: lem-sfb-group-scheme-differentials-from-identity). -/
noncomputable def groupDifferentialsIdentityComparison {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G]
    (a : (Scheme.Modules.tensorPullback (MonObj.mul (X := G)).left).obj
        G.hom.relativeDifferentials ≅
      (Scheme.Modules.tensorPullback (pullback.fst G.hom G.hom)).obj
        G.hom.relativeDifferentials) :
    G.hom.relativeDifferentials ≅ (Scheme.Modules.tensorPullback G.hom).obj
      ((Scheme.Modules.tensorPullback (MonObj.one (X := G)).left).obj
        G.hom.relativeDifferentials) :=
  ((Scheme.Modules.tensorPullbackSectionId G.left).app G.hom.relativeDifferentials).symm ≪≫
    eqToIso (congrArg
      (fun h ↦ (Scheme.Modules.tensorPullback h).obj G.hom.relativeDifferentials)
      (congrArg (fun h : G ⟶ G ↦ h.left) (MonObj.lift_comp_one_left (toUnit G) (𝟙 G))).symm) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp (groupDifferentialsIdentitySection G)
      (MonObj.mul (X := G)).left).app G.hom.relativeDifferentials ≪≫
    (Scheme.Modules.tensorPullback (groupDifferentialsIdentitySection G)).mapIso a ≪≫
    ((Scheme.Modules.tensorPullbackSectionComp (groupDifferentialsIdentitySection G)
      (pullback.fst G.hom G.hom)).app G.hom.relativeDifferentials).symm ≪≫
    eqToIso (congrArg
      (fun h ↦ (Scheme.Modules.tensorPullback h).obj G.hom.relativeDifferentials)
      (congrArg (fun h : G ⟶ G ↦ h.left)
        (lift_fst (toUnit G ≫ MonObj.one (X := G)) (𝟙 G)))) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp G.hom (MonObj.one (X := G)).left).app
      G.hom.relativeDifferentials

/-- The canonical isomorphism `Ω¹_{G/K} ≅ f* e* Ω¹_{G/K}`.
The two local formulas specify the base-change map `c` and shearing comparison `a`;
the last equality fixes the isomorphism to their pullback along `(e f, id)`.
There are no finiteness, smoothness, reducedness, commutativity or characteristic hypotheses.

Source: Stacks Project, groupoids.tex, Tag 047I,
`lemma-group-scheme-module-differentials`.
(blueprint: lem-sfb-group-scheme-differentials-from-identity).

Proof:
1. On `P = G ×_K G`, the shearing map `(g,h) ↦ (gh,h)` has inverse
   `(g,h) ↦ (g h⁻¹,h)`. The group diagrams and the fibre-product universal
   property (def-sc-group-scheme, def-pc-fibre-product) prove both inverse
   identities and show that both maps preserve the second projection.
2. Apply lem-trf-relative-differential-sheaf-base-change to the square defining
   `P` to obtain `c : p₀*Ω ≅ Ω_{P/G}`, with the first displayed local formula.
3. The shearing automorphism over the second G gives a cartesian square with
   bottom map the identity. The same base-change theorem gives its differential
   isomorphism, sending `1 ⊗ dz` to `d(τ♯z)`.
4. Pull back c by τ, compose with that isomorphism and c inverse, and use
   `p₀ τ = m` to get `a : m*Ω ≅ p₀*Ω`. Its normalization is the second formula.
   Both c and a are unique because differentials generate locally and tensor
   pullback is generated locally by pure tensors.
5. Pull a back by `s = (e f,id)`. Since `s m = id` and `s p₀ = f e`, the
   identity and composition comparisons of def-pc-module-pullback give exactly
   groupDifferentialsIdentityComparison. The uniqueness just noted proves
   uniqueness of the normalized final isomorphism. -/
theorem existsUnique_groupDifferentialsFromIdentity {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G] :
    ∃! φ : G.hom.relativeDifferentials ≅ (Scheme.Modules.tensorPullback G.hom).obj
        ((Scheme.Modules.tensorPullback (MonObj.one (X := G)).left).obj
          G.hom.relativeDifferentials),
      ∃ (c : (Scheme.Modules.tensorPullback (pullback.fst G.hom G.hom)).obj
            G.hom.relativeDifferentials ≅ (pullback.snd G.hom G.hom).relativeDifferentials)
        (a : (Scheme.Modules.tensorPullback (MonObj.mul (X := G)).left).obj
            G.hom.relativeDifferentials ≅
          (Scheme.Modules.tensorPullback (pullback.fst G.hom G.hom)).obj
            G.hom.relativeDifferentials),
        (∀ (U : G.left.Opens) (z : Γ(G.left, U)),
          c.hom.app ((pullback.fst G.hom G.hom) ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection (pullback.fst G.hom G.hom)
              G.hom.relativeDifferentials U
              (G.hom.relativeDifferentialsDerivation.d (X := op U) z)) =
            (pullback.snd G.hom G.hom).relativeDifferentialsDerivation.d
              (X := op ((pullback.fst G.hom G.hom) ⁻¹ᵁ U))
              ((pullback.fst G.hom G.hom).app U z)) ∧
        (∀ (U : G.left.Opens) (z : Γ(G.left, U)),
          (a.hom ≫ c.hom).app ((MonObj.mul (X := G)).left ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection (MonObj.mul (X := G)).left
              G.hom.relativeDifferentials U
              (G.hom.relativeDifferentialsDerivation.d (X := op U) z)) =
            (pullback.snd G.hom G.hom).relativeDifferentialsDerivation.d
              (X := op ((MonObj.mul (X := G)).left ⁻¹ᵁ U))
              ((MonObj.mul (X := G)).left.app U z)) ∧
        φ = groupDifferentialsIdentityComparison G a := by
  sorry

/-- The uniquely normalized isomorphism obtained by the shearing construction.
Its defining theorem determines the isomorphism, so this chooses no arbitrary
trivialization or basis.
Source: Stacks, Tag 047I (blueprint: lem-sfb-group-scheme-differentials-from-identity). -/
noncomputable def groupDifferentialsFromIdentityIso {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G] :
    G.hom.relativeDifferentials ≅ (Scheme.Modules.tensorPullback G.hom).obj
      ((Scheme.Modules.tensorPullback (MonObj.one (X := G)).left).obj
        G.hom.relativeDifferentials) :=
  Classical.choose (existsUnique_groupDifferentialsFromIdentity G)

end AlgebraicGeometry
