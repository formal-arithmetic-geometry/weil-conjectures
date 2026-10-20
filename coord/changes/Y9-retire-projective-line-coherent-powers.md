# AlgebraicGeometry.projectiveLine_twist_coherent_powers

## Reason

The Sheaf module duplicates a proved source-library declaration with the same name.
The source declaration is stronger: it does not require the unused pointwise multiplication
hypothesis. All consumers already import the source module; there is no direct or transitive
importer of the Sheaf module. Withdraw the unused duplicate and attach its DAG node to the
source declaration. No source-library file, target statement, definition or instance changes.

## Old

Module: Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers.

```lean
theorem projectiveLine_twist_coherent_powers (k : Type u) [Field k]
    (μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m))
    (hmul : (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x))) :
    (∃ (ePos : ∀ a : ℕ,
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a : ℤ))
        (eNeg : ∀ a : ℕ,
          (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-(a : ℤ))),
        (ePos 0).hom =
            Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                (SetLike.GradedOne.one_mem (A := MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫
              eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by norm_num)) ∧
        ePos 0 = eNeg 0 ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (ePos a).hom ▷ _ ≫ μ (a : ℤ) 1 =
            (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega))) ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
                eqToHom (congrArg
                  (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega)) =
            (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫
              (α_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1))
                ((dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                  a)).inv ≫
              dualEvaluation (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1) ▷
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≫
              (λ_ _).hom ≫ (eNeg a).hom))
```

## New

The Sheaf module is withdrawn via deleted.txt. The node uses the existing declaration in
WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers:

```lean
theorem projectiveLine_twist_coherent_powers (k : Type u) [Field k]
    (μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) :
    (∃ (ePos : ∀ a : ℕ,
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a : ℤ))
        (eNeg : ∀ a : ℕ,
          (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-(a : ℤ))),
        (ePos 0).hom =
            Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                (SetLike.GradedOne.one_mem (A := MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫
              eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by norm_num)) ∧
        ePos 0 = eNeg 0 ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (ePos a).hom ▷ _ ≫ μ (a : ℤ) 1 =
            (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega))) ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
                eqToHom (congrArg
                  (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega)) =
            (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫
              (α_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1))
                ((dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                  a)).inv ≫
              dualEvaluation (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1) ▷
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≫
              (λ_ _).hom ≫ (eNeg a).hom))
```

The old statement follows by applying this theorem to k, μ and hiso; hmul is unused.
A sandbox verification compiles that exact specialization and prints only propext,
Classical.choice and Quot.sound for both the source theorem and the specialization.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers | Y9 | Withdrawn duplicate; zero holes. |
| (no downstream modules) | none | No importer or declaration consumer requires adaptation. |

The existing source consumer WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistMultiplication
already imports the source module and calls the source theorem with k, μ and hiso.
WeilConjectures.lean also already re-exports the source module. Both stay verbatim.

## Status

landed 20261020T145553-L-2414203 2026-10-20 (merge of deliver/Y9/Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers)
