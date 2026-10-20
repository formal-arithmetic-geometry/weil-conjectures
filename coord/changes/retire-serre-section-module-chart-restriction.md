# AlgebraicGeometry.Proj.serreSectionModuleChartRestriction

## Reason

Retirement item from coord/retire-items.tsv, approved in
coord/changes/retire-sheaf-twins-20261020.md. The upstream twin proves the same
conclusion without the three unnecessary positivity hypotheses. Remove the
duplicate Sheaf declaration and use that proved upstream theorem in its consumer.
No upstream file or target statement changes. The node statement remains unchanged:
it is a special case of the stronger upstream signature.

## Old

In Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction:

```lean
theorem serreSectionModuleChartRestriction
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
    (alphaF : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (alphaG : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g)) →+
      LocalizedModule.Away g M)
    (hnormF : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (hnormG : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • b : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g))),
      alphaG s = mk (y : M) (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • b : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) g ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hg))
            (basicOpen (homogeneousSubmodule (Fin 2) k) g) s)
    (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) f)
    (e c : ℕ) (a : MvPolynomial (Fin 2) k)
    (he : 0 < e) (ha : a ∈ homogeneousSubmodule (Fin 2) k c) (hrel : g ^ e = a * f)
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alphaG (G.val.map (homOfLE inc).op s) =
      mk (a ^ m • (y : M)) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)
```

## New

The Sheaf module is withdrawn. Its node and consumer use the existing declaration in
WeilConjectures.AlgebraicGeometry.SerreSectionModuleChartRestriction:

```lean
theorem serreSectionModuleChartRestriction
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f g : MvPolynomial (Fin 2) k) (d b : ℕ)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
    (alphaF : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (alphaG : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g)) →+
      LocalizedModule.Away g M)
    (hnormF : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (hnormG : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • b : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g))),
      alphaG s = mk (y : M) (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • b : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) g ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hg))
            (basicOpen (homogeneousSubmodule (Fin 2) k) g) s)
    (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) f)
    (e c : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k c) (hrel : g ^ e = a * f)
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alphaG (G.val.map (homOfLE inc).op s) =
      mk (a ^ m • (y : M)) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SerreSectionModuleCharts | unclaimed | Replace the private proof import by the upstream twin; omit hd, hb and he from the restriction theorem application. All declaration signatures and other proof lines stay identical. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction | M3 | Withdraw the duplicate module. |
| Sheaf.AlgebraicGeometry.CoherentProjRepresentation | unclaimed | Transitive consumer only; does not mention the retired declaration. No edit: the public interface of SerreSectionModuleCharts is unchanged. |

tools/downstream.py lists SerreSectionModuleCharts and CoherentProjRepresentation
as downstream modules; only SerreSectionModuleCharts mentions the declaration.
The only direct consumer and the only call site were also found by searching both
Lean roots. The twin's imports are exactly the copy's imports, so this substitution does
not bring another pair of twins together. The consumer's public imports, theorem
statement and other proof dependencies remain unchanged. The DAG node keeps its
statement and proof route and now attaches to the existing upstream theorem.

## Status

landed 20261020T135416-L-1820367 2026-10-20 (merge of deliver/M3/Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction)
