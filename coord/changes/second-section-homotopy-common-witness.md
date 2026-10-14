# AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.second_section_homotopy_of_counit

## Reason

Review point 4: the arbitrary-q implication is false. For f:P¹_k→Spec(k), F=O(-2),
J=0, K=f_*I, l=id, β=0 and q=0, all hypotheses hold but the claimed homotopy
would annihilate the nonzero H¹. Tags 013P and 013S instead construct a common q
from a sheaf-level lift k and its lifting homotopy. The corrected theorem records
this existential construction uniformly in a: q is chosen before a, and its second
homotopy holds for every a satisfying ha. This generalization in place repairs
the duplicate of the core theorem identified by import_prune_check.py.
Importing Core back into Parts would create an import cycle.
The second reader has proved the corrected theorem completely from the common lift;
no remaining sorry restates the core conclusion.
No target or definition changes. The first theorem stays proved with its original signature.

## Old

```lean
theorem second_section_homotopy_of_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op)
    (q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
        (standardAbelianResolution X F).cocomplex)
    (hq : Nonempty (Homotopy
      (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
      (counitSectionMap f F J))) :
    Nonempty (Homotopy
      ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
        (forgottenResolutionMap X I)))
```

## New

```lean
theorem second_section_homotopy_of_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      ∀ (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
          ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
            (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
        (_ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
          (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op),
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I)))
```

## Users

`tools/downstream.py ... --uses second_section_homotopy_of_counit` finds exactly
these two textual users (the declaration itself and the core assembly).
All other transitive importers use an unchanged interface and require no edits.
There are no DAG citers in the base: no stmt_deps or proof_deps lists the second node.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts | F1 | Correct the second statement and construction docstring; the first signature and proof remain unchanged. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCore | unclaimed | Forced proof-only adaptation at lines 71–73: obtain q, hq, hr before a, then return q, hq, hr a ha. All existing signatures, visibility and imports stay identical. |

The original caller compiled against the base but fails against the corrected dependency
at line 73: `Function expected at second_section_homotopy_of_counit f I J K l hl β hβ a ha`.
Its type is now existential before a is supplied, and the old code applies it to a, ha, q and hq.
The adapted caller extracts the uniform witness and specializes its second homotopy to a and ha.

## Status

landed 20261014T071232-L-3199125 2026-10-14 (merge of deliver/F1/Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts)
