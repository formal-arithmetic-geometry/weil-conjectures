# CategoryTheory.TransitionIsoTransport.transport proof options

## Reason

The proof of the existing theorem uses local elaboration options and `omit` commands
to control transparency and section-variable inference. These commands are proof
implementation details, but the stage-3 preflight classifies them as changes to the
module interface and requires a change record. The theorem statement, definitions,
public imports, and declarations visible to consumers remain unchanged.

## Old

The existing public signature, verbatim, with a `sorry` proof:

```lean
theorem transport
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    (ε : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i))
    (hB : Coherent B d ε) :
    Coherent C (associator B C χ d) (unitIso B C χ ε) ∧
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (K : A i),
      (comparison B C χ hij hjk).hom.app K ≫
          (associator B C χ d hij hjk).hom.app K =
        (d hij hjk).hom.app K ≫ (χ (le_trans hij hjk)).hom.app K) ∧
    (∀ (i : I) (K : A i),
      (χ (le_refl i)).hom.app K ≫ (unitIso B C χ ε i).hom.app K = (ε i).hom.app K) ∧
    FiniteCoherent C (associator B C χ d) (unitIso B C χ ε) ∧
    ∃ (N : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
      (ρ : ∀ {i j : I} (h : i ≤ j), C h ≅ N h),
      (∀ i : I, N (le_refl i) = 𝟭 (A i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → N hij = C hij) ∧
      (∀ i : I, HEq (ρ (le_refl i)) (unitIso B C χ ε i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → HEq (ρ hij) (Iso.refl (C hij))) ∧
      Coherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      FiniteCoherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      (∀ i : I, HEq (unitIso C N ρ (unitIso B C χ ε) i) (Iso.refl (𝟭 (A i)))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) (le_refl i) hij)
          (Functor.leftUnitor (N hij))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) hij (le_refl j))
          (Functor.rightUnitor (N hij)))
```

## New

The same public signature, verbatim, now with a complete proof:

```lean
theorem transport
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    (ε : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i))
    (hB : Coherent B d ε) :
    Coherent C (associator B C χ d) (unitIso B C χ ε) ∧
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (K : A i),
      (comparison B C χ hij hjk).hom.app K ≫
          (associator B C χ d hij hjk).hom.app K =
        (d hij hjk).hom.app K ≫ (χ (le_trans hij hjk)).hom.app K) ∧
    (∀ (i : I) (K : A i),
      (χ (le_refl i)).hom.app K ≫ (unitIso B C χ ε i).hom.app K = (ε i).hom.app K) ∧
    FiniteCoherent C (associator B C χ d) (unitIso B C χ ε) ∧
    ∃ (N : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
      (ρ : ∀ {i j : I} (h : i ≤ j), C h ≅ N h),
      (∀ i : I, N (le_refl i) = 𝟭 (A i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → N hij = C hij) ∧
      (∀ i : I, HEq (ρ (le_refl i)) (unitIso B C χ ε i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → HEq (ρ hij) (Iso.refl (C hij))) ∧
      Coherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      FiniteCoherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      (∀ i : I, HEq (unitIso C N ρ (unitIso B C χ ε) i) (Iso.refl (𝟭 (A i)))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) (le_refl i) hij)
          (Functor.leftUnitor (N hij))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) hij (le_refl j))
          (Functor.rightUnitor (N hij)))
```

The new private proof helpers use the following file-local elaboration options:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Each of the private helper declarations `normalized_unit`, `normalized_left`,
and `normalized_right` is preceded by `omit [Preorder I] in`. This removes an
unused section assumption from those private signatures only. These options and
commands do not propagate through imports or modify any public declaration.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.TransitionTwistEvaluationIsoTransport | unclaimed | Its public import and use of `CategoryTheory.TransitionIsoTransport.transport` are unchanged; it compiles against the completed proof. |

## Status

landed 20261023T103428-L-3136948 2026-10-23 (merge of deliver/W3/Sheaf.CategoryTheory.TransitionAssociatorIsoTransport)
