## What changed

Repaired `HomologicalComplex₂.tensorBicomplex` and
`HomologicalComplex₂.tensorBicomplexMap` to be `abbrev`s of Mathlib's
`Functor.mapBifunctorHomologicalComplex` construction and its map. Added the
required `Mathlib.Algebra.Homology.Bifunctor` public import. `chainTensorMap`
was retained unchanged. The change record is
`coord/changes/tensor-bicomplex.md`.

## Proved and sorry left

All declarations in `Sheaf.Algebra.Homology.TensorBicomplex` remain closed:
`HomologicalComplex₂.tensorBicomplex`, `HomologicalComplex₂.tensorBicomplexMap`, and
`HomologicalComplex₂.chainTensorMap`. No `sorry` remains and no new holes were added. Holes closed: none (the baseline
module already had zero holes). Holes added: none. This is the upstream #1424
canonical-definition repair, not a net proof gain.

## No longer needed

Removed the redundant direct public import `Mathlib.Algebra.Homology.HomologicalBicomplex`;
`Mathlib.Algebra.Homology.Bifunctor` already publicly imports it through TotalComplex.
No project module or DAG dependency is pruned: both old proof dependencies,
`def-weil-pbc-chain-complex-tensor-module` and `def-weil-pbc-module-tensor-product`,
remain used by the canonical tensor construction and chainTensorMap.

## Where the brief, the DAG or earlier work was wrong

The earlier module duplicated Mathlib's canonical tensor bicomplex and map,
as identified by upstream review #1424. The prior report incorrectly treated
the duplicate as a no-op; this delivery replaces it with the canonical
construction and records the public interface change.

## Earlier second reading (a previous round; superseded)

The canonical Mathlib objects have exactly the required tensor terms and
differentials, and the bifunctor map has the same source and target as the
old declarations. The unit route is preserved while removing duplicate
implementation data. All three declarations compile with no `sorry`.


## Second reading by N2

1. Compared every delivered module with the repository. Verdict: unchanged types,
binders and visibility; only the two recorded def-to-abbrev/body changes and the
canonical-construction import are public interface changes. chainTensorMap is
byte-for-byte unchanged. Adapted files change only forced proof lines.
2. Compiled the module and all four direct users against a sandbox overlay.
The row/column cokernel modules and FlatResolutionTorComparison needed forced
adaptations; TorSymmetry compiles unchanged and is not delivered. Verdict: no
errors or warnings after repair, no sorry or prohibited declaration in the item.
Scratch #print axioms for all three item declarations reports only propext,
Classical.choice and Quot.sound. No arbitrary existence witness is introduced.
3. No statement was split off and no new node is added. Verdict: no restatement,
no new hole. Scratch examples verify terms, both unsigned differentials and map
components in arbitrary degrees, so zero and nonadjacent degrees are included.
4. Read Mathlib's Bifunctor construction and the upstream duplicate review.
Verdict: the existing canonical construction is the shorter route; removed the
redundant direct HomologicalBicomplex import. Both old DAG dependencies remain
used. The item is a tool below sk-thm-p1's realized statement/steps; none of the
unit's realized nodes or its route is bypassed.
5. Read the node and unit records. Verdict after repair: proof, proof_deps,
proof_origin and lean.statement agree with the canonical construction; the
original mathematical statement and unit are unchanged.

Second reading changed: three forced downstream proof adaptations, removal of
a redundant import, correction of the stale DAG construction description, and
completion of the change record with verbatim old/new declarations. Corrected
the progress report: zero holes closed, zero holes added. Change record:
coord/changes/tensor-bicomplex.md.

## Forced adaptations

### Sheaf.Algebra.Homology.FlatResolutionTorComparison
Original against changed dependencies failed:
```
p).f q,
                    g := (A.d p (p - 1)).f q, zero := ⋯ }.Exact) ∧
            ∀ (p q : ℕ),
              0 < q →
                { X₁ := (A.X p).X (q + 1), X₂ := (A.X p).X q, X₃ := (A.X p).X (q - 1), f := (A.X p).d (q + 1) q,
                    g := (A.X p).d q (q - 1), zero := ⋯ }.Exact)
        A →
      (n : ℕ) → (HomologicalComplex.opcycles A.flip 0).homology n ≅ (HomologicalComplex.opcycles A 0).homology n
h✝ :
  ∀ (A B : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hA :
      (fun A ↦
          (∀ (p q : ℕ),
              0 < p →
                { X₁ := (A.X (p + 1)).X q, X₂ := (A.X p).X q, X₃ := (A.X (p - 1)).X q, f := (A.d (p + 1) p).f q,
                    g := (A.d p (p - 1)).f q, zero := ⋯ }.Exact) ∧
            ∀ (p q : ℕ),
              0 < q →
                { X₁ := (A.X p).X (q + 1), X₂ := (A.X p).X q, X₃ := (A.X p).X (q - 1), f := (A.X p).d (q + 1) q,
                    g := (A.X p).d q (q - 1), zero := ⋯ }.Exact)
        A)
    (hB :
      (fun A ↦
          (∀ (p q : ℕ),
              0 < p →
                { X₁ := (A.X (p + 1)).X q, X₂ := (A.X p).X q, X₃ := (A.X (p - 1)).X q, f := (A.d (p + 1) p).f q,
                    g := (A.d p (p - 1)).f q, zero := ⋯ }.Exact) ∧
            ∀ (p q : ℕ),
              0 < q →
                { X₁ := (A.X p).X (q + 1), X₂ := (A.X p).X q, X₃ := (A.X p).X (q - 1), f := (A.X p).d (q + 1) q,
                    g := (A.X p).d q (q - 1), zero := ⋯ }.Exact)
        B)
    (Φ : A ⟶ B) (n : ℕ),
    (θ A hA n).hom ≫ HomologicalComplex.homologyMap (HomologicalComplex.opcyclesMap Φ 0) n =
      HomologicalComplex.homologyMap
          (HomologicalComplex.opcyclesMap
            ((HomologicalComplex₂.flipFunctor (ModuleCat R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map Φ) 0)
          n ≫
        (θ B hB n).hom
p q : ℕ
⊢ F.X p ◁ Q.complex.d (q + 1) q ≫ F.X p ◁ Q.complex.d q (q - 1) = 0

(with the modules compiled into /tmp/forced-adaptation-0aeuqlw_/.lbuild) [3.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso
Original against changed dependencies failed:
```
oduleCat R)).mapBifunctorHomologicalComplex (ComplexShape.down ℕ)
                              (ComplexShape.down ℕ)).map
                          a).app
                      Q.complex).f
                  p).f
              0 ≫
            (((((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex (ComplexShape.down ℕ)
                              (ComplexShape.down ℕ)).obj
                          P'.complex).map
                      b).f
                  p).f
              0) ≫
          (𝟙 (P'.complex.X p) ⊗ₘ Q'.π.f 0)))
      x✝
/tmp/forced-adaptation-pmywqpem/lean/Sheaf/Algebra/Homology/TensorResolutionColumnCokernelIso.lean:121:85: warning: This simp argument is unused:
  homMk_f_f

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, columnAugmentation, chainTensorMap, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id,
    tensorBicomplexMap, flipFunctor_map_f_f, Functor.flip_map_app, curriedTensor_obj_map, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hb]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-pmywqpem/lean/Sheaf/Algebra/Homology/TensorResolutionColumnCokernelIso.lean:123:66: warning: This simp argument is unused:
  hb

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, columnAugmentation, chainTensorMap, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id,
    tensorBicomplexMap, homMk_f_f, flipFunctor_map_f_f, Functor.flip_map_app, curriedTensor_obj_map, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

(with the modules compiled into /tmp/forced-adaptation-pmywqpem/.lbuild) [2.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso
Original against changed dependencies failed:
```
:64:42: warning: This simp argument is unused:
  tensorHom_comp_tensorHom

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, rowAugmentation, tensorBicomplex, ofGradedObject_d_f, ← Category.assoc,
    Category.comp_id, ProjectiveResolution.complex_d_comp_π_f_zero, HomologicalComplex.zero_f]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-hxksduq8/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:65:4: warning: This simp argument is unused:
  Category.comp_id

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, rowAugmentation, tensorBicomplex, ofGradedObject_d_f, ← Category.assoc,
    tensorHom_comp_tensorHom, ProjectiveResolution.complex_d_comp_π_f_zero, HomologicalComplex.zero_f]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-hxksduq8/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:65:22: warning: This simp argument is unused:
  ProjectiveResolution.complex_d_comp_π_f_zero

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, rowAugmentation, tensorBicomplex, ofGradedObject_d_f, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, HomologicalComplex.zero_f]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-hxksduq8/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:144:2: error: 'change' tactic failed, pattern
  ((P.π.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom) ≫ (b.f q ⊗ₘ 𝟙 M) ≫ (𝟙 (Q'.complex.X q) ⊗ₘ f) =
    (a.f 0 ⊗ₘ b.f q) ≫ (P'.π.f 0 ⊗ₘ 𝟙 (Q'.complex.X q)) ≫ (β_ M' (Q'.complex.X q)).hom
is not definitionally equal to target
  (rowAugmentation P Q ≫ chainTensorMap b f).f q = ((tensorBicomplexMap a b).f 0 ≫ rowAugmentation P' Q').f q

(with the modules compiled into /tmp/forced-adaptation-hxksduq8/.lbuild) [3.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
