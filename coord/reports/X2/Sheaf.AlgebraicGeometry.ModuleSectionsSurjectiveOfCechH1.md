## What changed

Repaired `Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1` by deleting five
private helper lemmas whose statements duplicate the established generic site theorem
module. The proof now imports `all Sheaf.CategoryTheory.SiteSesCechH1Surjective`,
which exposes and reuses those existing helpers; all call sites are unchanged. The
module-local lift lemma and the main algebraic-geometric surjectivity proof remain
unchanged.

The existing interface correction and forced adaptation remain part of this delivery:
`coord/changes/module-sections-cech-covering.md` records the covering hypothesis
and index-universe correction, and the three necessary caller lines in
`Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.module_sections_surjective_of_cech_h1_vanishing` remains
proved with no `sorry` declarations in the delivered module. No holes were added.

## No longer needed

The duplicate local declarations `site_projection_ext`, `site_cochain_congr`,
`site_d_zero_restrict`, `site_map_d`, and `site_compatible` were removed. Their
existing declarations in `Sheaf.CategoryTheory.SiteSesCechH1Surjective` are imported
with `import all` and used by the proof. No DAG node or target statement changed.

The import Mathlib.Algebra.Category.Grp.Zero and the private counterexample witnesses empty_family_cofinal and empty_family_cech_isZero were removed: the corrected covering hypothesis makes these witnesses unnecessary.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery reproduced generic site helper statements privately even though
the library already contained them. This triggered `import_prune_check.py`, which
checks private declarations as well as public ones. The repair follows the existing
`import all` reuse pattern and keeps the target statement and proof route intact.

## Earlier second reading (a previous round; superseded)

The repaired file compiles cleanly with `lcompile.py`. The generic helper names resolve
through the opened `CategoryTheory` namespace after the `import all`; no signatures,
visibility of existing declarations, or theorem statements were changed. The five
removed declarations are exactly the duplicates named by the return.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

1. **Repository comparison.** Compared both delivered modules with the read-only repository versions. Challenge.lean is unchanged. The intermediate theorem module_sections_surjective_of_cech_h1_vanishing adds hcover and changes the index universe from v to max u v, as recorded in coord/changes/module-sections-cech-covering.md. ModuleCechVanishingCriterion retains every existing signature and visibility; its only change is the three-line covering proof required by the corrected interface.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The delivered target has no `sorry`, forbidden declarations, or hollow definitions; its proof uses the existing generic site helpers.

3. **Statements and dependencies.** No new statements or nodes were added. The target statement remains exactly the DAG statement, including the covering hypothesis and universe correction. The removed private helpers duplicated declarations already provided by `Sheaf.CategoryTheory.SiteSesCechH1Surjective`.

4. **Proof route and pruning.** The proof retains the unit route through local lifts, Cech exactness, correction, and sheaf gluing. It now imports and reuses the established generic site helpers, so the five duplicate private declarations are pruned. The adapted caller line is necessary to supply the explicit covering hypothesis.

5. **DAG and report consistency.** The DAG node, proof dependencies, and realized unit route agree with the Lean proof; no node or target statement changed. The existing change record documents the forced adaptation.

Changed: removed five duplicate private helper lemmas and imported `all Sheaf.CategoryTheory.SiteSesCechH1Surjective`; retained the required caller adaptation and updated this report.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion
Original against changed dependencies failed:
```
te_products := ⋯,
    has_kernels := ⋯, has_cokernels := ⋯ }
this✝¹ : (toPresheaf X).Additive := module_cohomology_isZero_of_cech_vanishing._proof_1_10 X
T : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat := toPresheaf X
this✝ : T.Additive := module_cohomology_isZero_of_cech_vanishing._proof_1_11 X
this : PreservesLimits T := module_cohomology_isZero_of_cech_vanishing._proof_1_12 X
P : X.Modules → Prop :=
  fun G ↦
    ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens) (hom : (i : I) → V i ⟶ U),
      ⨆ i, V i = U →
        ∀ (C : SiteCechComplex V hom) (p : ℕ), 0 < p → IsZero ((C.cohomologyFunctor p).obj ((toPresheaf X).obj G))
S : ShortComplex X.Modules
hS : S.ShortExact
hG : P S.X₁
U : X.Opens
I : Type (max u ?u.249)
V : I → X.Opens
hV : ∀ (i : I), V i ≤ U
hcover : ∀ x ∈ U, ∃ i, x ∈ V i
⊢ ∃ K W, ∃ (_ : ∀ (k : K), W k ≤ U), ⨆ i, W i = U ∧ ∀ (k : K), ∃ i, W k ≤ V i
/tmp/forced-adaptation-zk56711j/lean/Sheaf/AlgebraicGeometry/ModuleCechVanishingCriterion.lean:92:75: error: unsolved goals
case hcech
X : Scheme
F : X.Modules
hcech :
  ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens) (hom : (i : I) → V i ⟶ U),
    ⨆ i, V i = U →
      ∀ (S : SiteCechComplex V hom) (p : ℕ), 0 < p → IsZero ((S.cohomologyFunctor p).obj ((toPresheaf X).obj F))
this✝⁴ : EnoughInjectives X.Modules := ⋯
this✝³ : Preadditive (TopCat.Presheaf AddCommGrpCat ↑X.toPresheafedSpace) := ⋯
this✝² : Abelian (TopCat.Presheaf AddCommGrpCat ↑X.toPresheafedSpace) := ⋯
this✝¹ : (toPresheaf X).Additive := ⋯
T : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat := ⋯
this✝ : T.Additive := ⋯
this : PreservesLimits T := ⋯
P : X.Modules → Prop := ⋯
S : ShortComplex X.Modules
hS : S.ShortExact
hG : P S.X₁
U : X.Opens
⊢ ∀ (I : Type (max u ?u.249)) (V : I → X.Opens),
    (∀ (i : I), V i ≤ U) →
      ⨆ i, V i = U →
        ∀ (f : (i : I) → V i ⟶ U) (Scech : SiteCechComplex V f),
          IsZero ((Scech.cohomologyFunctor 1).obj S.X₁.val.presheaf)

(with the modules compiled into /tmp/forced-adaptation-zk56711j/.lbuild) [14.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by X2

1. **Repository comparison.** The target proof module was compared with the repository version. The delivered theorem adds the necessary covering hypothesis and uses `Type (max u v)`, as documented in `coord/changes/module-sections-cech-covering.md`; the caller adaptation is limited to the required covering proof.

2. **Compilation and axioms.** Both delivered modules compile with `lcompile.py --all`. The target theorem has no `sorry`, forbidden declaration, or hollow definition; the remaining proof dependencies introduce no new holes.

3. **Statements and dependencies.** The corrected covering statement is mathematically required (the prior uncovered-family formulation is false). The existing generic site helper declarations are reused through `import all`; no new theorem or node is introduced.

4. **Proof route and pruning.** The proof follows local lifting, refinement, Cech correction, and sheaf gluing. Five duplicate private helpers and two obsolete empty-family witnesses were removed; no unit step is bypassed.

5. **DAG and report consistency.** The change record documents the interface correction and forced caller adaptation. The node metadata and realized unit route are retained; the delivery contains no additional split-off holes.

Changed: verified the corrected theorem and caller, generic-helper reuse, pruning, and DAG/change-record consistency.


## Forced adaptations

### Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion
Original against changed dependencies failed:
```
te_products := ⋯,
    has_kernels := ⋯, has_cokernels := ⋯ }
this✝¹ : (toPresheaf X).Additive := module_cohomology_isZero_of_cech_vanishing._proof_1_10 X
T : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat := toPresheaf X
this✝ : T.Additive := module_cohomology_isZero_of_cech_vanishing._proof_1_11 X
this : PreservesLimits T := module_cohomology_isZero_of_cech_vanishing._proof_1_12 X
P : X.Modules → Prop :=
  fun G ↦
    ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens) (hom : (i : I) → V i ⟶ U),
      ⨆ i, V i = U →
        ∀ (C : SiteCechComplex V hom) (p : ℕ), 0 < p → IsZero ((C.cohomologyFunctor p).obj ((toPresheaf X).obj G))
S : ShortComplex X.Modules
hS : S.ShortExact
hG : P S.X₁
U : X.Opens
I : Type (max u ?u.249)
V : I → X.Opens
hV : ∀ (i : I), V i ≤ U
hcover : ∀ x ∈ U, ∃ i, x ∈ V i
⊢ ∃ K W, ∃ (_ : ∀ (k : K), W k ≤ U), ⨆ i, W i = U ∧ ∀ (k : K), ∃ i, W k ≤ V i
/tmp/forced-adaptation-4jsgjcy0/lean/Sheaf/AlgebraicGeometry/ModuleCechVanishingCriterion.lean:92:75: error: unsolved goals
case hcech
X : Scheme
F : X.Modules
hcech :
  ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens) (hom : (i : I) → V i ⟶ U),
    ⨆ i, V i = U →
      ∀ (S : SiteCechComplex V hom) (p : ℕ), 0 < p → IsZero ((S.cohomologyFunctor p).obj ((toPresheaf X).obj F))
this✝⁴ : EnoughInjectives X.Modules := ⋯
this✝³ : Preadditive (TopCat.Presheaf AddCommGrpCat ↑X.toPresheafedSpace) := ⋯
this✝² : Abelian (TopCat.Presheaf AddCommGrpCat ↑X.toPresheafedSpace) := ⋯
this✝¹ : (toPresheaf X).Additive := ⋯
T : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat := ⋯
this✝ : T.Additive := ⋯
this : PreservesLimits T := ⋯
P : X.Modules → Prop := ⋯
S : ShortComplex X.Modules
hS : S.ShortExact
hG : P S.X₁
U : X.Opens
⊢ ∀ (I : Type (max u ?u.249)) (V : I → X.Opens),
    (∀ (i : I), V i ≤ U) →
      ⨆ i, V i = U →
        ∀ (f : (i : I) → V i ⟶ U) (Scech : SiteCechComplex V f),
          IsZero ((Scech.cohomologyFunctor 1).obj S.X₁.val.presheaf)

(with the modules compiled into /tmp/forced-adaptation-4jsgjcy0/.lbuild) [15.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
