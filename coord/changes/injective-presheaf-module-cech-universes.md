# CategoryTheory.injective_presheaf_module_cech_cocycle_lift

## Reason

The existing theorem is already STATEMENT-DISPUTED, with a reviewed counterexample
in coord/reports/C1/Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact.md.
Injectivity in PresheafOfModules.{s} R cannot extend morphisms from free
representables whose values live in a larger universe. The triangle example on
Type 1 with small rational-valued coefficients violates the original conclusion.
This repair aligns hom, ring, module-value, and index universes at v. It follows
the presheaf argument of Stacks Tags 03FC and 03F5. No Challenge target changes.

## Old

```lean
theorem injective_presheaf_module_cech_cocycle_lift
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{r})
    (M : PresheafOfModules.{s} R) [Injective M]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c
```

## New

```lean
theorem injective_presheaf_module_cech_cocycle_lift
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (M : PresheafOfModules.{v} R) [Injective M]
    {T : Type v} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c
```

The corrected theorem is proved from the separately stated exactness of the actual
free complex. Its Yoneda comparison and injective extension are completely proved.
This delivery is a decomposition, not a claim of an axiom-free proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact | B2 | Correct the false intermediate signature and prove the corrected statement from freeComplex_exactAt. |
| Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic | unclaimed | Original application fails with Category.{w} C and cochain universe mismatches. Keep its signature, visibility, imports, and documentation identical; replace only its proof body (lines 68–78 of the original) with by sorry. |

The downstream.py --uses search found these two textual users only. It also listed
290 transitive importers. They consume the unchanged downstream signature, so none
requires a signature or proof adaptation. This correction does not change any
definition used by a Challenge target.

The forced adaptation reopens
CategoryTheory.injective_module_cech_cohomology_isZero. Its existing node is
lem-weil-pbc-ringed-site-injective-module-cech-acyclic and its existing docstring
has the source and proof plan. We do not claim this general ringed-site statement
false: its hypotheses differ from those of the false presheaf statement. A future
worker needs a proof valid for its independent universes, or an authorized interface
repair with all necessary users adapted. Retaining the old proof would conceal the
invalid use of presheaf injectivity. The entire proof must be reopened because an
inner sorry is forbidden; this is the only forced edit to the unclaimed module.

## Status

landed 20261012T153008-L-2349915 2026-10-12 (merge of deliver/B2/Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact)
