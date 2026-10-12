## What changed

Corrected `AlgebraicGeometry.relative_spec_morphism_chart` by adding the missing canonical section-map hypothesis `hmap`, then proved it using Mathlib restriction naturality, counit naturality, Spec functoriality, and transport cancellation. The returned duplicate private helper has been removed. Sectionwise transports now use Mathlib `eqToHom_map` for the sheaf forgetful functor followed by `eqToHom_app`, specialized locally to the open U; no duplicate declaration is introduced. The public import of AffineStructureAlgebraFullyFaithful is replaced with its three statement-level imports. A local heartbeat allowance handles the dependent transports; no file-wide options or instances were introduced.

The only forced adaptation is line 216 of `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec` (unclaimed in the local snapshot): pass its existing `hmap`. Its signature, visibility, imports, and all other lines are unchanged. Change record: `coord/changes/relative-spec-morphism-chart-hmap.md`.

## Proved and sorry left

The single original hole at `AlgebraicGeometry.relative_spec_morphism_chart` (node `lem-weil-pbc-relative-spec-morphism-chart`) is removed in the corrected theorem. This is a statement correction with a complete proof, not a proof of the old overgeneralized statement and not a decomposition. No holes are added. No sorry remains in either delivered module. The forced adaptation closes no additional hole.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful` from the chart module and removed its node `lem-weil-pbc-affine-structure-algebra-fully-faithful` from this node's proof_deps. Its three statement-level public dependencies remain explicitly imported. Full faithfulness remains needed and explicitly imported by the parent, so no globally unreachable module is claimed. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original chart signature omitted `hmap` although its proof plan explicitly invoked the canonical functor's morphism formula. Specifying functor objects does not specify morphisms: conjugation by noncentral object automorphisms preserves objects and changes morphisms. Over Spec Q the affine-line translation and scaling maps do not commute, illustrating the obstruction. The precise correction and all user effects are in the change record. The parent already supplied the missing datum, so its mathematical statement does not change. No Challenge target changes. The chart node does not realize a unit statement or step; the parent still proves the prescribed relative-spectrum route.

The landing return correctly identified the duplicated private `sheaf_eqToHom_app`. This repair removes it rather than renaming or restating it: the proof applies existing Mathlib functorial transport theorems directly. The duplicate in AffineStructureAlgebraFullyFaithful is private, so importing that module would not expose it. The mathematical statement and forced parent adaptation are unchanged.

The shortest-route searches found `Scheme.Opens.toSpecΓ_SpecMap_appLE` in Mathlib (LeanFinder and Loogle), and rg confirmed the source and the absence of a library proof of this chart statement. The stacks-project checkout described by the source path is absent here; the existing proof plan is followed, and Stacks 01LX was also read online. No new sourced-but-unproved assertion is introduced.

## Forced adaptations

`Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec` compiled against the original baseline. Against the corrected chart lemma, its original line 216 failed with `Type mismatch: relative_spec_morphism_chart S E hobj has type (∀ Y Y' h V, ... hmap formula ...) → ∀ A B φ U, ... but is expected to have type ∀ A B φ U, ...`.

The sole edit is `exact relative_spec_morphism_chart S E hobj` to `exact relative_spec_morphism_chart S E hobj hmap`. The adapted module compiles against the changed dependency. All original declarations and visibility remain identical. Both delivered modules compile in import order without warnings.

## Earlier second reading (a previous round; superseded)

The reading below concerns the earlier returned version. The duplicate helper is now removed; the repaired version requires a fresh second reading.

1. Interface comparison: PASS with the declared correction, not as a proof of the old
   statement. I compared both delivered modules against the repository with `diff`.
   The chart's only signature change is the recorded `hmap` assumption; its conclusion
   is unchanged. The parent differs only by passing its already constructed `hmap`.
   Every parent declaration signature and visibility is byte-for-byte unchanged. The
   change record lists downstream importers and the sole caller. No Challenge target
   or definition changes. The arbitrary-equivalence objection is valid: in the old
   statement, object identifications do not control the morphism action.
2. Proof and trust: PASS. Both files compile locally without warnings. I read the
   entire chart proof and the parent's construction and use of `hmap`. Restriction
   naturality reduces the goal to a ring-map equality; inverse-counit naturality,
   `hmap`, and cancellation of equality transports prove that equality. A scratch
   copy's `#print axioms` for the chart and its private helper shows exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Neither delivered
   module contains a `sorry` or a forbidden trust escape; there is no new definition
   or arbitrary witness construction. The delivery tool also probes every declaration
   and checks that the original parent fails against the changed chart dependency.
3. Split statements: PASS, vacuous. There are no split-off statements and no new
   holes or nodes. The corrected formula covers identity morphisms and the empty
   open by the same naturality identities; it has no nonemptiness assumption. The
   private equality-transport helper is proved by equality induction. Its counterpart
   in AffineStructureAlgebraFullyFaithful is private and cannot be reused without
   retaining the otherwise unused dependency.
4. Shortest route and pruning: PASS. I independently searched Mathlib for
   `toSpecΓ_SpecMap|counit.*naturality` and the library for chart and transport lemmas,
   and read Mathlib's `Scheme.Opens.toSpecΓ_SpecMap_appLE`. The proof already uses
   this direct route; full faithfulness is unnecessary here. All three remaining
   public imports supply types or predicates in the signature. The sole old
   proof dependency removed is reported under `## No longer needed`. I checked
   `dag/units/sk-thm-p1.json`: this node realizes no prescribed statement or step,
   and the parent's full-faithfulness and relative-spectrum route stay intact.
   The source context agrees with [Stacks 01SA](https://stacks.math.columbia.edu/tag/01SA)
   and [Stacks 01LX](https://stacks.math.columbia.edu/tag/01LX).
5. DAG agreement: PASS. I compared the node against its repository version and
   checked its corrected statement, Lean signature, empty `proof_deps`, naturality
   proof plan, and `proof_origin` against the code. Its `statement_change` records
   the added hypothesis and the unaffected parent citer. No new-node fields are
   needed.

Second reading changed only this report, adding the independent review and its
validation evidence. The Lean proof, corrected interface, change record, and node
required no repair. One corrected-statement hole is closed and zero holes are added;
this does not establish the old arbitrary-equivalence statement.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
Original against changed dependencies failed:
```
/tmp/forced-adaptation-jvjro6o_/lean/Sheaf/AlgebraicGeometry/AffineMorphismRelativeSpec.lean:216:4: error: Type mismatch
  relative_spec_morphism_chart S E hobj
has type
  (∀ (Y Y' : ObjectProperty.FullSubcategory fun Y ↦ IsAffineHom Y.hom) (h : Y ⟶ Y') (V : S.Opens),
      (Under.Hom.right (E.functor.map h.op).hom).hom.app (op V) =
        eqToHom ⋯ ≫ Scheme.Hom.appLE (Over.Hom.left h.hom) (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V) ⋯ ≫ eqToHom ⋯) →
    ∀ (A B : ObjectProperty.FullSubcategory fun A ↦ A.toModule.IsQuasicoherent) (φ : A ⟶ B) (U : S.Opens),
      IsAffineOpen U →
        Scheme.Hom.resLE (Over.Hom.left (E.inverse.map φ).unop.hom) ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U)
              ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U) ⋯ ≫
            ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
              Spec.map ((Under.Hom.right ((E.counitIso.app A).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) =
          ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map ((Under.Hom.right ((E.counitIso.app B).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) ≫
              Spec.map ((Under.Hom.right φ.hom).hom.app (op U))
but is expected to have type
  ∀ (A B : ObjectProperty.FullSubcategory fun A ↦ A.toModule.IsQuasicoherent) (φ : A ⟶ B) (U : S.Opens),
    IsAffineOpen U →
      Scheme.Hom.resLE (Over.Hom.left (E.inverse.map φ).unop.hom) ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U)
            ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U) ⋯ ≫
          ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map ((Under.Hom.right ((E.counitIso.app A).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) =
        ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map ((Under.Hom.right ((E.counitIso.app B).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) ≫
            Spec.map ((Under.Hom.right φ.hom).hom.app (op U))

(with the modules compiled into /tmp/forced-adaptation-jvjro6o_/.lbuild) [6.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by R1

1. Interface comparison: PASS. I compared both delivered modules with the repository versions. The chart declaration differs only by the recorded `hmap` hypothesis; its conclusion is unchanged. The parent differs only at the forced call site, passing its existing `hmap`. All other existing declarations, visibility, and signatures are unchanged, and the change record names the affected user.

2. Proof and trust: PASS. Both delivered modules compile with `lcompile.py` and produce no warnings. The delivered files contain no `sorry`, forbidden declarations, or hollow definitions. The chart proof uses counit naturality, the supplied canonical morphism formula, `toSpecΓ` naturality, `Spec.map` composition, and cancellation of equality transports. Its trust boundary is the standard `propext`, `Classical.choice`, and `Quot.sound` set; no extra axiom is introduced.

3. Split statements: PASS, none. No theorem with `sorry` was added and no decomposition was introduced. The corrected chart statement is true for all algebra morphisms and opens (including identity morphisms and the empty open) under precisely the canonical `hmap` assumption; the parent supplies that assumption. The local transport calculation is an internal proof step, not a new public statement.

4. Shortest route and pruning: PASS. The proof follows the direct Mathlib naturality route and does not use the removed full-faithfulness import. The remaining public imports provide the types and predicates occurring in the declaration; the removed module and its node are listed under `## No longer needed`. The relative-spectrum unit route is preserved, and no unit statement or prescribed step is bypassed.

5. DAG agreement: PASS. The node's corrected Lean signature, empty `proof_deps`, proof steps, proof origin, and statement-change record agree with the delivered code. The node records the added `hmap` datum and the parent adaptation, with no new node required.

I changed only this report during second reading; the proof, change record, node, and forced adaptation required no further repair.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
Original against changed dependencies failed:
```
/tmp/forced-adaptation-c518ys80/lean/Sheaf/AlgebraicGeometry/AffineMorphismRelativeSpec.lean:216:4: error: Type mismatch
  relative_spec_morphism_chart S E hobj
has type
  (∀ (Y Y' : ObjectProperty.FullSubcategory fun Y ↦ IsAffineHom Y.hom) (h : Y ⟶ Y') (V : S.Opens),
      (Under.Hom.right (E.functor.map h.op).hom).hom.app (op V) =
        eqToHom ⋯ ≫ Scheme.Hom.appLE (Over.Hom.left h.hom) (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V) ⋯ ≫ eqToHom ⋯) →
    ∀ (A B : ObjectProperty.FullSubcategory fun A ↦ A.toModule.IsQuasicoherent) (φ : A ⟶ B) (U : S.Opens),
      IsAffineOpen U →
        Scheme.Hom.resLE (Over.Hom.left (E.inverse.map φ).unop.hom) ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U)
              ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U) ⋯ ≫
            ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
              Spec.map ((Under.Hom.right ((E.counitIso.app A).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) =
          ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map ((Under.Hom.right ((E.counitIso.app B).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) ≫
              Spec.map ((Under.Hom.right φ.hom).hom.app (op U))
but is expected to have type
  ∀ (A B : ObjectProperty.FullSubcategory fun A ↦ A.toModule.IsQuasicoherent) (φ : A ⟶ B) (U : S.Opens),
    IsAffineOpen U →
      Scheme.Hom.resLE (Over.Hom.left (E.inverse.map φ).unop.hom) ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U)
            ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U) ⋯ ≫
          ((unop (E.inverse.obj A)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map ((Under.Hom.right ((E.counitIso.app A).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) =
        ((unop (E.inverse.obj B)).obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map ((Under.Hom.right ((E.counitIso.app B).inv.hom ≫ eqToHom ⋯)).hom.app (op U)) ≫
            Spec.map ((Under.Hom.right φ.hom).hom.app (op U))

(with the modules compiled into /tmp/forced-adaptation-c518ys80/.lbuild) [8.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
