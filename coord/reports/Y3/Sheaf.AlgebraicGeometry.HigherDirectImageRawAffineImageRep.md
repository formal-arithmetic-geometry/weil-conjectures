## What changed

Proved `AlgebraicGeometry.Etale.exists_higher_image_raw_affine_image_rep` directly
from the existing raw complex presentation, its colimit consequence, Mathlib's
`Concrete.isColimit_exists_rep`, and the raw-over pullback comparison.
The complete colimit argument and comparison composition are in the item's file.
No new module, lemma, definition, or hole is delivered. The sole direct caller
`Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi` has forced
proof edits using the same existing comparison abbreviation in its local limit
comparison and stage evaluation. Its final simp step is unchanged.

The signature uses the existing raw-over presheaf and comparison abbreviations;
they expand to exactly the original expressions, with identical binders and
mathematical content. The naturality import is public because these abbreviations
appear in the signature. The change record is
`coord/changes/HigherDirectImageRawAffineImageRep-abbreviations.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_higher_image_raw_affine_image_rep`
(node `sbc-lem-higher-image-raw-affine-image-rep`). Zero holes added or split off;
no `sorry` remains in any delivered file. This is a proof from existing named
project theorems, which may still depend on their own documented holes.
The previous attempt's `exists_higherDirectImageRaw_affine_rep_core` module and
node are removed from the delivery, and its colimit argument is integrated here.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`;
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The first two remain available where the existing presentation needs them;
this report does not claim their transitive theory is eliminated globally.
The last is supplied through retained public imports.

The old node's direct proof dependencies no longer used directly here are
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-injective-module-abelian-acyclic`,
`def-sbc-module-higher-image-transitions`, and
`sbc-lem-module-higher-image-raw-comparison-locally-bijective`.
Complex continuity (`lem-weil-pbc-etale-cohomology-limit-complex-systems`)
stays a proof dependency: the existing presentation isColimit theorem applies it.
Definitions required by the statement stay. Any theory used transitively by the
raw complex presentation remains required there. The unused attempted new node
`sbc-lem-higher-image-raw-affine-image-rep-core` is not delivered.
The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous attempt isolated the representative step as a new hole because of
a timeout. That step has a complete proof from the existing presentation and
Mathlib colimit theorem. The expensive conversion also occurs in the expanded
upper signature with a `sorry` body. Existing abbreviations make the section
types explicit and permit the complete proof in a single file. No statement is
false, weakened, or replaced by an arbitrary choice of data.

## Forced adaptations

`Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi` (holder: unclaimed).
The original source compiled against the published baseline. Against the compiled
changed item, it failed at line 124, `simpa only [Functor.op_obj, τ, ht] using he`:
`he` still equated the two images of the stage representative, while the goal
equated the two images of the limit class. The new `ht` uses the existing raw-over
comparison abbreviation, which the old evaluation expressions did not match.

Only the local limit comparison `τ`, the stage evaluation used to form `he`, and
the displayed shape of `he` now use `higherDirectImageRawOverComparison`.
The final simp step, all imports, and every public signature and visibility are
unchanged. Unfolding only the hypothesis did not restore simp matching; adapting
only the stage expressions still incurred a mismatched implicit limit type.
The consistently abbreviated proof compiles against the changed dependencies.
The exact original error and complete diff appear in
`coord/changes/HigherDirectImageRawAffineImageRep-abbreviations.md`.


## Second reading by Y3

1. **Interfaces: pass, with the recorded abbreviation change.** Diffed both
   delivered modules against the repository. The item changes the textual
   signature exactly as recorded in
   `coord/changes/HigherDirectImageRawAffineImageRep-abbreviations.md`.
   Read `higherDirectImageRawOverPresheaf` and
   `higherDirectImageRawOverComparison` in HigherDirectImageRawOverNaturality:
   their bodies are exactly the old presheaf and comparison expressions, at
   both the stage and the limit. All binders, hypotheses, universes, the witness
   and section equality stay the same. No definition or target is changed.
   The adapted caller's public signature and visibility are byte-for-byte
   unchanged. The extra public import supplies abbreviations in the signature;
   the new imports used only by the proof are plain imports. The irreducibility
   attributes are local and the transparency option is scoped to the theorem.

2. **Proof and axioms: pass relative to existing open dependencies.** Read the
   entire item and caller. The presentation's isColimit certificate concerns
   the fixed raw cocone, not a chosen diagram. Mathlib's
   `Concrete.isColimit_exists_rep` gives a stage class with its cocone-leg
   equality. `higherDirectImageRawOverPullbackHom_apply` identifies that leg,
   and the symmetric raw-over comparison followed by congrArg of the limit
   comparison proves the required equality in the correct direction.
   No data are selected into a definition. Both files compile without warnings
   (item 49.2 seconds; caller 27.4 seconds). A scratch import with `#print axioms`
   for both delivered theorems reports exactly propext, Classical.choice,
   Quot.sound and sorryAx. The raw-over comparison is an existing open theorem;
   this delivery closes one local hole, not the whole dependency closure.
   No sorry or forbidden axiom/unsafe/opaque/extern command occurs in either
   delivered file.

3. **Split statements: pass, none added.** No new statement, definition, node
   or sorry is delivered. The formerly attempted core module is absent from
   the delivery. The existing complex presentation is a genuine identification
   of the input to continuity, not a restatement of the representative theorem;
   its isColimit consequence eliminates existential witnesses in a proof only.
   The argument handles every integer q through that existing theorem, and
   the required nonempty filtered index follows from IsCofiltered. There is no
   added positivity, flatness or nonzero-coefficient assumption.

4. **Route, pruning and caller: pass after correcting the dependency report.**
   Read the existing raw presentation, raw diagram, raw-over comparison and
   Mathlib's representative theorem. Searched lean/Sheaf and lean/WeilConjectures
   for representatives, surjectivity and uses of isColimit_exists_rep, and read
   the Mathlib concrete-colimit statement. The direct colimit route is already
   the short route; no duplicate auxiliary theorem is needed. Each retained
   proof import supplies a theorem or filtered-colimit instance used here.
   The three removed direct imports and all seven old proof dependencies are
   accounted for: six are removed, while complex continuity is retained through
   the presentation's isColimit theorem. The unit sk-lem-failure-field is
   unchanged; this node is not an entry of its realized statement or steps, and
   the replacement route stays within the same unit's cohomology-continuity
   argument. No claim of global pruning of the transitive theory is made.
   Independently compiled the original caller against the changed sandbox
   dependencies: it fails at the recorded final simp with a type mismatch.
   The adapted caller compiles. Each edited expression uses the existing
   comparison abbreviation consistently so ht can rewrite he; no other lines,
   declarations or imports of the caller change.

5. **DAG: pass after repair.** Compared the old and new node and read the four
   cited dependency nodes. The proof steps correspond to the presentation,
   colimit representative extraction, explicit cocone leg and canonical
   comparison in Lean. Added
   lem-weil-pbc-etale-cohomology-limit-complex-systems to the first step and
   proof_deps, because EtaleComplexCohomologyPresentation.isColimit applies its
   continuity theorem. The union of step uses now equals proof_deps. The node's
   natural-language statement is unchanged and its Lean statement matches the
   recorded abbreviation change; proof_origin describes the route used.

Second reading changed only the node's continuity dependency and its explanation,
corrected `## No longer needed` accordingly, and added this review. No Lean edits
were necessary; one original hole is closed, zero holes are added or split off.

## Forced adaptations

### Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi
Original against changed dependencies failed:
```
ap Λ k G q (c.π.app i)).hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        ((ConcreteCategory.hom
            ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
                  ((DerivedCategory.Plus.singleFunctor (Sheaf (D.obj i).left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                    (((D.obj i).hom)^*[ModuleCat Λ].obj G))).app
              (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
          t)) =
    (ConcreteCategory.hom (b'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        ((ConcreteCategory.hom
            ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
                  ((DerivedCategory.Plus.singleFunctor (Sheaf (D.obj i).left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                    (((D.obj i).hom)^*[ModuleCat Λ].obj G))).app
              (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
          t))
but is expected to have type
  (ConcreteCategory.hom (a'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
                ((DerivedCategory.Plus.singleFunctor (Sheaf c.pt.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                  ((c.pt.hom)^*[ModuleCat Λ].obj G))).app
            (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        z) =
    (ConcreteCategory.hom (b'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
                ((DerivedCategory.Plus.singleFunctor (Sheaf c.pt.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                  ((c.pt.hom)^*[ModuleCat Λ].obj G))).app
            (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        z)

(with the modules compiled into /tmp/forced-adaptation-5owx98xl/.lbuild) [13.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
