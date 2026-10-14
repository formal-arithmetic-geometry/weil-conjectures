## What changed

Corrected `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility`
to apply to an explicitly cycle-normalized edge. Its cohomology conclusion is
unchanged. The proof maps the homology data of C by F and f_*F, applies the cycle
normalization with the identity on the common cycle object, and cancels the
quotient epimorphism. This is a real Mathlib proof, with no application of an
unproved sheaf-edge helper. No new data are chosen from existence theorems.

Changed the node statement and its Lean signature record, proof, proof_deps and
proof_origin. The change record is
coord/changes/AffineDerivedPushforwardSheafEdgeCycleNormalization.md.

The only external adaptation is
`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge`: preserve its entire
signature, visibility, docstring, and imports, and replace its now ill-typed
three-line proof by `:= by sorry`. Its existing node and complete sourced proof
already describe the actual remaining normalized-existence construction. This
prevents the arbitrary zero transformation from being advertised as normalized.

## Proved and sorry left

`AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility` is proved
without sorry under the corrected cycle-normalization hypothesis.

The supplied brief is stale: the checkout has **zero** sorries in the assigned
module, having already replaced the original hole with an application of the
false fixed-component helper. Accordingly **0 existing holes closed, 1 existing
hole reopened, 0 new intermediate nodes or holes split off**. This is a statement
repair, not a claimed positive sorry-ledger result or decomposition.

The one sorry left by the delivery is
`AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge` in
`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge`, existing node
`lem-pc-affine-derived-pushforward-sheaf-edge`. Its statement is unchanged; it
still asks for genuine existence of a normalized natural transformation. The
remaining construction must glue the affine K-injective cycle-class comparison,
not choose the zero transformation. The source and full argument are in the
unchanged theorem docstring.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent`
and eliminated use of its declaration
`AlgebraicGeometry.affineDerivedPushforwardSheafEdge_component` and its node
`lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component`.
The module has no other textual users in the checkout, so this false restatement
leaves the relevant import path. The repair does not edit or attempt to prove it.

The old proof dependency `def-pc-ringed-spaces-derived-direct-image` is no longer
a proof step of compatibility: the derivation uses only Mathlib homology data,
functorial mapping, reassociation, and epi cancellation. The actual derived-unit
notion remains visible through the unchanged statement imports; its construction
is not pruned from the library. No unit statement or realized unit step is bypassed
(the unit record has empty realizations). The parent imports stay untouched because
it is an unheld forced adaptation, not an opportunity for unrelated edits.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original unnormalized theorem and the component helper
claim the equality for **every** natural transformation epsilon. A degree-zero
nonzero module on the identity affine morphism gives a nonzero derived-unit
comparison; epsilon = 0 makes the left side zero. The existing existence theorem
explicitly chooses zero, and therefore supplies no normalization at all.

The earlier component reduction is the original statement with binders moved,
not a strictly smaller argument. The original compatibility file already contained
this dispute marker yet applied that same disputed helper to remove its sorry.
This delivery repairs the interface and does not treat that removal as progress.

Stacks 0AVW uses the canonical resolution comparison, and 08D4 handles its unbounded
truncation calculation; neither proves compatibility of arbitrary edges.
Sources read: https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/08D4. The repaired cycle normalization spells
out which edge is meant. It is a premise of a conditional compatibility lemma,
not a hidden existence assumption in any target or in the parent theorem.
All Challenge statements and the parent's existential statement stay identical.

Searches actually run through msearch.py:
- Loogle `ShortComplex.mapHomologyIso`: 0 hits (unqualified identifier unknown).
- LeanFinder `homology comparison isomorphism composite functors preserving homology`:
  8 hits, including Mathlib's mapHomologyIso and homologyFunctorIso.
- Grep `mapHomologyIso.*comp|homologyComparison.*comp`: generic homology infrastructure,
  no canonical affine normalized edge.
Local rg searches read Mathlib ShortComplex/PreservesHomology.lean and Homology.lean,
and the library's edge and right-derived-functor modules. No additional canonical
normalized edge construction was found. The proof uses the actual Mathlib
mapHomologyIso definition and mapped LeftHomologyData, rather than restating them.

Edge cases: zero rings and zero complexes pose no problem; the same quotient
cancellation works. No nonzero hypothesis is added. The cycle comparison k is
constrained by its commuting inclusion; since U.i is monic, it cannot be rescaled
arbitrarily. The proof requires only the exactness instances already in the old
signature; exactness of f_* on all sheaves is neither asserted nor used.

## Forced adaptations

`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge` is unclaimed in the
local claims snapshot. The original compiled against the repaired compatibility
module fails at line 90 with `Application type mismatch` in
`Exists.intro ε (affineDerivedPushforwardSheafEdge_compatibility A B φ i ε)`:
the supplied term now requires cycle normalization before its universal F,C
conclusion, while the expected term is that conclusion directly. This was tested
by compiling the actual original parent with the sandbox overlay.

Changed only original lines 88-90, the proof body, to `:= by sorry`. There is no
available normalization for the arbitrary witness from Nonempty (whose current
proof chooses zero), so filling the new premise would reintroduce the false
claim. Restoring the named, sourced unresolved existence theorem is necessary to
keep the unchanged parent statement and prevent the false proof from escaping.
The independent reader can compile the original and adapted versions against the
overlay and compare all existing signatures and visibility. No other adaptation
was made.


## Second reading by G4

1. **Interfaces: pass, declared repair.** Independently diffed both delivered
   modules against the repository. The compatibility statement gains exactly
   the cycle-normalization premise declared in the change record; its original
   conclusion is unchanged. The parent's declaration, visibility, docstring,
   options and imports are byte-for-byte unchanged before its proof. Checked
   the change record's Old/New signatures and the node's Lean signature against
   the actual files by exact string equality. No target or definition changes.
   The old arbitrary-epsilon statement fails for the zero edge on a nonzero
   degree-zero complex with the identity affine map. The new premise explicitly
   identifies the canonical edge; it is not an existence assertion or a claimed
   proof of the old universal statement.
2. **Proof and adaptation: pass.** Both modules compiled together through
   lcompile.py without errors or warnings. Scratch copies with `#print axioms`
   show exactly propext, Classical.choice and Quot.sound for compatibility;
   the parent additionally uses sorryAx, as reported. Scanned both files: the
   parent named theorem is the only sorry; no definitions or forbidden commands
   were introduced. Independently compiled the original parent against the
   changed overlay: line 90 fails with Application type mismatch because the
   normalization premise is missing. The adapted parent compiles. Its only
   forced edit restores the sourced named existence theorem's unresolved proof;
   the trivial Nonempty witness cannot discharge normalization. No arbitrary
   witness data are chosen in either delivered proof.
3. **Split statements and sources: pass.** No new split statement, node, or
   intermediate sorry was added. Read the remaining parent's complete proof
   docstring and existing node. Independently read Stacks Tags 0AVW and 08D4:
   they concern the canonical K-injective comparison and unbounded truncation,
   not arbitrary transformations. The conditional normalization argument is
   valid also for the zero ring and zero complexes: the quotient remains epi
   and no nonzero or boundedness condition is used. The normalization premise
   does not silently assume exactness of direct image on all sheaves.
4. **Route and pruning: pass.** Read Mathlib's actual mapHomologyIso definition
   and mapped left homology data. The proof instantiates normalization on the
   two mapped data with the identity cycle map, then cancels the mapped quotient
   epimorphism; every step is necessary and generic. Independently searched via
   msearch grep for homologyπ_mapHomologyIso and LeftHomologyData.mapHomologyIso_eq,
   and searched the local homology modules for comparison routes. These provide
   generic infrastructure, not normalized affine-edge existence. No shorter
   route closes that remaining geometric construction in this review. Both
   statement imports are needed for their exposed types/instances. The removed
   component import and the sole old DAG proof dependency are both named in
   No longer needed. The forced parent imports are retained to avoid unrelated
   edits to the unheld module. Read sk-thm-picard-semicon.json: its realization
   arrays are empty and this auxiliary repair bypasses no realized unit step.
5. **DAG and accounting: pass.** The normalized node statement, exact Lean
   signature, elementary cancellation proof, empty proof_deps and proof_origin
   agree with the implementation. The old proof and old proof_deps are preserved
   in statement_change. The remaining parent's existing node and sourced proof
   plan still describe the unchanged open construction. Accounting is 0 old
   holes closed, 1 old hole reopened, 0 holes split off: a soundness repair, not
   positive proof progress.

Second reading added this independent review. No Lean repair was needed.
The dry run confirmed that statement_change.by uses the required schema spelling
"G4 stage 2" even for a stage-3 repair; the original attribution was correct
and is retained. The original parent also compiled against the unmodified
baseline, independently confirming that its overlay failure is forced.

## Forced adaptations

### Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge
Original against changed dependencies failed:
```
RSHom (Spec.map (CommRingCat.ofHom φ))))).map
              (((HomologicalComplex.sc C i).mapHomologyIso F).inv ≫
                ((DerivedCategory.homologyFunctorFactors
                        (SheafOfModules (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) i).app
                    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).inv) ≫
            ε.app
              { obj := DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C), property := hC } =
          ((HomologicalComplex.sc C i).mapHomologyIso
                (F ⋙
                  RingedSpace.moduleDirectImage
                    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom φ)))))).inv ≫
            ((DerivedCategory.homologyFunctorFactors
                      (SheafOfModules (moduleRings (Spec (CommRingCat.of B)).toSheafedSpace)) i).app
                  (((F ⋙
                            RingedSpace.moduleDirectImage
                              (LocallyRingedSpace.Hom.toShHom
                                (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom φ))))).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj
                    C)).inv ≫
              (DerivedCategory.homologyFunctor (SheafOfModules (moduleRings (Spec (CommRingCat.of B)).toRingedSpace))
                    i).map
                ((RingedSpace.moduleDirectImage
                        (LocallyRingedSpace.Hom.toShHom
                          (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom φ))))).rightDerivedFunctorUnit.app
                  ((HomotopyCategory.quotient (SheafOfModules (moduleRings (Spec (CommRingCat.of A)).toSheafedSpace))
                        (ComplexShape.up ℤ)).obj
                    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)))
in the application
  Exists.intro ε (affineDerivedPushforwardSheafEdge_compatibility A B φ i ε)

(with the modules compiled into /tmp/forced-adaptation-4k59hqaj/.lbuild) [7.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
