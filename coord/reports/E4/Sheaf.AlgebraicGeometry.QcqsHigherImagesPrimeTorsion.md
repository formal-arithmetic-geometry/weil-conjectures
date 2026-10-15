## What changed

Proved `AlgebraicGeometry.Etale.qcqs_higherDirectImages_prime_torsion` with its exact
existing signature. The only Lean file changed is the item module. All five public imports
are unchanged. Three proof imports provide the existing module-to-abelian comparison and
filtered-colimit preservation for higher direct images.

The proof first establishes a private, proved kernel-union helper for any additive functor
preserving Type-0 filtered colimits. Its index consists of positive natural numbers with
prime divisors in P, ordered by divisibility. The canonical colimit map is mono by AB5 and epi
by exact geometric stalks and joint faithfulness at algebraic-closure points. After applying
the functor, each colimit representative keeps its allowed annihilator.

For the application, convert abelian sheaves to modules over ULift Z using the actual
coefficient equivalence, apply higher direct image, forget coefficients and take the target
stalk. The existing higher-image continuity theorem gives filtered-colimit preservation.
The coefficient comparison and equivalence counit identify its value with the original
statement's stalk. Transporting the annihilator across that additive isomorphism completes
the proof. The two private helpers are fully proved implementation steps of the item node;
there is no new public obligation and no arbitrary object selected from mere existence.

Updated the item's DAG proof, proof_deps and proof_origin to this route. No target, definition,
existing signature, public import, unit record or other module was changed. The unit
sk-rem-rest has no realized statement or steps, and its higher-image torsion assertion is kept.

The checker classifies the added `open CategoryTheory.Limits` command as an interface
change. The record coord/changes/qcqs-prime-torsion-proof-scope.md documents that command,
the private index order and the absence of effects on downstream public interfaces.

Validation: the complete module compiles cleanly with lcompile.py in approximately 12 seconds.
A separate single-file compilation with #print axioms reports exactly propext,
Classical.choice and Quot.sound, with no sorryAx. The empty prime set (index 1), zero group,
empty schemes and q=0 require no extra hypotheses. The index is Type 0, so the existing
small filtered-continuity theorem suffices; no large-universe replacement is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.qcqs_higherDirectImages_prime_torsion`
(node lem-sbc-qcqs-higher-images-prime-torsion).

No sorry remains in the item or its new private helpers. No sorry or new module was added.
This is a proof, not a decomposition: holes closed 1, holes added 0.

## No longer needed

Removed these direct proof imports (the statements' public imports are unchanged):

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `Sheaf.AlgebraicGeometry.GeometricStalkColimits`
- `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

Removed these dependencies from the item's proof_deps; the explicit affine-neighbourhood,
cohomology-presheaf and sheafification argument is supplied inside the already existing
higher-direct-image filtered-continuity theorem instead:

- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-qcqs-over-affine`
- `lemma-openclosed-stalk-upperstar`
- `lem-weil-pbc-etale-directed-cohomology-colimit`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `sbc-lem-higher-direct-image-presheaf`
- `lem-weil-pbc-sheafification-geometric-stalk`
- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`
- `def-weil-pbc-geometric-stalks`
- `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`

These are dependencies no longer directly needed by this item, not a claim that all those
modules leave every target's transitive import closure. Some remain behind the reused
continuity and comparison modules. In particular the mathematical stalk-colimit fact
lem-kun-stalks-commute-colimits remains a proof dependency, but its separate Lean module is
unnecessary: Mathlib's skyscraper-sheaf adjunction supplies the required AddCommGrpCat
preservation instance directly. Additivity comes from the existing functor instances, so no
universal-delta-functor existence theorem is required.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan was mathematically sound, but it missed the shorter available route
through `preservesColimitsOfShape_higherDirectImage`. The original affine representative
construction and direct cohomology-continuity invocation need not be rebuilt here. Its Lean
declaration is already stronger than the old DAG statement: it assumes no torsion condition
on the diagram objects. The proof uses that existing signature, without changing the node.

The original geometricStalk_preservesColimits declaration concerns ModuleCat at a different
coefficient size from this abelian-sheaf statement; the needed stalk preservation is already
a Mathlib instance. Hence its module was removed while its mathematical fact remains cited.

Three search modes were run with msearch.py: LeanFinder for higher direct images of torsion
abelian sheaves, Loogle for CategoryTheory.Sheaf and torsion, and grep for the filtered-colimit
and torsion-union names. No direct theorem for the exact prime-set assertion was found.
Direct rg and signature reads found the continuity and coefficient-comparison route used.

The listed Stacks .tex file is absent in this read-only checkout. The source proofs were
read from the official pages https://stacks.math.columbia.edu/tag/0DDC,
https://stacks.math.columbia.edu/tag/0DDD and https://stacks.math.columbia.edu/tag/09Z1.
The latter's constant-scheme case gives the filtered higher-image argument, and the
restricted kernel union is the fixed-prime version of the former two. The original theorem
docstring is retained as the source's longer plan; the updated DAG records the actual proof.

No statement is disputed, no forced adaptations are needed, and no new nodes were created.
The new proof dependencies lemma-weil-pbc-direct-image-filtered-colimit,
lem-sbc-higher-direct-image-forget-comparison and
lem-weil-pbc-module-abelian-derived-direct-image-comparison are used as generic tools for
continuity and coefficient conversion; they do not replace any realized unit step.

## Second reading by E4

1. **Existing interfaces: pass.** Read the complete repository/sandbox diff and compared
   the substring from `theorem qcqs_higherDirectImages_prime_torsion` through its result,
   before `:= by`: it is byte-identical. All five public imports are identical. The same
   qcqs morphism, arbitrary set P, stalkwise element-dependent positive annihilators,
   every natural degree q and every target geometric stalk remain quantified. No public
   declaration or definition was replaced. The extra index, its order and both helpers
   are private; the changed open command only controls this file's name resolution.

2. **Proof and trust: pass.** Independently compiled the delivered module with lcompile.py
   (11.6 seconds, exit 0, no warnings). Compiled a scratch copy with `#print axioms` for
   `prime_torsion_of_filtered_functor`, `integerSheafForget_isEquivalence`, and
   `qcqs_higherDirectImages_prime_torsion`: each lists exactly propext, Classical.choice
   and Quot.sound, with no sorryAx. There are no holes, forbidden declarations or hollow
   definitions. Read the cancellation proving n kills its kernel subobject, the AB5
   monomorphism argument, and the stalkwise equality test proving epimorphy. In particular,
   the kernel lift uses exactness at the original stalk universe; the equality detector
   supplies the necessary universe lift internally. The integer coefficient equivalence
   is constructed by restriction of scalars and restricting an actual adjunction. The
   comparison isomorphism is used inside a proof, and its imported theorem is itself
   sorry-free as confirmed by the final axiom check.

3. **Split statements and edge cases: pass; none split off.** Both private helper theorems
   are fully proved. For P empty or containing only nonprimes, 1 still indexes the union;
   prime divisibility of 1 is impossible. Products preserve allowed prime divisors, so
   the directedness proof excludes no cases. The zero sheaf, empty schemes, and q=0 need
   no extra assumptions. The functor helper needs only additivity and Type-0 filtered
   colimits; it makes no exactness assumption on the higher-image functor. The integer
   action and equivalence are real constructions, not arbitrary data from an unproved
   existence claim.

4. **Route, sources and pruning: pass.** Independently read
   [Stacks 0DDC](https://stacks.math.columbia.edu/tag/0DDC),
   [Stacks 0DDD](https://stacks.math.columbia.edu/tag/0DDD), and the constant-scheme case of
   [Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1). The restricted kernel union is
   the fixed-prime refinement of the first source. The reused higher-image continuity
   theorem implements the affine-cohomology part of the second source. Inspected its
   exact Lean signature: it requires qcqs f and permits all module sheaves and all integer
   degrees. Inspected the forget-comparison theorem and the actual moduleAbelianForget
   functor and instances. Further rg searches for prime-torsion preservation and
   IsTorsionSheafOfPrimes found the upstream predicate and unrestricted torsion union,
   but no theorem retaining arbitrary prescribed annihilator primes. A separate msearch
   grep for IsTorsionSheafOfPrimes returned no Mathlib hit. No shorter applicable theorem
   was found. Each added proof import supplies declarations or instances used here; all
   statement imports remain public and all proof imports are plain. Compared the old
   proof_deps against `No longer needed`: every removed node is listed. The sk-rem-rest
   unit has empty realized.statement and realized.steps, and the proof retains the
   higher-image torsion assertion without bypassing a realized step. Recomputed both
   TargetsCheck import closures with leanindex: no module leaves or enters the closure.
   Thus fourteen direct imports are removed, but this delivery claims no modules pruned.

5. **DAG agreement: pass.** The only changed node fields are proof, proof_deps and
   proof_origin. Checked every cited dependency statement against its use. The first
   three steps match the private kernel-union helper; the fourth constructs the integer
   sheaf equivalence; the fifth applies filtered higher-image continuity and stalk
   colimit preservation; the sixth uses the coefficient comparison, equivalence counit
   and additive transport. The union of step uses is exactly proof_deps. The stalk
   preservation and elementwise-colimit facts are implemented by the stated generic
   Mathlib results, as the proof text explains. The separate module-abelian comparison
   import supplies moduleAbelianForget and its instances; its derived comparison also
   underlies the higher-image forget isomorphism. Source and original statement fields,
   unit records and other modules remain unchanged. No new node requires registration.

**Changes made during second reading:** no Lean proof repair was needed. Corrected the
scope change record to use the declaration title, verbatim old/new scope commands and
one downstream-user table row per module, including recorded holders. Added this
independent review and the exact closure-pruning qualification. The existing theorem
and both proved private helpers are unchanged from the first worker's submission.
