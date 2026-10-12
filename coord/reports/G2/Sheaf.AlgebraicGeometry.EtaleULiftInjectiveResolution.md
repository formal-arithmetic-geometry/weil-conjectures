## What changed

The original module imports two new proof-only modules, EtaleULiftHomology and
EtaleULiftInjective. Its theorem now constructs the lifted cocomplex and augmentation
explicitly as an InjectiveResolution. The augmentation is the inverse single-complex
comparison followed by the lifted original augmentation. Its quasi-isomorphism proof
uses preservation of homology. The evaluation comparison is Iso.refl, because both
complexes are definitionally equal. No existing signature or public import changed.
The parent DAG proof now records precisely these dependencies.

EtaleULiftHomology proves coefficient lift preserves homology. It proves additivity
by reflexivity, transfers parallel-pair limit preservation through the sheaf inclusion,
and proves epimorphism preservation using the equality of image sieves under up/down.
Mathlib's kernel-and-epi criterion then proves preservation of homology.
EtaleULiftInjective isolates the original plan's injectivity argument, with its source
and complete natural-language proof. No data is chosen from an unproved existence
statement: the resolution's cocomplex and augmentation are explicit constructions.

Validation: all three modules compile together in import order with lcompile.py,
without warnings. The helper assertions are valid for arbitrary schemes, including
an empty scheme and the zero sheaf. The exactness proof has no nonemptiness premise.
The injectivity assertion is only about injective objects and does not mention a
resolution, augmentation, or evaluated complex; it is strictly part of the argument.
The parent unit sk-prop-h2 has no realized node among this item's declarations, and
its statement and proof steps are unchanged.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.exists_etale_ulift_injectiveResolution
(node lem-sc-etale-ulift-injective-resolution): 1 of 1 original sorries closed.
The item's module has no sorry left.

Added one hole, AlgebraicGeometry.Scheme.etale_ulift_injective
(node lem-sc-etale-ulift-injective), in the new EtaleULiftInjective module.
Its proof is exactly by sorry. This is a decomposition with net hole change zero,
not a claim that the original theorem is free of sorryAx in its dependency closure.

AlgebraicGeometry.Scheme.etale_ulift_preservesHomology
(node lem-sc-etale-ulift-homology) is fully proved without sorry.
It and the explicit resolution construction discharge the exactness, augmentation,
and evaluation portions of the original plan.

## No longer needed

No original module import was removed. The parent no longer directly uses the old
proof dependency def-weil-pbc-etale-site: its use is now through the homology and
injectivity sublemmas, so its node and module are not pruned from the import closure.
The small affine site argument remains needed
in the injectivity sublemma, so neither its module nor its nodes are claimed pruned.
The parent still uses the original InjectiveResolution definition; the site definition
is used through the two new lemmas. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent node's proof dependencies named only definitions, rather than statements
proving its substantial injectivity and exactness claims. Exactness can nevertheless
be proved directly with existing Mathlib facts. Injectivity remains the substantial
unfinished step; its argument follows the original node and Stacks Tag 01DO, whose
extension criterion was checked against the source. No false statement, unusable
signature, or tool failure was found. The missing local Additive instance must be
provided explicitly before the mapped augmentation's QuasiIso instance is synthesized.

## New nodes

lem-sc-etale-ulift-injective: the lift of an injective small-coefficient etale abelian
sheaf is injective in the larger coefficient category. Source: Stacks Tag 01DO,
applied as in parent steps 1 and 2. Lean Finder returned the related ModuleCat ULift
result but no sheaf result; Loogle found no match, grep found no matching theorem,
and LeanSearch was unavailable. One named sorry remains here.

lem-sc-etale-ulift-homology: coefficient lift preserves homology. Source: parent
step 3 and Mathlib's sheaf epi criterion, ULift limit preservation, and the
kernel-and-epi preservation-of-homology criterion. The same searches found no direct
sheaf-compose theorem. This node has a complete Lean proof and introduces no hole.

No change record is needed: existing statements, definitions, and public imports
are unchanged.

## Second reading by G2

1. I compared the delivered resolution module with the repository version. The theorem
   signature and all existing declarations are byte for byte unchanged; the proof now
   constructs the resolution explicitly and uses only the two helper declarations.
   Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. The modules compile
   without warnings. Axiom probes give only `propext`, `Classical.choice`, and
   `Quot.sound` for the proved homology theorem; the resolution theorem has `sorryAx`
   only through the deliberately split injectivity theorem. There are no forbidden
   declarations and no sorry in a definition. Verdict: pass.

3. I checked the new statements against the library and recorded Mathlib, Lean Finder,
   Loogle, grep, and source searches. `etale_ulift_injective` is the strict injectivity
   subargument from Stacks Tag 01DO, while `etale_ulift_preservesHomology` is the exactness
   subargument; neither restates the parent target. The edge cases described in the
   report (empty scheme and zero sheaf) introduce no extra hypotheses. Verdict: pass.

4. The proof follows the shortest available formal route: Mathlib's kernel and local
   surjectivity criteria establish homology preservation, and the explicit lifted
   cocomplex supplies the resolution. The two broad helper imports were narrowed to
   `Preadditive.Injective.Basic` and `ShortComplex.PreservesHomology`; the parent imports
   remain needed for its public statement and construction. Verdict: pass.

5. The parent node's proof and proof dependencies now match the Lean proof, and the two
   new nodes document their source, proof route, searches, and remaining split status.
   The unit route is unchanged; it has no realized node for this item. Verdict: pass.

I changed the two helper imports as above, recorded the old direct site dependency
under No longer needed, and added this second-reading record. No
statements, definitions, target imports, or DAG statement fields were changed.
