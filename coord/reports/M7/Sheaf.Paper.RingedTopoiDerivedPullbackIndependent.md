## What changed

Proved `SheafOfModules.ringedTopoiDerivedPullbackIndependent` with its signature and
all original public imports unchanged. All added helpers are private and proved.
Generalized the existing specialized proof to independent site object, site Hom,
and coefficient universes. The proof establishes inverse-image exactness using
underlying sheaves, transports K-flatness through identity scalar extension, and
uses the invariance clause of the existing
`derivedChangeOfRingsIndependentCoefficients` theorem for scalar extension.
The resolving-class theorem then constructs the universal exact derived functor.
The resolution isomorphism is explicitly the inverse image of the augmentation
followed by the computation map; naturality and cancellation prove all five
comparison laws, packaged in `RingedPullbackResolutionComparisons`.

Private helper definitions construct scalar extension sectionwise and its identity
comparison explicitly; no data is chosen from an undetermined existence theorem.
The auxiliary extension functor supplied by the existing theorem is identified
with this concrete functor by its prescribed objects and morphisms.

The only route variation is using the existing independent-coefficient
change-of-rings interface instead of its older equal-universe standalone lemma.
This is the same mathematical argument as Stacks Tag 06YY. The use of
`lem-pur-derived-change-of-rings` is as a generic tool: only its ordinary functor
and quasi-isomorphism invariance clause are retained. Standard derived-category
instances are local to that proof and do not affect the theorem's chosen
localization universe. No unit statement or step is bypassed. The node also
records the existing `siteSheafTensorRightIso` flatness transport.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.ringedTopoiDerivedPullbackIndependent`
(node `lem-weil-pbc-ringed-topoi-derived-pullback`).
Added 0 holes; split off 0 statements. There are no `sorry`s in the delivered
Lean module. This proves the assigned theorem from the existing library
interfaces; their proof obligations are not relabelled as new statements.

## No longer needed

No original import was removed, and no module is withdrawn. In particular the
publicly imported specialized theorem remains available with its existing proof.
The new proof does not directly use the equal-universe
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso` /
`lem-pur-change-of-rings-kflat-quasi-iso`; its independent-universe content is
obtained from the already existing derived-change-of-rings interface instead.
This is a direct dependency replacement, not a claim that the old module is
unreachable: the retained specialized theorem and other existing declarations
still use it. No other dependency in the original node is pruned.

## Where the brief, the DAG or earlier work was wrong

The former node proof correctly described the mathematics, but its standalone
change-of-rings quasi-isomorphism dependency only accepts coincident site and
coefficient universes. Its existing independent-coefficient counterpart is
already a clause of `derivedChangeOfRingsIndependentCoefficients`, so no new
statement or definition repair was necessary. The monoidal flatness returned by
the existing resolution theorem also needs the existing site-tensor isomorphism
to match `IsFlatOnSite`.

Initial proof search used the prescribed LeanFinder, Loogle, grep, and local
source searches. No shorter direct Mathlib theorem supplied this unbounded
ringed-topos construction. The source Tag 06YY and the existing specialized
proof supply the route, including arbitrary unbounded complexes and arbitrary
coefficient maps (no flatness hypothesis on that map).

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
