## What changed

Completed `AlgebraicGeometry.AlgebraicSpace.presheaf_space_target_bootstrap`
without changing its signature or public imports. The proof follows Stacks Bootstrap
Tag 02YS: prove descent, choose two scheme atlases, compose their scheme-test
properties, and identify the given sheaf with the quotient of its represented
etale kernel relation. Four fully proved private helpers handle descent in the
representable fibres, the relative-property interface, monicity of the quotient
unit, and its sheafification universal property. The last helper uses subsheaf
closure inside the given sheaf, so no global small-valued sheafification on the
big site is assumed. The DAG proof and dependencies now describe this Lean route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.presheaf_space_target_bootstrap`
(`lem-sfb-presheaf-space-target-bootstrap`). Proved 1 of 1 original sorries.
Added 0 holes; 0 sorries remain in the delivered module. No split-off statements
or new modules. The existing kernel-relation and local-lifting theorems are used
as the stage brief permits; their proofs remain separate work.

Compilation: `lcompile.py` accepted the final module in 5.0 seconds with exit
code 0 and no warnings. Checked that the public theorem signature and public
imports are unchanged, all Lean lines have at most 100 characters, and DAG
`proof_deps` exactly equal the union of proof-step `uses`.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: neither `schemeSpace` nor
  `schemeSheaf_isAlgebraicSpace` is used. Descent uses the Yoneda sheaf condition
  directly, and the local-lifting dependency already supplies the subcanonical
  Yoneda sheaf interface needed later.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`:
  the fully proved Mathlib relative-property calculus works on arbitrary
  presheaves and directly provides the two pasted scheme-test computations.
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`: no covering-precoverage
  computation is needed; multiplicativity of etale and surjective scheme maps
  supplies the singleton composition case through relative morphism properties.
- `Mathlib.CategoryTheory.Sites.Sheafification`: its global functor is not used;
  the specified unit's universal property is proved using `Sites.Subsheaf`.
- `Mathlib.CategoryTheory.Limits.Shapes.KernelPair`: no regular-epimorphism
  coequalizer theorem is used; the represented kernel pair directly makes the
  presheaf quotient unit monic, and subsheaf closure gives reflection.

Removed proof dependencies `def-trf-scheme-algebraic-space`,
`lem-trf-space-representable-etale-scheme-tests`, and
`lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer` for the reasons above.
Removed the obsolete top-level tool approval for
`lem-trf-space-representable-etale-scheme-tests`. These are local proof prunings;
other consumers may still need the declarations and modules. No declaration is
withdrawn, and no source-library file changes. The etale-covering-composition
node is retained for its singleton composition case, supplied by Mathlib.

## Where the brief, the DAG or earlier work was wrong

No current return, rework row, or repair note for this item was found. The
statement is preserved. The old plan invokes the Mathlib regular-epimorphism
instance for sheaves, whose recorded match assumes `HasSheafify`. Such an
instance is not provided for arbitrary `Type u` presheaves on this big site.
The new proof instead uses the closure of a subfunctor of the already given
sheaf; this gives the same universal property without a size assumption.

The source's two-atlas argument and the unit route are preserved. Edge cases
checked: empty covering sieves, empty test schemes, identity maps and empty
source/target spaces. All constructions are categorical and require neither
nonempty covers nor a global lift of a section.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
