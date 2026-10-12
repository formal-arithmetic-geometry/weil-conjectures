## What changed

Replaced the sorry in `AlgebraicGeometry.exists_affine_derivedSheafHom_adjunction`
by a proof combining the existing underived affine Hom theorem with Mathlib's
absolute derived-adjunction construction at the cochain-complex localization.
The proof constructs the derived functors and comparison maps, checks their
universal properties using K-injective derivability, and proves the counit
compatibility by `Adjunction.derivedε_fac_app`.

Exactness of restriction follows from its two adjoints: the existing tensor
change-of-rings adjunction and the affine Hom adjunction. This avoids the
unneeded `DerivedRHomAlgebraModule` construction. Proof-only imports were added;
all existing public imports and all existing signatures are unchanged.

Added one strictly smaller theorem in
`Sheaf.Algebra.Homology.DerivedInternalHomSingleComparison`: uniqueness comparison
between a right derived functor of ordinary internal Hom and the chosen RHom
bifunctor with first argument in degree zero. Updated the item's DAG proof to
follow the compiled argument. The new theorem has no algebra action, affine map,
underived or derived adjunction, evaluation formula, or existential witnesses.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_affine_derivedSheafHom_adjunction`
(node `lem-sc-finite-sheafhom-affine-adjoint`). Its proof contains no sorry.

Added one named hole:
`CategoryTheory.derivedInternalHom_single_comparison`
(node `lem-sc-derived-internal-hom-single-comparison`). Its entire proof is
`:= by sorry`; its docstring and node give the construction and proof.
This is a decomposition: one hole closed, one strictly smaller hole added,
not a sorry-free proof of the import closure. The underived affine Hom and
tensor change-of-rings theorems are used as existing dependencies.

Compilation of both delivered modules succeeds. Edge cases of the new statement
were checked: zero M, empty scheme, arbitrary shifts and unbounded coefficient
complexes; no exactness of Hom(M,-) or infinite products is required.

## No longer needed

No original import was removed. Both original proof dependencies remain needed:
`lem-sc-finite-sheafhom-affine` and `lem-sc-derived-adjunction-from-underived`.
There are no original DAG proof modules to prune.

The proof does not need `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`
(node `def-pc-derived-rhom-algebra-module`), its separately constructed algebra
Hom functor, its resolution localization, or its underlying-functor comparison.
This was an explored dependency removed before delivery, not an original import
or a claim that the module becomes unreachable from all targets. No unsupported
global pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The DAG's abstract derived-adjunction leaf does not itself supply the concrete
comparison from the chosen RHom bifunctor to the unary derived Hom functor. That
missing part is now named explicitly. The existing `homComplex_single_iso`
(node `lem-sc-hom-complex-single`) is objectwise; its natural projection
construction must be used to establish a natural functor comparison, rather
than choosing its pointwise isomorphisms arbitrarily.

The two underived carrier spellings (pushed-forward RingCat sheaf and
`moduleRings (directImageAlgebraSpace f)`) are definitionally equal but required
explicit changes to guide localization and universe inference. No statement or
definition was changed. The unit's route is preserved.

## New nodes

`lem-sc-derived-internal-hom-single-comparison`, module
`Sheaf.Algebra.Homology.DerivedInternalHomSingleComparison`, declaration
`CategoryTheory.derivedInternalHom_single_comparison`: only the natural
identification of unary derived internal Hom with the shared RHom construction.
Its proof uses the existing single-source Hom-complex comparison and the
K-injective representative comparison. Mathlib and blueprint searches found
no equivalent unary sheaf-valued theorem. No change record is needed because
existing signatures and public imports are unchanged.

## Second reading by Y3

1. PASS: diffed the item against the repository. The existing theorem signature is
   byte for byte unchanged, as are its definitions and public imports. There is no
   change record because no existing statement or definition changes.
2. PASS: both delivered modules compile via lcompile.py. The item has no sorry;
   only CategoryTheory.derivedInternalHom_single_comparison has a named sorry.
   No forbidden declaration or hollow definition was added. Scratch #print axioms
   checks show only propext, Classical.choice, Quot.sound and sorryAx; inherited
   dependencies and the comparison remain open. R is selected by the right-derived
   universal property, which determines it up to natural isomorphism. H is only
   eliminated inside a theorem proof, not used to define arbitrary data.
3. PASS: the new theorem is exactly the remaining ordinary-module comparison,
   with no algebra action, adjunction or counit assertion. Read the construction
   of derivedInternalHom and the proved homComplex_single_iso, including its
   projection, differential and map formulas. Zero M and the empty scheme give
   zero Hom complexes; unbounded targets cause no product-exactness issue because
   only the degree-zero source factor survives. No projective or locally free
   hypothesis is needed. Independent leanfinder, loogle and grep searches found
   generic rightDerivedUnique, but no duplicate of the new comparison. Its
   docstring supplies a full naturality-and-localization argument. Formalizing
   that natural comparison is substantial, so the named hole remains.
4. PASS: the proof actually constructs the derived adjunction from the underived
   one and proves its evaluation compatibility; it does not simply reapply a
   renamed version of the item. Both original proof dependencies remain in use.
   No original module or dependency can be pruned. Inspected the unit's realized
   record (empty statement and step lists); no unit route is bypassed or changed.
   Tried removing PointwiseLeftDerived; compilation then lost
   isLeftDerivedFunctor_of_inverts, so restored this required proof import.
5. PASS: the item's proof steps and proof_deps match the actual underived
   adjunction, tensor adjunction, K-injective derivability, derived-adjunction
   constructor, comparison and counit calculation. The new node has its source,
   dependencies, searches, creation, blueprint and verbatim Lean statement.
   Read the Stacks affine-adjoint and affine-ext source proofs; the chosen route
   agrees with them. The accounting is one original hole closed and one smaller
   hole added: a decomposition, with zero net holes closed, not a fully proved
   import closure.

Changes by this reader: added the missing proof-only HomComplexSingle import to
the new comparison module, expanded its docstring and node proof to justify
K-injective derivability by homotopy equivalences, recorded the independent
searches in the new node, and appended this review. No Lean proof or signature
was rewritten.
