## What changed

Proved `CategoryTheory.ringedInternalHom_contravariant_exact` with its original
signature, including the arbitrary derived universe w. The only library module
changed is the assigned module. All added imports are private proof imports.

Choose a representative K of M and its existing functorial K-injective replacement
I. The existing Hom-complex sign comparison is natural for precomposition, as
checked on product projections. This identifies the opposite homotopy-category
signed Hom model with Qh.op followed by the recorded RHom(-,M). Apply the already
proved generic bifunctor Hom exactness theorem, descend its coherent shift
structure through localization, and detect triangulatedness by essential
surjectivity of the localization on arrows. Every helper is private and proved.
The item's DAG proof and proof dependencies follow this argument.
Local irreducibility and explicit category instances limit repeated unfolding of
large sheaf constructions during component conversions. A private definition names
the ordinary internal-Hom bifunctor once, so subsequent comparison proofs use its
compact interface. The imported
constructions and their public interfaces are unchanged.

## Proved and sorry left

Closed `CategoryTheory.ringedInternalHom_contravariant_exact`: 1 of 1 assigned
sorries proved, zero new holes, zero split off. No sorry remains in the delivered
module. No other library theorem is changed.

Validation: the assigned module compiled without errors or warnings in 39.9 seconds
using `lcompile.py`. `#print axioms ringedInternalHom_contravariant_exact` reported
exactly `propext`, `Classical.choice`, and `Quot.sound`; the diagnostic print command
was then removed. Static checks confirmed the original signature and public imports,
zero holes, permitted DAG-only proof edits, and acyclic imports for both main proof
inputs. The final delivery tool performs its own compile and preflight checks.

## No longer needed

The proof does not import or invoke the separate source- and target-shift modules
planned by `lem-pur-derived-internal-hom-shift-left` and
`lem-pur-derived-internal-hom-shift-right`. Their direct dependency edges are
removed. The associated modules
`WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft` and
`WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight` are not imported
by this proof. Generic signed bifunctor exactness supplies the coherent shifts and the
cone-triangle calculation together. The target does not ask for the additional
normalized shift equations. No original public import is removed, and no module
or declaration is withdrawn. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The statement needs no correction. Importing
`Sheaf.CategoryTheory.SignedDerivedInternalHomExact` here would close an import
cycle through this item, as confirmed by `tools/import_direction.py may`. This
proof uses the generic homotopy-category exactness input directly instead.

The direct proof uses the same Hom complex,
K-injective replacement and localization as the recorded derivedInternalHom; it
does not substitute a different derived closed structure. The comparison is
natural in the contravariant variable and keeps the universe w arbitrary.

Zero objects, negative shifts, characteristic two and unbounded complexes are
covered by the generic bifunctor theorem and the sign isomorphism. No exactness of
infinite products, boundedness, flatness or finiteness hypothesis is added. The
proper-base-change unit and its realized route are unchanged.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
