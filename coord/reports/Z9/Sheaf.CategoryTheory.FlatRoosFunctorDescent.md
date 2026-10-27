## What changed

Proved CategoryTheory.flatRoosFunctorDescent with its exact existing signature.
The proof uses a functorial flat-term K-flat resolution to establish localization
on good cochain representatives directly. Finite product localization gives Zbar.
Existing generic strict Roos derivation helpers apply in the independent coefficient
universe; uniqueness of right derived functors gives the normalized theta. Taking
Zhat = Zbar followed by RF gives beta and rZ. Naturality and cancellation prove the
formula for every K-injective resolution and its actual limit projections. Fully
faithful restriction gives the unique compatible pair of lift comparisons.

Added private proved localization, uniqueness and categorical cancellation helpers,
and a local instance caching existing CommRingCat-to-RingCat sheaf composition.
Profiling showed repeated HasSheafCompose searches dominating elaboration; the
cache returns the existing instance and changes no mathematical data. Its named
declaration is recorded in coord/changes/flat-roos-descent-local-compose-cache.md;
instance registration remains local, and no existing consumer uses the new name.
Local irreducibility keeps the explicit Roos constructions behind their proved API;
chosen localization lifts are consumed through existential factorization isomorphisms. Reused existing
private proved helpers through proof-only import all, without modifying their
owning modules. Updated the node proof, proof_deps and proof_origin to this route.
The unit sk-def-purity-conv has no realized statement or steps; its route is preserved.

## Proved and sorry left

Closed one original hole: CategoryTheory.flatRoosFunctorDescent
(lem-pur-flat-roos-functor-descent). Added zero holes. No sorry remains in the
item, and no new module or split-off theorem is added. The private helpers
flat_representative_localization, normalized_lift_unique, normalized_pair_unique,
resolution_formula and projection_transport are proved.
Single-file compilation passed without warnings in 29.2 seconds; the delivery tool
performs the final axiom and packet checks.

## No longer needed

Removed the direct proof import
Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients. The proof
uses functorial cochain resolutions rather than the site-derived-tensor equivalence;
that module remains transitively imported through the unchanged public interface.
The explicit cylinder construction and homotopy quotient of former node steps 1–2
are unnecessary. The proof no longer uses the statement of
lem-weil-pbc-site-derived-tensor-descent or lem-weil-strict-roos-comparison: it uses
the existing generic proved helpers in StrictRoosDerivation instead. Both modules
remain available through existing public imports; no global withdrawal is claimed.
The original proof dependencies def-pc-flat-sheaf-modules, def-pc-kflat-complex and
def-pc-tensor-complex-sheaves are used through the functorial-resolution helper's
existing dependencies, rather than through a new cylinder proof. Product localization,
levelwise cohomology and the localization universal property remain used. No module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The named strict Roos comparison has a common-universe statement, whereas this
item allows independent site and coefficient universes with essential smallness.
Its existing generic proved derivation helpers and the essentially-small-site
Grothendieck helpers already supply the needed argument without changing any
statement. Functorial flat resolutions also give localization directly, making
the DAG cylinder step unnecessary. No mathematical statement is disputed.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
