## What changed

Proved `CategoryTheory.affineProjectiveComplexDerivedHom` with its full original signature.
The item contains proved private helpers for internal Hom from a categorical projective on the
one-point site and for bounded-above exact-term Hom comparison. These adapt the existing proofs in
`RingProjectiveInternalHomExact` and `RingedSiteBoundedFreeRHomMapQuasiIso`: the former is adapted
to categorical projectivity, and the latter to exact-term Hom instead of finite-free retracts. No source-library declaration was edited.

The proof cuts the source separately for each homology degree, applies the existing bounded
exact-term Hom theorem, and compares a bounded-below injective replacement with any functorial
replacement. The derived representing isomorphism uses the canonical replacement map and
`derivedInternalHom_comparison`. The explicit negative-degree bound is `e - d`.

All helpers are private and proved; no public interface or definition changes. The zero-map
step in the isomorphism transport uses the proved Hom API directly. Its isomorphism is built
from explicit Hom maps, avoiding expansion of the full internal-Hom functor. Proof-local
irreducibility keeps elaboration from unfolding the large Hom-complex and derived-Hom functors;
their existing projection and comparison APIs suffice. No attribute change is exported.
A change record for the local proof commands is
`coord/changes/F5-affine-projective-hom-proof-commands.md`.
The DAG proof and
proof dependencies now describe this direct exact-term route. The unit route is unchanged.

Validation: the complete item compiles through `lcompile.py` in 19.2 seconds with exit code 0
and no diagnostics. The public signature and public imports match the repository byte-for-byte;
all lines satisfy the 100-character limit. The independent published-import probe also passes.
An ordered emitting compile then compiled the changed item in 54.0 seconds, followed by the
unchanged direct consumer `Sheaf.TraceFormula.UpperShriekBoundedCoherent` in 5.2 seconds and its
consumer `Sheaf.TraceFormula.AlgebraicShriekRelativePerfect` in 7.1 seconds. All three passed
without diagnostics against the changed item. The unchanged consumer copies are not delivered. A separate axiom check of the completed
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the single hole in `CategoryTheory.affineProjectiveComplexDerivedHom`
(node `lem-sc-affine-projective-complex-derived-hom`): 1 closed, 0 added, 0 split off.
There are no remaining `sorry` declarations in the delivered Lean module.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the statement uses
the original small-site `derivedInternalHom`, and its proved comparison suffices.

The proof does not need the K-projectivity result
`lem-sc-bounded-above-projective-kprojective`: direct exactness and finite-degree truncation give
the required comparison. Its statement dependency stays because the original statement uses the
projective-complex notion; the original public Mathlib import stays to preserve the visible API.
Neither `RingProjectiveInternalHomExact` nor `RingedSiteBoundedFreeRHomMapQuasiIso` is imported:
the first expects projectivity of the evaluated module, and the second finite-free retracts.
The needed general arguments are proved privately here. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained Z5 sandbox named by the route note is absent on this machine. The proof was rebuilt
from the current repository sources. The current bounded exact-term Hom module has migrated to
`WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`; an independent probe importing it
together with `WeilConjectures.Algebra.Homology.HomComplex` compiles (2.1 seconds). Thus the old
publication conflict is not present in this environment.

The original DAG invoked K-projectivity without exposing its bridge to this sheaf-valued Hom
complex. The delivered proof supplies that bridge directly through exact terms and truncation.
No hypotheses or conclusions changed. The zero ring, zero complexes, arbitrary projective rank,
all integer bounds, and unbounded-below K-injective replacement targets are covered.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
