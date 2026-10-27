## What changed

Proved `AlgebraicGeometry.Etale.flatConstructibleTensor_cohomology_and_bounds` without
changing its signature or any public definition or public import. All new helpers are
private and proved. The native ModuleCat-valued sheaf tensor avoids transporting the
ringed-site comparison across an equivalence of coefficient encodings.

The proof first makes the canonical localization tensorator invertible using K-flatness
of the flat single complex. The signed total tensor collapses degreewise, and exactness
supplies the homology isomorphism. Its naturality in cochain maps and in arbitrary maps
between flat sheaves is proved explicitly, including the surviving (i,0) summand equation.
Localization supplies naturality for all derived morphisms. A generic bifunctor assembly
then specializes to the existing full subcategories; doing that assembly generically
avoids expensive specialization/unfolding of the site-derived monoidal data.

The prescribed tensor-refinement witness supplies ordinary tensor constructibility.
The finite-value/finite-local-constancy equivalences preserve the given stratifications.
Transport across the cohomology comparison gives constructibility, boundedness and every
specified interval bound. Zero sheaves, empty schemes, zero coefficient rings and
unbounded ambient representatives require no exceptions; only the right factor is flat.

Single-file compile: exit 0, 26.7 seconds, no diagnostics. The delivery tool performs the
independent declaration/axiom probe and preflight. The item DAG proof now records this
route. No new modules, public declarations, definition repairs or consumer adaptations.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.flatConstructibleTensor_cohomology_and_bounds`
(node `lem-fd-flat-constructible-tensor`).

Added 0 holes. No sorry remains in the delivered module. This is a proof, not a
decomposition. The existing tensor-refinement theorem is used as stated.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `WeilConjectures.ConstructibleSheaf.MonoidalParts`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The declared dependency `lem-fd-ringed-flat-single-tensor-cohomology`
(`Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology`) is unnecessary for this item:
the complete flat-single computation is proved privately in its native coefficient
category, using the already adopted K-flat localization API. No generic ringed-site
transport or replacement axiomatized comparison is imported.

The old direct tools `lem-pc-kflat-resolution`,
`lem-weil-pbc-site-derived-tensor-descent` and
`lem-weil-pbc-ringed-topoi-module-pullback-tensor` are removed from this node's obsolete
top-level tool list: the native derived tensor implementation supplies its own K-flat
machinery, and the retained constructibility witness supplies its own geometric tensor
comparison. Their modules may remain needed transitively or by other consumers; none is
withdrawn. The unit's tensor-preservation step is retained, and no parent route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The planned ringed-site cohomology lemma uses
`SheafOfModules`, whereas this item uses ModuleCat-valued sheaves. Applying it directly
would require an additional derived monoidal comparison. The native K-flat tensorator
and exact-functor homology APIs yield a shorter fully proved route in the required
encoding. The generic naturality assembly keeps the final specialization within the
single-file compile limit; a direct specialized assembly caused expensive unfolding.

Current blueprint read: latest snapshot, `sec-fourier-transform/sk-thm-inversion/`
`thm-fd-transform-well-defined.md` and its proof. It retains tensoring with the lisse
kernel as the constructibility step. Sources checked locally: Stacks
`etale-cohomology.tex`, `lemma-tensor-product-constructible` (095I), and
`sites-cohomology.tex`, `definition-derived-tor` (06YU). Searches were run through
msearch.py: LeanFinder (8 module/representation Tor hits, no sheaf comparison), Loogle
(`"homologyFunctor", "tensor"`, 0 hits), and grep (`homology.*tensor|tensor.*homology`,
8 hits concerning Gabriel-Popescu and group homology). Source searches found the native
K-flat counit, single-tensor collapse, and constructibility comparison actually used.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
