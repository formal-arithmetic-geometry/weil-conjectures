## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CechH1Injective.lean` states
`AlgebraicGeometry.Scheme.Modules.cechH1_injective`. It binds a scheme `X`, an
index type `ι : Type u`, an open family `U : ι → X.Opens`, and the covering
condition `iSup U = ⊤`. It asserts existence of a family `c` of homomorphisms
from the degree-one homology of Mathlib's `CategoryTheory.cechComplexFunctor`
applied to `F.presheafModuleCat` to `RingedSpace.moduleCohomology X.toRingedSpace
1`. The first conjunct says each map satisfies the canonical comparison
predicate `IsModuleCechComparison U F 1 (c F)`, rendering the canonical map
clause. The second says `Function.Injective (c F).hom` for every `F`, rendering
injectivity of the first Cech cohomology map. No naturality clause is added to
this node's conclusion; naturality is supplied by the dependency
`lem-sc-cech-h1-map-natural` when constructing the canonical family.

The dependency declarations used are:

- `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme` (the
  scheme notion).
- `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` from
  `Sheaf.Paper.PQFCohomology` (the recorded module cohomology notion).
- `CategoryTheory.SiteCechComplex` from
  `Sheaf.CategoryTheory.SiteCechComplex` (the project's general site Cech
  construction; the concrete open-cover Cech complex in this statement is
  Mathlib's `CategoryTheory.cechComplexFunctor`, as used by the next
  dependency).
- `AlgebraicGeometry.Scheme.Modules.cechH1Map_natural` from
  `Sheaf.AlgebraicGeometry.CechH1MapNatural` (existence and naturality of the
  canonical comparison family).

The proof docstring records the two source steps: comparison of module and
underlying abelian-sheaf cohomology, then the first-quadrant Cech spectral
sequence whose `(1,0)` edge has no higher differentials and is therefore
injective; composition with the comparison isomorphism preserves injectivity.
The theorem proof is intentionally `sorry` at stage 2.

Edge cases checked: a one-open cover has zero first Cech cohomology, so the
injectivity assertion is consistent; the zero module gives the zero map between
zero groups and is injective; arbitrary (including empty-index) open families
are covered by the stated `iSup U = ⊤` hypothesis, so no finiteness assumption
was added.

Searches made: `msearch.py ... leanfinder "first Cech cohomology injective canonical map H^1 sheaf"` (no declaration);
`msearch.py ... loogle "cechComplexFunctor, IsModuleCechComparison, injective"` (no exact theorem);
`msearch.py ... grep "cech.*inject|inject.*cech"` over Mathlib Sites/AlgebraicGeometry (no relevant injectivity theorem);
`rg -n "cechH1_injective|cech.*inject"` over project `WeilConjectures/` and `lean/Sheaf` (no existing statement).
The existing canonical-map declaration was found at
`Sheaf.AlgebraicGeometry.CechH1MapNatural`; it does not assert injectivity, so
this node requires its own theorem.

## Earlier second reading (a previous round; superseded)

The statement was checked against Stacks Lemma 0B8R and the recorded canonical-map dependency. The Lean signature has exactly the scheme, open-family, covering, canonical-comparison, and injectivity clauses described above; no extra hypotheses or conclusion clauses were introduced.

## Second reading by H1

I reread the node statement, Stacks Cohomology Lemma 0B8R (the `lemma-cech-h1`
statement), the dependency nodes, and the Lean declaration item by item.

- **Scheme:** the node introduces a scheme `X`; Lean uses `(X : Scheme.{u})`.
  This is the same scheme object as `[def-pc-scheme]`.
- **Cover:** the node introduces an arbitrary indexed family of opens
  `U = {U_i}` covering `X`; Lean uses `{ι : Type u}`, `U : ι → X.Opens`, and
  `hcover : iSup U = ⊤`.  This is the project's open-cover convention and
  permits the empty index type only when the scheme is empty.
- **Coefficient object:** the node quantifies over every sheaf `H` of
  `O_X`-modules; Lean quantifies over every `F : X.Modules`.  Its
  `F.presheafModuleCat` is the presheaf used by the module-valued Cech
  complex, and `F` is the same O_X-module notion.
- **Cech group and target:** the node's first Cech cohomology of the
  underlying abelian sheaf maps to `H^1(X,H)`; Lean's source is
  `((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology 1`
  and its target is `(RingedSpace.moduleCohomology X.toRingedSpace 1).obj F`.
  These are the recorded module Cech complex and O_X-module cohomology,
  whose underlying additive homomorphism is the node's homomorphism.
- **Canonical map clause:** the node requires the canonical Cech-to-cohomology
  map; Lean witnesses a family `c` and requires
  `IsModuleCechComparison U F 1 (c F)` for every `F`.  This predicate is the
  dependency's canonical-map characterization, so the existential witness
  cannot be an arbitrary map.
- **Conclusion:** the node requires injectivity for every coefficient sheaf;
  Lean states `Function.Injective (c F).hom` for every `F`.  No naturality
  conclusion is added (naturality belongs to `lem-sc-cech-h1-map-natural`).

The hypotheses are neither strengthened by finiteness, quasi-coherence,
Noetherianity, characteristic, or a nonempty-index assumption, nor weakened.
The index universe is tied to the scheme universe as required for this open
cover construction.  The empty scheme/empty cover, a one-open cover, and the
zero module all typecheck and are mathematically consistent: the relevant
Cech H1 is zero in the one-open and zero-object cases, so the zero map is
injective.  The statement has no `n` parameter or characteristic hypothesis.

I searched for an existing declaration with `msearch.py` LeanFinder and Loogle
queries for first Cech H1 injectivity and canonical comparison maps, and with
`rg` over Mathlib's Sites/SheafCohomology and AlgebraicGeometry trees and the
project's `WeilConjectures/` and `lean/Sheaf/` trees.  No existing injectivity
statement was found.  I opened `CechH1MapNatural.lean` and its node: it gives
existence, canonicality, and naturality but not injectivity, so this module is
not a duplicate.  I also checked the `Scheme`, module-cohomology, Cech, and
`IsModuleCechComparison` declarations used by the signature.

No mismatch was found, and no source or Lean statement was changed.  The
module compiles cleanly with `lcompile.py`; its only proof hole is the required
stage-2 `sorry`.
