## Worker report

The module `Sheaf.TraceFormula.FiniteEtaModificationGluing` states
`AlgebraicGeometry.finite_eta_modification_gluing` with proof `sorry`.  It also
records the concrete overlap restriction, base, target, inclusion, and
categorical cocycle helpers used to render the overlap clauses.

The hypotheses are rendered as follows.  `S` and `Z` are schemes of the same
universe, `[IsIntegral S]` gives the integral base, and `hqcS` and `hqsS` are
quasi-compactness and quasi-separatedness of `S`.  `η : S` and
`hη : IsGenericPoint η Set.univ` give the generic point.  `f : Z ⟶ S` carries
`[Flat f]` and `[LocallyOfFinitePresentation f]`.  The finite cover is indexed
by `Fin n`; `H : Fin n → Z.Opens`, `hHqc`, and `hHcover` give quasi-compact open
members and their union.  The local schemes and maps are `Y`,
`q i : Y i ⟶ (H i).toScheme`; `hqfin` says each `q i` is finite.  The three
families `hYflat`, `hYlfp`, and `hYred` state flatness, local finite
presentation, and geometrically reduced fibres for each composite to `S`.
`hqη` is the `IsIso` assertion for the base change of each `q i` to the residue
field of `η`, hence the specified generic-fibre identification.

The conclusion first supplies an integral `S'` and `h : S' ⟶ S`, with
`IsFinite h`, `IsProper h`, `Surjective h`, and `IsIso (h.fiberToSpecResidueField η)`.
It then supplies a point over `η`, a scheme `Y'`, a finite map
`q' : Y' ⟶ pullback f h`, and its structure map `p'`, with the displayed
factorization `hp'`.  The displayed `Flat`, `LocallyOfFinitePresentation`, and
`GeometricallyReduced` predicates render the corresponding properties of
`Y' ⟶ S'`; the following pullback `IsIso` is the generic-fibre isomorphism.
The open `U` is schematically dense, as is `q' ⁻¹ᵁ U`, and the restriction of
`q'` over `U` is an isomorphism.  The family `φ i j` consists of isomorphisms
between the pulled-back restrictions over `H i ∩ H j`; the first two displayed
families say that they are over `S'` and over the pulled-back overlap in `Z`.
The identity and inverse equations give normalization and symmetry, and
`etaModificationOverlapCocycle` explicitly supplies the factorization maps and
triple cocycle (the categorical `GlueData` conditions).  The following
universal clause states uniqueness of each overlap isomorphism.  Finally the
open immersions `ιY i` cover `Y'` and their composites with `q'` are the
base-changed local maps, which is the stated gluing of the pulled-back `Y_i`.

The statement dependencies are used through their recorded declarations:
`AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties),
`IsGenericPoint` (Mathlib.Topology.Sober), `AlgebraicGeometry.Flat`
(Mathlib.AlgebraicGeometry.Morphisms.Flat),
`AlgebraicGeometry.LocallyOfFinitePresentation`
(Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation),
`AlgebraicGeometry.IsOpenImmersion` (Mathlib.AlgebraicGeometry.OpenImmersion),
`AlgebraicGeometry.IsFinite` (Mathlib.AlgebraicGeometry.Morphisms.Finite),
`CategoryTheory.Limits.pullback` (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback),
`AlgebraicGeometry.IsReduced` (Mathlib.AlgebraicGeometry.Properties),
`AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
`AlgebraicGeometry.Surjective` (Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap),
base change via the recorded `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`
conventions and pullback definitions, and
`AlgebraicGeometry.SchematicallyDenseOpen`
(Sheaf.TraceFormula.SchematicallyDenseOpen).

Edge cases checked were `n = 0` (the empty cover, forcing `Z` empty), empty
members and empty pairwise or triple overlaps, a one-member cover, `S` a
field (where `S' = S` is allowed), and the identity base modification.  No
normality, noetherianity, finite type over a field, or integralness of `q i`
was added.

Searches for an existing declaration were run before writing.  LeanFinder and
LeanSearch queries about finite generic modifications with geometrically
reduced fibres and their gluing returned only generic Mathlib definitions and
normalization interfaces, with no matching existence theorem.  Loogle queries
`QuasiCompact, IsFinite, IsProper, IsIso`, `"IsFinite", "IsIso"`, and
`"AlgebraicGeometry.IsFinite", "AlgebraicGeometry.Flat"` returned no matching
statement (one result was an unrelated `IsFinite` instance).  Grep over
Mathlib AlgebraicGeometry and the project for
`Riemann.?Zariski|finite.*modification|glue.*modification|eta.modification`
found no matching declaration.  The searches are also recorded in the copied
node's `mathlib_searches` field.

## Second reading by Q143

I reread the node, source place (Temkin Corollary 3.5.4 and Theorem 3.5.5,
Step 1), and the module.  The integral qcqs base, generic point, flat finitely
presented family, finite qc open cover, finite local maps, generic
identifications, and reduced geometric fibres are each present.  The
conclusion contains exactly the finite proper surjective base modification,
unchanged generic fibre, overlap isomorphisms with base/overlap compatibility,
identity/inverse/uniqueness and explicit cocycle clauses, the glued finite
map, its generic and schematically dense isomorphism open, and flat finitely
presented reduced-fibre output.  No mismatch or omitted hypothesis was found.

## Maintainer review fix

The cc second reader corrected three rendering faults (H3) and one docstring
fault (H8).  (1) `QuasiCompact (𝟙 S)` and `QuasiSeparated (𝟙 S)` hold for every
scheme, so the node's qcqs hypothesis on `S` was missing; it is now
`[CompactSpace S] [QuasiSeparatedSpace S]`.  (2) The node's "flat and finitely
presented" for `Z → S` means locally of finite presentation, quasi-compact and
quasi-separated (def-sbc-locally-finite-presentation); `[QuasiCompact f]
[QuasiSeparated f]` are added.  With them `Y i → S` is quasi-compact and
quasi-separated automatically (finite, then quasi-compact open immersion, then `f`),
and `QuasiCompact (H i).ι` is equivalent to `H i` being quasi-compact.  (3) The
conclusion "`Y → S'` is flat and finitely presented" now also has
`QuasiCompact p' ∧ QuasiSeparated p'`.  (4) The statement docstring now gives the
node's 13 proof steps.  The corrected module compiles clean.
