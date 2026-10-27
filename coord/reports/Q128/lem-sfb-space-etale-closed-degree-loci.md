## Worker report

States `AlgebraicGeometry.AlgebraicSpace.etale_closed_degree_loci` in
`Sheaf.AlgebraicGeometry.SpaceEtaleClosedDegreeLoci`. Its only proof is `sorry`.
No definitions, auxiliary theorems, new nodes or dependency modules are introduced.
The natural-language statement and proof are unchanged. The statement-dependency
list gains four existing, recorded definition nodes, as authorized by brief-stage2
section 5: `def-a1-algebraic-space-point-classes`, `def-a1-space-open-subspace`,
`def-sfb-space-quasi-compact-presheaf-map`, and
`def-sfb-presheaf-map-separated-diagonal`. These own the actual interfaces used.

### Clause-by-clause reading

- The base scheme is `{S : Scheme.{u}}`; `X : AlgebraicSpace S` is the existing
  full subcategory of fppf sheaves with representable diagonal and an etale atlas.
  The universe is explicitly declared as `u`, with `autoImplicit false`.
  Schemes and fields are in the same universe; point classes live in `Type (u+1)`.
  No independent smaller test universe can make the geometric-point quantifier vacuous.
- The scheme source over S is `W : Over S`. Its morphism to X is the natural
  transformation `f : yoneda.obj W ⟶ X.obj.obj`. This is exactly a scheme-source map
  to X, without making a new scheme-space construction or selecting an atlas of X.
- Quasi-compactness is `hqc : IsQuasiCompactPresheafMap f`, the existing affine-test
  quasi-compact etale-atlas condition. For the representable map f this is the
  scheme-test meaning of quasi-compact in the node.
- Separatedness is `hsep : IsSeparatedPresheafMap f`, which is
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` of the canonical
  presheaf diagonal. Thus it is precisely closed-immersion representability of
  the diagonal, with no separatedness assumption on S or X.
- Etaleness is `het : IsEtale f`, the existing representable scheme-test predicate.
  It includes representability and etaleness of every scheme pullback.
- A geometric point is `x : PointRepresentative X.obj.obj` with `[IsAlgClosed x.K]`.
  The structure already contains a field `x.K : Type u`, its `Field` instance,
  the map `x.base : Spec (CommRingCat.of x.K) ⟶ S`, and the section `x.value`.
  `yonedaEquiv.symm x.value` is the corresponding natural transformation from
  the actual represented field spectrum to X. This is equivalent to the explicit
  field-and-map formulation; no geometric point is fixed or omitted.
- Its geometric fibre is `Limits.pullback f (yonedaEquiv.symm x.value)` on
  presheaves. Both presheaves are sheaves, so this is the actual sheaf fibre
  product on underlying presheaves. Representability of f identifies it with a
  scheme; `Point` is its set of underlying field-valued point classes, not its
  set of rational sections and not the fibre of the map on point classes.
- The uniform bound is `hbound : ∃ N : ℕ, ∀ (x : PointRepresentative X.obj.obj)
  [IsAlgClosed x.K], Cardinal.mk (Point (...)) ≤ (N : Cardinal)`.
  An integer finite bound is equivalent to a natural finite bound, also on an
  empty base (where zero suffices). Cardinal inequality is used so an infinite
  fibre would never silently have degree zero as it would with `Nat.card`.
- Every integer r >= 0 is `∀ r : ℕ`. The asserted subset D_r is
  `∃ D : Set (Point X.obj.obj)`. `IsClosed D` uses the existing atlas topology.
  The next conjunct characterizes it exactly:
  `Quot.mk _ x ∈ D ↔ Cardinal.mk (Point (...)) ≤ (r : Cardinal)` for EVERY
  algebraically closed field representative x. In particular membership agrees
  for different geometric representatives of a point. Every point class admits
  a representative over the algebraic closure of its field in the same universe,
  so this characterization determines all of D, not just a subset of its points.
- The final conjunct quantifies over `O : OpenSubspace X`, the actual open
  subfunctor with scheme-test open-immersion inclusion. `Dense (pointImage O.val.ι)`
  states density of its point image. The hypothesis quantifies over all geometric
  x with `Quot.mk _ x ∈ pointImage O.val.ι` and gives the bound r. The conclusion
  gives exactly the same bound for all geometric x over X, with no membership
  restriction. This is the stated dense-open consequence, and uses the same r.
- The introductory descriptions of quasi-separated, integral and open immersions
  are ambient terminology, not additional assumptions on f. There is no hypothesis
  that X is quasi-separated, integral, nonempty or quasi-compact, and no claim that
  f is integral or surjective. The existing finite/integral modules are imported
  to retain the original statement-dependency imports; their terminology is not
  redefined. Open immersions enter the open-subspace type and the proof plan.

### Dependencies read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `CategoryTheory.Over` give the base, scheme source and scheme maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  `PointRepresentative.Rel`, `Point`; `CategoryTheory.yonedaEquiv` is Mathlib's
  existing Yoneda equivalence. The point of x is the quotient `Quot.mk _ x`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  and `pointImage`. No private point set or topology is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `diagonalPresheafMap`, and `IsSeparatedPresheafMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. The actual construction uses Mathlib's
  `CategoryTheory.Limits.pullback`, not a chosen unidentified representative.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`. Read the recorded
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` as well:
  the geometric representative here encodes the field map directly by Yoneda.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  `Etale.etale_comp`, `Etale.of_comp`, plus the open-immersion etale instance.
  The algebraic-space etale predicate uses this recorded scheme notion.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite` and
  `IsIntegralHom` (ambient glossary only, as explained above).
- `def-weil-size-convention` is metatheoretic, with no owning module or object;
  the explicit universe u implements it. No derived construction occurs here.
- Proof-only imports: `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`
  (`chartwise_etale_permanence`),
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` (`etale_open_image`),
  and `Sheaf.EtaleCohomology.SepClosedFieldVanishing`
  (`AlgebraicGeometry.Etale.sepClosedField_etale_decomposition_and_vanishing`,
  first conjunct only). Their source signatures and docstrings were read.
  The remaining proof dependencies are already available in the public imports.
  No proof-only import is omitted for a cycle.

### Sources and edge cases

Read `literature/stacks-project/decent-spaces.tex`, the full statement and relevant
proof of `lemma-quasi-compact-reasonable-stratification` (07S8), and the degree
decrease in `lemma-there-is-a-scheme-integral-over` (09YB, lines 1855--1866).
The source explicitly uses that degree does not go up under specialization.
The five-step configuration-space proof from the node is in the theorem docstring.

Checked mathematically before writing:

- r = 0: D is the complement of the open image of W, including points where the
  fibre is empty. No positivity assumption on r or on N is present.
- Empty X: no geometric representatives, D is empty/universal in an empty point
  space, closed, and the dense-open clause is vacuous.
- Empty W: all geometric fibres are empty, the bound N = 0 works, and D is all X.
- Open immersion W -> X: fibre cardinalities are zero or one and D_0 is the
  closed complement of W. This tests the direction of the closed inequality.
- A disjoint union of d copies of X over a scheme X: D_r is empty for r < d and
  all X for r >= d. No nonempty fibre or surjectivity hypothesis is assumed.
- r >= N: D is all X. The node's finite bound is retained even though the
  configuration-space closedness argument itself does not require it.
- All characteristics and all universes u are allowed; S and X need not be
  separated. The topology and the quotient are the recorded shared definitions.

### Searches

All search wrappers used the group/item `Q128 lem-sfb-space-etale-closed-degree-loci`.

- `msearch.py ... leanfinder`: "For a quasi compact separated etale morphism to an
  algebraic space the locus of geometric fibres of cardinality at most n is closed".
  Eight hits: scheme `isClosedMap_isZariskiLocalAtTarget`, compactness of fibres,
  `LocallyQuasiFinite`, universally closed morphisms, and `isProper_eq`; none
  states the algebraic-space closed cardinality loci or the dense-open consequence.
- `msearch.py ... leansearch`: "closed bounded cardinality locus separated etale
  morphism algebraic space". Eight hits on ring etale loci and scheme Etale;
  none is the requested statement.
- `msearch.py ... loogle`: "AlgebraicGeometry.Etale, IsClosed". Zero hits.
- `msearch.py ... grep`: "AlgebraicSpace|[Ee]tale.*[Cc]ard|[Cc]ard.*[Ee]tale"
  under AlgebraicGeometry. Zero hits.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` with the preceding regex found
  scheme fibre-degree and constructible-sheaf stalk-cardinality lemmas, not this
  statement. `grep -rn` for the item id in `lean/WeilConjectures` found no match.
- `rg` in `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/TraceFormula` for geometric
  fibre/cardinality/bounded-degree and closed-degree patterns found the existing
  point, open-subspace, QC and separation interfaces, the diagonal-complement
  lemma, and consumers referring to this node; no existing declaration states it.
- `rg` for `etale_closed_degree_loci` in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` found no declaration with this name.
- The exact existing definition nodes owning the four added dependencies were
  found by reading the DAG's Lean records for the relevant modules. No new notion
  is needed and no existing notion is copied.

### Validation

Compiled the delivered file with the prescribed `scompile.py` on the live server.
The initial attempt exposed namespace shadowing: bare `pullback` resolved to the
etale pullback functor of AlgebraicSpace. Qualifying every fibre construction as
`Limits.pullback` repaired it. The final sandbox compile and the actual named
module compile both pass cleanly (1.9 s and 1.8 s); no diagnostics remain.
No local or global build was run. No live source was edited or Git command run.

No statement correction, disputed assertion, dependency-record repair or node
fault is required.

## Second reading by Q128

I reread the node and final file in a separate pass; the independent delivery
review remains the maintainer's. Each binder was checked against the mathematical
hypotheses: arbitrary S, W over S, X an algebraic space, a genuine Yoneda map f,
QC, separatedness, representable etaleness, and a uniform finite geometric bound.
The conclusion has both requested clauses, with the same r, actual point topology,
actual sheaf fibre products, and actual dense open subspaces. Quantification over
every algebraically closed representative gives the geometric-point independence,
and Cardinal.mk prevents infinite-cardinality misinterpretation. There is no added
QS assumption or requirement that f be onto. The empty and r = 0 cases remain.
The second pass found no mathematical mismatch; the only compilation repair was
qualification of the shadowed pullback name, already described above. The module
has one theorem, its full source/proof docstring, and one postponed proof, with
no scratch checks, new definition, private notation or local instance.
