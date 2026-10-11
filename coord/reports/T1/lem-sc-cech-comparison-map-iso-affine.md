## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine` states
`AlgebraicGeometry.Scheme.Modules.moduleCechComparison_isIso_of_affine` with proof `sorry`.
It asserts invertibility of the canonical comparison itself, rather than the existence
of an unspecified equivalence. There are no definitions or additional theorem nodes.

Clause-by-clause reading:

- A scheme X is `(X : Scheme.{u})`.
- The indexed family of open subschemes is `{ι : Type u} (U : ι → X.Opens)`.
  As in both recorded Čech dependencies, the index lies in the scheme's universe;
  the universe u is explicit and arbitrary.
- The covering condition is `(hcover : iSup U = ⊤)`, with no finiteness,
  nonemptiness, separatedness or Noetherian hypothesis.
- Every intersection of p+1 members is affine is
  `(hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))`.
  The tuple can repeat indices. The zero-fold intersection is not required affine.
- The O_X-module F is `(F : X.Modules)` and quasi-coherence is
  `[SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]`.
  This is the Mathlib notion explicitly endorsed by pqf-def-coherent's module,
  not the stronger coherent predicate recorded as that node's main declaration.
- Every nonnegative degree is `(p : ℕ)`.
- Čech cohomology is
  `((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p`.
  Sections are modules over Γ(X,O_X), with the existing presheaf restricting scalars.
- Sheaf cohomology is `(RingedSpace.moduleCohomology X.toRingedSpace p).obj F`.
  This is right-derived module-valued global sections in Mod(O_X), as required
  by the project's cohomology convention.
- The map c has precisely these source and target objects. The binder
  `(hc : IsModuleCechComparison U F p c)` identifies it as the canonical map
  of the naturality dependency: the shared predicate requires the alpha/beta
  equation for every injective resolution. This is a characterization of the
  named map, not an extra geometric hypothesis. Its existence is supplied by
  lem-sc-cech-comparison-map-naturality; the statement applies to every such map.
- `IsIso c` says that this particular canonical map gives the Čech/cohomology
  identification. There is no second chosen isomorphism to which it must be equal:
  lem-pc-cech-computes records only `Nonempty` of equivalences, not a chosen map.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  read their signatures and Scheme's locally affine locally ringed-space data.
- Sheaf.AlgebraicGeometry.Coherent: AlgebraicGeometry.RingedSpace.IsCoherent;
  read its full definition and documentation of Mathlib quasi-coherence. Only the
  latter notion is needed here. The coherent module itself is not imported unused.
- Sheaf.Paper.CechComparisonMapNaturality:
  AlgebraicGeometry.Scheme.Modules.cechComparisonMapNaturality. Read the full
  reviewed signature from its node record and the source delivery module in C1's
  sandbox (the latter still has its pre-review ∃! form). Its reviewed signature
  supplies existence for each F and naturality for all predicate-satisfying maps.
  The source file named by the record is not yet present in this clone/library;
  no replacement is created, and the current statement only needs the already
  landed characterization definition, not the naturality theorem as an import.
- WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray:
  AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H. Read the
  entire signature, docstring and implementation: nonempty finite Finset
  intersections affine, cover, quasi-coherence, every degree, Nonempty of a
  Γ(X,O_X)-linear equivalence into F.H. This uses abelian-sheaf cohomology and
  explicitly says the edge map is not named. Therefore it does not already
  state this item; it is a proof dependency/identification, not an import needed
  for the new signature. Stage 3 must bridge the cohomology encodings and show
  canonicality, rather than infer canonicality from bare Nonempty.
- Sheaf.AlgebraicGeometry.ModuleCechComparison:
  AlgebraicGeometry.Scheme.Modules.IsModuleCechComparison. Read the full predicate
  and its alpha/beta and resolution-identification declarations. Added its
  already-landed node `def-sc-module-cech-comparison` to stmt_deps, as permitted
  for landed notions needed by the signature. No new definition is made.
- Also read RingedSpace.moduleCohomology (Sheaf.Topology.RingedSpaceModuleCohomology)
  and Scheme.Modules.presheafModuleCat
  (WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf).

Edge cases: p=0 asserts the gluing/global-section identification is invertible;
for the zero module both sides vanish; a singleton affine cover has only the
one affine open condition; repeated indices and disjoint opens are included
(the empty intersection open is affine); an empty index type is permitted, and
hcover then forces X empty. No affine condition on X or on an empty tuple is
added, so a non-affine X with affine-intersection cover remains covered. No
characteristic restriction or finite-cover restriction is imposed.

Searches performed with msearch.py (T1, this item):

- leansearch: `Cech comparison map isomorphism quasi coherent sheaf affine open
  intersections`: unavailable, Internal Server Error; no search verdict inferred.
- leanfinder: `Canonical Cech cohomology comparison is an isomorphism for a quasi
  coherent sheaf on an affine intersection open cover`: eight hits concerning
  affine Zariski equivalence, gluing and componentwise sheaf isomorphisms;
  none states invertibility of the canonical cohomology comparison.
- loogle: `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H,
  IsModuleCechComparison`: zero hits, unknown identifier for the project name.
- grep Mathlib: `cech.*comparison|comparison.*cech|IsModuleCechComparison`:
  no hits. Explicit rg in WeilConjectures and lean/Sheaf for
  `IsModuleCechComparison|moduleCechComparison.*[Ii]so` finds only the shared
  predicate and affine naturality sibling in Sheaf, no isomorphism theorem.
- rg in WeilConjectures for this item id: no hits. Read the upstream Leray
  declaration found via dag/lean_names_upstream.json. The proposed name
  moduleCechComparison_isIso_of_affine has no upstream/DAG-name match.

Source read online because this machine's literature/stacks-project checkout
is absent: [01XD](https://stacks.math.columbia.edu/tag/01XD),
[01ET](https://stacks.math.columbia.edu/tag/01ET), and
[01EQ](https://stacks.math.columbia.edu/tag/01EQ).
01XD gives the module-valued Čech identification; 01ET derives it from
vanishing on intersections; 01EQ gives the alpha/beta canonical comparison.
No mathematical statement correction or STATEMENT-DISPUTED flag is needed.

Validation: lcompile.py compiled the module cleanly, with explicit universes
and auto-implicit variables disabled. The sole theorem has proof `sorry`.
The final server compile and preflight are run by deliver2.py --no-push;
second reading and push are left to the appointed second reader.

## Second reading by T1

The node introduces, in order: a scheme `X : Scheme.{u}`; an index type
`ι : Type u` and family of opens `U : ι → X.Opens`; the cover hypothesis
`hcover : iSup U = ⊤`; the affine-intersection hypothesis for every
`n : ℕ` and `y : Fin (n + 1) → ι`; a module `F : X.Modules` with the
quasi-coherence instance; a degree `p : ℕ`; the Čech cohomology object;
the module cohomology object; and the canonical comparison map.  The Lean
signature renders these as `(X : Scheme.{u})`, `{ι : Type u}`, `U`, `hU`,
`hcover`, `F`, `[SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]`,
`p`, and `c` with exactly the source and target displayed in the node.
The final hypothesis `hc : IsModuleCechComparison U F p c` is the recorded
canonical-map characterization from `def-sc-module-cech-comparison`, and
the conclusion `IsIso c` states that this canonical comparison is an
isomorphism.  Quantifier order, universes, and all clauses agree; no
additional finiteness, separatedness, Noetherian, characteristic, or affine
assumption occurs.

The source place was checked against Stacks Tags 01XD, 01ET, and 01EQ.
Tag 01XD assumes precisely a scheme, an open cover, affine finite
intersections, and a quasi-coherent sheaf, and asserts the Čech/cohomology
identification for every degree.  Tag 01EQ supplies the canonical map;
`IsModuleCechComparison` is the project's explicit encoding of that map.
The dependency declarations were checked: `IsModuleCechComparison` has the
same source and target as `c`, and `nonempty_cechComplex_linearEquiv_H` is
only the previously recorded existence of an abstract equivalence, so it
does not duplicate this canonical-map statement.

Edge cases are covered: `p = 0`; the zero module; an empty index type (where
`hcover` forces an empty scheme); singleton covers; repeated indices;
empty intersections (which are affine opens); non-affine `X`; and arbitrary
universe `u`.  No characteristic or nonemptiness hypothesis is introduced.

Searches were rechecked with `rg` in Mathlib, `WeilConjectures`, and
`lean/Sheaf`, plus the recorded LeanFinder/Loogle searches.  No declaration
of this comparison-isomorphism theorem exists elsewhere; the only related
declarations are the shared predicate, the naturality theorem, and the
abstract nonempty equivalence.  No mismatch was found and no file was
changed.  The sandbox module compiles with `lcompile.py`; its only warning is
the permitted theorem `sorry`.
