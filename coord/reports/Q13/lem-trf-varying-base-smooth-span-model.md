## Worker report

The module `Sheaf.AlgebraicGeometry.VaryingBaseSmoothSpanModel` states
`AlgebraicGeometry.exists_varyingBase_smooth_span_model` with one `sorry`.
The real-data helper `AlgebraicGeometry.varyingBaseSpanProjection` is `pullback.map`
with identity on the original family and `r` on the varying base. All variables
and the universe `u` are explicit, with both auto-implicit options disabled.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0GDX,
`lemma-relative-map-approximation-pre`, especially the second and third proof
paragraphs constructing smooth affine stages, factoring the map to T, fixing
X_i and Y_i, and descending the span. The item is an auxiliary statement,
not the blueprint unit's own statement. No statement correction is needed.

Hypotheses, in order:

- S = Spec R and T = Spec D are rendered with `R D : CommRingCat.{u}`.
  The maps `sZ`, `tZ` to `Spec (.of (ULift.{u} ℤ))`, with
  `LocallyOfFiniteType` and `QuasiCompact`, express finite type over Spec ℤ.
  The lift realizes the integers in the same universe as the schemes; it
  imposes no size or characteristic restriction.
- X and Y are arbitrary `Scheme.{u}` with `IsAffine` instances; `f`, `g`
  are their structure morphisms. Their `LocallyOfFiniteType` and
  `QuasiCompact` instances express finite type, with the same conjunction
  as the recorded finite-type dependency.
- `s : Spec R` is arbitrary. The repeated `AdicCompletion` type is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
  ((Spec R).presheaf.stalk s)`. Thus A is the actual stalk, not another local
  ring or an assumed localization. B is its actual spectrum.
- `b` is a point of this B and `hb : IsClosed ({b} : Set B)` specifies its
  closed point. A is Noetherian under the finite-type hypothesis, and its
  maximal-ideal completion is local, so this is exactly the unique closed
  point, without imposing an extra Noetherian instance as a hypothesis.
- `lam : B ⟶ Spec D` is the arbitrary varying map; t is represented by
  `lam b`. the explicit composite `Spec.map (CommRingCat.ofHom (algebraMap A Â)) ≫
  (Spec R).fromSpecStalk s` is the canonical B → S (A and Â abbreviate the
  displayed stalk and completion types only in this report).
- `H` is affine and `p : H ⟶ B` is locally of finite presentation. Since
  H and B are affine, p is automatically quasi-compact and quasi-separated,
  so this says exactly finite presentation, including the global clauses.
- `h : H` and `hh : p h = b` give the marked point over b.
- `a : H ⟶ pullback f β` (β denotes that explicit composite in this report) and
  `c : H ⟶ pullback g lam` have the actual prescribed targets X_B and Y_B.
  `Etale a`, `Etale c` give étaleness; `ha`, `hc` say that both are
  B-morphisms. `haκ`, `hcκ` assert that their canonical residue maps at h
  are isomorphisms. The points x_B and y_B are the expressions `a h`, `c h`.

Conclusions, in order:

- `∃ V q, IsAffine V ∧ Smooth q` is the affine S' with smooth q : S' → S.
- The next existentials give `r : B ⟶ V`, `lam' : V ⟶ Spec D`,
  `hr : r ≫ q = β` (with the composite written out in Lean), and
  `hlam : r ≫ lam' = lam`. These say exactly that r is over S and factors
  the given varying map. The name `hlam` denotes a proof, not a new map.
- `H'`, `p' : H' ⟶ V`, `IsAffine H'` and
  `LocallyOfFinitePresentation p'` give the affine finitely presented model.
  Again all bases are affine, so the global finite-presentation clauses follow.
- `a' : H' ⟶ pullback f q` and `c' : H' ⟶ pullback g lam'` are the
  prescribed arrows to X' and Y'. Both `Etale` predicates and both equations
  with `pullback.snd` give exactly étale S'-morphisms.
- `e : pullback p' r ≅ H` and its equation after `p` give the B-isomorphism.
  The following two equations compare `e.hom ≫ a` and `e.hom ≫ c` after
  the canonical projections to X' and Y'. Together with the B-equation,
  they characterize equality with the actual base-changed stage arrows:
  the other projections are fixed by `ha`, `hc` and the two stage equations;
  the universal property of each pullback gives precisely the comparison
  with X_B and Y_B. No arbitrary comparison isomorphism or arbitrary map
  has been substituted for an actual base change.
- Write h' = `(e.inv ≫ pullback.fst p' r) h`, x' = `a' h'`,
  y' = `c' h'`, and s' = `r b`. These are expressions, not opaque let binders.
  The five point equations give q(s')=s, lam'(s')=t and h', x', y' over s'.
- `IsIso (q.residueFieldMap (r b))` and
  `IsIso (r.residueFieldMap b)` are the two canonical arrows in
  κ(s) → κ(s') → κ(b). The point equations identify their domains correctly.
- The next two `IsIso` clauses apply the canonical pullback projections at
  `a h` and `c h`. Their domains are κ(x') and κ(y'): evaluating the two
  arrow comparison equations at e⁻¹(h) identifies their image points with
  x', y'. They are exactly κ(x') → κ(x_B), κ(y') → κ(y_B).
- `IsIso ((e.inv ≫ pullback.fst p' r).residueFieldMap h)` is κ(h') → κ(h).
  The final two `IsIso` clauses are κ(x') → κ(h') and κ(y') → κ(h').
  Thus all seven canonical residue maps in the node appear explicitly.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  and its quasi-compactness import: `QuasiCompact`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`
  and its ring and algebra structures.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`. The scheme-conventions node is a convention
  record, so it has no module or declaration to import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`. The completion
  algebraMap and `Spec.map` are composed directly in every occurrence of the
  canonical B → S map. The item has exactly its original stmt_deps.

The recorded proof-dependency modules are imported privately, including
`Sheaf.AlgebraicGeometry.FixedFamilyEtaleSpanDescent` and the upstream
G-ring, Noetherian completion, directed reindexing, finite-type integer G-ring,
localization regularity, regular composition, Popescu and affine limit modules.
Mathlib leaves use their recorded modules. The theorem docstring follows all
eight proof steps, including deriving ring finite presentation from the scheme
hypotheses instead of identifying those assertions by definition.

Edge cases checked mathematically before writing: s may be generic or closed,
of characteristic zero or positive characteristic; no perfectness, finite
residue field, closedness of s in S, or finite residue extension is assumed.
Empty S has no s; an empty span H has no h, exactly as the node requires.
A zero coordinate ring is likewise excluded only by the specified point.
Fields and zero-dimensional bases have their ordinary zero-ideal completion.
The two étale arrows need not be surjective; H need not be connected. No
arbitrary-index universe was introduced. The factorization of the base residue
isomorphism through a field proves both arrows are isomorphisms at every
smooth stage, which verifies the key pointed edge of the construction.

Searches actually run:

- `msearch.py ... leanfinder` with “An etale span over a completed local base
  descends to a smooth affine model while a map to a finite type integer scheme
  factors through that model”: eight hits, about standard smooth charts,
  localization-span étaleness and related morphism properties; no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale"`:
  one hit, `AlgebraicGeometry.Etale.instSmooth`; not this theorem.
- `msearch.py ... grep 'smooth.*span|span.*smooth|varying.*base' AlgebraicGeometry`:
  no hits in Mathlib.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for smooth spans,
  varyingBase/varying_base and the item id found no exact theorem. The literal
  `grep -rn` for this blueprint id in `lean/WeilConjectures` had no hit.
  The source, Sheaf, Mathlib and upstream-name index searches for both new
  declaration names found no collisions.
- Searching completion-base constructions found the existing
  `Scheme.completionBaseMap`. Following the H2 return, its defining composite
  is written directly in the statement; there is no duplicate declaration. The
  fixed-family affine-span and étale-span descent declarations were read in full;
  both require an already-given inverse system, so neither states this item.

Validation: the module compiled cleanly through scompile.py in both sandbox
and library modes, with no errors or non-sorry warnings. Delivery preflight
and another per-file compile passed through deliver2.py --no-push (OK).
No `STATEMENT-DISPUTED` issue, new definition node, or dependency repair.

## Second reading by Q13

This is a second self-reading, not an independent review: the dispatcher brief
forbids starting other agents and assigns the independent reading to the
maintainer. I reread the node and the final file together. The potentially
subtle clauses were checked explicitly: finite presentation uses affineness
rather than dropping quasi-separatedness; the completed base is the actual
stalk completion; hb selects the unique closed point without a new assumption;
all arrows have the fixed original families as their pullback targets; the
B-equation and both projection equations enforce actual base-change agreement;
and all seven residue maps have their canonical source points. The point
identifications needed for the two target residue maps follow by evaluating
the displayed arrow equations at e⁻¹(h), not by an unstated choice. The
compiler caught the reserved identifier λ and a split dotted-notation line;
these were repaired to `lam` and an explicit `Scheme.Hom.residueFieldMap` call.
No mathematical hypothesis or conclusion was changed during that repair.

## Returned delivery repair

H2 (immutable head 63041f55d4b9): removed the added theorem node
`lem-trf-completed-local-base-change` from stmt_deps, restoring exactly the
current main branch's original list. In every occurrence of the canonical
B → S morphism, the Lean statement now writes the actual composite
`Spec.map (CommRingCat.ofHom (algebraMap A Â)) ≫ (Spec R).fromSpecStalk s`,
with A and Â expanded to the actual stalk and its maximal-ideal completion.
Removed the import of `Sheaf.AlgebraicGeometry.CompletedLocalBaseChange` and
imported `Mathlib.AlgebraicGeometry.Stalk` publicly instead. This is the
maintainer's second proposed repair, with no new node or definition.

Compared the retained sandbox node against current main: before repair the
only changed fields were lean and the added stmt_dep; after repair only lean
differs. The wrapper refreshes current main and builds the new delivery commit.
All hypotheses, conclusion clauses, the real-data pullback projection helper,
and the proof sketch retain the independently accepted content. The explicit
composite is definitionally the old map. Updated the verbatim lean.statement
and this report; no mathematical statement correction is involved.
