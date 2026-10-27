## Worker report

States `AlgebraicGeometry.projectiveBundle_comp` in
`Sheaf.AlgebraicGeometry.ProjectiveBundleComposition`. Its sole theorem has a `sorry`
proof; it introduces no definition. The node changes only in its `lean` record.

The source was read in `literature/stacks-project/morphisms.tex`, lines 10805–10821:
Stacks Tag 0C4P, lemma-composition-projective. The node and source agree exactly.
The previous attempt confused Q28's reviewed stage-1 split with a stage-2 statement:
the live node has no `lean` record. This delivery supplies that missing statement.

Each hypothesis and clause is rendered as follows:

- Schemes A, B, C: `{A B C : Scheme.{u}}`, for an explicitly declared arbitrary universe u.
- Morphisms f:A→B and g:B→C: `(f : A ⟶ B) (g : B ⟶ C)`.
- Quasi-compactness of C: `[CompactSpace C]`; Mathlib imposes no Hausdorff condition.
- Quasi-separatedness of C: `[QuasiSeparatedSpace C]`. Mathlib's
  `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated` identifies this with the
  quasi-separated terminal structure map, matching the scheme convention.
- Projective-bundle projectivity of f and g: `(hf : IsProjectiveBundle f)` and
  `(hg : IsProjectiveBundle g)`, using the dependency's exact definition, with a finite-type
  quasi-coherent module and a closed immersion into its canonical relative Proj of Sym.
- Projective-bundle projectivity of g∘f: `IsProjectiveBundle (f ≫ g)`.

There is no hypothesis on the intermediate scheme B, and no field, Noetherian,
separated, positive-rank or finite-projective-space assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  recorded by def-pc-scheme. Imported publicly through ProjectiveBundleMorphism.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, recorded by
  def-weil-pbc-quasi-compact-scheme; available through the public geometry imports.
- def-weil-pbc-scheme-conventions is explicitly a convention collection with no
  declaration or module. Its quasi-separated scheme convention is represented by
  `QuasiSeparatedSpace`, publicly imported through
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle`, the recorded declaration of
  def-trf-projective-bundle-morphism, imported publicly without duplication.
- Proof-only imports: `Sheaf.TraceFormula.ProjectiveBundleProper` supplies
  `AlgebraicGeometry.projectiveBundle_proper` (lem-trf-projective-bundle-proper), and
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` supplies
  `AlgebraicGeometry.IsProper.instCompScheme` (lem-weil-pbc-proper-composition).
  The other three proof inputs have no recorded Lean declarations yet:
  lem-sfb-projective-bundle-relative-ample,
  lem-sfb-quasiprojective-qc-composition, and
  lem-sfb-proper-relative-ample-projective-bundle. They occur in the proof docstring;
  there is no module to import for them. They are not needed to type this statement.

Edge cases checked before writing: identities give back the same projective-bundle
predicate; empty A is permitted, as are empty B and C whenever the morphisms exist;
rank-zero/zero-module projective bundles are not excluded. Arbitrary universe u permits
all scheme sizes covered by the dependency. Quasi-compactness is not a separatedness
or Hausdorff assumption. Only the final base has qcqs assumptions. No node fault or
STATEMENT-DISPUTED issue was found.

Searches made with `msearch.py N6 lem-sfb-projective-bundle-composition`:

- leanfinder: "Composition of projective bundle morphisms over a quasi compact quasi
  separated scheme is projective". Eight hits concern properness composition,
  quasi-compactness/quasi-separatedness composition and an absolute Proj formula;
  none states projective-bundle projectivity of the composite.
- loogle: `"AlgebraicGeometry", "IsProjective"`. Zero hits.
- grep, Mathlib AlgebraicGeometry: `IsProjectiveBundle|[Pp]rojective.*[Cc]omp`.
  Zero hits.
- leansearch: "Composition of projective morphisms of schemes over a quasi compact
  quasi separated scheme is projective". Eight hits concern quasi-compactness,
  affine/separated/quasi-separated composition and properness; none is the item.
- `rg -n` in project `lean/WeilConjectures` and `lean/Sheaf` for projective-bundle
  composition and `projectiveBundle_comp`: no matching theorem. Existing projective
  bundle pullback coherence and flag-unit component declarations are different statements.
- `grep -rn "lem-sfb-projective-bundle-composition" lean/WeilConjectures`: no hits.
  Some Sheaf consumer docstrings mention the node; they do not state its theorem.
- Read `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: its `IsProjective`
  requires an H-projective finite-projective-space embedding, so it is not substituted
  for the required projective-bundle predicate.

Validation: compiled with the prescribed scompile.py against the published live library;
expected `sorry` warnings alone are permitted. The dry run and delivery results are
recorded by deliver2.py.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
