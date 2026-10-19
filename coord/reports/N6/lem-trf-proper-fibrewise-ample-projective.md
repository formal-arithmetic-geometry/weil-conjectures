# Stage-2 repair: lem-trf-proper-fibrewise-ample-projective

## Worker report

This delivery supplies the previously absent Lean statement in
`Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective`, with main declaration
`AlgebraicGeometry.proper_fibrewise_ample_projective`. Its sole postponed proof is
`sorry`. The auxiliary `AlgebraicGeometry.normalizedFibreComponentDegree` contains
real data: the existing cohomological degree of the actual pulled-back module on
`Z.normalization`, with its structure map explicitly composed to `Spec K`.
No new definition node, dependency repair, or statement correction is required.

The returned head `991455d07825` contained a stage-1 split, no Lean record, and no
Lean module. Its review identified the incorrect `## Review by N6` heading; its
replacement report was placed at a path that `--apply-fixes` does not accept.
The sandbox at this retry contained only dispatcher marker files. I compared the
immutable packet and review with the current node: the mathematical statement
and its six-step proof route agree. I reconstructed the delivery on the current
node, preserving all of its current non-owned fields rather than restoring the
old stage-1 `split_report`. This report supplies the exact required headings,
and the delivery now contains the actual stage-2 statement, not an unchanged
re-push of the stage-1 packet. `deliver2.py` rebases its packet on current
`origin/newtargets-dag` through its authorized bookkeeping.

Hypotheses and clauses, matched individually:

- Noetherian schemes Y and X: `{X Y : Scheme.{u}} [IsNoetherian X]
  [IsNoetherian Y]`. Mathlib's class is locally Noetherian plus compactness;
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with exactly a
  finite affine cover by spectra of Noetherian rings. No separation of X or Y
  over an additional base is assumed.
- The specified proper map: `(f : Y ⟶ X) [IsProper f]`. This is the recorded
  properness class, including separatedness, universal closedness, and finite
  type (quasi-compactness follows from universal closedness).
- An invertible O_Y-module: `(L : Y.Modules) [L.IsInvertible]`, using the
  recorded Zariski-locally-trivial rank-one predicate. It already entails
  quasi-coherence; no separate stronger condition is added.
- Every geometric fibre has dimension at most one: `hdim` quantifies over every
  field `K : Type u` with `[IsAlgClosed K]` and every `x : Spec (.of K) ⟶ X`,
  and asserts `topologicalKrullDim ↥(pullback f x) ≤ 1`. This uses the exact
  recorded fibre product and topological Krull dimension. In particular it
  includes the algebraic closure of every residue field. The field universe
  is the scheme universe, not an independent smaller universe: all residue
  fields and their algebraic closures fit. Testing larger geometric points
  gives the same property by field-extension invariance, so no geometric
  point case is lost to this size convention.
- Every one-dimensional irreducible component of the reduced geometric fibre:
  `hdegree` ranges over integral schemes `Z` and maps `i : Z ⟶ pullback f x`,
  requiring `IsClosedImmersion i`, `Set.range i ∈ irreducibleComponents
  ↥(pullback f x)`, and `topologicalKrullDim Z = 1`. An integral closed
  subscheme with component support is exactly the reduced induced component:
  its defining ideal is radical and its closed support determines that radical
  ideal. Reduction does not change the fibre's topological components. The
  quantifier over such presentations includes each reduced component and
  permits all its isomorphic presentations; it neither tests arbitrary
  subcurves nor assumes the fibre itself integral or reduced.
- Positive degree after normalization: the conclusion of each test is
  `0 < normalizedFibreComponentDegree f L K x i`. The helper calls the recorded
  `Scheme.Modules.degree` on `Z.normalization` with field structure
  `Z.fromNormalization ≫ i ≫ pullback.snd f x`, and on the module pulled back
  along `Z.fromNormalization ≫ i ≫ pullback.fst f x`. Thus degree is measured
  over the geometric-point field, not the component's function field. The
  normalization is the actual recorded construction, not a witness chosen
  from a mere existence statement.
- f-ampleness over every affine open: the first conjunct is `∀ U : X.Opens,
  IsAffineOpen U → Scheme.Modules.IsAmple (f ⁻¹ᵁ U).toScheme
  ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L)`. This uses the recorded
  absolute ample predicate on the inverse-image open scheme.
- A positive tensor exponent: the second conjunct begins `∃ n : ℕ, 0 < n ∧`.
- A finite-type quasi-coherent O_X-module: the same conjunct quantifies
  `∃ (E : X.Modules) (hE : E.IsQuasicoherent), E.IsFiniteType ∧`.
  E is not assumed locally free. These are exactly the predicates used by
  the recorded projective-bundle definition.
- The actual projective bundle: its target is
  `(@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProj`, the canonical
  relative Proj of the symmetric-degree graded algebra of E. No arbitrary
  graded algebra or projective-space model is substituted.
- A closed immersion over X: `∃ i : Y ⟶ ...`, `IsClosedImmersion i`, and
  `i ≫ ...relProjHom = f`. Thus it is an X-morphism, not an unrelated
  embedding of the underlying scheme.
- Pullback of O(1) equals the same tensor power: `∃ O1 : ...relProj.Modules,
  Nonempty (TautologicalTwistData X ... O1) ∧ Nonempty
  ((Scheme.Modules.pullback i).obj O1 ≅ L.tensorPow n)`. The first condition
  identifies O1 as the actual degree-one twist: every affine chart restricts
  it to `Proj.twist ... 1`, the restriction maps act on homogeneous generators
  as the canonical localization maps, and `chart_overlap` enforces gluing.
  This is not an arbitrary line bundle or an unnormalized family of local
  isomorphisms. The existing structure works for any graded algebra data and
  imposes no finite-locally-free hypothesis on E. For Sym(E), degree one
  generates, so these compatible normalized charts characterize O(1) up to
  isomorphism, exactly the equality notion needed by the pullback clause.
- The final stated projectivity consequence is the third conjunct,
  `IsProjectiveBundle f`, using the dependency declaration unchanged.

Dependency declarations read and reused:

- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, whose codomain is
  `WithBot ℕ∞`, including dimension minus infinity for the empty space.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`; its signature takes the field,
  field-scheme structure, and module, and computes chi(L) minus chi(O).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, its pullback instance, and `tensorPow`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization` and `Scheme.fromNormalization` for an integral scheme.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`;
  this uses `SymmetricAlgebraSheaf.gradedAlgebraData`, finite type,
  quasi-coherence, closed immersion, and the over-base equation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, and `pullback.snd` on schemes; the geometric-fibre dependency
  explicitly records this specialization and needs no private replacement.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used in Mathlib's
  `IsLocallyNoetherian`/`IsNoetherian` characterization in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- The additional already-landed dependency
  `lem-pur-projective-bundle-tautological-geometry` records
  `AlgebraicGeometry.TautologicalTwistData` in
  `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`. I opened
  its full structure, `tautologicalTransport`, and tensor-pullback comparison.
  Only this definition is used; its finite-locally-free geometry theorem is
  not applied or assumed. The owning node is added to `stmt_deps` under the
  stage-2 rule permitting an added dependency with a landed Lean record.
  Reading its transitive dependencies found no path back to this item.

All recorded proof-dependency modules are imported without `public` when
not already public statement imports: proper coherent higher direct images,
ampleness descent, coherent locality, and the quasi-coherent finite-type
predicate. The five stage-1-only auxiliary proof nodes have no recorded Lean
module and thus supply no import yet. The docstring records all six proof
steps, including geometric-to-ordinary fibre descent and the two steps making
the evaluation immersion closed. No proof prerequisite was assumed as an
extra hypothesis.

Edge cases checked before writing: empty X or Y; empty and zero-dimensional
fibres; a point fibre; reducible and nonreduced fibres; a component with degree
zero; every characteristic; n=0; E of rank zero on part of the base; and E
finite type but not locally free. Empty/zero-dimensional fibres impose no
component-degree test, while dimension minus infinity still satisfies the
bound. A degree-zero one-dimensional component fails the strict positivity
hypothesis. The existence conclusion requires n>0; tensorPow has its actual
unit at zero. No smoothness, flatness, reducedness of Y, nonemptiness,
finite-locally-free condition on E, or characteristic exclusion is introduced.

Searches made (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: "proper morphism Noetherian schemes positive degrees line bundle
  normalized components geometric fibres dimension one relatively ample
  projective embedding". Eight results about Proj properness, its valuative
  criterion, and relative normalization; none states this theorem.
- Loogle: "IsProjectiveBundle, IsAmple, Scheme.Modules.degree". Zero results;
  IsProjectiveBundle is unknown to that Mathlib service.
- Mathlib grep in AlgebraicGeometry:
  `ample.*[Ff]ibre|ample.*[Ff]iber|IsProjectiveBundle|relativelyAmple`.
  Zero results.
- LeanSearch: "proper family of curves positive degree on irreducible
  components of every geometric fibre implies relatively ample invertible
  sheaf". Eight properness definitions/constructors, no matching theorem.
- Direct `rg -n` in upstream WeilConjectures and project lean/Sheaf for
  fibrewise/fiberwise, degree-and-ample, relative ampleness, and projective
  bundle terminology: found the absolute smooth-curve criterion in
  Curve/RiemannRoch, degree positivity in Modules/Ample, the projective-bundle
  predicate, and the normalized tautological chart structure. None states
  this proper-family theorem. Their full relevant declarations were read.
- `grep -rn lem-trf-proper-fibrewise-ample-projective` in the upstream source
  returned no declaration. The current item's Lean record is absent, as in
  the returned immutable packet. The added helper's name was checked against
  the source and project declaration searches and by clean elaboration.

The Stacks source passages were reopened locally: varieties.tex at
lemma-ampleness-in-terms-of-degrees-components; more-morphisms.tex at
lemma-ample-in-neighbourhood; and morphisms.tex at
lemma-relatively-very-ample and lemma-finite-type-ample-very-ample.
There is no statement dispute or source correction.

Validation: `scompile.py` compiled the sandbox statement and its named library
module cleanly (8.0s and 3.7s respectively). The first elaboration required an
explicit scheme-to-type coercion `↥(pullback f x)` in the topological predicates;
that was repaired and the final module has no diagnostics. All variables and
universes are explicit, `autoImplicit` is false, and no declaration is proved
in this delivery.

## Second reading by N6

I reopened the completed module, its verbatim Lean record, the current item,
and the recorded dependency declarations after the first compilation. This
final reading is carried out in this worker, as the dispatch brief prohibits
starting another agent; it is not represented as a separate reviewer approval.
The maintainer's independent review remains the delivery gate.

The mathematical checklist found: two Noetherian schemes and the same proper
f map; the same invertible L; universal algebraically closed field-valued fibre
tests of dimension at most one; precisely integral reduced closed components
of dimension one; the actual normalization map and geometric-field degree;
strict positivity; ample restriction on every inverse-image affine base open;
one common positive n; a finite-type quasi-coherent E; the canonical relative
Proj of Sym(E); a closed immersion over X; normalized compatible degree-one
twist charts; a global pullback isomorphism to L.tensorPow n; and the exact
recorded IsProjectiveBundle predicate. Every hypothesis and clause matches its
Lean expression in the checklist above.

I checked especially that the normalization degree's field map uses the second
projection while its module pullback uses the first projection. I checked the
four fields of TautologicalTwistData, so the O(1) clause does not merely ask for
unrelated local isomorphisms. Its general definition has no locally-free-rank
binder; the finite locally free hypothesis belongs only to the other theorem
in that imported module. I checked that no normalization finiteness, smoothness,
flatness, or nonempty-fibre assumption appears in the new theorem. Empty and
zero-dimensional fibres, nonreduced/reducible fibres, arbitrary finite-type E,
and positive rather than zero tensor exponents remain covered. There are no
new nodes or dependency modules to reread.

The repairs to the return are concrete: the required report heading is now
present; the current packet contains the missing Lean module and binding;
and the report no longer labels a stage-1 split with no Lean declaration as a
completed stage-2 formalization. The six-step source route and informal
statement are unchanged.
