## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveFiniteGeometricFibres` states
`AlgebraicGeometry.isFinite_of_isProjective_of_finite_geometricFibres` with `sorry`.
No definitions, new nodes, dependency replacements or statement corrections are needed.

Hypothesis and conclusion correspondence:
- Schemes D and T and morphism f: `{D T : Scheme.{u}} (f : D ⟶ T)`.
- Projective morphism, with the blueprint H-projective convention: `[IsProjective f]`.
- Locally Noetherian target: `[IsLocallyNoetherian T]`.
- Quasi-compact target: `[CompactSpace T]`. This is quasi-compactness of the underlying
  topological space, with no Hausdorff requirement; together with the preceding hypothesis it
  is precisely Noetherian as defined in the node and in Mathlib `IsNoetherian`.
- Every geometric fibre has finitely many points: `hf : ∀ t : T, Finite (...)`, where the
  type inside `Finite` is the underlying point type of the scheme
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
  (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t)`.
  This is exactly the expression prescribed in `def-weil-geometric-fibre`'s recorded
  declaration and note, using the chosen standard algebraic closure. An explicit
  `Scheme.{u}` annotation makes the category of the pullback unambiguous.
- Finite conclusion: `IsFinite f`, the affine-local finite-module condition.

Dependency declarations read and used:
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsProjective`,
  extending `IsHProjective` and `QuasiCompact`. The recorded module is absent from the local
  source snapshots, so its complete source was read directly, read-only, on the server.
  Its finite coordinate-type formulation agrees with the blueprint finite-dimensional
  projective-space formulation: enumerate a nonempty finite coordinate type; the empty
  coordinate type gives empty projective space and hence only the empty source, which also
  embeds in projective zero-space. No replacement definition is introduced.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  its affine-cover characterization is documented by the dependency record. Also read
  `IsNoetherian`, which extends `IsLocallyNoetherian` and `CompactSpace`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, imported through `Mathlib.AlgebraicGeometry.Fiber`.
  Read the full signature and docstring. `Scheme.residueField` and
  `Scheme.fromSpecResidueField` are the standard residue field and its canonical point map.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, in the same
  universe as the residue field; `algebraMap` gives its specified field inclusion.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.

The proof docstring reproduces the node's three-step proof: projective implies proper;
faithful flatness of the algebraic closure and surjectivity after base change give finite
ordinary fibres from finite geometric fibres; Tag 02OG implies finiteness. Proof imports
include the recorded `ProjectiveSpace.instIsProper`, the faithful-flat tensor-product
instance and `PrimeSpectrum.comap_surjective_of_faithfullyFlat`, and
`Sheaf.AlgebraicGeometry.FiniteIffProperFiniteFibres` with
`AlgebraicGeometry.isFinite_iff_isProper_and_hasFiniteFibres`. The ordinary fibre and
base-change-surjectivity proof dependencies are supplied by the public Fiber import.

Edge cases checked before writing: the empty target makes the universal fibre condition
vacuous and forces the source empty; an empty source or individual empty fibre is allowed
by `Finite`; nilpotents are unrestricted because only the underlying points are counted;
projective dimension zero is allowed by the projectivity definition; no field characteristic,
connectedness, reducedness, surjectivity or flatness hypothesis was added. The sole universe
`u` covers arbitrary schemes, and the algebraic closure has the residue field's universe,
so there is no smaller-universe test-object quantification. Fixing the standard algebraic
closure loses no geometric fibres, since alternative algebraic closures are isomorphic.

Searches for existing declarations:
- `msearch.py leanfinder`, query "A projective morphism with Noetherian target and finite
  geometric fibres is finite": eight hits, including properness of finite morphisms,
  `IsFinite.iff_isProper_and_isAffineHom`, and properness of Proj; no exact statement.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProjective`:
  zero hits, unknown identifier `AlgebraicGeometry.IsProjective` in the Mathlib service.
- `msearch.py grep`, query `of_isProper_of_locallyQuasiFinite|finite.*geometric|finite.*projective`
  in `AlgebraicGeometry`: four hits in ZariskisMainTheorem. Read
  `IsFinite.of_isProper_of_locallyQuasiFinite` and its iff: these need properness and local
  quasi-finiteness, so are not the requested projectivity/geometric-fibre statement.
- `rg` of the source `WeilConjectures` and the project's `lean/Sheaf` for geometric fibres,
  finite fibres and projective finiteness found the general proper/finite-fibres criterion
  and unrelated field-base geometric fibres, but no exact theorem. The exact node-id search
  in source `WeilConjectures` returned no matches. Declaration-name search in `lean/Sheaf`
  and `dag/lean_names_upstream.json` returned no collision.

No statement dispute or mathematical node fault found. All writes are in the item sandbox;
compilation uses only `scompile.py` on the server, with nice 19, two threads and 60 seconds
per file. The delivery dry run is performed with `--no-push`; the independent second reader
will supply their own reading and deliver.


## Second reading by NW

Read independently against the item node, its master-blueprint source, the four statement
dependency nodes and their actual declarations, and the proof-dependency records. Read Stacks
`coherent.tex`, lemma-characterize-finite (02OG), `morphisms.tex`,
lemma-locally-projective-proper (01WC), and `properties.tex`, definition-noetherian (01OV).
These places impose no ambient field, characteristic, reducedness or connectedness assumption.
The blueprint assumes exactly the Noetherian target stated by the node; 02OG itself needs only
locally Noetherian, which does not authorize dropping the node's quasi-compactness hypothesis.

Object/hypothesis/conclusion checklist, written from the natural statement:

- Schemes D and T: `{D T : Scheme.{u}}`. PASS: arbitrary schemes, without nonemptiness,
  separation or field-base restrictions.
- A morphism f from D to T: `(f : D ⟶ T)`. PASS: correct direction and same morphism
  throughout the hypotheses and conclusion.
- f is projective: `[IsProjective f]`. PASS: opened the canonical upstream
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` read-only on the server at
  `/home/ubuntu/weil-conjectures-sheaf/lean/WeilConjectures/AlgebraicGeometry/Morphisms/Projective.lean`.
  Its parent `IsHProjective` requires a closed immersion into projective space for a finite
  coordinate type, with composite f; `IsProjective` adds `QuasiCompact f`. This is the
  dependency node's H-projective convention, not the broader projective-bundle convention.
  A nonempty finite coordinate type can be enumerated to give dimension n >= 0. An empty
  coordinate type gives empty projective space and an empty D, already admitted by an
  embedding into projective zero-space; it adds no extra scheme case.
- T is locally Noetherian: `[IsLocallyNoetherian T]`. PASS: the actual Mathlib class asks
  for Noetherian section rings on affine opens. The cover characterization recorded by
  `pqf-def-locnoeth` agrees with Stacks 01OV.
- T is quasi-compact: `[CompactSpace T]`. PASS: Mathlib compactness has no Hausdorff
  requirement, and `IsNoetherian` extends precisely these two classes.
- At every t in T the geometric fibre has finitely many points: `(hf : ∀ t : T,
  Finite ((pullback f (...) ) : Scheme.{u}))`. PASS: opened the recorded `pullback`
  signature, `Scheme.residueField`, `Scheme.fromSpecResidueField`, and `AlgebraicClosure`.
  The second pullback leg is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
  (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t`.
  Thus this is D times Spec of the algebraic closure over T, as prescribed by
  `def-weil-geometric-fibre`, and `Finite` concerns the coerced underlying point type.
  It does not assume that the morphism of this fibre to its field is already finite.
  The fixed canonical closure is a permitted choice: other algebraic closures give
  isomorphic schemes and hence the same finiteness of points.
- Conclusion f is finite: `IsFinite f`. PASS: opened its class; it extends affine
  morphisms and requires finite ring maps on every affine target open, precisely the
  finite clause of `def-weil-finite-integral-morphism`. No conclusion clause is missing.

Edge cases: empty T forces empty D and makes `hf` vacuous; empty D and empty individual
fibres satisfy `Finite`. No nonempty index type is introduced. Nilpotent structure and the
zero ring/empty affine scheme are unrestricted. Dimension-zero projective space is included.
Every characteristic is allowed. The single explicitly bound universe u is arbitrary;
residue fields and their canonical algebraic closures live in u, so the pullback is in the
same Scheme universe. There is no quantification over test fields in a smaller universe.
All variables and universes are bound with `autoImplicit false`.

Independent H4 searches (queries differ from the worker's):

- `msearch.py leanfinder`: "Finite morphism from a relatively projective scheme when all
  algebraically closed residue field fibres have finite underlying spaces". Eight hits;
  the finite-fibre instance assumes `IsFinite f` (the reverse direction), while properness
  and projective-spectrum results do not state this criterion.
- `msearch.py loogle`: `AlgebraicGeometry.IsFinite, "fiber"`. Two hits. Opened
  `locallyQuasiFinite_iff_isFinite_fiber`: it concerns finiteness of ordinary fibre
  morphisms under quasi-compactness, not the present geometric point-count hypothesis.
- `msearch.py grep`: `finite.*(geometric|projective)|isFinite_of.*[Pp]rojective|finite_preimage_singleton`
  in AlgebraicGeometry. Nine hits, including ordinary finite-fibre results. Opened
  `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`: it assumes properness
  and concerns a neighbourhood of one ordinary fibre, so is not this declaration.
- Independent `rg` searches of the upstream WeilConjectures tree, this project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no exact statement or name
  collision. The existing `isFinite_iff_isProper_and_hasFiniteFibres` was opened: it
  has properness and ordinary finite fibres, and remains the intended proof dependency.

H5/H6/H8/H9: no definitions or auxiliary statements are introduced; the sole theorem has
whole proof `sorry`. Module and theorem docstrings cite the source and blueprint id, and
all three DAG proof steps are reproduced, including faithful-flat descent of point
finiteness. Statement dependencies and the recorded properness/finite-fibre criterion
use the existing declarations rather than private copies. There are no new definition
nodes, dependency replacements, or statement corrections to review. The node's
`lean.statement` was checked byte-for-byte against the theorem signature, and every line
is within 100 characters.

Mismatches found: none. Changes: appended this independent reading only; preserved the
worker's module and node record. Server compilation and delivery preflight are recorded
by the required scripts; no local compiler or global build was run.
