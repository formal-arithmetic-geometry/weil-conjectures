## Worker report

The module `Sheaf.AlgebraicGeometry.SyntomicEtaleSourceLocality` states
`AlgebraicGeometry.syntomic_etale_source_locality`, with its sole proof `by sorry`.
The node statement, proof plan, and proof dependencies are unchanged. Its statement
dependencies gain the definition node `def-sfb-complete-intersection-fibres`.
Following the H2 return on ca68d1b97d4c, maintenance commit `474770ef2d1`
extracted the two existing fibre predicates verbatim from
`SyntomicLocusBaseChange` to `Sheaf.AlgebraicGeometry.CompleteIntersectionFibres`
on the server base. The former module publicly imports the latter, preserving
its locus definition, theorem statement, and all published proofs. The locality statement
imports the definition module directly and does not cite the unused locus theorem.

Hypothesis and clause correspondence:

- Arbitrary schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Syntomic means exactly `Flat f ∧ LocallyOfFinitePresentation f ∧
  f.HasCompleteIntersectionFibres`. `Flat` is the recorded affine-local class,
  equivalent to flatness of all stalk maps; `LocallyOfFinitePresentation` is the
  recorded class without quasi-compactness or quasi-separatedness assumptions.
- Unfolding the existing fibre predicate gives `∀ (s : S) (y : f.fiber s),
  f.IsCompleteIntersectionAtFiberPoint s y`. The latter uses
  `Algebra.IsCompleteIntersectionLocalAlgebra (S.residueField s)` on the stalk
  `(f.fiber s).presheaf.stalk y`, with scalar map given by the inverse of
  `Scheme.ΓSpecIso`, the canonical `f.fiberToSpecResidueField s`, and the germ.
  Thus these are ordinary scheme-theoretic fibres, every base point and every
  fibre point, and the specified residue-field action, rather than geometric
  fibres or an unspecified scalar structure. The local-algebra predicate says
  local, essentially finite type, and isomorphic over that field to a regular
  local essentially finite type algebra modulo a finite regular sequence in its
  maximal ideal. This is the local-ring meaning of `lci_pointwise_criterion`.
  In that criterion the presentation's properness follows from the nonzero local
  target, so the regular-sequence entries lie in the maximal ideal. Its local
  Noetherian assumptions follow for regular local essentially finite type rings.
- Clause (1) is the first outer conjunct. Its premise is the syntomic conjunction
  for `f`. It quantifies over every `(U : Scheme.{u}) (h : U ⟶ X)`, assumes
  `Etale h`, and concludes that same conjunction for `h ≫ f`, Lean's `f ∘ h`.
- Clause (2) is the second outer conjunct. `(I : Type v)` is an arbitrary set in
  an independently declared universe; `(U : I → Scheme.{u})` and
  `(h : ∀ i : I, U i ⟶ X)` specify the family. Etaleness is
  `(∀ i : I, Etale (h i))`. The images cover exactly when
  `∀ x : X, ∃ (i : I) (z : U i), h i z = x`. The next premise says every
  `h i ≫ f` has the syntomic conjunction. The conclusion is that conjunction for
  `f`. The source need not have been assumed syntomic in this clause.
- There is no quasi-compactness, separation, Noetherianity, field-base,
  nonempty-index, or surjectivity-of-each-member hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` identifying the node's stalkwise meaning.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, and
  `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.TraceFormula.LciPointwiseCriterion`:
  `AlgebraicGeometry.lci_pointwise_criterion`, whose full signature and docstring
  fix the complete-intersection local-ring meaning.
- `Sheaf.AlgebraicGeometry.CompleteIntersectionFibres`:
  `Scheme.Hom.IsCompleteIntersectionAtFiberPoint` and
  `Scheme.Hom.HasCompleteIntersectionFibres`, now owned by the new definition
  node `def-sfb-complete-intersection-fibres`. Their signatures and bodies are
  copied byte for byte from the prior owning module; only their blueprint
  docstring tags change. The standalone module imports only Mathlib's fibre
  construction and `Sheaf.RingTheory.CompleteIntersectionLocalAlgebra`.
  It makes no flatness, finite type, finite presentation, or nonempty-fibre
  assumption. The canonical scalar action is unchanged.

All recorded, stated proof dependencies are imported privately: the source/target
properties theorem; affine pullback, open immersion base change, finite
presentation base change and composition, affine stalk localization, essentially
finite type algebra, etale scheme and covering base change, pullback projections,
the fibre-local-ring isomorphism, etale fibre discrete separable points, the
complete-intersection local-algebra definition, and the flat-local source/closed
fibre criterion. Their owning modules are the plain imports in the file. The
five proof steps of the node are reproduced in the theorem docstring, including
the compatible field actions and the regular presentation with an empty sequence.

Sources opened: `literature/stacks-project/descent.tex`, the complete statements
and proofs of Tags 036S and 05B7; `morphisms.tex`, Tags 01UE, 01UG and 02GQ;
the current blueprint direct-image stability proof under `literature/blueprint/latest/`.
There is no statement correction or disputed statement.

Edge cases checked by reading the quantifiers and definitions:

- If `I` is empty and `X` is empty, the covering condition and component
  conditions are vacuous; flatness, local finite presentation, and every fibre
  local-ring test for the empty source are vacuous as well.
- If `I` is empty and `X` has a point, the covering premise is false, as required.
- Empty ordinary fibres require no local-ring witness. An empty `U` in clause
  (1) is allowed; a non-surjective etale `h` is allowed as well.
- An empty base forces any source admitting a map to it to be empty; no extra
  base inhabitant or residue-field choice is requested.
- Identity maps and singleton covering families are included. The complete
  intersection predicate permits the empty regular sequence, so field stalks
  and regular local stalks are included. Zero-ring affine charts have no points
  and contribute no local rings.
- The ambient schemes use arbitrary `u`, and the covering family arbitrary `v`.
  This is a covering family, not a limit or test-algebra quantifier, so no
  restriction on `v` or smallness hypothesis is needed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Syntomic morphisms of schemes are preserved and
  detected by jointly surjective etale covers on the source"`: eight hits about
  joint surjectivity and etale properties, none the requested syntomic result.
- `msearch.py ... loogle "Syntomic, IsSyntomic"`: zero hits; unknown identifier
  `Syntomic`.
- `msearch.py ... grep "Syntomic|IsSyntomic|CompleteIntersection"
  AlgebraicGeometry`: zero hits in Mathlib.
- `msearch.py ... leansearch "Syntomic morphisms are local on the source for
  jointly surjective etale families"`: eight hits on etale or source-local
  properties, none on syntomicity.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for syntomic declarations and
  `HasCompleteIntersectionFibres`: no existing locality theorem, but the exact
  fibre predicate was found in `SyntomicLocusBaseChange.lean` and reused. The
  affine chart predicate in `SyntomicGeometricFibresAffineCriterion.lean` is a
  different interface, not a definition on arbitrary scheme morphisms.
- `grep -rn` for the exact item id in `lean/WeilConjectures` and `rg` for the
  theorem name in the upstream name index: no match. `rg` over the DAG locates
  the owning record of `HasCompleteIntersectionFibres` at
  `lem-trf-syntomic-locus-base-change`. The H2 return requires extracting those
  plain definitions into their own definition node instead of citing that theorem.

Validation of the returned packet passed compilation and preflight before
ca68d1b97d4c. For this repair `scompile.py` successfully compiled all three delivered modules
as separate files in dependency order, with no diagnostics (exit 0).
The required `deliver2.py --no-push` check follows this compilation. Every variable and universe is explicitly bound.
The new definition module has no theorem and no `sorry`; published proofs in the
repaired dependency remain unchanged; the locality theorem retains `by sorry`.

## Second reading by Q51

This is this worker's separate rereading pass; the dispatcher explicitly forbids
starting other agents, and the maintainer supplies the independent review.
With the node and final Lean file open together, I checked both outer conjuncts
individually: the first assumes syntomicity of `f`, whereas the second assumes
only syntomicity of all composites plus the etale covering condition. Each
syntomic occurrence has all three required clauses. The composition order is
`h ≫ f`, and the family covers the underlying points of `X`, not `S` or a
chosen affine subset. No nonemptiness or finiteness of the family is present.
Unfolding the imported fibre predicate retains the canonical residue-field
action and all base and fibre points. The auxiliary presentation universes and
local-ring conventions agree with the recorded criterion.

The H2 dependency ownership mismatch found by the maintainer is repaired:
`stmt_deps` now cites the landed definition node instead of the unrelated theorem.
Maintenance commit `474770ef2d1` moved the definitions and repaired the old owner
on the server base. The signature and body comparison was exact; only blueprint
owner tags changed. The locality theorem statement and proof plan are unchanged.

## Return repair H2

The return of immutable head ca68d1b97d4c required extracting the plain fibre
predicates from the unused locus theorem's module. The retained worker repair
compiled, but preflight refused the old owner's module after the old theorem
left the consumer's prerequisite closure. Maintenance commit `474770ef2d1`
performed the shared extraction first. This packet now contains only the
locality node, locality module and this report; the four already-landed
extraction files are preserved as `.bak` copies outside the active packet.
The item adds only the landed `def-sfb-complete-intersection-fibres` dependency
and its Lean record. No unused theorem edge or statement correction is needed.

## New nodes

None in this packet. The new definition owner
`def-sfb-complete-intersection-fibres` and its module were committed by
maintenance in `474770ef2d1`. Its source is Stacks 02V3/01UE/00SD. Its node
retains the original worker's LeanSearch, LeanFinder and grep evidence.
The canonical residue-field action and both definition bodies are unchanged.

## Dependency modules

None in this packet. Maintenance `474770ef2d1` repaired
`Sheaf.TraceFormula.SyntomicLocusBaseChange` on the base: it publicly imports
`Sheaf.AlgebraicGeometry.CompleteIntersectionFibres`, no longer declares the
two moved predicates, and its node cites the definition owner with a Lean note.
Its locus definition, theorem statement, private helpers and proofs are unchanged.

## Maintenance validation

On 2026-10-24 tools/lean_file.sh compiled the extracted definition module
(14.5 s), the existing locus module (22.8 s), and this locality module (8.6 s),
one file at a time with the default 60 s limit, without Lean diagnostics.
The extraction passed incremental DAG and Lean record checks. The normal
`deliver2.py --no-push` check is rerun against this committed base.
