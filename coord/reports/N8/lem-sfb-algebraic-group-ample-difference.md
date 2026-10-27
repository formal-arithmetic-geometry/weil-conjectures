## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicGroupAmpleDifference` states
`AlgebraicGeometry.Scheme.Modules.exists_ample_tensor_dual_of_group`, with its
only proof `sorry`. It introduces no definitions and preserves every field of
the accepted node except `lean`.

The old worker ending describes a stage-1 split refusal. The current
`coord/brief-stage2.md` section 0 explicitly permits recording the Lean statement
of an accepted split. The current queue assigns this node stage 2, and the node
has no Lean record or released repair note. This delivery preserves that split.

Hypothesis and clause correspondence:

- The arbitrary field k is `(k : Type u) [Field k]`.
- The group scheme H over k is `(H : Over (Spec (CommRingCat.of k))) [GrpObj H]`.
  This is the existing group-object encoding, with its structural multiplication,
  identity, inverse and axioms. No commutative-group instance is requested.
- Separatedness of its structure morphism is `[IsSeparated H.hom]`. Mathlib's
  definition is precisely that its diagonal is a closed immersion.
- Finite type is `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, precisely the
  two parts of the definition node's recorded interface.
- The given invertible O_H-module is `(L : H.left.Modules) [L.IsInvertible]`.
  Invertibility is the existing local rank-one triviality predicate, with no
  extra quasi-coherence assumption; quasi-coherence follows from local triviality.
- The existential modules A and B are `∃ (A B : H.left.Modules)`.
- Their invertibility is explicitly bound by the following existential witnesses
  `(_ : A.IsInvertible) (_ : B.IsInvertible)`; neither is an input hypothesis.
- Their absolute ampleness is `IsAmple H.left A ∧ IsAmple H.left B`, with the
  witnesses in scope, using the node's recorded absolute ampleness definition.
- The isomorphism is `Nonempty (L ≅ A ⊗ B.dual)`; Nonempty expresses the existence
  of an actual isomorphism of sheaves, with the required orientation.
- The prescribed inverse is `B.dual`, the existing abbreviation for
  `Scheme.Modules.homObj B (SheafOfModules.unit _)`. Its homObj is the internal
  sheaf Hom, so this is exactly Hom(B,O_H), not an arbitrary tensor inverse.
- The tensor `⊗` uses the existing monoidal category of scheme modules, whose
  tensor is the sheafification of the sectionwise presheaf tensor.
- There is no properness, smoothness, commutativity, symmetry or connectedness
  hypothesis. No characteristic or algebraic-closure restriction is imposed.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (extends CommRing and DivisionRing).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the application
  to `Over (Spec (.of k))` is documented in the imported
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its imported QuasiCompact module gives
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated`, defined by the closed diagonal.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorObj`, and the existing
  monoidal structure on X.Modules. This is the recorded definition of rank one.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, whose definition includes
  CompactSpace X and positive-power sections with affine nonvanishing opens.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`:
  `AlgebraicGeometry.Scheme.Modules.dual` and `homObj`, as described above.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded tensor node's `SheafOfModules.cochainModulesMonoidal` and its
  imports retain the existing sheaf tensor; this module is imported publicly.
  The concrete scheme monoidal instance is already supplied by Invertible.

The stated proof dependencies are imported without `public`: the modules
`Sheaf.AlgebraicGeometry.CoherentFiniteType` (IsQuasiCoherentFiniteType),
`WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration`
(exists_finite_generatingSections_tensorPow_of_isAmple),
`WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower`
(isAmple_positive_tensorPow),
`WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover`
(globalGeneration_nonvanishing_cover), and
`WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen`
(tensor_section_affine_open). Their signatures and proof docstrings were read.
The proof-only node `lem-sfb-finite-type-group-ample-line` currently has no Lean
record and thus no module to import. It is named in the proof docstring and
retained in proof_deps. It is not needed to type this stage-2 statement.

Source and edge checks: read `literature/stacks-project/groupoids.tex`,
lemma-algebraic-quasi-projective (0BF7), including the definition of algebraic
as finite type immediately before that section, and `morphisms.tex`,
lemma-invertible-add-enough-ample-very-ample (0FVC). The former supplies an ample
line for arbitrary algebraic group schemes; the latter gives sufficiently
positive ample twists of any line. The proof docstring follows the node's four
steps: choose M; twist L to global generation and take B=M^(n+1); use affine
nonvanishing loci to make A=M tensor (L tensor M^n) ample; cancel B with its
internal dual. In particular the high twist can be chosen nonnegative and B
has strictly positive exponent even when n=0.

Checked Spec k and trivial L; affine G_a and G_m; finite disconnected groups;
and nonreduced alpha_p in characteristic p. None requires an extra restriction.
A negative-degree line on an elliptic curve confirms why two ample modules are
needed and why the statement must not assert L itself ample. Empty H cannot be
a group scheme over a field because its identity section has source Spec k;
no additional nonemptiness binder is needed. The arbitrary common universe u
follows the project's Scheme/Over interface and excludes no geometric case by
a finiteness or countability condition. No node fault or statement dispute was
found.

Searches performed in this session:

- msearch.py / leanfinder, query "Every invertible sheaf on a finite type
  separated group scheme over a field is the tensor quotient of two ample
  invertible sheaves": 8 hits on ring Picard groups, quasi-separated clearing
  denominators, and unrelated scheme facts. None states this theorem or supplies
  ampleness.
- msearch.py / leansearch, query "Every invertible sheaf on an algebraic group
  over a field is a difference of two ample invertible sheaves": 8 hits on Picard
  modules, relative Picard groups and sectionwise subtraction/inversion. No match.
- msearch.py / loogle, query `"IsAmple"`: zero hits.
- msearch.py / grep in Mathlib/AlgebraicGeometry, query
  `ample.*difference|difference.*ample|ample.*quotient|quasiProjective.*[Gg]roup`:
  zero hits.
- rg on both project source roots using the ample-difference patterns and the
  node id: the only substantive occurrence was the consuming
  SymmetricLinePowerProlongation proof docstring, which cites this node but does
  not state its theorem. Other hits were unrelated prose about quotients.
- rg for existing ample-existence declarations found curve, dimension-one and
  abelian-variety statements. These impose different hypotheses and do not
  express this arbitrary-group tensor quotient conclusion.
- rg on Mathlib, both source roots and dag/lean_names_upstream.json for
  `exists_isAmple_tensor_dual|exists_ample_tensor_dual_of_group`: no hits.

No new nodes, dependency repairs or statement corrections are required.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
