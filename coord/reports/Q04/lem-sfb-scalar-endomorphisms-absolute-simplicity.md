## Worker report

The module `Sheaf.AlgebraicGeometry.ScalarEndomorphismsAbsoluteSimplicity` states
`AlgebraicGeometry.RationalRepresentation.scalar_endomorphisms_absolute_simplicity`.
Its only theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The natural-language statement and six-step proof plan are unchanged. The module docstring
and theorem docstring cite Milne, Algebraic Groups (2017), Proposition 4.19(b), printed
pp.90–91, and Remark 4.18, printed p.90. I read these passages in the supplied PDF.

Hypotheses and clauses, matched individually:

- A field k is `{k : Type u} [Field k]`.
- The k-scheme H is `(H : Scheme.{u}) [H.Over (Spec (.of k))]`; its group structure
  is `[GrpObj (H.asOver (Spec (.of k)))]`, precisely the recorded group-object definition.
- Affineness is `[IsAffine H]`. Finite type is
  `[LocallyOfFiniteType (H ↘ Spec (.of k))] [QuasiCompact (H ↘ Spec (.of k))]`.
- The vector space is `(V : Type u) [AddCommGroup V] [Module k V]`.
  Finite dimension is `[FiniteDimensional k V]`, and V ≠ 0 is `[Nontrivial V]`.
- The rational representation is `(r : NaturalRepresentation (k := k) H V)` from the
  landed rational-representation/comodule dictionary. Its data are group homomorphisms
  `r.action A : H(A) →* (A ⊗[k] V ≃ₗ[A] A ⊗[k] V)` with naturality for every
  homomorphism of commutative k-algebras. The dictionary's `finite_dictionary` identifies
  exactly these actions with group-scheme homomorphisms to the existing GL(V).
- A rational subrepresentation is written inline, rather than introducing another
  definition: for `U : Submodule k V`, every A, point x and vector z satisfy
  `z ∈ U.baseChange A → r.action A x z ∈ U.baseChange A`. Mathlib's
  `Submodule.baseChange` is the image of the scalar-extended inclusion, so this is
  stability of A ⊗ U in A ⊗ V. As k is a field, tensoring the inclusion is injective.
  Since x ranges over a group, applying the condition to x⁻¹ gives equality as well.
- Simplicity is `hsimple`: every U satisfying that full rational stability test is
  `⊥` or `⊤`. This tests all commutative algebras and all points, including
  infinitesimal points, rather than merely H(k).
- A rational equivariant endomorphism is `f : Module.End k V` together with the
  commutation equation in `hscalar`, quantified over every commutative k-algebra A
  and every `x : points (H.asOver (Spec (.of k))) A`.
  `f.baseChange A` is the actual map 1 tensor f.
- The scalar-endomorphism hypothesis concludes
  `∃ a : k, f = a • (LinearMap.id : Module.End k V)`, with no extra hypothesis on k.
- Every field extension is quantified as `∀ (K : Type u) [Field K] [Algebra k K]`.
  This is the recorded field-extension notion. All schemes, individual vector spaces,
  fields and test algebras are in the same arbitrary universe u, using the existing
  natural-representation interface and its fixed-universe convention.
- Every candidate subrepresentation after extension is
  `W : Submodule K (K ⊗[k] V)`. A test K-algebra is A with `[CommRing A] [Algebra K A]`,
  its underlying k-algebra `[Algebra k A]` and compatibility `[IsScalarTower k K A]`.
  These last two structures express the composite k → K → A; every K-algebra has them.
  The A-valued points of H_K are canonically the k-morphisms Spec A → H, so the point
  binder is again `x : points (H.asOver (Spec (.of k))) A`.
- The action on A ⊗_K (K ⊗_k V) is expressed explicitly as
  `cancelBaseChange.symm (r.action A x (cancelBaseChange z))`, where cancellation is
  `TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A V`.
  It sends a tensor (b tensor v), with outer factor a, to
  (algebraMap K A b * a) tensor v.
  Therefore this conjugate is exactly the scalar-extended rational action of H_K,
  with no arbitrary comparison map or extra assumption about the action.
- The premise on W tests this action on every A, x and z in `W.baseChange A`.
  The conclusion `W = ⊥ ∨ W = ⊤` is precisely the node's asserted simplicity.
- There are no smoothness, connectedness, reductivity, splitness, algebraic-closedness,
  characteristic-zero, separability or finiteness conditions on K/k.

Dependency declarations used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, read at lines 170–180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`, read at lines 40–48; its scheme specialization
  is documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-wf-algebraic-representations`: the recorded upstream
  `AlgebraicGeometry.GeneralLinearGroup.RationalHom.representation` and
  `standardRepresentation` were read in full, including docstrings. The underlying
  `RationalHom` and `RationalHom.points` definitions are in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`.
  The recorded upstream `RationalHom.IsSimple` additionally requires an algebraically
  closed characteristic-zero base, so it is deliberately not substituted for rational
  simplicity over an arbitrary field. This does not require a dependency repair: the
  landed natural-representation dictionary already supplies the exact general notion.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`, lines 90–101,
  with `Field` on both k and K.
- Added the landed definition node `def-sfb-rational-natural-representation` to
  `stmt_deps`. Its `existing: true` Lean record owns
  `AlgebraicGeometry.RationalRepresentation.NaturalRepresentation` and `genericPoint`
  in `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`.
  The statement uses the structure `NaturalRepresentation`, including its naturality
  field, without using a theorem conclusion. The dictionary theorem remains in
  `proof_deps`, where `dictionary`, `intertwines_iff` and `finite_dictionary` supply
  the proof's comodule and finite-dimensional interpretations. The module import
  remains the same because the definition owner records the same source module.
- Mathlib's `Submodule.baseChange`, `LinearMap.baseChange`, and
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` are read in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, at lines 831–832, 658–665 and 431–453.
  Their actual definitions, not replacement maps, appear in the statement.

The proof imports retain the recorded plan: the coordinate-Hopf instance of
`Mathlib.AlgebraicGeometry.Group.Affine`, the landed
`Coalgebra.dual_action_detection` in `Sheaf.RingTheory.CoalgebraDualActionDetection`,
`Module.Free.of_divisionRing` in `Mathlib.LinearAlgebra.Basis.VectorSpace`,
`Module.Finite.toModuleEnd_moduleEnd_surjective` in `Mathlib.RingTheory.SimpleModule.Basic`,
`AlgebraicGeometry.pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`, the
composition/base-change instances of `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
and `.QuasiCompact`, and the tensor universal-property/map modules. The docstring follows
all six original proof steps: comodule dictionary, convolution action, double centralizer,
base change, extension of functionals, and matrix units.

Edge cases checked before writing:

- V = 0 is excluded exactly by the explicit V ≠ 0 hypothesis, not by a dimension-index
  convention. Subspaces 0 and V remain among the tested submodules.
- A = 0 is allowed: `CommRing A` does not require nontriviality, and scalar extensions
  and their stability conditions still make sense.
- K = k is included, with the actual tensor cancellation equivalence, so identity
  extension is not dropped.
- Arbitrary inseparable and transcendental field extensions are included; no finite,
  algebraic or separable hypothesis is introduced.
- Nonreduced group schemes and finite fields are included. Testing only k-valued points
  would fail to encode the source notion in these cases; the statement tests all A.
- The trivial group and a one-dimensional trivial representation satisfy the expected
  boundary case. A higher-dimensional trivial representation fails `hsimple`.

Searches actually run through `msearch.py` (logged in sandbox `searches.jsonl`):

- LeanFinder: “A simple rational representation of an affine group scheme whose
  equivariant endomorphisms are scalars remains simple after every field extension”.
  Eight hits: `FDRep.simple_iff_end_is_rank_one`, `FDRep.finrank_hom_simple_simple`,
  `simple_of_finrank_eq_one`, `CSA.isSimple`, the categorical Schur results and
  `FDRep.simple_iff_char_is_norm_one`. None is this arbitrary-field rational
  scalar-extension criterion.
- Loogle: `IsSimpleModule, TensorProduct`. Zero hits.
- Mathlib grep: `(baseChange|extendScalars).*(IsSimpleModule|IsIrreducible)|` followed
  by `((IsSimpleModule|IsIrreducible).*(baseChange|extendScalars))`. Zero hits.
- LeanSearch: “A simple finite dimensional rational representation whose endomorphisms
  are all scalars remains simple after extension of the ground field”. Eight hits,
  principally Schur's lemma and endomorphism-dimension results; no exact statement.
- Direct source searches with `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for absolute simplicity, scalar endomorphisms and
  simplicity with base change found no matching theorem. The exact node-id search
  in `lean/WeilConjectures` found none. Searches for rational actions located the
  existing natural-representation dictionary, which is reused here.

No statement correction, new node, dependency module or STATEMENT-DISPUTED flag is needed.
Validation uses only the prescribed server `scompile.py` and `deliver2.py` wrappers.

## Repair of returned delivery 5265b1a8b88f

H2: the former added statement dependency was the theorem node
`lem-sfb-rational-representation-comodule-dictionary`, while the Lean signature uses
only its plain structure `NaturalRepresentation`. Re-read the current main node and
the landed definition owner `def-sfb-rational-natural-representation`, including its
`existing: true` record and the source structure's full signature and docstring.
Refreshed the sandbox node from the current main snapshot, retaining the delivery's
Lean record, and replaced the former added dependency with this definition owner.
The prescribed delivery wrapper rebases the packet on current server main.
The dictionary theorem remains in `proof_deps`. Updated this report and `lean.note`
to distinguish the definition used in the statement from the theorem used in the proof.
The Lean module and `lean.statement` are byte-identical to the returned delivery;
the natural-language statement and proof dependencies are also unchanged.
Compilation, dry run, and submission use the prescribed wrappers.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
