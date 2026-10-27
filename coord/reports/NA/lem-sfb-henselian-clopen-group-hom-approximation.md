## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianClopenGroupHomApproximation` states
`AlgebraicGeometry.exists_clopen_groupHom_of_completion`. Its only postponed proof is
that theorem's whole `sorry` body. No definition is introduced, no proof is supplied,
and the node changes only in `lean`.

Read the assigned node and all nine statement dependencies, including their records
and the defining Lean declarations. Read Stacks `smoothing.tex`,
`lemma-henselian-pair` (Tag 0AH5), including its proof. This is a finite polynomial
certificate consequence, rather than a verbatim Stacks theorem: the node's thirteen
proof steps, with their dependencies, are included in the theorem docstring. The
source gives order-one approximation of a finite system of polynomial equations.
The node explains explicitly how a homomorphism and its clopen-factor inverse give
such a system, retaining relation-membership witnesses and all group diagrams.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative henselian local ring: `(A : Type u) [CommRing A]
  [HenselianLocalRing A]`. The latter class extends `IsLocalRing A`; no separate
  local-ring hypothesis is necessary.
- G-ring: `(hA : IsGRing A)`. This is the recorded upstream definition, which
  includes `IsNoetherianRing A` and regularity of the prime-local completion maps.
- Maximal ideal: `IsLocalRing.maximalIdeal A`, the unique maximal ideal of `A`.
- Residue field `k = A / m`: the target of
  `AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)` is literally
  `A ⧸ IsLocalRing.maximalIdeal A`. This is definitionally
  `IsLocalRing.ResidueField A`, the local-ring quotient used by the recorded scheme
  residue-field declaration. No arbitrary residue field or identification is assumed.
- Completion with its canonical A-algebra structure:
  `AdicCompletion (IsLocalRing.maximalIdeal A) A` and its `algebraMap A ...`.
  `AdicCompletion` is the compatible-sequence inverse limit, including a harmless
  initial quotient at exponent zero.
- Coordinate algebras `P,Q`: `(P Q : Type u) [CommRing P] [CommRing Q]
  [Algebra A P] [Algebra A Q]` and both `Algebra.FinitePresentation` instances.
- The affine A-schemes are exactly `(Spec (.of P)).asOver (Spec (.of A))`
  and `(Spec (.of Q)).asOver (Spec (.of A))`. The `specOverSpec` instance
  uses the specified `algebraMap A P` or `algebraMap A Q` as the structure map.
- Group structures: the two `GrpObj` binders on those A-schemes. These supply
  multiplication, identity, inverse, associativity, both unit identities and both
  inverse identities. The product in `Over (Spec A)` is the scheme fibre product.
  They impose no commutativity of the group laws.
- Scalar extension to the completion: `(Over.pullback (Spec.map
  (CommRingCat.ofHom (algebraMap A ...)))).mapGrp`. On underlying schemes this
  is precisely pullback along `Spec Ahat -> Spec A`, with the transported operations.
- Given completed group homomorphism: `v` is a morphism in the category of group
  objects between these two specified base changes. Its underlying scheme map is
  `v.hom.hom.left`. A bundled homomorphism preserves identity and multiplication;
  inverse compatibility is implied, as proved by Mathlib's `GrpObj.inv_hom`.
- Both input immersion hypotheses: `hvOpen : IsOpenImmersion v.hom.hom.left`
  and `hvClosed : IsClosedImmersion v.hom.hom.left`.
- Existence of an A-group homomorphism: the existential `w` is a morphism between
  `Grp.mk` of the original two A-group objects.
- Both output immersion clauses: `IsOpenImmersion w.hom.hom.left` and
  `IsClosedImmersion w.hom.hom.left` in the existential conclusion.
- Exact residue equality: the last conjunct equates the two group homomorphisms
  obtained by pulling `w` first to Ahat and then to k, and pulling `v` to k, in
  the SAME category between the SAME double-pullback objects. The second pullback
  is along `Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ ...).toRingHom)`.
  The equation `AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk` identifies the
  composite `A -> Ahat -> k` with the quotient `A -> k`. The canonical natural
  isomorphism `Over.pullbackComp` therefore identifies the left side with `w_k`.
  Conjugating BOTH sides by those same canonical pullback-composition isomorphisms
  gives exactly `w_k = v_k`. Thus the double-pullback form neither strengthens nor
  weakens the clause. In particular this is equality of scheme/group maps, not
  just equality on field-valued points, and the k map is fixed rather than chosen.
- There is no assertion that the completed maps themselves agree. No flatness,
  smoothness, cocommutativity, diagonalizability, reducedness, or separability of k
  is required.

Dependency declarations used:

- `def-weil-pbc-henselian-terminology`: imported
  `WeilConjectures.Mathlib.RingTheory.Henselian`, using its re-exported
  `HenselianLocalRing` from `Mathlib.RingTheory.Henselian`. The strictly henselian
  class in that record is not assumed.
- `def-weil-pbc-g-ring`: `WeilConjectures.RingTheory.GRing`, `IsGRing`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` uses `IsLocalRing.ResidueField` of a local stalk.
  Here the already specified local ring is A itself, so the quotient is the
  underlying `IsLocalRing.ResidueField A`, as defined in
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs`; it needs no new definition.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, with canonical algebra and `evalOneₐ` from `.Algebra`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `Limits.pullback`;
  used by `Over.pullback`, whose implementation was read in
  `Mathlib.CategoryTheory.Comma.Over.Pullback`. Its object is
  `Over.mk (pullback.snd g.hom f)` and its underlying scheme is `pullback g.hom f`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `IsOpenImmersion`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.

Mathlib also already supplies `GrpObj`, `Grp`, `Grp.homMk`, and
`Functor.mapGrp` (`Mathlib.CategoryTheory.Monoidal.Grp`), the cartesian monoidal
structure on schemes over a base and the braided pullback functor
(`Mathlib.CategoryTheory.Monoidal.Cartesian.Over`), and the canonical algebra-to-
relative-spectrum instance (`Mathlib.AlgebraicGeometry.Group.Affine`). These
are used directly; there is no new general group-scheme notion to define.
`def-sc-group-scheme` was inspected as a reuse candidate, but its text is
specifically over a field, so it is not added as a premise of this ring-base lemma.

All recorded proof dependencies have imports: their modules are public where
needed in the signature, and otherwise ordinary imports. Besides the public
imports, these include `Mathlib.Algebra.MvPolynomial.Basic`,
`Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Mathlib.RingTheory.Spectrum.Prime.Topology`,
`Mathlib.RingTheory.AdicCompletion.Completeness`, and
`WeilConjectures.RingTheory.HenselianPairApproximation`. The affine product theorem
is re-exported by the public affine-group module, and the affine-basic-open and
evaluation statements by the public residue-field module. The approximation
theorem's full signature and docstring were read. No proof import closes a cycle.

Edge cases checked before writing:

- A field is a permitted local G-ring: the maximal ideal is zero and both
  completion/residue pullbacks retain the intended comparison. No positive
  dimension or nonzero maximal ideal is assumed.
- The trivial group and identity homomorphism are allowed; no positive rank,
  nontrivial group or nonempty presentation-generator list is required.
- Presentations may have zero variables or zero relations: this is retained by
  `Algebra.FinitePresentation`; no auxiliary witness cardinality is constrained.
- The empty affine scheme cannot be a group scheme over the nonempty spectrum
  of a local ring, since it has no identity section. This is excluded by the
  mathematical group-object hypothesis itself, not by an extra binder.
  A zero base ring is likewise excluded by the standard local-ring definition.
- Nilpotents, positive characteristic, imperfect residue fields, and nonflat or
  noncommutative group schemes are not excluded. `CommRing P/Q` concerns
  coordinate functions, not commutativity of the group multiplication.
- The single arbitrary universe `u` is the scheme universe. All base and
  coordinate rings are in that same universe, as required by Mathlib's relative
  spectrum/Over API; `u` is unrestricted and can encompass any of the input
  rings. There is no extra test-algebra universe or vacuous quantification.

Searches for reuse (the exact machine search records are also in `searches.jsonl`):

- `leanfinder` query `A homomorphism of finitely presented affine group schemes over a henselian local G-ring completion that is open and closed can be approximated over the original ring with the same residue map`: 8 hits; HenselianLocalRing, Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq, Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete, IsAdicComplete.henselianRing, HenselianLocalRing.TFAE, HenselianRing, Algebra.FormallySmooth.exists_lift, Algebra.FormallySmooth.lift.
- `loogle` query `HopfAlgebra, GroupObj`: 0 hits; loogle: unknown identifier 'GroupObj'.
- `grep` query `GroupObj|HopfAlgebra|henselian.*approx` in `AlgebraicGeometry`: 4 hits; Mathlib/AlgebraicGeometry/Group/Affine.lean, Mathlib/AlgebraicGeometry/Group/Affine.lean, Mathlib/AlgebraicGeometry/Group/Affine.lean, Mathlib/AlgebraicGeometry/Group/Affine.lean.
- `leansearch` query `A clopen affine group scheme homomorphism over the completion of a henselian local G-ring approximates over the ring with the same residue homomorphism`: 8 hits; UniformSpace.Completion.extensionHom_coe, UniformSpace.Completion.mapRingHom_coe, UniformSpace.Completion.coe_mapRingHom, UniformSpace.Completion.mapRingHom, AlgebraicGeometry.HasRingHomProperty.mk, UniformSpace.Completion.extensionHom, AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE, AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover.
- `loogle` query `CategoryTheory.GrpObj`: 12 hits; CategoryTheory.GrpObj, CategoryTheory.Grp.mk, CategoryTheory.Grp.grp, CategoryTheory.GrpObj.inv, CategoryTheory.GrpObj.instIsIsoInv, CategoryTheory.GrpObj.instTensorUnit, CategoryTheory.GrpObj.ofIso, CategoryTheory.GrpObj.toMonObj.

The finder results concern smooth lifting or general henselian terminology, not
approximation of this given affine group homomorphism with both immersion
conditions. LeanSearch hits concern uniform completions and finite-presentation
morphism properties, not this assertion. The corrected Loogle query finds the
existing group-object API, which is used directly. The first Loogle query used
`GroupObj`, an incorrect identifier; its failed-name result was not relied on.
Grep identified the existing affine group/Hopf correspondence. Direct `rg`
searches of `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for
`clopen.*(approx|completion)|henselian.*clopen|exists_clopen_groupHom` found the
separate henselian-clopen restriction lemma and unrelated modules, but no statement
of the assigned approximation theorem. The node-id search in `WeilConjectures`
found no declaration. DAG group-scheme searches found the field-base notion just
discussed. No missing notion or unusable dependency interface was found.

Validation: compile this sole delivery module through `scompile.py`, then run
`deliver2.py --no-push` and the normal delivery. Only the expected theorem-sorry
warning is acceptable. There are no statement disputes or source corrections.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
