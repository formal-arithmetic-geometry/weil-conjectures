## Worker report

The module `Sheaf.AlgebraicGeometry.DenseRestrictionSemisimple` states
`AlgebraicGeometry.GeneralLinearGroup.RationalHom.dense_restriction_semisimple`.
It contains one theorem, with proof `sorry`, and no new definitions. The node's
statement, dependencies and accepted Q153 proof split are preserved verbatim;
only `lean` is added. The prior worker's stage-1 unchanged-item gate is inapplicable:
this is stage 2, the live queue lists stage 2, and the item has no Lean record.
There is no repair note for this item.

Source read directly: Milne, Algebraic Groups (2017), printed p.85, Proposition 4.3
and Corollaries 4.4--4.5; p.90, Definition 4.15 and Proposition 4.17; p.256, proof
of Lemma 13.6 (PDF pages 97, 102 and 268). The first passage tests subspaces on a
schematically dense set and on all coefficient algebras. The second supplies simple
summands and complements. The last uses simplicity on the dense subset and stable
sections. Smoothness in the node makes topological density sufficient by reducedness.

Hypotheses and clauses matched with Lean:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A k-group scheme: `G : Over (Spec (.of k))` and `[GrpObj G]`. Affineness is
  `[IsAffine G.left]`; smoothness is `[Smooth G.hom]`; finite type is
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the recorded convention.
- An abstract subgroup of G(k): `Γ : Subgroup (AlgebraicGeometry.points G k)`.
  The `MonObj` scope activates the canonical group on scheme-valued points.
- Zariski density: `hdense : DenseRange fun γ : Γ ↦ γ.val.left
  (IsLocalRing.closedPoint k)`. This evaluates each rational point on the unique
  point of Spec k and asserts that its image is dense in the underlying scheme.
  No topology on the abstract subgroup and no finite-generation assumption occurs.
- A finite-dimensional rational representation: finite `m`, and
  `ρ : RationalHom G m` with `[IsMonHom ρ]`. Choosing a basis identifies any
  finite-dimensional vector space with `m → k`. This is the project's existing
  general linear group interface, not a change of mathematical objects. An empty
  basis is allowed. The existing point representation is `ρ.representation`.
- For a subspace S and a commutative k-algebra A, the expression
  `Submodule.span A ((fun w : m → k ↦ fun j ↦ algebraMap k A (w j)) '' (S : Set _))`
  is its scalar extension inside `m → A`. The canonical identification
  `(m → k) ⊗[k] A ≃ (m → A)` identifies the image of `S ⊗[k] A` with this span;
  over a field the inclusion tensors injectively. This uses all commutative
  k-algebras in the site's universe, including nonreduced algebras. Such algebras
  have the same universe as k and G, as required by the existing `points` interface;
  larger tests are detected already by the coordinate algebra and naturality.
- Rational stability: for every `A`, its ring/algebra instances and `g : points G A`,
  the displayed span is contained in its `comap (Matrix.toLin' (ρ.points A g))`.
  Containment is equivalent to preservation as an equality because the same
  containment holds for the inverse of every g. This predicate is written inline,
  not replaced by stability of k-points or by an assumed abstract semisimplicity.
- Finite direct sum of simple rational summands: `hM` provides `n : ℕ` and
  `S : Fin n → Submodule k (m → k)` with `iSupIndep S` and supremum top. Each S i
  is nonzero (`S i ≠ ⊥`) and rationally stable. Every rationally stable T below
  S i satisfies `T = ⊥ ∨ T = S i`, exactly simplicity of the restricted rational
  action: tensor inclusions identify stability in S i with stability in the ambient
  space. No hypothetical section or complement is assumed in hM.
- Restriction: the existing abstract representation
  `ρ.representation.comp Γ.subtype`.
- Finite sum of simple abstract summands: the first conclusion supplies
  `S : Fin n → Subrepresentation (ρ.representation.comp Γ.subtype)` with
  `(S i).toRepresentation.IsIrreducible`, independent underlying subspaces and
  supremum top. `Subrepresentation` is Mathlib's stable k-subspace, and its
  `IsIrreducible` says nonzero and no nonzero proper stable subspace.
- Every invariant subspace has an invariant complement: the second conclusion
  quantifies over all N of that `Subrepresentation` type and supplies C with
  `IsCompl N.toSubmodule C.toSubmodule` (intersection zero and sum the whole space).
- Every surjective equivariant k-linear map q to any abstract representation:
  the third conclusion quantifies over an arbitrary `V : Type v`, additive group,
  k-module, `σ : Representation k Γ V`, and an existing `IntertwiningMap` q, with
  `Function.Surjective q`. It supplies the opposite-direction `IntertwiningMap` s
  with `q.toLinearMap.comp s.toLinearMap = LinearMap.id`. Thus the section is both
  linear and equivariant. No rationality or finite-dimensionality is imposed on V;
  finite-dimensionality follows from surjectivity but is not added as a hypothesis.
- Zero spaces and disconnected groups: there is no `Nonempty m`, `Nontrivial`
  ambient-space binder, or connectedness binder. There is no characteristic or
  cardinality restriction on Γ.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (line 180), from `def-weil-field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed` (line 62), the
  algebraically-closed clause of `def-weil-algebraic-closure`'s Mathlib record.
- `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj` (line 43),
  and the group-on-Hom convention documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, for `def-sc-group-scheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`
  (line 62), for `def-sbc-smooth-morphisms`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`
  (line 43), and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `QuasiCompact` (line 43), for `def-weil-finite-type-morphism`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`,
  `RationalHom` (line 336) and `RationalHom.points` (line 345), and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation`,
  `RationalHom.representation` (line 64), supply the existing representation.
  The unrelated `IsSimple`/`IsSemisimple` abbreviations in the latter require
  `CharZero k` and are deliberately not used: that would exclude positive
  characteristic and would only test k-points without the rational stability data.
- `Mathlib.RepresentationTheory.Subrepresentation`, `Subrepresentation` and
  `toRepresentation`; `Mathlib.RepresentationTheory.Irreducible`,
  `Representation.IsIrreducible`; `Mathlib.RepresentationTheory.Intertwining`,
  `Representation.IntertwiningMap` and its `toLinearMap`.
- Proof dependency `lem-wf-stabilizer-density`: the two recorded declarations in
  `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`,
  `Matrix.GeneralLinearGroup.mulVec_mem_of_mem_zeroLocus_vanishingIdeal` and
  `forall_mulVec_mem_iff_forall_mem_zeroLocus_vanishingIdeal` (lines 599--621),
  were read; that module is a plain proof import.
- Proof dependency `lem-sfb-module-socle-complements`: its Mathlib match
  `IsSemisimpleModule.of_sSup_simples_eq_top` and `IsSemisimpleModule` were read
  in `Mathlib.RingTheory.SimpleModule.Basic` (lines 63--66 and 200--202).
  That module is explicitly included as a plain proof import.
- Proof dependency `lem-sfb-smooth-group-rational-point-subspace-test` has no Lean
  record, Mathlib match or upstream audit declarations. It is therefore not yet
  imported, as the rule applies to proof dependencies that are stated. No notion
  from this unstated theorem is needed to TYPE this statement: the all-algebra
  predicate is written out. Its eventual module can be added by maintenance.

Edge cases checked before writing: `m` empty and `n = 0` give zero source and empty
sum. A surjection from it forces zero target. N zero and N whole allow C whole and
C zero. Algebraic closure of any positive-characteristic field is allowed; no
Maschke assumption is smuggled in. The regular representation of a cyclic p-group
in characteristic p fails the simple-direct-sum hypothesis, as it should. A torus
with distinct characters and an infinite dense subgroup preserves the same simple
lines; replacing that subgroup by a nondense finite group can create additional
stable lines, confirming why density is essential. A disconnected smooth group
and a subgroup meeting every component are not excluded. Test algebras include
k, dual numbers and the zero algebra; over the zero algebra the extended span is
zero, so stability is automatic rather than an obstruction.

Searches actually run with `msearch.py`:

- LeanFinder: `A semisimple rational representation of a smooth affine algebraic group
  restricts semisimply to a Zariski dense subgroup`: eight hits, including
  `Module.End.IsSemisimple.restrict`, Wedderburn-Artin, and Maschke. These concern
  single endomorphisms or finite groups and do not state the dense-group theorem.
- Loogle: `IsSemisimpleModule, Representation`: one hit,
  `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`.
  Its complete source was read: it compares abstract representations and modules,
  not rational representations and dense subgroups.
- Mathlib grep: `baseChange|map.*algebraMap` in `LinearAlgebra/Matrix`: 17 hits,
  chiefly matrix coefficient extension and change-of-basis lemmas, no target theorem.
- LeanSearch: `A representation restricted to a Zariski dense subgroup has the same
  invariant subspaces`: eight hits, including `Representation.toInvariants`,
  `Representation.le_comap_invariants`, `Rep.subrepresentation`, and invariants
  constructions. None compares rational subspaces with a dense abstract subgroup.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for rational
  representations, rational semisimplicity, dense restriction, and the node id.
  It found the exact general-purpose `RationalHom` and abstract representation
  interfaces described above. The only subgroup semisimplicity restriction theorem
  read is Clifford's theorem for a NORMAL subgroup; normality is not assumed here.
  The exact node id and proposed theorem name have no existing Lean declaration.
  The upstream name index was also searched. No new notion or second definition
  was introduced, and no new node or dependency module is needed.

Validation: compiled only through the prescribed `scompile.py` against the live
published library. The first compile identified the missing `MonObj` scope for
the canonical group on points; enabling its existing scoped instance and renaming the basis index to avoid
the scope's inverse notation fixes that interface issue. No instance or mathematical hypothesis was added. Final compile
and server preflight results are recorded below after validation.

Final `scompile.py`: PASS, both sandbox and library-module compilation, with no
errors or warnings (14.4 s and 9.6 s). The additional elaboration repair was to
spell `Representation.IntertwiningMap` explicitly instead of field notation on
the underlying `MonoidHom`; its type and mathematical meaning are unchanged.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
