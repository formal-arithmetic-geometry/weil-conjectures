## Worker report

The module `Sheaf.AlgebraicGeometry.NilpotentQuotientUnipotentCentre` states
`AlgebraicGeometry.nilpotent_quotient_unipotent_centre`, with its only proof `sorry`.
There is one supporting definition module, with a fully written Prop-valued body
and no postponed data or auxiliary theorem. Nilpotence is written directly as
the central-series formula in the hypothesis and conclusion. No original statement or proof is corrected.

Source read: Milne, Algebraic Groups (2017), Lemma 16.45 and its proof using 16.43,
printed p.340; Definition 6.34, Remark 6.35 and Proposition 6.37, p.133;
Theorem 14.5(a),(b), pp.281--282. The latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` concerns stability of
the six functors; this item is a supporting group-theoretic input, not that unit's statement.
The instructed CompactObject example is currently withdrawn and has no declarations;
its node record and the current module-mode examples were read instead.

Clause-by-clause correspondence:

- Field: `{k : Type u} [Field k]`.
- All groups are k-group schemes: `G D H : Grp (Over (Spec (.of k)))` and similarly
  the quantified S and the output C. Bundled morphisms `iD`, `q`, `j`, `f`, `iC`
  preserve the group law. No separate arbitrary action or map is substituted.
- Affine finite type: `hG`, `hD`, `hH : SolvableGroupStructure.IsAlgebraic ...`,
  whose recorded definition is `IsAffine ... ∧ LocallyOfFiniteType ... ∧ QuasiCompact ...`.
  The output C is explicitly algebraic. Closed subgroup terms of a series in an
  algebraic ambient group are automatically affine finite type over the field.
- Closed subgroup D: `hiD : IsClosedSubgroupScheme iD.hom.hom`.
- Connected ambient G: `hconn : ConnectedSpace G.X.left`, including nonemptiness.
- Nilpotent G: `hnil` explicitly quantifies a finite family
  `N : Fin (s+1) → Grp ...` with closed normal embeddings `i j` into G,
  `IsIso (i 0)`, final group isomorphic to `Grp.trivial _`, adjacent inclusion
  factorizations, and all commutators of G(A) with N_j(A) factoring through N_(j+1)(A).
- D lies in the scheme-theoretic centre: `hcentral` puts every algebra-valued D-point
  in `centralizerPoints (𝟙 G) A`. This recorded predicate checks commutation after
  every algebra extension, not just commutation in G(k).
- D has multiplicative type: `hmult : MultiplicativeType.IsMultiplicativeType D`.
  Its existing definition uses actual base change to `AlgebraicClosure k` and
  a closed subgroup inclusion into the finite product `splitTorus`; rank zero is allowed.
- Largest such subgroup of Z(G): `hmax` quantifies over all closed multiplicative-type
  inclusions `j : S ⟶ G` whose points satisfy that same universal centre condition,
  and concludes `∃ f : S ⟶ D, f ≫ iD = j`. This is exactly containment of represented
  closed subgroups, including nonreduced subgroups. S need not be separately assumed
  algebraic because closed in the affine finite-type G implies that property.
- Represented fppf quotient: `hq : SolvableGroupStructure.IsFppfQuotient iD.hom.hom q`.
  This is the dependency's actual cover/kernel definition (flat, surjective, locally
  finitely presented, with the specified kernel isomorphism commuting with iD).
  Its docstring explains the equivalent sheafification of the pointwise coset functor.
- Quotient H connected and nilpotent: the first two conclusion conjuncts are
  `ConnectedSpace H.X.left` followed by the explicit finite central-series
  existential for H, with the same closedness, normality, endpoints, inclusion
  factorizations and all-algebra commutator containment as in `hnil`.
- Its centre is unipotent: the remaining conclusion gives a closed normal commutative
  algebraic subgroup `iC : C ⟶ H` whose image on EVERY commutative algebra equals
  `centralizerPoints (𝟙 H) A`, and `IsUnitriangularUnipotentGroupScheme C`.
  The set equality specifies exactly Z(H); it is not an arbitrary central subgroup.
  The new unipotence predicate gives positive n and a closed group immersion to GL_n
  with diagonal one and lower entries zero on all A-points. This is exactly a closed
  immersion to U_n: the defining matrix equations force factorization through that
  closed subscheme, and a closed immersion to GL_n remains closed in U_n.
- There is no smoothness, perfectness, reducedness, or characteristic assumption.
  The unipotence conclusion is about Z(H), without an additional conclusion about H.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.CategoryTheory.Monoidal.Grp`:
  `CategoryTheory.GrpObj` and `Grp` (the standard bundled group objects).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`; their full functor-of-points
  signatures, including injectivity on all algebras, were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`; `...ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including `toNonempty`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `...Basic`: `IsAlgClosed` and `IsAlgClosure`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `baseChange`, `splitTorus`,
  `IsMultiplicativeType` in `AlgebraicGeometry.MultiplicativeType`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, and the actual
  multiplicative group, reused by splitTorus. Affine k-algebra points are reused throughout.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` imports the actual upstream GL construction;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` supplies
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`. The index is
  `ULift.{u} (Fin n)` to respect that construction's common universe, with entries
  indexed by the lifted standard ordered finite basis.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsFppfQuotient`.
  Its `IsUnipotent` was read but is NOT used: it explicitly includes smoothness.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.centralizerPoints`;
  `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`:
  `exists_affine_group_centre_baseChange`. The conclusion uses its precise represented
  centre interface; no noncanonical centre object is chosen from an existence theorem.

Plain proof imports are `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`
(`affine_normal_quotient_geometry`), `...AffineHomomorphismFlatImage`
(`affineGroupHom_exists_faithfullyFlat_closedImmersion`), and Mathlib
`RingTheory.Flat.FaithfullyFlat.Basic` and `...Algebra`
(base-change faithful flatness, `Module.FaithfullyFlat.tensorProduct_mk_injective`).
The proof dependencies `lem-sfb-commutative-multiplicative-part` and
`lem-sfb-normal-multiplicative-layers-central` have no recorded Lean declarations,
so they are named in the proof docstring but have no import yet. Neither is needed
in the statement. No declared proof dependency import is omitted.

Edge cases checked mathematically before writing:

- G = D = H = 1: the length-zero central series works, and U_1 is the trivial
  group, so n = 1 witnesses unipotence. Nothing forces a nontrivial group or positive
  central-series length. For s = 0 the initial isomorphism and terminal triviality
  correctly force G trivial; the successor conditions are empty.
- Rank-zero split tori and D = 1 are allowed. For commutative multiplicative-type G,
  taking D = G gives trivial quotient and trivial unipotent centre.
- In characteristic p the connected nonsmooth group alpha_p has trivial multiplicative
  part and embeds in U_2; it is included, unlike the older smooth predicate.
- A zero test algebra is allowed: 0 = 1 there and the matrix equations are consistent.
- Nonreduced test algebras are essential and are quantified, so infinitesimal central
  and multiplicative-type subgroups are not lost by testing only fields.
- Empty schemes cannot be group schemes over a field: the identity section prevents it.
  ConnectedSpace retains the nonempty condition required by the node.
- The field, schemes, and test algebras share the existing library universe u, with no
  smaller independent test universe and no equality imposed between unrelated universes.

Searches performed via msearch.py (full authentic response records follow below):
LeanSearch, LeanFinder, Loogle and Mathlib grep found abstract-group nilpotence,
ordinary subgroup centres, matrix topologies, and general closed-immersion facts,
but no theorem matching the item. The repair removes the proposed nilpotence
predicate; the formula is stated directly, as in the existing series theorems. Project rg on
`lean/WeilConjectures` and `lean/Sheaf` by item id, nilpotence, and unitriangular words
found no existing theorem. `AdjointKernelCentralQuotientUnipotent` and
`CharZeroCommutativeUnipotentVectorGroup` have inline unitriangular conditions;
`CentralMaximalTorusNilpotent` and `NilpotentConnectedCentralSeries` have inline
central-series formulas. These are statements, not reusable definitions.
Searching all DAG definition nodes by nilpotent/unipotent/unitriangular terms found
only the smooth unipotence and split-additive-series notions, not these two notions.
`tools/blueprint_refs.py search unitriangular` returned no blueprint node; search
`nilpotent` returned abstract linear-algebra and unrelated nilpotent-ideal nodes.
The required upstream item-id search returned no declaration. No statement dispute.

## New nodes

`def-sfb-unitriangular-unipotent-group-scheme` owns
`Sheaf.AlgebraicGeometry.UnitriangularUnipotentGroupScheme` and
`IsUnitriangularUnipotentGroupScheme`. Its source is Theorem 14.5(a),(b), pp.281--282.
It uses the actual upstream GL and its natural point/matrix equivalence; its
closed embedding and universal matrix equations express exactly the closed U_n
embedding, without a smoothness assumption. The existing smooth geometric
predicate cannot describe alpha_p. Three authentic searches are recorded.

The remaining new node inherits the item's chapter, unit, and blueprint provenance,
including its null ancestor (confirmed by `blueprint_refs.py ancestor`). It
is reached from the former target `thm-weil-final` through this item, so its
required import_flags are empty. Only the item's lean record and addition of
this one stmt_dep are changed; other fields remain unchanged.

Validation: both delivered modules compiled independently through scompile.py against
the live published server library, in dependency order. No warnings or errors;
the sole theorem is intentionally postponed for stage 3.

Search response records:

```jsonl
{"t": "2026-10-24T07:59:00Z", "tool": "leanfinder", "query": "Connected nilpotent affine group scheme quotient by largest central multiplicative subgroup has unipotent centre", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["nilpotent_center_quotient_ind", "of_quotient_center_nilpotent", "nilpotencyClass_quotient_center", "nilpotencyClass_eq_quotient_center_plus_one", "nilpotent_quotient_of_nilpotent", "Group.IsNilpotent.nilpotent", "Group.IsNilpotent.nilpotent'", "LieAlgebra.nilpotent_of_nilpotent_quotient"], "digest": "aeeb7a79e2c9b6cf"}
{"t": "2026-10-24T07:59:01Z", "tool": "loogle", "query": "\"IsNilpotent\", \"center\"", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["LieAlgebra.non_trivial_center_of_isNilpotent", "AddGroup.IsNilpotent.center_ne_bot", "Group.IsNilpotent.center_ne_bot", "Group.IsNilpotent.prime_dvd_card_center", "AddGroup.IsNilpotent.inf_center_ne_bot_of_normal", "Group.IsNilpotent.inf_center_ne_bot_of_normal", "AddSubgroup.isNilpotent_of_ker_le_center", "Subgroup.isNilpotent_of_ker_le_center"], "digest": "e9c8f36120887afc"}
{"t": "2026-10-24T07:59:01Z", "tool": "grep", "query": "unitriangular|Unitriangular|nilpotent.*[Gg]roup[Ss]cheme", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-24T08:00:21Z", "tool": "leansearch", "query": "The centre of a connected nilpotent group scheme modulo its maximal central multiplicative subgroup is unipotent", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["nilpotencyClass_quotient_center", "of_quotient_center_nilpotent", "nilpotent_center_quotient_ind", "nilpotent_quotient_of_nilpotent", "Subgroup.center", "upperCentralSeries_nilpotencyClass", "nilpotencyClass_eq_quotient_center_plus_one", "Group.IsNilpotent.nilpotent"], "digest": "a0bd64a69d35feeb"}
{"t": "2026-10-24T08:00:41Z", "tool": "leansearch", "query": "An affine group scheme has a finite central series of closed normal subgroup schemes", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["upperCentralSeries", "upperCentralSeries_normal", "nilpotent_iff_finite_ascending_central_series", "IsAscendingCentralSeries", "Group.IsNilpotent.nilpotent", "upperCentralSeriesAux", "nilpotent_iff_finite_descending_central_series", "Group.IsNilpotent.nilpotent'"], "digest": "913ec334f66c744a"}
{"t": "2026-10-24T08:00:42Z", "tool": "leanfinder", "query": "A group scheme admits a closed embedding into upper unitriangular matrices over every commutative algebra", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["Matrix.SpecialLinearGroup.isClosedEmbedding_toGL", "Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt", "Matrix.SpecialLinearGroup.isEmbedding_mapGL", "Matrix.SpecialLinearGroup.isEmbedding_toGL", "CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding", "CategoryTheory.PreGaloisCategory.autEmbedding_range_isClosed", "Matrix.SpecialLinearGroup.isInducing_mapGL", "Topology.IsClosedEmbedding.matrix_map"], "digest": "10bae4afb42bf603"}
{"t": "2026-10-24T08:00:43Z", "tool": "leansearch", "query": "Unipotent group scheme closed immersion upper triangular matrices diagonal one", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["AlgebraicGeometry.IsSeparated.instIsClosedImmersionLiftSchemeId", "AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono", "AlgebraicGeometry.isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange", "AlgebraicGeometry.IsClosedImmersion.instIsPreimmersion", "AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion", "AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion", "AlgebraicGeometry.IsImmersion.instDiagonalScheme", "AlgebraicGeometry.IsImmersion.instLiftSchemeId"], "digest": "d8dd6cc612f1416e"}
{"t": "2026-10-24T08:00:46Z", "tool": "leanfinder", "query": "Nilpotent group scheme finite descending central series of closed normal subgroup schemes", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["nilpotent_iff_finite_descending_central_series", "nilpotent_iff_finite_ascending_central_series", "nilpotent_iff_lowerCentralSeries", "Group.IsNilpotent.nilpotent", "Group.IsNilpotent.nilpotent'", "Group.IsNilpotent", "Group.isNilpotent_iff", "Group.IsVirtuallyNilpotent"], "digest": "7265c5bbeeb7e660"}
{"t": "2026-10-24T08:06:22Z", "tool": "grep", "query": "IsNilpotentGroupScheme|IsUnitriangularUnipotentGroupScheme|unitriangular|nilpotent.*[Gg]roup[Ss]cheme", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
```


## Repair of returned head 98840818d9d4

The sole return point reports a collision for
`AlgebraicGeometry.IsNilpotentGroupScheme` with the module
`Sheaf.AlgebraicGeometry.IsNilpotentGroupScheme`. The named module remains
unavailable: prescribed `scompile.py --source` exits 1, and the module-mode
import probe fails in both compilation and server confirmation because its
object file does not exist. No matching declaration or owning node is readable
in the current source/DAG. The earlier retry stopped at this discrepancy.

This repair removes the colliding declaration altogether, instead of renaming
it or creating a purported existing binding. Specifically it removes
`lean/Sheaf/AlgebraicGeometry/NilpotentGroupScheme.lean`, removes the proposed
`def-sfb-nilpotent-group-scheme` node and that added stmt_dep, and drops its
import from the item. The theorem now writes exactly the removed definition's
body directly at its two uses: the nilpotence hypothesis on G and the nilpotence
conclusion on H. There is no new nilpotence declaration, definition node or
alias. All the ingredients are recorded declarations already owned by the
item's original dependencies: group objects, closed/normal subgroup inclusions,
trivial groups, isomorphisms, and algebra-valued point multiplication.
This follows the existing inline statements in NilpotentConnectedCentralSeries
and CentralMaximalTorusNilpotent. It resolves the actual duplicate-declaration
failure without needing the unavailable import.

The expanded formulas are alpha-renamings of the deleted body, with N replacing
C for the series terms so the final centre C stays unambiguous. For each ambient
J = G or H they quantify s and N_0,...,N_s with embeddings into J, require every
embedding closed and normal, require the first embedding an isomorphism and the
last group trivial, require adjacent inclusions to commute with the embeddings,
and require every [g,c] over every commutative algebra to factor through the
next term. Length zero, nonreduced algebras and nonsmooth groups remain covered.
The original natural-language statement, hypotheses, conclusions and proof plan
are unchanged. The node's lean.statement is regenerated verbatim from the file.
The repair changes Lean code and removes a module and node relative to the
returned packet; it is not an unchanged re-push or a declaration rename.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
