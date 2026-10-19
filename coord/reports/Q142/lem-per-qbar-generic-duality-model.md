## Worker report

Repair of the delivery returned at immutable head fdab24ae8fd9, points H3, H4 and H11.
The saved packet was inspected and dry-run first, as instructed. That dry-run failed:
its partially repaired module had typeclass heartbeats, a structure-map IsOver failure,
and unresolved universes. No delivery was pushed by that run. The retained module path
is `lean/Sheaf/DeligneLaumon/GenericDualityModel.lean`; its main theorem is
`AlgebraicGeometry.Scheme.PerAdic.lem_per_qbar_generic_duality_model`, with proof `sorry`.
All changes are in the sandbox. The delivery wrapper prepares the current-base commit.

The module now uses the recorded intrinsic common-stage category and actual Verdier
and adic lisse operations. It adds only packaging/transport helpers for this statement:
`genericModelConstantRank`, `genericModelCohomology`, `genericModelDualTensor` and
`genericDualityClause`, plus the separation instance derived from the structure morphism.
Each has real data and a source/blueprint docstring. All are listed in `lean.declarations`.
There are no new nodes or dependency repairs. The already landed definition node
`def-a1-common-stage-lisse-lattice` is added to `stmt_deps` under brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES); it supplies whole-component lissity. The item's
natural-language statement, proof and proof dependencies are unchanged.

Hypothesis and conclusion correspondence, against the complete node statement:

- Any field: `(k : Type u) [Field k]`. No perfectness, algebraic closedness,
  finite Galois cohomological dimension or smoothness assumption is introduced.
- Prime invertible in k: `(l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]`.
- Fixed coefficient algebraic closure: `Qbar : Type (u + 1)` with `Field`,
  `Algebra (Padic l) Qbar` and `IsAlgClosure (Padic l) Qbar`. This is the recorded
  lisse calculus' coefficient convention; geometric test fields have universe u,
  matching the schemes, their residue fields, and their algebraic closures.
- Nonempty separated finite-type k-scheme T: `W : PerAdic.Base k`,
  `hW : Nonempty W.scheme`. The Base fields are the structure map, relative
  separatedness, locally finite type and quasi-compactness. Its existing instances
  supply Noetherianity, finite dimension and stalkwise invertibility of l.
  `baseSchemeSeparated` constructs absolute separatedness by composing the separated
  structure map with the separated morphism from Spec k to the terminal scheme.
- Category C_T: `intrinsicPbcQbarCategory l Qbar W.scheme`, the recorded alias of
  `generalAlgebraicallyClosedConstructibleCategory`, not an unrestricted sheaf category.
- Standard cohomology: `genericModelCohomology l Qbar W C r` is exactly
  `C.comparison.inverse ⋙ C.cohomology r ⋙ C.comparison.functor`.
  `AdicLisseCalculusModels.cohomology_integral` identifies C.cohomology, on every
  integral stage, with `adicCalculusIntegralCohomology`, the standard integral
  t-structure cohomology followed by inclusion. `comparison_integral` fixes the
  equivalence on those same stages. Every rational-stage object is an integral
  representative, and common-stage objects are finite-field pairs. These
  normalizations specify the same standard cohomology as the recorded adic-heart
  theorem in the intrinsic coefficient presentation. This helper transports that
  existing functor and does not choose a new t-structure or a free cohomology functor.
- Finite family: `s : ℕ`, `K : Fin s → intrinsicPbcQbarCategory ...`.
- Dense open U: `U : W.scheme.Opens` and `Dense (U : Set W.scheme)`.
- Contains every generic point: `∀ x, x ∈ genericPoints W.scheme → x ∈ U`.
  Mathlib's `genericPoints` means generic points of irreducible components. The
  former `IsGenericPoint x Set.univ` clause was inadequate on a reducible scheme.
- Finite disjoint decomposition: `t : ℕ`, `V : Fin t → Base k`, open immersions
  `j i : (V i).scheme ⟶ W.scheme`, containment of their ranges in U, equality
  of U with their union, and pairwise disjoint ranges. The explicit
  `(j i).IsOver (Spec (.of k))` clause makes them open k-subschemes.
- Every component is nonempty and irreducible: separate explicit clauses
  `∀ i, Nonempty (V i).scheme` and `∀ i, IrreducibleSpace (V i).scheme`.
- Dimension d_alpha is finite and nonnegative: `d : Fin t → ℕ` and
  `topologicalKrullDim (V i).scheme = (d i : WithBot ℕ∞)`; no tautological
  nonnegativity conjunct is needed for a natural number.
- Reduced closed complement dimension drop: the strict inequality between
  `topologicalKrullDim (((U : Set W.scheme)ᶜ : Set W.scheme))` and
  `topologicalKrullDim W.scheme`. U is open, so its complement is closed;
  reduction preserves exactly this underlying topological space and dimension.
- All restricted H^r(K_a) are lisse of constant rank on the entire component:
  for every a,r,i, `∃ n : ℕ, genericModelConstantRank ... H n`, where H is
  cohomology of `(ArbitraryFieldVerdier.pull l hl.out Qbar (j i)).obj (K a)`.
  Pull is the recorded completed common-stage inverse image. Its t-exactness
  identifies this with the restriction of H^r(K_a). ConstantRank requires the
  existing `HasCommonStageLisseLattice` on this entire component, and equality
  of every algebraically closed geometric fibre's `Module.finrank Qbar` to n.
  Fibres use C.fiber after C.comparison.inverse; C.fiber_integral pins them to
  completed pullback, point sections, and finite-field scalar extension. A mere
  lisse stratification is nowhere used as a lissity hypothesis or conclusion.
- Canonical omega and D: `B i : ArbitraryFieldVerdier.Datum ... (𝟙 (V i).scheme)`
  and `Nonempty (ArbitraryFieldVerdier.Properties ... (B i))`. This is the
  recorded Verdier datum applied to the identity of the component. Its X
  structure functor is the identity compact-support functor followed by Ra!,
  so `Datum.omegaX` is the right-adjoint value of the coefficient unit, and
  `Datum.dualX` is the specified internal Hom into that object. Properties includes
  the source adjunction normalization, duality, compact-support realization and
  finite-field compatibility. No free dual functor or free dualizing object remains.
- Rank-one lisse O_alpha: `O i : LisseAlgebraicSheaf l (V i).scheme Qbar`, realized
  by `(C i).comparison.functor.obj ((C i).realization.obj (O i))`, with
  `genericModelConstantRank ... 1` on this object. Rank is imposed on O, not on
  the shifted dualizing complex.
- The required omega isomorphism is explicit:
  `Nonempty ((B i).omegaX l hl.out Qbar ≅
    ((C i).comparison.functor.obj ((C i).realization.obj (O i)))⟦2 * (d i : ℤ)⟧)`.
- Every bounded L with lisse cohomology is covered by `genericDualityClause`:
  `∀ L`, with hypothesis `∀ r, HasCommonStageLisseLattice ... (H^r L)`.
  This is whole-component lissity, allowing all local finite ranks and rank zero.
- The duality formula: for every r the clause produces a genuine lisse adic sheaf
  M, an identification of its realization with `H^(-r-2*d)(L)`, and an isomorphism
  from `H^r((B.dualX ...).obj (op L))` to `genericModelDualTensor ... C M O`.
  The latter is the recorded `adicCalculusTensor` applied to the realizations of
  `C.dual.obj (op M)` and O, then transported by C.comparison.functor. Thus O is
  present in the formula and the dual and tensor are precisely the recorded
  operations, not existential free functors. The explicit existence of M and
  source identification also prevents a vacuous universal representation clause.
- The right side is lisse: `HasCommonStageLisseLattice` of this dual-tensor object.
- Zero exactly when the source cohomology is zero: `IsZero` of that same object
  iff `IsZero` of `H^(-r-2*d)(L)`. Both sides are objects of the recorded category.

Dependency modules and declarations actually used:

- `Sheaf.Paper.IntrinsicQbarCategory`: `WeilConjectures.intrinsicPbcQbarCategory`.
- `Sheaf.Paper.AdicHeartIntrinsicFibres` publicly retains the recorded adic-heart
  interface and its `PerAdic.Base`, `baseNoetherian`, `baseDimension`,
  `basePrimeUnit`, standard heart, truncation and cohomology convention.
- `Sheaf.SixFunctors.ArbitraryFieldVerdier`: `ArbitraryFieldVerdier.Datum`,
  `Datum.omegaX`, `Datum.dualX`, `Properties` and `pull`.
- `Sheaf.Paper.AdicLisseCohomologyCalculus`: `AdicLisseCohomologyCalculus`,
  its normalized comparison, realization, cohomology, fibre and dual fields,
  and `adicCalculusTensor`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: the recorded module reexports
  `LisseAlgebraicSheaf` and the original integral/rational lisse interfaces.
- `Sheaf.Paper.CommonStageLisse`: `WeilConjectures.HasCommonStageLisseLattice`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`; Mathlib's `genericPoints`
  is read in `Mathlib.Topology.Sober` and is available through these imports.

Every recorded proof-dependency module is also imported (non-public when proof-only).
The theorem docstring contains the complete ten-step proof: component separation,
generic lisse shrinking and constant ranks, regular reduction by excellence, dimension
of the complement, normalized finite coefficient dualizing towers, lisse/Milnor/derived
limit reconstruction, rationalized adjunction descent and Yoneda, finite free evaluation,
truncation induction and the -r-2d shift, and fibrewise vanishing detection.

Sources were read directly from the local PDFs via pdftotext: Bhatt--Scholze Lemma
6.7.20, Proposition 6.8.14 and Remark 6.8.15 (printed pp.58,61-62), and ILO XVII,
proof of Proposition the project server (printed p.294). The latter explicitly reduces to a dense
regular open, assumes it connected, and identifies the dualizing complex with a Tate
line shifted by twice the dimension function. It does not assume smoothness.

Edge cases checked: s=0 is allowed; W empty is excluded exactly by hW; t=0 cannot
cover a dense open of nonempty W; reducible W requires all component generic points
(the repaired genericPoints clause); nonreduced W is allowed and its complement is
measured topologically; d=0 permits an empty complement of dimension bottom; all
r are integers; zero lisse sheaves have constant rank zero; O must have rank one;
L=0 is allowed and gives the zero-object equivalence; positive dimension uses
H^(-r-2d), so for a sheaf in degree zero the nonzero dual degree is -2d. There is
no perfectness or smoothness requirement. No statement correction or dispute is needed.

Searches (the saved search packet was retained):

- Saved `msearch.py ... leanfinder` query “On a dense open a constructible l-adic
  complex has lisse cohomology and Verdier dual reverses degrees with shift twice
  the dimension”: eight generic derived-category hits, no exact theorem.
- Saved `msearch.py ... loogle 'topologicalKrullDim, Dense'`: zero hits.
- Repair `msearch.py ... leanfinder` query “dense open irreducible components lisse
  cohomology Verdier dual dualizing rank one shift dimension”: eight hits, including
  Sheaf.H and ordinary derived-category single-object lemmas, no exact theorem.
- Repair `msearch.py ... loogle '"dualizing"'`: zero hits.
- `rg` of `dualizing|Dualizing|[Ll]isse` in Mathlib AlgebraicGeometry and CategoryTheory
  found only generic category dualization comments, no lisse/dualizing theorem.
- `rg` of the node id, `generic.duality|generic_duality|GenericDuality` and helper
  names in upstream WeilConjectures and lean/Sheaf found no statement for this item.
  Upstream WeilSheaf duals concern a different Weil-sheaf category.
- Targeted project searches for lisse/cohomology definitions found the normalized
  AdicLisseCohomologyCalculus, the finite-field-only SfConstructibleHeart interface,
  and `CommonStageLisse.HasCommonStageLisseLattice`. The last already has a landed
  node and is reused directly; no second lissity predicate is delivered.

Validation: the revised final module compiled cleanly with scompile.py in both the
sandbox and its actual module location (6.7 s and 6.6 s respectively), under the
unchanged 60-second limit. Only the main theorem is postponed with sorry; no data is
postponed. The initial failing dry-run diagnostics have been repaired by using the
intrinsic category, explicit datum universes, the identity-morphism datum and the
recorded normalized cohomology interface, without increasing any timeout or budget.

## Second reading by Q142

This is the author's second reading, as the dispatcher prohibits additional agents;
the maintainer supplies the independent review. I reopened the complete node and final
module, rather than relying on the old report, and checked the correspondences above.

H3: the returned arbitrary D, omega and dualTensor have been removed. `B.dualX` and
`B.omegaX` are used directly; B is the actual compact-support adjunction/internal-Hom
datum with its full Properties. The rank-one object O is a lisse adic sheaf, enters the
dual-tensor formula, and is explicitly related to omega by the shift 2d. Every component
is nonempty and irreducible. Lissity uses the existing whole-scheme lisse-lattice
predicate, and a separate common geometric-fibre rank n is required for each K_a's
cohomology on each component. The premise on general L is whole-component lissity.
The saved partial repair's degree-r representative was also wrong: M now represents
exactly the source degree -r-2d, and its existence is in the conclusion.

H4: the modules and full signatures of both recorded dependencies named in the return
were read and are public imports. Their datum/object/functor fields are actually used.
The current recorded coefficient category is intrinsic, so the canonical calculus
comparison transports its cohomology, lisse realizations, fibres and tensor between
coefficient presentations. The independent landed lisse-lattice predicate is reused
and its node is added to stmt_deps. No private category or free duality operation remains.

H11: the previous second reading was inaccurate. This reading specifically checks all
field/scheme hypotheses, the finite family, density, generic points of every component,
open k-subscheme decomposition, nonemptiness, irreducibility, natural dimensions,
strict complement drop, lisse constant ranks, rank-one O, omega ≅ O[2d], universal L/r
quantification, both degrees of cohomology, the specified dual/tensor including O,
right-side lissity and zero equivalence. It also found and repaired the reducible-scheme
generic-point defect and made the k-linearity of the open embeddings explicit.
All helpers are constructions or Prop packaging of these recorded notions; none contains
sorry. The theorem has the source-based proof docstring. No source statement was altered.
