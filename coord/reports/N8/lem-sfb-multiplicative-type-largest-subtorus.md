## Worker report

The live node is a stage-2 queue item (queue.tsv lists stage 2) with an accepted stage-1 split and no Lean record. The inherited failure was a stage-1 live-wins refusal; brief-stage2 §0 explicitly distinguishes that from this statement assignment. No repair note exists for this item. The retained sandbox initially contained no files.

The delivery states `AlgebraicGeometry.MultiplicativeType.multiplicativeType_largestSubtorus` in `Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus`. Its only proof is `sorry`. The original statement, accepted proof split, source, status and review are preserved; `stmt_deps` only gains the new definition node.

Hypotheses and clauses, in the order of the node:

- The field is `(k : Type u) [Field k]`. Group schemes are Mathlib's `Grp (Over (Spec (.of k)))`: the bundled version of the dependency's `GrpObj`.
- Every ambient quantified group is affine by `[IsAffine G.X.left]` and finite type by `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`. The existential torus carries those same three properties as explicit conjuncts.
- All subgroup inclusions are `IsClosedSubgroupScheme j.hom.hom`, the dependency's exact predicate on the underlying over-category morphism. The bundled group morphism retains multiplication compatibility.
- The node's definition of a torus is `IsTorus`: after `baseChange` to `AlgebraicClosure k`, an isomorphism in bundled group schemes to `splitTorus` of some `n : ℕ`. Rank zero is the tensor unit; successor rank is the product with the recorded G_m. Thus these are group-scheme isomorphisms, not merely isomorphisms of underlying schemes.
- Multiplicative type is `IsMultiplicativeType`: a closed subgroup inclusion of the algebraic-closure base change into a split torus of finite rank. No smoothness or reducedness is built into it.
- “Every torus is smooth and connected” is the first conjunction: `IsTorus T → Smooth T.X.hom ∧ ConnectedSpace T.X.left`. Geometric connectedness in the node is explanatory terminology, not an additional asserted conclusion; the proof docstring follows its use of geometric connectedness.
- “There is a largest subtorus” is the second conjunction, existentially quantifying its actual group scheme T and inclusion i. `IsLargestSubtorus i` includes closedness and the torus property and requires every closed subtorus inclusion j to factor as `f ≫ i = j` in group schemes.
- “For every field extension, (D^t)_K = (D_K)^t as subgroup schemes” is `∀ (K : Type u) [Field K] [Algebra k K], IsLargestSubtorus ((baseChange ...).map i)`. This expresses precisely that the base-changed inclusion represents the largest subobject, independently of the representatives chosen for either subgroup. Since closed immersions are monomorphisms, mutual factorization gives an isomorphism commuting with the inclusions, hence equality of subgroup schemes. Literal equality of arbitrarily chosen domains would incorrectly assert equality of representatives. The functor is the canonical `Over.pullback` lifted by Mathlib's `mapGrp`, not a freely supplied map.
- Closed subgroups of multiplicative-type groups remain of multiplicative type: the third conjunction, with the actual inclusion j and `IsMultiplicativeType D → IsMultiplicativeType H`.
- Smooth connected multiplicative-type groups are tori: the fourth conjunction `IsMultiplicativeType H → Smooth H.X.hom → ConnectedSpace H.X.left → IsTorus H`.
- The stated special case is retained explicitly in the fifth conjunction, for a smooth connected closed H in a torus T.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.homMk`, `Functor.mapGrp`, and tensor products of bundled group objects.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme` and `IsClosedSubgroupScheme` (including their full signatures and pointwise-injectivity and closed-immersion fields).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; the imported quasi-compact predicate is `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`, with coordinate algebra `LaurentPolynomial k` and its existing Hopf group law. Read the source, including its affine construction.
- New helper dependencies use `Algebra` and `algebraMap` (`Mathlib.Algebra.Algebra.Defs`), `AlgebraicClosure` (`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`), and `Over.pullback` with `Functor.mapGrp`. The recorded base-change conventions module is publicly imported and its docstring identifies precisely this pullback construction.

Stated proof dependencies are imported privately: closed immersion is already publicly available through the subgroup definition; smooth descent uses `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`; algebraic-closure connectedness uses `Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`; the rational-point criterion uses `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`; proper/smooth base change uses Mathlib Proper/Smooth; the finite-basis lemma uses `Mathlib.LinearAlgebra.FreeModule.PID`. The two new stage-1 structural inputs `lem-sfb-multiplicative-character-antiduality` and `lem-sfb-diagonalizable-group-geometric-criteria` have no recorded Lean module yet; no proof-only module can be imported for them. Their arguments are retained in full in the theorem docstring, matching the six accepted proof steps.

Edge cases checked mathematically: the empty product is the trivial group and is permitted by n = 0; finite multiplicative-type groups have trivial largest torus; μ_p in characteristic p is allowed to be nonsmooth and does not satisfy the smooth-torus criterion; prime-to-p μ_n is disconnected; a nonsplit real norm torus is tested after algebraic closure, not required to split over the ground field; characteristic zero has no extra hypothesis; every extension including identity, inseparable and transcendental is quantified without separability or finiteness hypotheses. Universes are explicit, and the field, schemes, test rings in the upstream subgroup predicate, algebraic closure, and extension fields share the standard Scheme.{u} convention. There are no auto-bound implicits, private definitions, local notation, added axioms, chosen arbitrary objects, or hollow data.

Searches actually run (msearch.py N8, logged in searches.jsonl):

- LeanFinder: “An affine group scheme of multiplicative type has a largest torus subgroup compatible with field extensions”: eight unrelated hits (absolute Galois groups, AffineSpace, affine transition limits, units, Galois categories), no match.
- Loogle: `"Torus", "Scheme"`: zero hits.
- Mathlib grep: `IsTorus|MultiplicativeType|subtorus`: zero hits.
- LeanSearch: “An algebraic group is a torus if it becomes a product of multiplicative groups over an algebraic closure”: eight hits, analytic UnitAddTorus and unrelated torsion/geometrically reduced definitions, no group-scheme predicate.
- `rg` of WeilConjectures and Sheaf for torus, multiplicative type, diagonalizable: toric chart constructions and textual mentions, no general predicate or largest-subtorus theorem. The existing multiplicative group and group-object functor APIs were read and reused. Upstream name index has no torus or multiplicative-type entry.
- DAG statement searches find this item and other statements that define the terminology inline; no definition node owns it. `tools/blueprint_refs.py search torus` returns zero blueprint nodes. `ancestor` reports None, preserved in the new node's blueprint.from.node.

Read Milne's actual local PDF with pdftotext, printed pp.230--241: Definition 12.14 (and smooth-connected subgroup paragraph), Definition 12.17 (closure under subgroups and the criterion), Theorem 12.23, Corollary 12.24, Notation 12.29 (largest torus and arbitrary extension compatibility). No statement fault or STATEMENT-DISPUTED issue found. No statement correction is made.

Validation: both files compiled individually in dependency order through scompile.py against the published live library, without errors or unexpected warnings. Final dry-run and delivery results are recorded by the wrapper.

## New nodes

`def-sfb-tori-multiplicative-type` owns the missing terminology explicitly introduced in the item's statement: finite products of the existing G_m, their canonical scalar extensions, torus and multiplicative-type predicates, and the factorization property defining a largest subtorus. Its source is Milne, Theorem 12.9(c), Definitions 12.14 and 12.17, Notation 12.29. Its own module `Sheaf.AlgebraicGeometry.ToriMultiplicativeType` contains five declarations with real definitions, no postponed proof and no choice. It cites the existing field, group scheme, subgroup, G_m, algebraic closure, field extension and base-change nodes. The searches above and their actual logged results are copied into its mathlib_searches. The existing toric monoid chart tori are particular schemes, not this predicate for arbitrary group schemes.

## Second reading by N8

This is the author's separate second reading; the dispatcher explicitly prohibits starting other agents, and the maintainer supplies the independent delivery review. I reopened the item, both delivered modules, the seven original dependency records, and Milne's definitions and Notation 12.29. I checked each conjunction against the clause mapping above, including the finite-type/affine restrictions on every original quantified group, closed subgroup structure, group-law preservation in the geometric isomorphism, and the inclusion-commuting interpretation of subgroup equality. The first definition draft had an extra closing parenthesis in the binder for IsLargestSubtorus; it was repaired before compilation. The second reading also added the recorded base-change conventions import for the new node's dependency. No mathematical mismatch or statement change was found. In particular the choice-free largest-subtorus property suffices to state the equality of subgroup schemes, and no assumption that D or its geometric fibre is smooth or connected has slipped into the existence clause.

Preflight record repair: added the empty import_flags array required by the live server schema for the new node. Corrected lean.statement extraction to retain named-argument := tokens inside the theorem signature; it now ends only at the theorem proof assignment.
