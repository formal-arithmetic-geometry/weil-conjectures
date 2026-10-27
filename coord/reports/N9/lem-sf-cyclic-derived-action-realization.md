## Worker report

The module `Sheaf.CategoryTheory.CyclicDerivedActionRealization` states
`CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedActionRealization`.
Its only theorem has proof `sorry`. There are no new definitions or helper theorems.
The original natural-language statement and all seven accepted proof steps are unchanged.

Q76's accepted delivery, reviewed on 2026-10-22, is the stage-1 split: its report explicitly
says that no Lean source was written. The current node has no `lean` or `reviewed_lean`
record. The previous N9 worker's stale-dispatch diagnosis confused the two stages.
This delivery supplies the missing stage-2 statement, without splitting the node again.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Grothendieck abelian category A | `{C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]` |
| Additive exact autoequivalence P | `(F : C ⥤ C) [F.Additive] [F.IsEquivalence]`; equivalences preserve finite limits and colimits, so exactness is inferred rather than added as an independent assumption |
| B = A^P | The existing `CategoryTheory.Endofunctor.IsoAlgebra F`, definitionally the full subcategory of `Endofunctor.Algebra F` where `IsIso A.str` |
| Forgetful U | The existing `CategoryTheory.Endofunctor.IsoAlgebra.forget F`, the full-subcategory inclusion followed by `Algebra.forget F` |
| Ordinary derived categories | `DerivedCategory C`, `DerivedCategory (IsoAlgebra F)`, with independent `[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{wF} (IsoAlgebra F)]` localization choices |
| Structure induced by a representing complex | `((Functor.mapDerivedCategoryCompIso (forget F) F).symm ≪≫ Functor.mapDerivedCategoryNatIso (F := forget F ⋙ F) (G := forget F) (NatIso.ofComponents (fun (K : IsoAlgebra F) ↦ K.str) (fun f ↦ f.hom.h))).hom.app M`; its existing definition localizes the natural isomorphism with components `K.str` and uses the canonical exact-functor composition comparison |
| N with bounded cohomology | `(N : DerivedCategory C) (hN : DerivedCategory.TStructure.t.bounded N)`; the canonical bounded predicate is the intersection of the bounded-below and bounded-above predicates |
| Prescribed invertible v : D(P)N → N | `(vN : F.mapDerivedCategory.obj N ≅ N)` |
| Existence of M and e : D(U)M ≅ N | `∃ (M : DerivedCategory (IsoAlgebra F)) (e : (forget F).mapDerivedCategory.obj M ≅ N), ...` |
| e θ_M = v D(P)(e) | The preceding canonical structure component composed with `e.hom` equals `F.mapDerivedCategory.map e.hom ≫ vN.hom`; Lean composition reads from left to right |
| Same interval of bounded cohomology | For every `a b : ℤ`, vanishing of every `H^i(N)` with `i < a ∨ b < i` implies the identical vanishing for `H^i(M)` in the fixed-pair category |
| Any isomorphism-invariant class S | `∀ S : ObjectProperty C, S.IsClosedUnderIsomorphisms → ...`; this quantifier is inside the realization's existential, so the same M works for every S |
| All H^i(N) in S imply all underlying H^i(M) in S | `(∀ i : ℤ, S ((DerivedCategory.homologyFunctor C i).obj N)) → ∀ i : ℤ, S ((forget F).obj ((DerivedCategory.homologyFunctor (IsoAlgebra F) i).obj M))` |
| No functorial choice or equivalence asserted | The result is purely existential; neither a realization functor nor an equivalence of categories is introduced |

Dependency declarations read and used:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, including its docstring,
  the class fields, and `IsGrothendieckAbelian.hasColimits`. Its recorded Mathlib match
  explicitly specializes the Grothendieck size to the morphism universe `v`.
- `def-weil-endofunctor-fixed-pair-category`: its recorded `Endofunctor.Algebra`
  specialization and full-subcategory construction. Read `Algebra`, `Algebra.Hom`,
  `Algebra.forget` and `ObjectProperty.ι`, and the exact existing project implementation
  `IsoAlgebra`, `IsoAlgebra.str`, `IsoAlgebra.forget` in
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`. The latter is precisely
  the full-subcategory expression specified in the Mathlib match, with no new notion
  or interface repair needed. The abelian and exact-forgetting instances are in
  `WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor` and are publicly
  exposed by the imported existing modules.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, and
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and
  `DerivedCategory.homologyFunctor` with its factorization in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The independent
  localization universes impose no small-Hom assumption on the derived categories.
- `Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` give the
  canonical action directly. Its natural isomorphism has components `K.str` and
  naturality `f.hom.h`. This is the defining term of the existing
  `cyclicDerivedStructure`, inlined as expressly permitted by return H2. The
  exact-sequence theorem and its module are no longer dependencies.
- The proof imports include every recorded module of the original proof dependencies:
  `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`,
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
  `Mathlib.CategoryTheory.Adjunction.Limits`,
  `Mathlib.CategoryTheory.Limits.HasLimits`, and
  `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`.
  Statement dependencies already expose the remaining repeated definition dependencies.

Source and edge-case audit: read the current blueprint's
`cor-coef-verdier-weil-equivariance.proof.md`, including the final exceptional-adjunction
sentence, and Q76's full seven-step proof and accepted review. The blueprint does not
itself prove this realization, which the node honestly attributes to an agent construction.
The theorem docstring includes all seven steps, the initial-leg inverse check, the
cohomology calculation, and the exact equivariance cancellation.

Before writing, checked N = 0 (including a nonzero acyclic representing complex), F = id
with either identity or a nontrivial automorphism such as -1 on Z[0], and a nonidentity
autoequivalence such as swapping the two factors of Ab × Ab. No strict inverse of the
quasi-isomorphism representing v is assumed. The interval clause covers a = b, arbitrary
integer endpoints, and a > b (an empty interval forces N and M acyclic). S is arbitrary:
the empty class gives a conditional statement with an unsatisfied premise, the total class
works, and the zero-object class gives the acyclic case. There is no colimit-stability
assumption on S. The same M and e satisfy all intervals and all classes simultaneously.
Object, morphism and both derived localization universes are explicit and independent.

Searches actually run through `msearch.py` on 2026-10-22 (raw records in `searches.jsonl`):

- LeanFinder: `Realizing an invertible derived action of an exact autoequivalence by a
  complex of fixed pairs`. Eight hits, including `Equivalence.mapHomologicalComplex`
  and unit isomorphisms, and differential-object equivalences; none realizes a
  prescribed derived twisted action in D(A^P).
- Loogle: `Functor.mapDerivedCategory, Endofunctor.Algebra`. Unknown identifier
  `Functor.mapDerivedCategory`; this query did not establish absence of a theorem.
- Loogle: `"DerivedCategory", "Action"`. Two calculus-of-fractions instances,
  neither an action realization.
- Mathlib grep: `fixedPair|FixedPair|strictif|rectif` in `Algebra/Homology/`: zero hits.
- LeanSearch: `A bounded derived object with an invertible action of an exact
  autoequivalence is realized by a complex of fixed pairs`. Eight hits; bounded
  representatives, single-object fixed points and opposite-complex equivalences,
  none states the realization. In particular
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` produces an underlying complex
  with cohomological bounds, without the strict fixed-pair action.
- `rg` in `lean/WeilConjectures` for the node id: zero hits. Concept searches in
  `lean/WeilConjectures` and `lean/Sheaf` for fixed pairs, cyclic realizations,
  strictification and rectification found the existing `IsoAlgebra` implementation
  and `cyclicDerivedStructure`; the canonical term underlying the latter is inlined. Other strictification results
  concern site systems or squares, rather than the current essential-surjectivity claim.

No statement dispute, source correction, new node or dependency module is needed.

Validation: prescribed `scompile.py N9 lem-sf-cyclic-derived-action-realization ...`
compiled both its sandbox probe and its actual library module cleanly (6.2 s and 7.5 s).
No compiler warning or error was reported. All file mutations are confined to this
item's sandbox, and no repository git command or global build was run.

## Second reading by N9

This is a second pass by the dispatched worker, not an independent agent review:
the dispatch explicitly prohibits starting agents, and the maintainer independently
reviews the delivery. Re-read the original node and final source side by side.

The equation has source D(P)D(U)M and target N on both sides; `e.hom` follows
`theta_M` on the left, while `vN.hom` follows `D(P)(e.hom)` on the right.
The action is the existing localized structure, never an arbitrary isomorphism.
M belongs to the native derived category of fixed pairs, rather than a fixed-pair
category formed after deriving. In particular, no false derived-equivalence or
derived-faithfulness assertion is used.

The interval conclusion is about H^i(M) in the fixed-pair category, and the class
conclusion applies U to this same H^i(M). These are exactly the two different
cohomology clauses in the node. Neither clause has been silently replaced by a
statement only about D(U)M. Quantifiers for a, b and S occur after the existential,
and impose no additional restrictions on the input N or v. The boundedness
hypothesis remains even though the accepted sequential-colimit construction is
more general. No mismatch was found and no statement correction was made.

The module contains only its named theorem, with explicit universes and variables,
`autoImplicit false`, the required module-mode header, public statement imports,
private proof imports and its seven-step proof docstring. No new definition of fixed
pairs, forgetting, the derived action, or cohomology has been written.

## Repair of return H2

The returned immutable head was `dd74661e27fe`. Its sole H2 fault was citing
`lem-sf-cyclic-derived-hom-exact-sequence` just for a plain definition in that
module. The initial saved-packet dry run passed at `5c17718744d`, but that mechanical
pass does not repair H2. Followed the return's explicit second option: inline
`(Functor.mapDerivedCategoryCompIso (forget F) F).symm ≪≫
Functor.mapDerivedCategoryNatIso (F := forget F ⋙ F) (G := forget F) (NatIso.ofComponents (fun K ↦ K.str) (fun f ↦ f.hom.h))`
in the theorem signature and restore the base's original three `stmt_deps`.
Removed the Hom-exact-sequence import and publicly imported only the existing
construction APIs and type structure needed by the statement. No theorem is used
as the source of this structure. No definition was moved, copied or introduced.
The `lean.statement` is regenerated verbatim from the repaired file. Compared the
saved packet against current main: all non-`lean` fields now equal current main,
including `stmt_deps`; the seven proof steps and natural-language statement remain
verbatim. The theorem is definitionally the same statement as the returned version.
The preceding clause and edge-case audit therefore continues to apply. This
second reading was performed by the dispatched worker, with no other agents.

The inlined natural isomorphism explicitly names its source `forget F ⋙ F` and
target `forget F`; these annotations resolve elaboration without changing data.

Repair validation: `scompile.py` compiled the sandbox probe (8.5 s) and the
actual library module (6.6 s), with no errors or warnings. The final self-check
finds no lines over 100 columns, confirms `lean.statement` verbatim, and confirms
that only `lean` differs from current main. All original `stmt_deps` are restored.
