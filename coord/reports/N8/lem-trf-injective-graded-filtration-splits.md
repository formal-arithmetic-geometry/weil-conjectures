## Worker report

Repair of the return on immutable head e709bfbb47b8. The sandbox provided to this
session contained only .brief2 through .brief5, with no retained node, module or
report. I read the return in coord/returns/N8.md and reconstructed the packet from
the current shared node. The delivery wrapper rebases the packet on current
newtargets-dag. No direct Git commands or shared-source writes were used.

The new module `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits` states
`CategoryTheory.FilteredObject.injective_graded_filtration_splits`. It contains
one theorem with `sorry`, no new definitions, and no other postponed facts. Its
module and declaration docstrings cite Stacks Tag 05TP and the item blueprint id;
the theorem docstring reproduces all six steps of the node's descending induction.
The source was read at literature/stacks-project/derived.tex,
`lemma-filtered-injective`, including its displayed split filtration and proof.
The item mathematics is unchanged and no statement correction is needed.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| An abelian category A | `{C : Type u} [Category.{v} C] [Abelian C]`; both universes explicitly bound |
| An object I with a decreasing filtration F | `(X : FilteredObject C)`; `X.obj` is I and `X.filtration : DecreasingFiltration X.obj` |
| Integers a ≤ b | `(a b : ℤ) (hab : a ≤ b)` |
| F^a I = I | `ha : X.filtration.F a = ⊤` in `Subobject X.obj` |
| F^(b+1) I = 0 | `hb : X.filtration.F (b + 1) = ⊥` |
| gr^n I is injective for every a ≤ n ≤ b | `hgr : ∀ n : Set.Icc a b, Injective (X.filtration.gradedPiece n.1)` |
| Objects J_n on exactly that interval | `∃ J : Set.Icc a b → C` |
| Each J_n is injective in the extension-property sense | `∀ n : Set.Icc a b, Injective (J n)` |
| Isomorphisms J_n ≅ gr^n I | `∀ n : Set.Icc a b, Nonempty (J n ≅ X.filtration.gradedPiece n.1)` |
| An isomorphism θ : I ≅ the finite biproduct of J_n | `∃ θ : X.obj ≅ @biproduct _ C _ _ J (HasBiproduct.of_hasProduct J)` |
| θ identifies F^p with the embedded tail for every integer p | `∀ p : ℤ, (Subobject.map θ.hom).obj (X.filtration.F p) = imageSubobject (@biproduct.fromSubtype ... (fun n : Set.Icc a b ↦ p ≤ n.1) ...)` |

The `Nonempty` isomorphism clause asserts existence at every index; classical
choice equivalently supplies a whole family of these isomorphisms. It does not
replace the explicitly existentially quantified θ, which must satisfy every
subobject equality simultaneously. `biproduct.fromSubtype` is Mathlib's actual
canonical inclusion. Its composite with `biproduct.toSubtype` is the identity,
so its image subobject is precisely the tail sub-biproduct, including empty tails.

Dependency declarations read and used:

- `def-sp-abelian`: Mathlib.CategoryTheory.Abelian.Basic,
  `CategoryTheory.Abelian`; finite products and the other abelian structure are
  the recorded Mathlib interface.
- `def-sp-filtration`: the recorded
  WeilConjectures.CategoryTheory.Abelian.Filtration,
  `CategoryTheory.DecreasingFiltration`, with fields `F` and `F_succ_le` and
  `gr n = cokernel (Subobject.ofLE _ _ (F_succ_le n))`. Its source was obtained
  through `scompile.py --source`, since the older local source lacks the file.
  `Sheaf.CategoryTheory.Filtration` publicly imports that same declaration and
  provides `DecreasingFiltration.gradedPiece` as an abbreviation of `gr`.
  Its upstream import WeilConjectures.CategoryTheory.Filtration supplies the
  existing `CategoryTheory.FilteredObject` with fields `obj` and `filtration`;
  this source was also read via `scompile.py --source`.
- `def-sp-injective-resolutions`, injective-object clause:
  Mathlib.CategoryTheory.Preadditive.Injective.Basic,
  `CategoryTheory.Injective`, whose field `factors` extends any morphism into
  the object along any monomorphism. The node's recorded
  `CategoryTheory.InjectiveResolution` in the Resolution module was read too;
  this item uses only its explicitly recorded injective-object clause.
- Proof dependencies: `CategoryTheory.Injective.instPiObj` in
  Mathlib.CategoryTheory.Preadditive.Injective.Basic, and
  `CategoryTheory.ShortComplex.ShortExact.splittingOfInjective` in
  Mathlib.Algebra.Homology.ShortComplex.ShortExact. Their complete relevant
  signatures and the splitting identities were read. The former module is
  public because the statement itself uses Injective; the latter is a
  proof-only import.
- Mathlib.CategoryTheory.Preadditive.Biproducts,
  `CategoryTheory.Limits.HasBiproduct.of_hasProduct`, is available through the
  abelian dependency. Its explicit arguments construct each finite biproduct
  from the finite products already supplied by Abelian. No extra instance
  hypothesis, local instance, alternative filtration or helper definition is
  introduced. Mathlib.Data.Int.Interval supplies the finite interval instances.

Edge cases checked before writing and again in the second pass: zero I and zero
summands; a = b (one summand); negative a and b; p < a (whole biproduct); p = a;
p = b; p = b + 1 (empty tail); p > b + 1 (empty tail). Decreasingness and the
endpoint equalities force exactly the corresponding top/bottom filtration
subobjects. No injectivity outside [a,b] or EnoughInjectives assumption appears.
The node explicitly assumes a ≤ b, so the whole indexing interval is not empty;
its tail is allowed to be empty. Independent object/morphism universes are kept.

Searches made with msearch.py under N8 and this item:

- LeanFinder: "A finite decreasing filtration in an abelian category whose graded
  pieces are injective splits as the finite biproduct of its graded pieces
  compatibly with every filtration subobject". Eight hits, including
  instHasInjectiveDimensionLTBiprod, DoldKan.Γ₀.splitting,
  IsModuleFiltration.mk_int, and Grothendieck-category declarations; none state
  the finite compatible splitting.
- Loogle: `CategoryTheory.FilteredObject, CategoryTheory.Injective`: zero hits.
- Mathlib grep: `(filtration|filtered).{0,50}(split|biproduct)|injective.{0,50}(quotient|graded)`
  restricted to CategoryTheory: zero hits.
- LeanSearch: "A finite filtration in an abelian category with injective graded
  pieces admits a splitting preserving all filtration subobjects": eight hits,
  notably ShortComplex.ShortExact.splittingOfInjective and Splitting. These split
  one short exact sequence, not the given entire filtration compatibly.
- Direct rg with the same filtration/splitting expression in the named upstream
  WeilConjectures tree found only unrelated ring, field, torsor and sheaf facts.
  Direct rg for the item id in that tree found no declaration.
- Direct rg in shared lean/Sheaf found the parent
  EnoughStrictFilteredInjectives referring to this item as its proof input,
  but no statement of this item. Filtration.lean supplies the existing notions.
- Direct rg for `injective_graded_filtration_splits|InjectiveGradedFiltrationSplits`
  in dag/lean_names_upstream.json, shared lean/Sheaf and upstream WeilConjectures
  found no collision.

Return points repaired:

- H1: the packet now has the owned Lean module and the required Second reading
  section, and states the actual item rather than claiming an existing match.
- H2: the node copy is freshly copied from the shared current node, with only
  `lean` added. In particular `split_report.summary` and all other non-lean fields
  are exactly preserved. The record contains the exact multiline signature,
  module, full declaration, file, branch newtargets-dag, by N8, UTC date and
  existing false.
- H11: the second pass below reads every hypothesis and conclusion against the
  actual node and actual compiled file.

Validation: the prescribed scompile.py invocation on the delivered module passed
on the server, with both sandbox and library compile results at 1.5 seconds and
no diagnostics. All variables/universes are explicitly bound, autoImplicit is
false, and every Lean line is at most 100 characters. There is no statement
dispute, new node, dependency repair or source discrepancy.

## Second reading by N8

I reopened the current node, the finished Lean file, and the Tag 05TP text for a
separate second pass after compilation. This is the dispatcher's worker
self-review; the brief expressly prohibits starting another agent, and the
maintainer performs the independent review. I do not claim a separate reviewer.

1. The node says an arbitrary abelian category. The declaration binds C, both
   universes, Category and Abelian only. The explicit finite-biproduct existence
   arguments are consequences of Abelian's finite products, not additional
   assumptions. There is no enough-injectives or Grothendieck hypothesis.
2. The node's pair (I,F) is exactly FilteredObject C: obj is I and filtration is
   the recorded upstream DecreasingFiltration. The code uses F directly and the
   existing gradedPiece abbreviation, whose cokernel is F^n/F^(n+1). No second
   notion of filtration or graded quotient has been made.
3. The two integer endpoints and a ≤ b are bound. The two endpoint hypotheses
   are top at a and bottom at b + 1, not at b. Thus one-step and zero cases are
   allowed and no shift or extra F^0 assumption appears.
4. The injectivity hypothesis quantifies over Set.Icc a b, so it includes both
   endpoints and nothing outside them. Injective is the same extension-property
   class identified by the dependency node, rather than existence of an
   injective resolution.
5. The conclusion quantifies J over exactly the same interval; its first
   conjunct supplies every summand's injectivity. Its second conjunct supplies
   an isomorphism from each J n to precisely gr^n I, with no missing endpoint.
   Objectwise Nonempty is equivalent to the requested family of witnesses.
6. The third conjunct gives an actual isomorphism from X.obj to the full finite
   biproduct of these very J n. It is outside the quantifier over p: one fixed
   θ works for all filtration steps, as required.
7. The final equality maps the original subobject along θ.hom and compares it
   with the image of the actual canonical subtype inclusion. The predicate is
   p ≤ n.1, so it selects the tail n ≥ p rather than the complementary head.
   Because fromSubtype has the canonical retraction toSubtype, its image is
   the tail sub-biproduct itself, not an arbitrary object isomorphic to it.
8. The final p ranges over all ℤ, with no interval restriction. I separately
   checked p below a, at a, at b, at b + 1, and above b + 1, including negative
   bounds, zero objects and zero summands. Top and bottom agree in these cases
   exactly as in Step 6 of the node's proof.
9. I compared the six numbered docstring steps to the six node proof entries:
   choice of J and induction invariant; injectivity of the previous tail;
   injective-kernel splitting; inverse block maps; preservation of all
   inclusions; endpoint and exterior-index cases. Both named non-elementary
   proof dependencies are imported, with the splitting module proof-only.
10. I compared the JSON copy with the current shared node: deleting lean gives
    identical parsed records, including the restored split_report.summary.
    The exact signature in lean.statement comes from the finished file.

The returned delivery's missing statement, missing binding, unauthorized summary
change and absent clause-by-clause second reading are repaired. This pass found
no further mathematical mismatch and required no statement changes.
