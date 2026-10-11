## Worker report

The module `Sheaf.AlgebraicGeometry.SimplicialHomObjectExists` states
`AlgebraicGeometry.Scheme.exists_simplicial_hom_object`. Its sole proof is `sorry`.
No definition, auxiliary node, dependency repair, or statement correction is needed.
The node copy changes only `lean`.

Hypotheses and clauses, in the order of the node:

- A scheme X: `(X : Scheme.{u})`, without any finiteness, nonemptiness, or
  separation condition on X.
- A simplicial object K in SR(X):
  `(K : SimplicialObject (FormalCoproduct.{w} X.Etale))`. This is exactly the
  category used by the recorded semi-representable-object dependency.
- A simplicial set S: `(S : SSet.{t})`, Mathlib's functor from the opposite
  simplex category to types.
- Finitely many nondegenerate simplices: `[S.Finite]`, whose defining field is
  `Finite S.N`, the type of all nondegenerate simplices in all degrees.
- Each S_n finite: `hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌))`.
  This explicit clause is also derivable from S.Finite but retained as in the node.
- Each S_n nonempty: `hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))`.
- An object H in SR(X): `∃ (H : FormalCoproduct.{w} X.Etale)`.
- Maps u_s in every degree: the next existential binder
  `u : ∀ n, S.obj (op ⦋n⦌) → (H ⟶ K.obj (op ⦋n⦌))`.
- Compatibility for every monotone φ:[m]→[n] and every s in S_n:
  `u n s ≫ K.map φ.op = u m (S.map φ.op s)`.
  Lean's composition order is left to right, so this is K(φ) ∘ u_s = u_{S(φ)s}.
- Every object W and every family f_s: the universal W and f binders in the
  second conjunct range over precisely the same category and all degrees.
- Compatibility of f: the implication's antecedent is
  `f n s ≫ K.map φ.op = f m (S.map φ.op s)` for all m,n,φ,s.
- A unique map g:W→H factoring the family: `∃! g : W ⟶ H`, with predicate
  `∀ n s, g ≫ u n s = f n s`. This is f_s = u_s ∘ g with equality reversed,
  and uniqueness concerns the same all-degree factorization predicate.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`: the recorded category
  `CategoryTheory.Limits.FormalCoproduct.{w} X.Etale` and its finite-limit instance
  `AlgebraicGeometry.Scheme.semiRepresentableHasFiniteLimits`. Read the full module,
  including points, coverings, matching objects and hypercovers. The theorem needs
  only its category, so no extra hypercover hypothesis appears.
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`: `SSet`;
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`: `SSet.degenerate` and
  `SSet.nonDegenerate`; `Mathlib.AlgebraicTopology.SimplicialSet.Finite`:
  `SSet.Finite`, its field, and its degreewise finiteness instance. These supply
  the simplicial-set dependency's mathlib_match; no missing lean record is a fault.
- `FormalCoproduct` and its morphisms were read in
  `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`.

Edge cases: degree zero is included by the ℕ binders; φ includes all maps,
including identity, face, and degeneracy maps. The empty simplicial set fails
hnonempty, exactly as in the node. A point and a finite discrete simplicial set
satisfy the hypotheses and recover K_0 and finite products respectively. Empty
formal families and the empty scheme remain allowed. The family-index universe w,
scheme universe u, and simplex universe t are independent; the finite truncation
requires only finite limits, so no universe bound or extra smallness assumption
is imposed. All variables and universes are explicit. No false or untypable
statement was found.

Searches for an existing statement:

- msearch.py leanfinder: "object representing compatible maps from a finite
  simplicial set to a simplicial object in a category with finite limits".
  Eight hits: standard simplex, its finite presentability, SSet.cosk, SSet,
  simplicial nerve, nerve, SSet.hasLimits, truncated simplicial objects. None
  states this representability result in SR(X).
- msearch.py loogle: "SSet.Finite, SimplicialObject". Zero hits; service reports
  unknown identifier SimplicialObject.
- msearch.py grep: "cotensor|homFromSSet|simplicial.*[Hh]om" in CategoryTheory.
  Only an unrelated oplax monoidal cotensorator hit.
- rg over WeilConjectures and lean/Sheaf:
  "homFromSSet|cotensor|simplicial_hom_object|017K|lem-weil-pbc-simplicial-hom-object-exists".
  Results: unrelated module-pullback cotensorators and the already recorded finite
  initial indexing theorem; no existing statement of this node.
- tools/lean_names_upstream.py show for the item: no matching declaration.

Source check: the local Stacks TeX is absent on this machine, so read the primary
source pages https://stacks.math.columbia.edu/tag/017J and
https://stacks.math.columbia.edu/tag/017K. The compatible-family description and
finite-limit representability agree with the node. Read the landed
SimplicialIndexFiniteInitial module to confirm the orientation of the indexing
category in the natural-language proof. The module docstring gives all three
node proof steps, names their dependencies, and leaves them to stage 3.

## Second reading by V1

Independent review of the node copy and the complete delivered module, followed by
opening both statement-dependency nodes and their recorded declarations. No mathematical
mismatch found; the Lean module and node record are unchanged. Added this review only.

Source reading: fetched the primary Stacks TeX into this item's scratchpad because
`literature/stacks-project/` is absent here. Read `simplicial.tex`, section
`section-hom-from-simplicial-sets`, including the preceding definition and the statements
and proofs of `lemma-exists-hom-0-from-simplicial-set` (017J) and
`lemma-exists-hom-0-from-simplicial-set-finite` (017K). Also read `hypercovering.tex`,
`definition-SR` (01G0) and `lemma-coprod-prod-SR` (01G2).
Primary source links: https://stacks.math.columbia.edu/tag/017J,
https://stacks.math.columbia.edu/tag/017K, https://stacks.math.columbia.edu/tag/01G2.
017K assumes binary coproducts and finite limits, finite nonempty levels, and eventual
degeneracy. With finite levels, eventual degeneracy is equivalent to finitely many
nondegenerate simplices: only finitely many finite levels can contribute; conversely
a finite collection has bounded degrees. These category structures are provided by
formal coproducts of the small étale category, without a condition on the base scheme.
017J's countable-limit assumption is replaced by finite limits in 017K and must not
be added to this statement.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. Scheme X: `(X : Scheme.{u})`. No field, characteristic, finiteness,
   separation or nonemptiness hypothesis is present.
2. Simplicial object K of SR(X):
   `(K : SimplicialObject (FormalCoproduct.{w} X.Etale))`.
   The semi-representable dependency explicitly uses this category. Opened
   `SemiRepresentableObject.lean`, particularly `semiRepresentableHasFiniteLimits`.
   Opened Mathlib `FormalCoproducts/Basic.lean`: objects have an index type `I`
   and components `obj`; morphisms have an index map `f` and component maps `φ`,
   with exactly the node's composition. Opened `Morphisms/Etale.lean`:
   `Scheme.Etale` is `MorphismProperty.Over @Etale ⊤ X`, and its forgetful functor
   to `Over X` is fully faithful. Thus these are all étale X-schemes and all
   X-morphisms, without a finite-type or affine specialization.
3. Simplicial set S: `(S : SSet.{t})`. The dependency's Mathlib match is used.
   Opened `SimplicialSet/Basic.lean`: `SSet` is `SimplicialObject (Type t)`.
4. Finite levels: `hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌))`.
   Retained the node's explicit clause even though `[S.Finite]` implies it.
5. Nonempty levels: `hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))`.
6. Finitely many nondegenerate simplices: `[S.Finite]`. Opened `Finite.lean`,
   `Degenerate.lean` and `NonDegenerateSimplices.lean`: the class field is
   `Finite S.N`, and N records a degree and a nondegenerate simplex; degeneracy
   is the image of an operator to a strictly lower degree, as in the dependency.
7. Representing object H in SR(X): `∃ (H : FormalCoproduct.{w} X.Etale)`.
8. All-degree family u_s:H→K_n: existential binder
   `u : ∀ (n : ℕ), S.obj (op ⦋n⦌) → (H ⟶ K.obj (op ⦋n⦌))`.
9. Compatibility for every monotone φ:[m]→[n] and s∈S_n:
   `∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
   u n s ≫ K.map φ.op = u m (S.map φ.op s)`.
   All simplex-category morphisms are covered; both contravariant operators
   have the correct direction.
10. Every W in SR(X) and every all-degree family f_s: universal W and f binders
    in the second conjunct have precisely the corresponding types from 7 and 8.
11. Compatibility of f_s: the implication's antecedent repeats clause 9 with f.
    No assumption on W or f is added.
12. Unique g:W→H factoring every f_s:
    `∃! g : W ⟶ H, ∀ (n : ℕ) (s : S.obj (op ⦋n⦌)), g ≫ u n s = f n s`.
    Lean composes left to right; reversing the node's equality changes nothing.
    Uniqueness concerns the full family. H and u are chosen before W and f,
    exactly as required by the representability universal property.

Edge cases: n=0 and all identity, face, degeneracy and other monotone maps are
included. The empty simplicial set is excluded precisely by hnonempty. For a
constant one-point S the result represents evaluation at degree zero; a finite
nonempty constant set gives a finite product of K_0. Empty index families for
K, H or W are allowed by FormalCoproduct; no nonemptiness hypothesis is imposed
on them or on X. There is no additive zero object in this category; its empty
formal family (initial object) is allowed. Characteristic is unrestricted.
Universes u (schemes), w (formal-family indices), t (simplices) are separately
bound; finiteness allows reindexing the finite truncation in any universe, so
there is no size restriction linking them. No unbound variable or universe.

Independent searches, with queries different from the first reader's:

- msearch leanfinder: "finite weighted limit of a simplicial diagram representing
  compatible simplex indexed morphisms". Eight hits, including Čech nerve,
  simplicial-object limits and standard simplices. None proves this existence
  theorem using only finite limits and finite nondegenerate simplices.
- msearch loogle: "SSet.Finite". Twelve hits: the finiteness class, degreewise
  finiteness, dimension bound and preservation under monos/epis/isomorphisms.
  No representing-object existence theorem.
- msearch grep: "weighted.*[Ll]imit|finite.*simplicial.*[Hh]om|represent.*compatible".
  Weighted-limit definitions and an unrelated site lemma.
- Direct rg across Mathlib, WeilConjectures and repository lean/Sheaf:
  "weightedLimit|WeightedLimit|simplicial.*represent|exists.*simplicial.*hom|
  Hom.*simplicial set|finite.*cotensor". Inspected the weighted-limit module:
  `HasWeightedLimit` is a predicate assuming existence, and its cone/lift API
  does not prove existence for this finite simplicial weight. Other hits were
  matching-object comparisons, standard-simplex representability and unrelated
  homology. No duplicate statement or definition is needed.

No new nodes, dependency modules or statement correction are present, so H12,
H13 and correction-citer checks do not apply. The single theorem has proof
`:= sorry`; there are no definitions or additional proofs in the delivery.
Both imports are used. Header, namespace, line lengths and source/blueprint
markers satisfy the conventions. Its docstring carries the node's three proof
steps with their dependencies; the opposite indexing category agrees with the
opened `AlgebraicTopology/SimplicialIndexFiniteInitial.lean` declaration and its
limit-comparison clause. Checked the node's lean.statement against the literal
signature from `theorem` through the conclusion: verbatim equal.

Validation: scompile.py on the absolute sandbox module path succeeded on the
server in 2.0 seconds, with no errors or warnings. An initial relative-path
invocation failed locally to locate the file; corrected to the sandbox path.
