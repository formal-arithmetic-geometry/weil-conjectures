## Worker report

The module `lean/Sheaf/CategoryTheory/Triangulated/TriangleMorphismExtension.lean`
states `CategoryTheory.Pretriangulated.triangle_morphism_extension`, with one
`sorry` and no new definitions. The node is unchanged except for `lean`.

Source read: BBD, *Faisceaux pervers*, Proposition 1.1.9 and Corollaire
1.1.10 (ii), printed pp. 23–24, PDF pages 24–25. The literature PDF was not
present on this machine, so I obtained the Numdam scan in the sandbox from
https://www.numdam.org/item/AST_1982__100__1_0.pdf and read both page images.
The source writes Hom^{-1}(X,Z'); shifting identifies this with Hom(X[1],Z').
No statement correction, disputed statement, or missing notion was found.

Hypotheses and clauses:

- The pre-triangulated category is `{C : Type u} [Category.{v} C]`,
  `[Preadditive C] [HasZeroObject C] [HasShift C ℤ]`, additive integer shifts,
  and `[Pretriangulated C]`. This is the dependency's recorded Mathlib encoding:
  zero objects and TR1–TR3 give finite biproducts, and integer shifts are
  autoequivalences. No octahedral axiom is imposed.
- The two sextuples are `T T' : Triangle C`; their objects are `obj₁`, `obj₂`,
  `obj₃`, and their arrows are `mor₁`, `mor₂`, `mor₃`. Distinguishedness is
  exactly `hT : T ∈ distTriang C` and `hT' : T' ∈ distTriang C`.
- The given middle map is `g : T.obj₂ ⟶ T'.obj₂`, with no extra condition.
- Clause (1a) is `T.mor₁ ≫ g ≫ T'.mor₂ = 0`, i.e. v' g u = 0.
  Lean composition runs from left to right.
- Clause (1b) is `∃ f, f ≫ T'.mor₁ = T.mor₁ ≫ g`.
- Clause (1b') is `∃ h, T.mor₂ ≫ h = g ≫ T'.mor₂`.
- Clause (1c) is `∃ τ : T ⟶ T', τ.hom₂ = g`. Its first and last
  components supply the existential f and h, and the triangle morphism type
  includes all three commutative squares. The first conjunct contains three
  separate iff statements, comparing (a) to (b), (b'), and (c); this says all
  four conditions are equivalent, without assuming that any condition holds.
- Clause (2)'s extra vanishing is the antecedent
  `Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)`. A Hom group has zero, so
  Subsingleton says exactly that every map is zero. Two universally quantified
  first-square solutions `f₁ f₂` are equal; two universally quantified
  second-square solutions `h₁ h₂` are equal. These assertions say at most one
  solution, with existence conditional on (1), exactly as in the node.
- The consequence in (2) quantifies over every pair `f h` satisfying those
  squares and gives `τ` with components `f,g,h`. It also spells out
  `T.mor₃ ≫ f⟦(1 : ℤ)⟧' = h ≫ T'.mor₃`, i.e. d' h = f[1] d,
  the third square explicitly stated by the node.
- Clause (3) assumes `Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃)` and says
  every `x` with `Triangle.mk T.mor₁ T.mor₂ x ∈ distTriang C` equals
  `T.mor₃`. Existence of that third arrow is already `hT`, since `T` is
  precisely the triangle with its own three arrows. Thus this is the full
  assertion that d is the unique such x, not an existence-free weakening.

Dependency declarations read in full:

- `def-weil-triangulated-category`: Mathlib leaf, no `lean` record required.
  `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, including its
  docstring and TR1–TR3 fields, and `distTriang` notation. The node also
  defines triangulated categories and exact functors, which this statement
  does not use; it needs only its usable pre-triangulated clause.
- `def-weil-pbc-triangles-with-shift`: Mathlib leaf,
  `CategoryTheory.Pretriangulated.Triangle` in
  `Mathlib.CategoryTheory.Triangulated.Basic`, with `Triangle.mk`,
  `TriangleMorphism` and `triangleCategory`. Read their signatures and
  docstrings. These are imported transitively through Pretriangulated.

Edge cases checked: zero triangles and the zero category are included;
Hom vanishing then makes both uniqueness assertions immediate, and the only
third arrow is zero. Nonzero Hom groups impose no uniqueness condition.
For g with nonzero obstruction all four conditions in (1) are false, while
(2) states uniqueness only of maps satisfying the square equations. T = T'
and g = identity is allowed and is exactly the case used for (3).
Objects and Hom universes are independent (`u v`); no size restriction,
nonzero-object condition, t-structure, or full triangulated structure is added.

Searches actually run:

- `msearch.py ... leanfinder`: "A middle map between distinguished triangles
  extends if its composite with the first and second arrows is zero, with
  uniqueness when Hom(X[1], Z') vanishes". Eight hits: t-structure
  `triangle_map_ext`, TR3 completion lemmas, and exact Hom sequences. None
  states all three parts without a t-structure hypothesis.
- `msearch.py ... loogle`: "CategoryTheory.Pretriangulated.Triangle,
  CategoryTheory.Pretriangulated.TriangleMorphism". Twelve hits: the
  triangle morphism type and its identity, composition, and projections.
  These confirm the existing definition, not the theorem.
- `msearch.py ... grep`: "triangleHom_ext|exists_triangleHom|unique.*mor₃|
  cancel_mor.*subsingleton" in CategoryTheory/Triangulated. Zero Mathlib hits.
- `msearch.py ... leansearch`: "BBD distinguished triangle morphism middle
  component extension unique Hom vanishing". Service unavailable (HTTP
  Internal Server Error); not recorded as a negative search result.
- `rg` on the source project's WeilConjectures for triangle/morphism
  extension found
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
  Read `exists_triangleHom_of_comp_eq_zero`, `triangleHom_ext_of_subsingleton`,
  `Triangle.cancel_mor₁_of_subsingleton` and `Triangle.cancel_mor₂_of_subsingleton`
  with docstrings and full signatures. They supply narrower existence and
  cancellation results, but no declaration states the equivalences,
  arbitrary compatible-pair consequence, and final-arrow uniqueness together.
  Therefore no exact existing declaration can represent this node.
- `rg` for the item id and proposed declaration name in upstream names,
  source WeilConjectures, Mathlib, and project `lean/Sheaf`: no exact declaration.
  Concept search in `lean/Sheaf` found other triangle statements (denominator
  completion, refinements, derived triangles), none equal to the item.

Validation: the server single-file compile is clean (only the intended theorem
proof is `sorry`). The module docstring and theorem docstring cite the source
and blueprint; the theorem docstring carries all nine proof steps with their
DAG dependencies. No proof was attempted in stage 2.

## Second reading by R1

Independent reading of the node, its two dependency nodes, the delivered module,
Mathlib declarations, and BBD scan pages 24–25 (printed 23–24). Also read BBD
1.1.1: the ambient category is additive, with an autoequivalence shift; its
integer powers define Hom^n. BBD assumes a triangulated category throughout,
but the proof of 1.1.9 and 1.1.10(ii) uses only exact Hom sequences and triangle
completion. Those follow from TR1–TR3, so the node's pre-triangulated formulation
is valid without adding the octahedral axiom. Hom^{-1}(X,Z') is Hom(X,Z'[-1]),
identified by the shift equivalence with Hom(X[1],Z').

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- Ambient pre-triangulated category T: `{C : Type u} [Category.{v} C]`,
  `[Preadditive C] [HasZeroObject C] [HasShift C ℤ]`, additive integer shifts,
  and `[Pretriangulated C]`. Opened `def-weil-triangulated-category` and
  Mathlib's `CategoryTheory.Pretriangulated`: its fields are precisely
  isomorphism closure, contractible triangles, cone existence, rotation, and
  first-square completion. Binary biproducts are supplied by this structure,
  so no additive-category hypothesis is missing. No `IsTriangulated` is added.
- Objects X,Y,Z,X',Y',Z' and arrows u,v,d,u',v',d': `T T' : Triangle C`,
  with `obj₁`, `obj₂`, `obj₃`, `mor₁`, `mor₂`, `mor₃`. Opened
  `def-weil-pbc-triangles-with-shift` and Mathlib's `Triangle`, `Triangle.mk`,
  `TriangleMorphism`, and `triangleCategory`. The third arrow has target
  `obj₁⟦(1 : ℤ)⟧`; morphisms have exactly the three required squares.
- Both distinguishedness hypotheses: `hT : T ∈ distTriang C` and
  `hT' : T' ∈ distTriang C`. No additional object conditions.
- Arbitrary middle map g: `(g : T.obj₂ ⟶ T'.obj₂)`. No obstruction vanishing
  is assumed globally; it is one of the equivalent conditions.
- (1a) v'gu = 0: `T.mor₁ ≫ g ≫ T'.mor₂ = 0`.
- (1b) first-square solution: `∃ f : T.obj₁ ⟶ T'.obj₁,
  f ≫ T'.mor₁ = T.mor₁ ≫ g`.
- (1b') second-square solution: `∃ h : T.obj₃ ⟶ T'.obj₃,
  T.mor₂ ≫ h = g ≫ T'.mor₂`.
- (1c) existence of a triangle morphism with middle component g:
  `∃ τ : T ⟶ T', τ.hom₂ = g`. Its other components are the required f,h.
  The three iff conjuncts compare (1a) with each other condition, hence
  express precisely mutual equivalence, without asserting any condition.
- (2) vanishing hypothesis: `Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)`
  as an implication antecedent. Hom is an abelian group with zero, so this
  means the entire Hom group vanishes, without a hollow hypothesis.
- (2) uniqueness of f and h: universal pairs `f₁ f₂` and `h₁ h₂`, each
  followed by its two square hypotheses and equality. This is at most one
  solution; existence comes from (1) when its conditions hold. Thus this
  does not claim existence for a map g with nonzero obstruction.
- (2) consequence for every compatible pair: `∀ f h`, the two square
  hypotheses imply existence of `τ` with `hom₁ = f`, `hom₂ = g`, `hom₃ = h`.
  `T.mor₃ ≫ f⟦(1 : ℤ)⟧' = h ≫ T'.mor₃` states the last square explicitly,
  as the node does. Its redundancy with the triangle-morphism type adds no
  stronger conclusion.
- (3) vanishing for X[1],Z: the last antecedent is
  `Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃)`. For every arrow x of the
  required type, `Triangle.mk T.mor₁ T.mor₂ x ∈ distTriang C → x = T.mor₃`.
  Existence of d with this property is already hT; `Triangle.mk` rebuilds
  precisely the given triangle. This is the full uniqueness assertion.

Edge cases: the zero category and zero/contractible triangles are allowed;
there is no nonzero assumption. When the Hom group is nontrivial, no
uniqueness is asserted. When the obstruction is nonzero, all four conditions
are false and uniqueness of square solutions is vacuous. T = T' and identity
g are included. Object and Hom universes u,v are independent and explicitly
bound. There is no ring, characteristic, scheme, index set, or degree n in
this statement, so those edge cases introduce no additional restriction.

Independent searches:

- LeanFinder: "The connecting arrow of a distinguished triangle is determined
  by the first two arrows when the negative Hom group vanishes" returned eight
  hits: t-structure `triangle_map_ext`, TR3 completion, and exact Hom lemmas.
  Opened `TruncLTGE.lean`: its ext/existence lemmas require a t-structure and
  degree bounds and are not this general statement.
- Loogle: `CategoryTheory.Pretriangulated.Triangle.mor₂,
  CategoryTheory.Pretriangulated.Triangle.mor₃` returned twelve hits for
  triangle morphism construction, projections, rotation, and shifts, no match.
- Search-service grep: `connecting.*unique|unique.*connecting|mor₃.*mor₃|
  triangleHom_ext` returned nineteen Mathlib ingredient hits, no combined
  extension/equivalence/uniqueness assertion.
- Independently searched Mathlib triangulated files, source WeilConjectures,
  and project lean/Sheaf with connecting/third arrow/middle component/unique
  triangle terms. Opened the upstream `exists_triangleHom_of_comp_eq_zero`,
  `triangleHom_ext_of_subsingleton`, and both cancellation lemmas. They have
  only the existence or uniqueness pieces, not the whole node. Opened project
  `TruncationCouple.existsUnique_boundary`: it is restricted to the canonical
  derived truncation triangle, not arbitrary pre-triangulated triangles.
- Exact declaration/id search of the upstream name table, source and project
  found no declaration already rendering this node.

No new node, definition, dependency module, or statement correction is present
or needed. No mismatch found; Lean and node record preserved. There is exactly
one named theorem with `sorry`, no proof or hollow definition. The docstrings
name BBD and the blueprint and carry all nine proof steps and their dependency
ids. All universes and variables are bound; no private notion or file-local
notation/instance. Checked `lean.statement` byte-for-byte against the signature
and every Lean line is at most 100 characters.

Second-reader validation: `scompile.py R1
lem-weil-pbc-triangle-morphism-extension
lean/Sheaf/CategoryTheory/Triangulated/TriangleMorphismExtension.lean`
compiled cleanly on the server in 1.7 seconds, exit code 0, no warnings.
