## Worker report

The exact notion already exists: `CategoryTheory.Rationalization.W` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`.
The source signature is verbatim `def W : MorphismProperty C :=`, and its body is
`(torsion M C).trW`. This delivery completes the existing attachment with the actual
current module path, declaration, signature, branch, author, UTC date and `existing: true`.
No Lean module is delivered, no proof is postponed, and only the item's `lean` field changes.
The existing node status and audit fields are preserved.

I read the current blueprint node in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` under
`sk-def-sfb-rationalization/def-sfb-rationalization-morphisms.md`; it agrees verbatim with
the DAG statement. There is no repair note for this item.

Hypotheses and clauses, matched individually:

- The situation of `lem-sfb-torsion-triangulated` uses `{R : Type w} [CommRing R]`,
  `(M : Submonoid R)`, `(C : Type u) [Category.{v} C]`, `[Preadditive C]`, `[Linear R C]`,
  `[HasZeroObject C]`, `[HasShift C ℤ]`, `[∀ n : ℤ, (shiftFunctor C n).Additive]`,
  `[∀ n : ℤ, (shiftFunctor C n).Linear R]`, and `[Pretriangulated C]`.
  All are the upstream section variables. `W` itself does not need the linear-shift
  instance: Lean omits that unused parameter. It is available without restriction in
  exactly the node's situation. No octahedral `[IsTriangulated C]` assumption is needed.
- A class of morphisms of the same category is `W M C : MorphismProperty C`.
  `MorphismProperty C` quantifies over both objects and a morphism `f : X ⟶ Y`.
- Having an M-torsion mapping cone is `(torsion M C).trW f`. Reading the Mathlib definition
  and `ObjectProperty.trW_iff` gives precisely
  `∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (_ : Triangle.mk f g h ∈ distTriang C), torsion M C Z`.
  Thus the first arrow is the given `f`, the second arrow is `g`, the third arrow is `h`,
  and the triangle must be distinguished. This is existential, as in the node; it does not
  select an arbitrary cone or require chosen cones.
- M-torsion of that third object is exactly `∃ m ∈ M, m • 𝟙 Z = 0`, by the already recorded
  `CategoryTheory.Rationalization.torsion` definition.
- The final Verdier-quotient description is realized in the same existing module:
  `CategoryTheory.Rationalization` is `(Rationalization.W M C).Localization`, and
  `CategoryTheory.Rationalization.Q` is `(W M C).Q`. Consequently this is the defining class
  inverted by that localization. The triangulated-subcategory instance of the dependency
  supplies the Verdier interpretation. These quotient declarations are source evidence for
  this descriptive clause; the separate quotient node is not restated in this delivery.

Dependency declarations read in full, with docstrings and section variables:
`lem-sfb-torsion-triangulated` records
`CategoryTheory.Rationalization.instIsTriangulatedTorsion` and
`CategoryTheory.Rationalization.smul_id_obj₂_eq_zero`, both in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`.
The instance supplies zero, shift and triangle closure of `torsion M C`; the companion lemma
supplies exactly the product annihilator for the middle object. I also read the dependency's
own prerequisite `CategoryTheory.Rationalization.torsion` in that module. The Mathlib
construction used is `CategoryTheory.ObjectProperty.trW` from
`Mathlib.CategoryTheory.Triangulated.Subcategory` (definition and `trW_iff` around lines
460–469). No private copy or alternate object property is introduced.

Edge cases checked against the definitions: `0 ∈ M` makes every object torsion and hence
all morphisms belong to W, since every morphism has a distinguished cone. For `M = ⊥`,
only the identity scalar is needed, so a cone is torsion precisely when its identity is zero.
The zero object is torsion with witness 1 and no nontriviality assumption on R is imposed;
this also covers the zero ring. Integer shifts, including shift 0, are unrestricted.
Object, morphism and ring universes are independent (`u`, `v`, `w`). No boundedness,
finiteness, field, nonzero scalar or chosen-cone assumptions occur. The definition only needs
a pretriangulated category, exactly as the item says.

Searches made before recording the match:

- `msearch.py leanfinder`, query `morphisms with torsion mapping cone in a linear
  pretriangulated category`: eight hits, including `CategoryTheory.ObjectProperty.trW_iff`.
- `msearch.py loogle`, query `CategoryTheory.ObjectProperty.trW,
  CategoryTheory.Rationalization.W`: zero hits, unknown identifier for the project-specific W.
- `msearch.py leansearch`, query `morphisms whose cone lies in a triangulated subcategory`:
  eight hits including the general `trW` construction and fraction/compatibility instances.
- `msearch.py grep`, query `trW|torsion` in `CategoryTheory/Triangulated`: 24 hits, identifying
  `trW` and `trW_iff`. An initial `W` query in `CategoryTheory/DerivedCategory` had no hits.
- `rg` in upstream `WeilConjectures` located the exact W definition and module documentation
  in `CategoryTheory/DerivedCategory/Complete/Rationalization.lean` (around line 141).
  The old `CategoryTheory/DerivedCategory/Rationalization.lean` path does not exist locally.
  `scompile.py --source` confirmed the full current module at the correct Complete path.
- `grep -rn 'def-sfb-rationalization-morphisms'` in upstream had no node-tag hits;
  searching the source name in `dag/lean_names_upstream.json` had no hits. Direct source
  inspection and the current dependency records supply the match despite those old indexes.
- `rg` for `Rationalization.W` in `lean/Sheaf` had no hits. A broader torsion/trW search in
  `lean/Sheaf/CategoryTheory` found other torsion work, not another definition of this notion.
- The existing node itself already carries an attachment for W and Rationalization with a
  stale module path in its audit; no extra notion or definition node is needed.

Validation: `scompile.py NC def-sfb-rationalization-morphisms` compiled the scratch-only
`ExistingChecks.lean` against the current library, with no errors or warnings. It checks
`@W`, the dependency instance and product lemma, `@ObjectProperty.trW_iff`, and the existing
quotient and Q signatures. A fully universe-bound scratch `Iff.rfl` example checks that W
expands definitionally to exactly the distinguished-triangle existential and annihilator
above. `#print axioms CategoryTheory.Rationalization.W` lists only `propext`,
`Classical.choice`, `Quot.sound`. The scratch file is not a delivered module.

No statement correction, new node, dependency module, or disputed statement is needed.
The independent second reading is left to the second reader.

## Second reading by NC

I independently opened the sandbox node and its blueprint source, the nodes
`lem-sfb-torsion-triangulated` and `def-sfb-torsion-objects`, their actual upstream
declarations, and Mathlib's `ObjectProperty.trW` and localization construction.
The item's source is the named blueprint Markdown node, not a Stacks tag. Its text
agrees verbatim with the DAG statement. There is no statement_change or repair note.
The current source returned by `scompile.py --source` agrees with the local Complete
module for all declarations used here.

My list of the mathematical objects, hypotheses and clauses, with the Lean match:

- Commutative coefficient ring R: `{R : Type w} [CommRing R]`. Verdict: exact;
  no field, domain, characteristic, or nontriviality hypothesis.
- Multiplicative submonoid M of that same R: `(M : Submonoid R)`. Verdict: exact;
  no assumption that its elements are nonzero or units.
- Pretriangulated R-linear category T: `(C : Type u) [Category.{v} C]`,
  `[Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]`,
  `[∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]`.
  Verdict: these are the structures comprising the node's situation, with independent
  ring, object and morphism universes. Neither an Abelian nor an IsTriangulated instance
  is added.
- R-linear integer shifts in the cited dependency:
  `[∀ n : ℤ, (shiftFunctor C n).Linear R]` is used by
  `Rationalization.instIsTriangulatedTorsion` to give shift closure. Verdict: exact.
  W itself simply names a class and does not use that instance; Lean's omission of
  this unused section parameter does not change the class in the stated situation.
- Objects X, Y and their arrow f: `MorphismProperty C` ranges over `{X Y : C}` and
  `f : X ⟶ Y`. Verdict: same ambient category and no object restriction.
- Class W_M: `CategoryTheory.Rationalization.W M C`, whose entire definition is
  `def W : MorphismProperty C := (torsion M C).trW`. Verdict: exact existing notion;
  the node's lean.statement is the signature verbatim through `:=`.
- Membership means existence of a cone triangle, with f as its first arrow:
  `∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), torsion M C Z`.
  Verdict: exactly Mathlib's trW definition, with the same existential order, shift,
  distinguishedness and third object. No chosen cone or arbitrary comparison map.
- The cone is M-torsion: the dependency's very same `Rationalization.torsion M C Z`
  is `∃ m ∈ M, m • 𝟙 Z = 0`. Verdict: exact; the scalar may depend on the cone.
  I read both the object-property definition and its isomorphism-closure instance.
- These are the arrows inverted in the quotient by the torsion objects:
  `Rationalization M C := (Rationalization.W M C).Localization` and
  `Rationalization.Q M C := (W M C).Q`. Verdict: this is the specified defining
  localization class. Mathlib's Construction.lean defines this localization by formal
  inverse arrows and relations Winv₁/Winv₂, and `Localization.Construction.wIso` exhibits
  their inverses. The compiler confirms that Rationalization and Q themselves need only
  Pretriangulated, although the later triangulated-functor instance uses IsTriangulated.
  Thus no extra octahedral hypothesis is hidden in this descriptive clause.

The dependency interface is usable without repair: instIsTriangulatedTorsion supplies
ContainsZero, all integer shifts and triangle closure, while smul_id_obj₂_eq_zero has
the precise conclusion `(m₁ * m₃) • 𝟙 T.obj₂ = 0` from annihilation of T.obj₁ and T.obj₃.
Their section assumptions match the dependency node. No new node or dependency module
is included, so H12/H13 introduce no further records to review.

Edge cases: there is no index family, scheme or natural-number bound in this statement.
M cannot be empty because it contains 1. If 0 belongs to M, every cone is torsion and
every arrow is in W; a distinguished cone exists in a pretriangulated category. If
M is the bottom submonoid, torsion means identity zero, so membership requires a zero
cone. The zero object is torsion with scalar 1. A zero ring and arbitrary characteristic
are allowed. The empty category cannot satisfy the given zero-object assumption, and
no additional nonemptiness is imposed. All integer shifts, including 0, remain available.
The compiler prints three independent universes, with no equality or smallness condition.

Independent searches, using different wording from the first reader:

- LeanFinder: `Verdier quotient arrows whose third triangle object is annihilated by
  a scalar`, eight hits, including ObjectProperty.trW and its triangle constructor.
  Some hits use older Subcategory.W names; I checked the current source rather than
  accepting those names as new declarations.
- Loogle: `CategoryTheory.ObjectProperty.trW`, twelve hits, confirming the general
  cone-property construction, its isomorphism and fraction interfaces.
- LeanSearch: `An arrow belongs to the class associated to an object property if it
  admits a distinguished triangle whose third object satisfies that property`, eight
  hits, including trW and trW_iff.
- msearch grep: `cone satisfies|class of morphisms whose cone` in
  CategoryTheory/Triangulated, one hit at Subcategory.lean:460, read through trW_iff.
- Direct rg of upstream CategoryTheory for cone annihilation, torsion/cone and
  torsion/trW found the exact Complete.Rationalization.W; RationalizationMap consumes
  it. Direct rg throughout lean/Sheaf for Rationalization, `torsion M C` and `.trW`
  found specialized rationalization constructions and acyclic-complex uses, with no
  competing general M-torsion-cone definition. No second definition is warranted.

Validation: I reran `scompile.py NC def-sfb-rationalization-morphisms
scratchpad/ExistingChecks.lean`. Both wrapper checks succeeded without errors or warnings.
The fully bound scratch example is definitionally Iff.rfl for the complete existential
and annihilator above; the printed dependency, W, quotient and Q signatures agree with
this reading. `#print axioms CategoryTheory.Rationalization.W` lists only propext,
Classical.choice and Quot.sound. The scratch file is not delivered.

Mismatches found: none. I preserved the correct existing attachment and statement,
and appended this independent reading only. There is no new data definition, proof,
sorry, delivered module or docstring to repair; existing upstream source is read-only.
