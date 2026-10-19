## Worker report

The module `lean/Sheaf/CategoryTheory/RationalizationLinear.lean` defines
`CategoryTheory.Rationalization.HasLinearExtension`.  This is the aggregate
predicate in the node: it records that every scalar from `M` acts invertibly on
every object of the rationalization and that the given `R`-action has a unique
extension to an `A`-linear category structure for every localization `A` of `R`
at `M`.

The hypotheses are rendered by the explicit binders `{R : Type w}` with
`[CommRing R]`, `M : Submonoid R`, `{C : Type u}` with
`[Category.{v} C]`, `[Preadditive C]`, `[Linear R C]`, `[HasZeroObject C]`,
`[HasShift C ℤ]`, additive and `R`-linear shift functors, `[Pretriangulated C]`,
`[IsTriangulated C]`, and `{A : Type w'}` with `[CommRing A]`, `[Algebra R A]`,
and `[IsLocalization M A]`.  The first clause is rendered exactly as
`∀ (m : R), m ∈ M → ∀ (Y : Rationalization M C), IsIso (m • 𝟙 Y)`.
The second clause is `∃! l : Linear A (Rationalization M C), ...`, so `l` is
an `A`-linear structure and the uniqueness quantifier compares structures.
For each `r : R`, objects `X Y` and `f : X ⟶ Y`, the compatibility clause uses
the scalar operation supplied by `l` explicitly:

```
@SMul.smul A (X ⟶ Y)
  (SemigroupAction.toSMul (self :=
    MulAction.toSemigroupAction (self :=
      DistribMulAction.toMulAction (self :=
        Module.toDistribMulAction (self := Linear.homModule (self := l) X Y)))))
  (algebraMap R A r) f = r • f
```

This explicit projection avoids a `let`-bound local instance in the statement;
the right side is the original `R`-action.  Thus the body states the displayed
formula `\bar r • f = r • f` while retaining the full `Linear A` structure.
The rationalization and its canonical scalar action are imported from
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`.

The dependency declarations used are:

- `def-sfb-rationalization-quotient`: the recorded Mathlib declarations
  `CategoryTheory.MorphismProperty.Localization`,
  `CategoryTheory.MorphismProperty.Q`, and
  `CategoryTheory.Triangulated.Localization.isTriangulated_functor`, which
  specialize to the imported `CategoryTheory.Rationalization` and `Q`.
- `def-weil-linear-category`: `CategoryTheory.Linear` from
  `Mathlib/CategoryTheory/Linear/Basic.lean`.
- `lem-weil-pbc-ring-localization-universal-property`:
  `IsLocalization.lift` and `IsLocalization.ringHom_ext` from
  `Mathlib/RingTheory/Localization/Defs.lean`.
- The source module also supplies
  `CategoryTheory.Rationalization.isIso_smul_id`,
  `CategoryTheory.Rationalization.linear`, and
  `CategoryTheory.Rationalization.algebraMap_smul`; these are used as the
  canonical constructions underlying this aggregate predicate.

Edge cases checked: `M = {1}` leaves the original action and gives the identity
localization; if `0 ∈ M`, the zero localization case remains covered; the
localization map need not be injective; the empty category and zero coefficient
ring introduce no extra assumptions; and no object or index universe is
restricted beyond the explicit universes.

Searches for an existing declaration were made before writing the module:

- `msearch.py ... leanfinder "unique A-linear extension of the R action on a triangulated rationalization"` returned generic localization and derived-category declarations, with no aggregate predicate.
- `msearch.py ... loogle "CategoryTheory.Linear, IsLocalization, IsIso"` returned no combined hit (the service reported `IsIso` unknown).
- `msearch.py ... grep "HasLinearExtension|Rationalization.*linear" CategoryTheory` and `rg` over `WeilConjectures/` and `lean/Sheaf/` found only the existing `Rationalization.isIso_smul_id`, `Rationalization.linear`, and `Rationalization.algebraMap_smul`.
- `msearch.py ... leansearch "The Verdier quotient of a linear triangulated category by torsion objects is linear over a localization"` returned only generic localization declarations.

No exact existing declaration was found, and no `STATEMENT-DISPUTED` or node
fault remains.

## Earlier second reading (a previous round; superseded)

I opened the node, blueprint statement and proof, and the completed module.  The
first conjunct matches the quantifiers over `m`, membership in `M`, objects `Y`,
and `IsIso (m • 𝟙 Y)`.  The second conjunct quantifies over the same localization
`A`, asks for a unique `Linear A` structure, and states the compatibility for
every scalar `r`, pair of objects, and morphism.  The explicit `SMul.smul`
projection is exactly the action of the candidate `l`, while `r • f` is the
existing `R`-action; no hypothesis, object, clause, or edge case was added or
dropped.  All universes and instances are bound explicitly, and compilation via
`scompile.py` is clean.

## Second reading by Q114

I independently opened the item JSON, its blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-rationalization/def-sfb-rationalization-linear.{md,proof.md}`,
the quotient blueprint statement, all three statement-dependency nodes, and
the actual Lean declarations. I also read the three additional proof-dependency
nodes and the relevant Mathlib localization, center and triangulation sources.
The earlier second-reading paragraph above is superseded by this reading.

The source's object/hypothesis/conclusion checklist and its final Lean rendering:

| Source item | Lean rendering and verdict |
| --- | --- |
| A commutative coefficient ring R | `{R : Type w} [CommRing R]`; exact, including the zero ring. |
| A submonoid M of R | `(M : Submonoid R)`; exact, no nonzero-denominator assumption. |
| An R-linear triangulated category T | `{C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]`, `[HasZeroObject C] [HasShift C ℤ]`, additive shifts, `[Pretriangulated C] [IsTriangulated C]`; exact encoding of the structure required by the quotient dependency. |
| R-linear shift functors | `[∀ n : ℤ, (shiftFunctor C n).Linear R]`; exact for every integer. The separately listed additive-shift instance is part of Mathlib's triangulated interface, not an additional mathematical condition. |
| D is T[M^-1], the quotient at the torsion-cone class | `Rationalization M C`; exact. I followed its reducible definition to `(Rationalization.W M C).Localization`, then `W` to `(torsion M C).trW`, then `torsion` to `∃ m ∈ M, m • 𝟙 X = 0`. Thus it is the dependency's Verdier quotient, not the tensor-Hom scalar-localization category elsewhere in this project. |
| The existing R-action on D | The `Linear R` instance supplied by `CategoryTheory.Localization.linear`, applied to the additive localization `Q`; exact. `Q` is the dependency's `MorphismProperty.Q` and is R-linear. |
| Every m in M and every object Y of D | `∀ (m : R), m ∈ M → ∀ (Y : Rationalization M C), ...`; exact, with the same quantifier order. |
| Multiplication by m on the identity is invertible | `IsIso (m • 𝟙 Y)` in the first conjunct; exact, on arbitrary quotient objects. |
| Any localization A of R at M, with its localization map | `{A : Type w'} [CommRing A] [Algebra R A] [IsLocalization M A]`; exact arbitrary-model localization, with map `algebraMap R A`. The theorem is polymorphic in A and its independent universe. |
| Existence and uniqueness of an A-linear structure extending the R-action | `∃! l : Linear A (Rationalization M C), ...`; exact structures on the fixed preadditive quotient, rather than a merely chosen action or a different category. |
| Compatibility for every r and every morphism f:X→Y | `∀ (r : R) {X Y : Rationalization M C} (f : X ⟶ Y), ...`; exact. The explicit `@SMul.smul` projection through `Linear.homModule (self := l) X Y` applies the candidate structure l to `algebraMap R A r`; the right-hand `r • f` uses the original R-action. |
| Both conclusions hold under these hypotheses | Now a theorem `CategoryTheory.Rationalization.isIso_smul_id_and_existsUnique_linear` with these two conjuncts as its type and whole proof `sorry`; exact. The original `def HasLinearExtension ... : Prop := ...` merely named the claim without stating that it holds. This was the main mismatch. |

Dependency verification: `CategoryTheory.Linear` in
`Mathlib/CategoryTheory/Linear/Basic.lean:48` has exactly the Hom-module field
and two composition bilinearity fields. The quotient dependency's Mathlib
`MorphismProperty.Localization` and `Q` (Construction.lean:107,112) are exactly
the reductions of the imported rationalization and Q; the triangulated
localization instances are in Localization/Triangulated.lean:208,229,231.
`IsLocalization.lift`, `lift_eq`, `lift_mk'`, and `ringHom_ext` in
`Mathlib/RingTheory/Localization/Defs.lean:488-546` give the stated universal
property without injectivity. I read Stacks `algebra.tex`,
`proposition-universal-property-localization` (00CP, lines 1083-1112), including
the preceding warning about zero divisors, and `dga.tex`,
`definition-linear-category` (09MJ, lines 2863-2883). Neither adds a field,
Noetherian, nontriviality, characteristic or finiteness hypothesis.

I also checked `lem-sfb-additive-localization-linear` against
Mathlib's `Localization.linear`, `functor_linear`, `inverts`, and essential
surjectivity; and `lem-sfb-category-center-linear` against `CatCenter`,
`Linear.toCatCenter`, `ofRingMorphism` and its scalar formulas. The recorded
`lem-sfb-smul-id-in-w` source path was missing locally, so I read its current
server source with
`scompile.py --source WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`.
This is the same torsion-cone construction and its two recorded lemmas,
`smul_id_cone_eq_zero` and `W_smul_id`, with the required signatures. The
delivery now imports that current module path instead of the older
`DerivedCategory.Complete.Rationalization` path. No private copy or dependency
repair is needed. There are no new nodes or sibling dependency modules, and
no `statement_change`: the natural-language node and all its dependencies stay
unchanged; this repairs its Lean rendering only.

Edge cases: M cannot be empty because a submonoid contains 1. M={1} and
submonoids consisting of units are included. If 0∈M, the zero localization and
the zero quotient are included: in a zero category the zero identity is also
invertible. R and A may be zero rings, and the localization map may have a
kernel (for example R=ℤ/6 with the submonoid generated by 2). A zero category
is included; a literally empty category is already excluded by the source's
triangulated-category assumption, since it requires a zero object. The first
worker's claim that an empty category is allowed was inaccurate. There is no
index family, scheme, or natural-number degree in this node. Shift degree
n=0 and negative integers are included. There is no characteristic assumption.
The universes w,w',u,v are independently declared and used explicitly; the
quotient construction may enlarge its Hom universe automatically but imposes
no equality between object, morphism, or coefficient universes. Quantifying
over `Linear A D` ranges over structures on the same fixed Hom groups; equality
of actions identifies those structures by extensionality and proof irrelevance.

Independent searches, using different concept wording from the first worker:

- `msearch.py Q114 def-sfb-rationalization-linear leanfinder "There is exactly one scalar multiplication by a localized ring making composition bilinear and agreeing with the original scalar multiplication"` returned module-localization scalar compatibility and localized-module constructions; no rationalization uniqueness statement.
- `msearch.py ... loogle "CategoryTheory.Linear"` returned the Linear class, Hom module field, generic instances and composition maps; no unique localized extension statement.
- `msearch.py ... leansearch "Uniqueness of extending a linear category structure to a localization of the coefficient ring"` returned generic localization linear instances and uniqueness of localized-module maps; no exact aggregate statement.
- Independent `rg` searches for `existsUnique.*[Ll]inear`, `∃!.*Linear`, uniqueness/linearity in both word orders, `HasLinearExtension` and the new theorem name across Mathlib CategoryTheory, upstream CategoryTheory, project CategoryTheory and the upstream name index found no such declaration. Broader rationalization searches over all upstream `WeilConjectures/` and project `lean/Sheaf/` found the canonical invertibility/existence/compatibility results and specialized paper constructions, but no uniqueness declaration for this arbitrary-submonoid quotient. I opened both the older source and the current framework rationalization modules, rather than relying on names. The existing generic tensor-Hom scalar-localization results concern a different construction and do not replace this item.

Repairs: replaced the named but unasserted proposition with the theorem above,
retaining the correct hypothesis binders, conjuncts, and explicit candidate
scalar-action term. Expanded the declaration docstring from a one-sentence
summary to all six DAG proof steps, naming the dependencies, fraction-model
transport and recovery of a unique structure. Added direct public imports for
statement dependencies and non-public imports for the Mathlib proof-dependency
modules, and selected the current upstream rationalization path. Updated only
the node's `lean` record, including its full signature verbatim and date.
There are no hollow definitions, local notation, local instances, unbound
universes, or new proofs; the sole theorem proof is `sorry`.

Validation: `scompile.py Q114 def-sfb-rationalization-linear
.../lean/Sheaf/CategoryTheory/RationalizationLinear.lean` compiled both its
sandbox and library-module contexts cleanly (1.3 s and 1.7 s), with no errors
or warnings. The Lean file has no lines exceeding 100 characters. A direct
JSON comparison confirmed that no node field other than `lean` changed, and
the recorded `lean.statement` is the complete theorem signature copied
verbatim from the file up to `:=`.
