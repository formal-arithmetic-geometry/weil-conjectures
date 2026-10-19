## Worker report

Item: `lem-pur-etale-at-point-from-differentials`; group Q49, stage 2, 2026-10-17.

The module `Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials` states
`AlgebraicGeometry.Scheme.exists_etale_open_of_coordinate_differentials_basis`, with
its sole proof `sorry`. There are no new definitions, helper theorems, dependency
repairs, or statement corrections. The module docstring gives the source, and the
theorem docstring gives all six steps of the node's existing proof.

I read the current reviewed node (Q111's merged stage-1 split), each statement
dependency's statement and Lean record/Mathlib match, the declarations listed
below, the example CompactObject module and node, and Stacks `morphisms.tex`
Tag 02GU (`lemma-etale-at-point`, condition (8), lines 8318 onward), Tag 01V7
(`lemma-smooth-locally-standard-smooth`, lines 7191 onward), and `algebra.tex`
Tag 00T7 (`lemma-standard-smooth`, part (2), lines 37274 onward).

Each hypothesis and clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| k is any field | `(k : Type u) [Field k]` |
| U is a k-scheme | `(U : Scheme.{u}) [U.Over (Spec (.of k))]`, with structural map `U ↘ Spec (.of k)` |
| U is finite type over k | `[LocallyOfFiniteType (U ↘ Spec (.of k))]` and `[QuasiCompact (U ↘ Spec (.of k))]`, the recorded finite-type convention |
| U is smooth over k | `[Smooth (U ↘ Spec (.of k))]` |
| the point u and the nonnegative integer d | `(x : U) (d : ℕ)`; the point is renamed x |
| the d chosen global functions | `(h : Fin d → Γ(U, ⊤))`; h denotes the family, indexed from zero |
| the k-morphism with precisely those functions | `AffineSpace.homOfVector (U ↘ Spec (.of k)) (fun j : ULift.{u} (Fin d) ↦ h j.down)`; `homOfVector_over` and `homOfVector_appTop_coord` give its structure map and its exact coordinate pullbacks |
| relative differential sheaf | `(U ↘ Spec (.of k)).relativeDifferentials`, the recorded upstream definition |
| its stalk at the chosen point | `(RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj (U ↘ Spec (.of k)).relativeDifferentials` |
| the residue field and its canonical stalk action | `IsLocalRing.ResidueField (U.presheaf.stalk x)`, definitionally the carrier of the recorded `U.residueField x`; `IsLocalRing.ResidueField.algebra` is induced by the quotient map |
| the cotangent fibre | the residue field tensored over `U.presheaf.stalk x` with the preceding module stalk; this uses the left-scalar convention of the recorded base-change node, canonically equivalent to the reversed tensor order in the node |
| each class dh_j | `TensorProduct.tmul (U.presheaf.stalk x) (N := ...) 1` applied to the germ at x of `relativeDifferentialsDerivation.d (h j)` |
| these classes form a basis | `hbasis : ∃ b : Module.Basis (Fin d) ... ..., ∀ j, b j = ...`; existence of this basis with the specified values is exactly linear independence and spanning of this family, with no replacement of the family |
| an open neighbourhood of u | `∃ V : U.Opens, x ∈ V ∧ ...` |
| the restriction of the same map is etale | `Etale (V.ι ≫ AffineSpace.homOfVector ... ...)` |

Dependencies used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`,
  Mathlib.AlgebraicGeometry.Over; supplied through the affine-space API.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace`, together with its
  `homOfVector`, `homOfVector_over` and `homOfVector_appTop_coord`,
  Mathlib.AlgebraicGeometry.AffineSpace. The index is `ULift.{u} (Fin d)` as in
  that node's record; this does not change the set of d coordinates.
- `def-sc-relative-differential-sheaf`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and its recorded module's
  universal derivation `relativeDifferentialsDerivation`,
  WeilConjectures.AlgebraicGeometry.Modules.Differentials.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`,
  Mathlib.AlgebraicGeometry.ResidueField. Its defining expression is used to make
  the canonical scalar instances visible, rather than taking an arbitrary algebra
  structure as an additional hypothesis.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
- `def-weil-module-base-change`: `TensorProduct`, `TensorProduct.tmul`, and its
  left module structure, from Mathlib.LinearAlgebra.TensorProduct.Tower and its
  imports. The action is exactly the extension of scalars specified by the node.
- Added the already recorded `def-pc-module-stalk-functor` to `stmt_deps`, under
  brief-stage2 section 5's permission to gain landed nodes. Its declaration is
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, in the recorded module
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor. I read the current source
  using `scompile.py --source WeilConjectures.Algebra.Homology.ModuleStalkFunctor`;
  this is the upstream replacement for the still-present older Sheaf module.
  The module is imported from its recorded upstream location to avoid duplicates.

The proof-only imports supply the standard smooth differential basis, tilde stalk
localization, polynomial partial derivatives, localization away from an element,
and the square Jacobian criterion, as in the node's six-step proof. No downstream
lemma, arbitrary coordinate map, additional regularity assumption, affine-source
assumption, closed-point assumption, or separability assumption is introduced.

Edge cases checked mathematically before stating:

- `d = 0`: the family and basis index are empty, so the hypothesis says the
  differential fibre is zero; a smooth k-scheme is etale near such a point, and
  the constructed map is to zero-dimensional affine space. No positivity
  assumption or nonempty index instance occurs.
- Empty U has no x, so the pointwise assertion is vacuous, as in the node.
- Arbitrary nonclosed points are allowed by `(x : U)`; the tensor uses their
  actual residue fields, not k or an algebraic closure.
- Over characteristic p, the map on A^1 given by t^p has zero differential,
  so its one-element family is not a basis of the one-dimensional fibre;
  the theorem does not falsely call Frobenius etale.
- The map A^2 to A^1 using one coordinate fails the spanning hypothesis;
  a zero or repeated coordinate fails independence in positive rank.
- Identity coordinates on A^d satisfy the hypothesis, as do a separable
  zero-dimensional smooth k-scheme with the empty coordinate family.
- Universes are explicit (`universe u`, `Type u`, `Scheme.{u}`); any field
  and scheme can be placed in a common ambient universe. No test-object
  universe, extra equality of universes, or implicit variable is introduced.

Searches actually run for this worker (via msearch.py, Q49/item):

1. LeanFinder: `A smooth scheme map to affine space is etale near a point when
   the chosen coordinate differentials form a basis in the cotangent fibre`.
   Eight hits: standard-smooth existential etale polynomial charts, relative
   dimension zero implies etale, standard etale presentations, etale locus,
   and an etale-implies-smooth instance. None states the prescribed-coordinate
   scheme-level differential-fibre criterion.
2. Loogle: `Algebra.FormallyEtale, KaehlerDifferential`. Seven hits: vanishing
   differentials for formally etale algebras, the constructor and equivalent
   criterion also requiring H1-cotangent vanishing, and canonical differential
   base-change equivalences. No exact statement.
3. Grep: `etale.*differential|differential.*etale|Etale.*basis` in
   `AlgebraicGeometry`: zero hits. This is a case-sensitive pattern; no broad
   absence conclusion is inferred from that one search.
4. LeanSearch: `A smooth scheme map to affine space is etale if its prescribed
   coordinate differentials form a basis in the cotangent fibre`. Eight hits
   concerning the definitions of smooth and etale, standard-smooth relative
   dimension zero, and formally smooth plus unramified implies formally etale;
   no exact statement for the given coordinate map.
5. Direct rg in the upstream WeilConjectures and shared lean/Sheaf trees for
   the item id, `etale.*[Dd]ifferential|[Dd]ifferential.*etale`, and
   `exists_etale.*basis`. The scheme results concern already-smooth maps with
   zero relative differential modules, or simultaneous coordinates for a
   smooth closed pair; they do not state this criterion. The standard smooth
   conormal chart results are algebra-level construction statements.
6. The exact proposed declaration name was searched in Mathlib, upstream,
   lean/Sheaf and dag/lean_names_upstream.json: no collision. The item id has
   no upstream declaration. I inspected AffineSpace's homOfVector API and the
   standard smooth polynomial-chart and differential-basis candidates rather
   than defining another affine space, derivation, or stalk functor.

No STATEMENT-DISPUTED or mathematical node fault was found. The previous worker's
unchanged stage-1 split is superseded by Q111's reviewed split on the base. This
packet only adds the stage-2 record/module, adds the existing stalk definition
as a statement dependency, and leaves that reviewed split untouched.

Validation: scompile.py compiled both the sandbox and final library module
cleanly (1.7 s and 2.0 s), with no errors or warnings. All variables and universes
are bound explicitly and `autoImplicit` is disabled. The source lines are at
most 100 characters. The final delivery dry run is recorded below.

Dry run result: `OK (dry run): commit 3e32a96dc0 compiles and passes the preflight except for the second reading, which the second reader writes; nothing pushed.`


## Second reading by Q49

I independently opened the reviewed node, its source place, the dependency records, and
`EtaleAtPointFromDifferentials.lean`. The item-by-item comparison is:

- The field is rendered by `(k : Type u) [Field k]`; verdict: exact.
- The scheme over the field is `(U : Scheme.{u}) [U.Over (Spec (.of k))]`; its
  structural map is `U ↘ Spec (.of k)`; verdict: exact, with the common universe required
  by the scheme morphism API and no extra geometric hypothesis.
- Finite type is rendered by `[LocallyOfFiniteType (U ↘ Spec (.of k))]` and
  `[QuasiCompact (U ↘ Spec (.of k))]`; verdict: the recorded finite-type convention.
- Smoothness is `[Smooth (U ↘ Spec (.of k))]`; verdict: exact.
- The point and nonnegative integer are `(x : U) (d : ℕ)`; verdict: exact, including
  `d = 0`.
- The functions are `h : Fin d → Γ(U, ⊤)`; verdict: exact encoding of the d global
  functions.
- The prescribed k-morphism is
  `AffineSpace.homOfVector (U ↘ Spec (.of k))
  (fun j : ULift.{u} (Fin d) ↦ h j.down)`; verdict: exact Mathlib affine-space
  construction, with the `ULift` index forced by that construction and no changed
  coordinate family.
- The relative differential sheaf is
  `(U ↘ Spec (.of k)).relativeDifferentials`; verdict: the recorded upstream
  `Scheme.Hom.relativeDifferentials` declaration.
- Its stalk at x is
  `(RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
  (U ↘ Spec (.of k)).relativeDifferentials`; verdict: exact, using the recorded stalk
  functor dependency.
- The residue field is
  `IsLocalRing.ResidueField (U.presheaf.stalk x)`; verdict: definitionally the
  recorded `U.residueField x`, with its canonical stalk algebra structure.
- The cotangent fibre is
  `IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[U.presheaf.stalk x]` applied to
  the differential stalk; verdict: the canonical Mathlib left scalar-extension
  presentation of the node’s module base change. The node writes the commuted order
  `Ω ⊗ κ`; the recorded base-change interface identifies these by `TensorProduct.comm`,
  so no mathematical object or hypothesis is changed.
- The class `dh_j` is rendered by `TensorProduct.tmul ... 1` applied to the germ of
  `relativeDifferentialsDerivation.d (h j)`; verdict: exact class in the displayed
  scalar-extension presentation.
- The basis condition is
  `∃ b : Module.Basis (Fin d) ... ..., ∀ j, b j = ...`; verdict: exact specified
  basis, hence both independence and spanning of the prescribed classes.
- The neighbourhood conclusion is
  `∃ V : U.Opens, x ∈ V ∧ Etale (V.ι ≫ AffineSpace.homOfVector ...)`; verdict:
  exact open neighbourhood and restriction of the same coordinate map.

The source reading was checked against Stacks `morphisms.tex`, Tag 02GU
(`lemma-etale-at-point`, especially condition (8)), Tag 01V7
(`lemma-smooth-locally-standard-smooth`), and `algebra.tex`, Tag 00T7
(`lemma-standard-smooth`, part (2)). These give the same smooth finite-type setup,
standard-smooth local chart, Jacobian criterion, and differential basis used by the
node. No hypothesis is added and no conclusion clause is dropped or strengthened.

Edge cases checked: `d = 0` uses `Fin 0` and an empty basis with no nonemptiness
assumption; an empty U has no point and is vacuous; arbitrary (including nonclosed)
points use the actual residue field; characteristic p and Frobenius coordinates do not
satisfy the basis hypothesis; zero or repeated coordinates fail the basis condition when
appropriate; and all field/scheme universes are explicit. No extra characteristic,
separability, affine-source, closed-point, or regularity assumption occurs.

For independent searches I ran `msearch.py` LeanSearch, LeanFinder, and grep queries
for a prescribed-coordinate differential basis criterion. LeanSearch and LeanFinder
returned only constituent smooth/etale and algebraic cotangent-basis results; grep in
both the upstream `WeilConjectures` tree and shared `lean/Sheaf` found no exact
scheme-level declaration. The exact theorem name and item id also have no collision in
Mathlib, upstream, or `dag/lean_names_upstream.json`. Thus the module is required and
is not a duplicate definition.

No mismatch was found, so no Lean or node repair was needed. The sandbox node’s only
stage-2 addition is the already-recorded `def-pc-module-stalk-functor` statement
dependency, whose upstream declaration was read and used. `scompile.py` compiles both
the sandbox and library module without errors or warnings.
