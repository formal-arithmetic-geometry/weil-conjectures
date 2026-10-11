## Worker report

The theorem `AlgebraicGeometry.Scheme.exists_pow_smul_eq_zero_of_perfect_supported`
states Stacks Tag 08EJ exactly. The source was read at
https://stacks.math.columbia.edu/tag/08EJ (the literature TeX is not present locally).
Its proof is `sorry`; no mathematical results were proved in this delivery.

Hypothesis and conclusion correspondence:
- Scheme X: `(X : Scheme.{u})`, from def-pc-scheme.
- Quasi-compact: `[CompactSpace X]`; quasi-separated: `[QuasiSeparatedSpace X]`.
  These are the topological qcqs properties of a scheme, with no separatedness hypothesis.
- Global function f: `RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)`.
  This is the ring of compatible local sections. Every family is uniquely determined by its
  component at `op ⊤`, by compatibility with each restriction from the top open; conversely,
  restricting any section of Γ(X,⊤) gives such a family. Thus all global functions are allowed.
- Objects and morphism in D_QCoh: `(E E' : schemeDerivedQCohCategory X) (α : E ⟶ E')`.
  The recorded full subcategory carries exactly quasi-coherence of every cohomology sheaf.
  `α.hom` is the same morphism in the ambient derived category, via the full inclusion.
- Source perfect: `(hE : X.IsPerfect E.obj)` uses the recorded local strictly-perfect definition.
- T = V(f): its complement is `X.basicOpen (f.val (op ⊤))`, the nonvanishing locus D(f).
  No separate closed-subscheme structure on T is required or imposed.
- Every cohomology sheaf of E' vanishes off T: `hSupport` quantifies over every `i : ℤ` and
  asserts `IsZero` of the restriction of `H^i(E'.obj)` by `SheafOfModules.overFunctor` to D(f).
  On the Zariski localized site this is precisely the module sheaf on the open D(f).
- Some integer n ≥ 0: `∃ n : ℕ`. Nonnegative integers and natural numbers are equivalent here.
- f^n alpha = 0: `schemeDerivedScalar X (f ^ n) α.hom = 0`. This is the canonical localized
  sectionwise action, not an arbitrary scalar structure supplied as a hypothesis.

The `HasDerivedCategory.{w}` binders for the global and all open module categories are the
shared universe-polymorphic infrastructure needed by `schemeDerivedCategory` and `IsPerfect`.
They neither assume cohomological boundedness nor introduce alternative abelian instances.
Universes are explicitly declared and all variables are bound.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.DerivedCategory: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`; the latter two define the QCoh
  full subcategory using Mathlib's homology functor and `SheafOfModules.IsQuasicoherent`.
- Sheaf.AlgebraicGeometry.PerfectComplex: `AlgebraicGeometry.Scheme.IsPerfect`, whose local
  representatives use `IsStrictlyPerfect` (bounded terms, direct summands of finite free modules).
- Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule: `SheafOfModules.homLinear` and its
  `homModule`; these give the sectionwise compatible-family scalar action and bilinearity.
- Mathlib.Algebra.Homology.DerivedCategory.Linear: the derived linear instance obtained by
  localization of the homotopy-category action.
- Sheaf.Paper.DerivedHomMayerVietoris (through DerivedCategory): `moduleRings` and the shared
  exactness instances for `SheafOfModules.overFunctor`, also used in the perfect definition.
- This delivery's `AlgebraicGeometry.schemeDerivedScalar` names that specialized canonical
  derived action and is the only additional notion needed.

Edge cases checked before writing: the empty scheme is allowed; the zero source, zero target,
zero map, and n = 0 are allowed. For f = 0, D(f) is empty and exponent 1 kills every map.
For an invertible f, D(f) = X, so the support hypothesis makes every cohomology sheaf zero
and the target is zero. Nilpotent f also has empty D(f) and a sufficiently large power acts
by zero. Both complexes may be unbounded; only E is perfect, and E' is not required perfect,
coherent, finite type, or bounded. No characteristic restrictions are imposed.

Searches (all service searches logged by msearch.py in searches.jsonl):
- LeanFinder: "morphism from a perfect complex to a complex supported on the zero locus of a
  global function is annihilated by a power of the function": eight generic results including
  derived maps to/from single projectives/injectives and scalar annihilation of ordinary
  structure-sheaf sections; none is the derived-support theorem.
- Loogle: "DerivedCategory, Linear": unknown identifier Linear, no hits.
- LeanSearch: "perfect complex map supported on zero locus killed by power of function":
  unavailable, Internal Server Error.
- msearch grep "smul|[Ll]inear" in Mathlib's module-sheaf directory: three unrelated
  change-of-rings lines, no global-section derived scalar definition.
- LeanFinder: "canonical action of global functions on morphisms in the derived category of
  module sheaves on a scheme": eight ordinary sheaf-module morphism results, no derived action.
- LeanSearch on that same query: unavailable, Internal Server Error.
- Loogle: "DerivedCategory.Q, SMul": no hits.
- msearch grep "global.*scalar|scalar.*global|sectionsSubring" in Mathlib's derived-category
  directory: no hits. Direct inspection found and reused the generic derived linear instance.
- rg in WeilConjectures and lean/Sheaf for perfect/support and the proposed declaration names:
  no matching theorem or specialized derived scalar definition. Upstream `Scheme.Modules.smulHom`
  is ordinary module multiplication, not a derived action on the shared module category.
- DAG grep and `tools/blueprint_refs.py search 'global scalar derived'`: no derived action node;
  DAG grep found def-pur-sheaf-modules-hom-module, whose landed action is reused.

No statement correction or STATEMENT-DISPUTED issue was needed. Both modules compiled together
on the server with exit code 0 and no warnings. The theorem docstring carries the full affine
stupid-truncation proof and the qcqs Mayer–Vietoris induction, with the original proof-node IDs.

## New nodes

`def-sc-derived-global-scalar` defines the canonical global-function action on derived morphisms
of O_X-module sheaves, as used in Tag 08EJ. It cites the existing derived category and the
existing compatible-section action `def-pur-sheaf-modules-hom-module`. Its module sets the
canonical `homLinear` instance explicitly and uses Mathlib's derived linear instance; all data
is given in full, with no sorry. It does not reconstruct sheaf scalar multiplication or generic
localization. This specialization needs a name because instance synthesis does not recover the
commutative-ring presheaf from `moduleRings` in the theorem. Searches above found no existing
specialized declaration or DAG node. The new node is cited by the item's added stmt_dep.


## Second reading by J1

I independently read the item node, both delivered modules, and the recorded dependency
nodes and their declaration bodies. I read the Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex at
`lemma-perfect-into-support-on-T` (Tag 08EJ), the chapter conventions, and the beginning
of the lifting-complexes section. The local literature checkout is absent. The source
has no standing base-field, characteristic, Noetherian, separatedness, or boundedness
assumption beyond those in the node. The node and Lean require no correction.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. An arbitrary scheme X is `(X : Scheme.{u})`. The recorded Mathlib `Scheme`
   extends a locally ringed space with an affine neighbourhood at every point;
   I opened its structure declaration, not merely its name.
2. Quasi-compactness is `[CompactSpace X]`; quasi-separatedness is
   `[QuasiSeparatedSpace X]`. These require qcqs, with no stronger separatedness
   or Noetherian hypothesis.
3. A global function f is the binder of type
   `RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})`.
   I opened `sectionsSubring`: its carrier consists of compatible sections of
   the ring presheaf. On this site every such family is determined by its top-open
   section, and conversely restriction produces a compatible family from any
   top-open section. Evaluation and restriction preserve ring operations, so this
   encoding includes precisely all global functions, including their powers.
4. T is the closed subset V(f); the Lean eliminates its determined name and uses
   `X.basicOpen (f.val (op ⊤))` for its complement. I opened `Scheme.basicOpen`
   and `mem_basicOpen`: this is the locus where the germ is a unit, exactly D(f).
   No closed-subscheme structure or independently chosen T is introduced.
5. E and E' belong to D_QCoh(O_X), and alpha is any morphism between them:
   `(E E' : schemeDerivedQCohCategory X) (α : E ⟶ E')`. The recorded
   `schemeDerivedQCohProperty` requires quasi-coherence of the homology sheaf
   in every integer degree, and `schemeDerivedQCohCategory` is its full
   subcategory in the recorded derived category of O_X-module sheaves.
   Thus `α.hom` is the same map under full inclusion, with no map constraint.
6. E is perfect: `(hE : X.IsPerfect E.obj)`. I opened the recorded
   `Scheme.IsPerfect` and `IsStrictlyPerfect`: at each point an open neighbourhood
   has a derived representative with finitely many nonzero terms, each a retract
   of a finite free module. The source is locally perfect; the statement does not
   choose an affine or globally bounded representative as extra input.
7. Every cohomology sheaf of E' vanishes off T: `hSupport` is `∀ i : ℤ, IsZero`
   of `SheafOfModules.overFunctor` applied to the homology sheaf of `E'.obj` on
   D(f). I opened the recorded homology definition and Mathlib's `overFunctor`,
   whose body is restriction via `Over.forget`. On opens this is restriction to
   the open subset; zero as a module sheaf is exactly vanishing there. The
   `IsZero` predicate is applied to a categorical module-sheaf object, not a bare
   stalk type. All degrees, including negative degrees, are covered.
8. For each such f, E, E', alpha and hypotheses, there exists a nonnegative
   exponent: `∃ n : ℕ`. This is precisely an integer n ≥ 0; n may depend on
   all the preceding data, with no asserted uniform exponent.
9. The conclusion is the equality
   `schemeDerivedScalar X (f ^ n) α.hom = 0` in the ambient derived Hom group.
   Full inclusion preserves and reflects this equality. I followed the new
   definition through the recorded `SheafOfModules.homLinear` / `homModule`
   to upstream `PresheafOfModules.sectionsSMul`, and through Mathlib's
   `DerivedCategory.instLinear` to `Localization.linear`. Its value is
   multiplication by the specified global function, localized canonically;
   there is no arbitrary action in the hypotheses.

The two `HasDerivedCategory.{w}` binders are the exact shared infrastructure
required by `schemeDerivedCategory` and the recorded local perfectness definition.
They supply localizations globally and on opens, not finiteness, boundedness, an
alternative abelian instance, or a chosen model for E or E'. Both universe levels
are explicit; there are no unbound variables or independent test-object universes.

Edge cases: the empty scheme is permitted (the neighbourhood condition in
perfectness is vacuous there); zero source, zero target and zero morphism are
permitted. Exponent zero is allowed. For f = 0 the support condition is on the
empty open and exponent one kills any map. For a unit f the support condition
makes every cohomology sheaf vanish globally. For nilpotent f its vanishing locus
is all of X and some positive power is zero. There is no nonempty index type,
fixed characteristic, field, positive-exponent, or target boundedness restriction.

Independent searches, using different phrases from the worker:

- msearch LeanFinder: "power of a section kills a derived category morphism whose
  target has cohomology supported on a principal closed subset". Eight results
  were generic projective/injective derived-map or cohomological-degree vanishing
  statements; none has this support-annihilation conclusion.
- msearch Loogle: `DerivedCategory, smul`. It rejected the identifier `smul`;
  this query supplies no evidence of absence.
- msearch grep `supported|annihilat|sectionsSubring` in
  Mathlib/Algebra/Homology/DerivedCategory: no hits.
- For the new definition, msearch LeanFinder: "linear structure on the derived
  category of sheaves of modules over the ring of compatible sections". This
  found `DerivedCategory.instLinear` and the linear localization functors, which
  the delivered definition already reuses. No specialized scheme declaration
  was found. msearch grep `Linear|SMul|scalar` in the corresponding Mathlib
  Linear file found the same generic infrastructure; I read the file in full.
- Direct rg of WeilConjectures and lean/Sheaf for
  `perfect.*support|support.*perfect|global.*(action|scalar)|derived.*(smul|scalar)|sectionsSubring`
  found the recorded sheaf-module action, upstream presheaf section actions,
  and unrelated coefficient-extension or derived-completeness material.
  I opened the upstream section-action bodies and the derived-completeness
  declarations: the latter concern constant coefficients and scalar-invertible
  objects, not this variable structure sheaf or this theorem.
- An independent scan of DAG titles and statements for global scalar/action
  and derived scalar/multiplication found coefficient-change and tensor-model
  notions, not a global-function action on this derived module-sheaf category.
  The existing non-derived action node is cited and used. The worker's logged
  LeanSearch attempts are unavailable and are not treated as successful searches.

New-node reading: `def-sc-derived-global-scalar` gives the scalar operation
appearing in Tag 08EJ. It specializes existing sectionwise and generic derived
linear infrastructure, without reconstructing either notion. No DAG node or
existing specialized declaration was found. Its objects, ring and conclusion
match its Lean definition; the definition has complete data and no sorry.
Its chapter, unit, creation fields, source, three search kinds, empty proof and
proof dependencies, null Mathlib match, and none-state audits meet §5. Its
blueprint ancestor is `lem-sc-finite-duality`, independently checked using
`tools/blueprint_refs.py ancestor`; the recorded via chain follows the item
and its ancestors. The item cites this new node. There are no dependency
modules requiring repair and no statement correction requiring citer review.

Docstrings retain the source and blueprint IDs. The theorem docstring follows
both node proof steps: affine finite-projective reduction by stupid truncation,
then qcqs Mayer–Vietoris induction. The only theorem in the delivery has proof
`sorry`; no result was proved. Line lengths and imports satisfy the conventions.
Both node `lean.statement` records match their file signatures.

Mismatches found: none. Changes: appended this independent second-reading report;
Lean, statement records and new-node metadata are unchanged. Both delivered
modules compiled together with scompile.py in dependency order on the server:
exit code 0, 2.5 seconds, no errors or warnings.
