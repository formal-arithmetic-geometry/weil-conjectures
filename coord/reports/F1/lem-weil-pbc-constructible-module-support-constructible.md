## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSupport` states
`AlgebraicGeometry.Scheme.constructibleEtaleModuleSupport`, with a single `sorry`
proof and no new definitions. The declaration docstring carries all six proof steps
of the DAG node, with their supporting node names. No statement correction is needed.

Hypotheses and clauses, matched individually:

- The scheme is `X : Scheme.{u}`. Quasi-compactness is `[CompactSpace X]`, and
  quasi-separatedness is `[QuasiSeparatedSpace X]`; these are the underlying-space
  versions of the scheme conventions, not stronger separation assumptions.
- The finite commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[Finite Λ]`. No nonzero-ring or characteristic restriction is imposed.
- The sheaf of constant-coefficient modules is
  `G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. This is the encoding used
  by the recorded constructibility dependency, and explicitly accepted by the mixed
  `def-weil-pbc-etale-sheaves` record (the constant-ring `SheafOfModules` encoding
  coexists with this one; their comparison is stage 3).
- Constructibility is precisely `hG : IsConstructibleEtaleModuleSheaf G`, with the
  dependency's finite locally closed constructible stratification and finite module
  trivializations, not the source's alternate constructibility predicate.
- The underlying abelian sheaf is the local `let F := ...`, obtained by
  `sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat Λ) AddCommGrpCat)`.
  No independent sheaf or comparison hypothesis is introduced.
- The support formula is the existing `etaleSheafSupport F`, whose body is
  `{x | ∃ Ω, ∃ Field Ω, ∃ IsAlgClosed Ω, ∃ s : Spec Ω ⟶ X,
    s default = x ∧ ¬ IsZero ((pointSmallEtale s).sheafFiber.obj F)}`.
  The landed node `def-kun-support` is added to `stmt_deps` to cite this definition.
  Its support declaration is general in X (no field or finite-type hypotheses).
- Clause (i), its first assertion, is the first conjunct: for every `x`, both
  algebraically closed fields and both morphisms `s`, `s'`, their image equalities
  `s default = x` and `s' default = x` imply an iff between the two `IsZero` stalks.
  Both geometric-point fields are independently quantified.
- Clause (i), its consequence, is the second conjunct: for every geometric point
  `s` over `x`, an `IsZero` stalk implies `x ∉ etaleSheafSupport F`.
- Clause (ii) is the last conjunct,
  `Topology.IsConstructible (etaleSheafSupport F)`, using the exact recorded
  Mathlib constructible-subset predicate, with retrocompact open generators.
  Categorical `IsZero` of an abelian group is exactly the trivial-group condition.

Dependencies read and used:

- `def-weil-pbc-scheme-conventions`: convention record; no declaration to import.
  The needed underlying properties are `CompactSpace` and `QuasiSeparatedSpace`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: the module-sheaf convention in the record;
  imported transitively by `EtaleSupport`, with the accepted ModuleCat encoding above.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, read as the general
  ring-sheaf category behind the conventions; its constant-ring encoding is not
  the input of the recorded constructibility predicate.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`, identifying
  the geometric-point morphisms with points and residue-field maps; the theorem
  uses the equivalent morphism form, `[Field Ω] [IsAlgClosed Ω]`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`;
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`. These are
  exactly the geometric stalk dependency's recorded declarations.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- Added landed dependency `def-kun-support`, module
  `Sheaf.AlgebraicGeometry.EtaleSupport`, declaration `Scheme.etaleSheafSupport`.
- Mathlib `CategoryTheory.sheafCompose` (Sites/Whiskering) and `forget₂`
  (ModuleCat/Basic) give the underlying abelian sheaf without sheafification.

Source checked: local Stacks checkout text at
`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`, lines 3416ff (04FN),
3984ff and Definition support (04FS), and 11867ff (09YS(3)). The repository's
literature copy is absent on this machine. 09YS assumes qcqs and a Noetherian
coefficient ring; the node's finite ring satisfies this. The source states the
isomorphism class of the stalk over a point is well defined before 04FS.

Edge cases checked: the empty scheme has no points or geometric-point maps, and
empty support is constructible; the zero sheaf and the zero coefficient ring give
zero stalks and empty support; a nonzero constant module gives full support on a
nonempty scheme. No connectedness, nonemptiness, finite-type or Noetherian-scheme
hypothesis is added. The empty stratification on the empty scheme is allowed by
the dependency. Universe u is arbitrary; geometric-point fields lie in u as in
Mathlib's `pointSmallEtale` and the landed support definition. Any larger-universe
instance can be considered after increasing u (schemes and sheaves can be lifted).

Searches performed (2026-10-11):

- msearch LeanSearch, "support of a constructible etale sheaf of modules is a
  constructible subset": UNAVAILABLE, Internal Server Error. No verdict from this
  unavailable service.
- msearch LeanFinder, "support of a constructible etale sheaf of modules is
  constructible and vanishing stalk is independent of geometric point": 8 hits,
  including `RingedSpace.exists_res_eq_zero_of_germ_eq_zero`,
  `Algebra.etaleLocus_eq_compl_support`, and `exists_of_res_zero_of_qcqs`.
  None states this theorem; these concern ringed-space germs or ordinary modules.
- msearch Loogle, `Topology.IsConstructible, "stalk"`: 0 hits.
- msearch grep, `support|IsConstructible`, Mathlib `AlgebraicGeometry/Sites`: 0 hits.
- rg over project `WeilConjectures/ConstructibleSheaf` for support, sheafCompose,
  forget₂: no existing support theorem. Broader source search for support and
  constructibility together found unrelated blowup/curve/derived-stability comments.
- rg for the exact item id in WeilConjectures: no match.
- rg over `lean/Sheaf` found `EtaleSupport.lean` with the reusable definition and
  `EtaleClosedImmersionEssentialImage.lean` using it, but no theorem stating the
  present constructibility assertion. Opened and read that definition in full.
- rg over `dag/lean_names_upstream.json`, lean/Sheaf and WeilConjectures for
  `etaleModule.*support|isConstructible_etale|support_constructible`: no collision.

Validation: server compilation of the complete module succeeded; a long docstring
line identified by the first compile was shortened. The final delivery dry run
printed OK: clean server compile and preflight pass except for the intentionally
pending independent second reading. Nothing was pushed; no second-reading section
was authored by this worker.

## Second reading by F1

I read the node statement and the Lean signature item by item. The scheme object is `X : Scheme.{u}` with `[CompactSpace X]` and `[QuasiSeparatedSpace X]`, matching the node's quasi-compact and quasi-separated hypotheses. The coefficient object is a finite commutative ring `Λ : Type (u + 1)` with `[CommRing Λ]` and `[Finite Λ]`; no nonzero, characteristic, Noetherian, or finite-type assumption is added. The sheaf object is `G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, matching the recorded module-sheaf encoding, and `hG : IsConstructibleEtaleModuleSheaf G` is the recorded constructibility notion.

The `let F := sheafCompose ... (forget₂ ...)` clause is exactly the underlying abelian sheaf required by the node. The support is the recorded `etaleSheafSupport F` definition, which quantifies algebraically closed residue fields and geometric-point morphisms. Clause (i)'s independence assertion is rendered by the first universal conjunct: two fields, their `Field` and `IsAlgClosed` instances, two morphisms `s` and `s'`, and the two equalities to `x`, followed by an iff of categorical `IsZero` stalk conditions. Its consequence is the second conjunct, which quantifies one geometric point and derives `x ∉ etaleSheafSupport F` from a zero stalk. Clause (ii) is the final `Topology.IsConstructible (etaleSheafSupport F)`. Quantifier order and conjunction nesting match the node.

Edge cases are covered: empty schemes and empty index/stratification data give empty support; zero coefficient rings, zero modules, and zero sheaves are allowed; nonempty constant nonzero modules can have full support; no connectedness, nonemptiness, characteristic, or Noetherian-scheme restriction is introduced. The universe convention is the same as the project declarations (`X : Scheme.{u}`, coefficient modules in `u + 1`, geometric fields in `u`).

I searched Mathlib, the source repository, and `lean/Sheaf` for support/constructibility and for the exact item or declaration; only the general `etaleSheafSupport` definition and unrelated support notions were found. LeanSearch was unavailable, while LeanFinder/Loogle and grep found no theorem with this statement. The dependency declarations and the support definition were opened and agree with their nodes.

No mismatch was found. The worker module already compiles cleanly with its single `sorry` proof, has no hollow definitions or extra declarations, and its node `lean.statement` is verbatim identical to the theorem signature. No source or Lean repair was needed.
