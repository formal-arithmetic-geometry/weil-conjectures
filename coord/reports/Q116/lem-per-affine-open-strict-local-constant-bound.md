## Worker report

The module `Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstantBound` states
`AlgebraicGeometry.Etale.isZero_cohomology_constant_affineOpen_of_quasiExcellent_strictlyHenselian`.
Its sole theorem has proof `sorry`; there are no new definitions, dependency repairs,
statement corrections, or disputed statements.

Source checked directly: ILO, Travaux de Gabber, Expose XV 1.2.4, printed p. 220
(PDF p. 226), together with 1.2.3, 1.2.5--1.2.6 and sections 2--3, pp. 219--224.
Corollary 1.2.4 says that for a strictly local quasi-excellent scheme of dimension d,
an affine open U, and an invertible n, H^q(U,Z/n) vanishes for q>d. This is exactly
the node. Its eight proof steps are included, with prerequisite ids, in the docstring.

Clause-by-clause correspondence:

- Scheme S: `(S : Scheme.{u})`.
- Strictly local: `[IsAffine S] [IsStrictlyHenselianLocalRing Γ(S, ⊤)]`.
  A strictly local scheme is the spectrum of a strictly henselian local ring;
  affineness here spells out that notion, and imposes no additional condition.
  The global sections formulation includes every such scheme, without choosing
  a presentation by a ring or an isomorphism.
- Noetherian: `[IsNoetherianRing Γ(S, ⊤)]`, equivalent to Noetherian S since S is affine.
- Quasi-excellent: `(hS : IsQuasiExcellent Γ(S, ⊤))`. This is the recorded ring
  predicate, with its Noetherian, G-ring, and J-2 clauses; no universal catenarity
  or excellence assumption has been added.
- Finite dimension e>=0: `(e : ℕ)` and
  `(he : ringKrullDim Γ(S, ⊤) = (e : WithBot ℕ∞))`.
  Spectrum dimension and ring dimension agree by the recorded dimension definition.
- Affine open U in S: `{U : Scheme.{u}} [IsAffine U] (j : U ⟶ S)
  [IsOpenImmersion j]`. This describes any open subscheme, up to its usual canonical
  isomorphism, and includes the empty one. No density or nonemptiness is required.
- Integer m>=1: `(m : ℕ) (hm : 1 ≤ m)`, which includes exactly the positive integers.
- Invertible on S: `(hunit : IsUnit (m : Γ(S, ⊤)))`, the global unit condition,
  equivalent to invertibility in every stalk. No prime or prime-power condition.
- Constant abelian sheaf on the ordinary small etale site:
  `(constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod m)))`.
  This is sheafification of the constant presheaf, not the constant presheaf itself.
  `ULift` only places the finite group in the site's prescribed coefficient universe.
- Nonnegative degree q and strict inequality: `(q : ℕ) (hq : e < q)`.
- Right-derived global-sections cohomology: apply
  `cohomology AddCommGrpCat.{u + 1} U (q : ℤ)` to the constant sheaf placed in
  degree zero by `DerivedCategory.singleFunctor _ 0`.
- Vanishing: `IsZero` of the resulting object of `AddCommGrpCat.{u+1}`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; scheme objects/morphisms and the affine interpretation.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` and the scheme/global-ring
  identification. `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`; this is a declaration of
  the recorded excellent-ring node, whose main record names `IsExcellent`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`,
  extending `HenselianLocalRing` with separably closed residue field.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: ordinary small-etale sheaves
  `Sheaf U.smallEtaleTopology AddCommGrpCat.{u+1}` as its recorded mixed interface.
  Its current source was read with `scompile.py --source` because the old source
  checkout lacks this module.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology`
  and its definition via `Etale.rightDerivedGlobalSections` and homology.

All proof dependencies with recorded modules are imported as non-public imports,
except those already publicly needed by the statement. The Mathlib-only local-completion, affine-qcqs, and quasi-compact-open finite-type
prerequisites are imported via `Mathlib.RingTheory.AdicCompletion.LocalRing`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, and
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (AffineScheme is already public).
Unstated proof nodes have no module to import. They do not obstruct stating this theorem.

Edge cases checked before writing: m=1 gives the zero coefficient group and is
allowed; m=0 is excluded exactly as in the node; composite m is included; e=0
requires vanishing only for positive q; q=e is intentionally not claimed; an empty
U is allowed and has zero cohomology; U=S is allowed and agrees with strict-local
acyclicity. A zero base ring cannot satisfy the strict-local class, matching the
existence of the closed point in a strictly local scheme. No irreducibility,
reducedness, completeness, or density condition has been imposed on S or U.

Searches for existing statements/notions:

- `msearch.py ... leansearch "Etale cohomology of constant finite sheaves vanishes
  above the dimension on an affine open of a strictly local quasi-excellent scheme"`:
  8 hits, smallEtaleTopology, Scheme.Etale, etaleTopology, Artinian dimension zero,
  etale locus and affine stalk facts; no matching vanishing theorem.
- `msearch.py ... leanfinder "Etale cohomology of a constant finite sheaf on an affine
  open of a quasi-excellent strictly henselian local scheme vanishes above its dimension"`:
  8 hits, affine-transition-limit and cotangent-complex vanishing facts; no match.
- `msearch.py ... loogle "IsStrictlyHenselianLocalRing, IsQuasiExcellent, Sheaf.H"`:
  no hits; index does not know the project-only strictly-henselian name.
- `msearch.py ... grep "affine.*[Ll]efschetz|strict.*local.*[Vv]anish|IsQuasiExcellent"`:
  no matching Mathlib theorem. Direct `rg` searched the same concept patterns in
  the source project's `WeilConjectures` and the shared `lean/Sheaf` directories.
- Source-project grep for this blueprint id: no result. The exact new declaration
  name was also searched in Mathlib, the source project, side modules, and
  `dag/lean_names_upstream.json`: no result.
- Side-source searches found `Sheaf.AlgebraicGeometry.AffineOpenStrictLocalCohomology`.
  It also uses right-derived cohomology, but assumes excellence and prime-power
  coefficients and allows arbitrary module sheaves. It is a related result, not
  the node's quasi-excellent constant-coefficient statement. Reusing it would add
  excellence and restrict moduli. `IsQuasiExcellent` already exists and is reused.

Validation: prescribed `scompile.py Q116 lem-per-affine-open-strict-local-constant-bound`
compiled both sandbox and library forms successfully (initially 3.5 seconds each;
with the final explicit Mathlib proof imports, 5.2 and 4.9 seconds), with no errors
or warnings. No direct Lean or Lake invocation was used.

## Second reading by Q116

I reopened the node and the completed Lean file and checked every binder and the
conclusion against the clauses above. The quasi-excellent predicate, positivity of
m, exact dimension e, unit condition, affine open immersion, arbitrary natural q>e,
constant abelian coefficient sheaf and right-derived cohomology all agree. In
particular this theorem does not silently use the stronger excellent-base hypothesis
of its related side-library theorem. No mismatch or edit was found in this rereading.
This is the dispatcher's single worker's own second pass; no independent worker or
sub-agent was started, as the task explicitly prohibits starting other agents. The
maintainer's independent review remains the delivery review.
