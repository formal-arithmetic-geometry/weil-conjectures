## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherenceComposition` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_comp_iff`, with `sorry` as its
only proof. It defines no new notion. The node copy changes only `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-composition-relative-pseudo-coherent` (Tag 09UT), statement and proof,
lines 17234 onward. Its arbitrary object of D(O_X), integer degree and structure-sheaf
hypothesis agree with the DAG statement. The proof docstring expands all five DAG proof
steps, including the exact closed-pushforward comparison on arbitrary complexes.

Clause-by-clause rendering:

- Schemes X, Y and S: `{X Y S : Scheme.{u}}`.
- The composable morphisms X → Y → S: `(f : X ⟶ Y) (g : Y ⟶ S)`;
  X → S is the actual composite `f ≫ g`, so there is no additional compatibility datum.
- Local finite type of f, Y → S and X → S: `[LocallyOfFiniteType f]`,
  `[LocallyOfFiniteType g]`, `[LocallyOfFiniteType (f ≫ g)]` respectively.
- O_Y[0] pseudo-coherent relative to S: `hY : IsPseudoCoherentRelativeTo g (...)`.
  Here `SheafOfModules.unit (moduleRings Y.toRingedSpace)` is the structure module;
  `(DerivedCategory.singleFunctor (SheafOfModules.{u}
  (moduleRings Y.toRingedSpace)) 0).obj` places that module in degree zero in D(O_Y).
  The predicate quantifies over every integer approximation degree, with independent
  existential affine charts in each degree, exactly as the dependency defines it.
- Every integer m: `(m : ℤ)`, including zero and negative integers.
- Every E in D(O_X): `(E : schemeDerivedCategory X)`, the full unbounded derived category.
- E m-pseudo-coherent relative to Y: `IsMPseudoCoherentRelativeTo f m E`.
- If and only if E m-pseudo-coherent relative to S:
  `↔ IsMPseudoCoherentRelativeTo (f ≫ g) m E`.
- No quasi-coherence or Noetherian hypothesis: neither is present. In particular E does
  not lie in the full subcategory `schemeDerivedQCohCategory`.

The explicitly bound universe variables are `u w`; `set_option autoImplicit false`
forbids accidental binders. The family
`[∀ T : Scheme.{u}, HasDerivedCategory.{w}
(SheafOfModules.{u} (moduleRings T.toRingedSpace))]` is exactly the infrastructure binder
of the recorded relative-coherence definitions. It supplies the shared localization for
all schemes occurring in affine charts; it imposes no geometric assumption or equality
between u and w.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; read their signatures and docstrings.
- `def-pc-morphism-conventions`: convention record, used through
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; read its all-affine-pairs signature/docstring.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`; read its full signature and docstring.
- `def-sfb-relative-pseudo-coherent-complex`:
  `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`,
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo` and
  `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`; read both complete definitions
  and docstrings. The module uses them directly, without replacements.

All four statement dependencies are public imports (the convention is represented by
FiniteType). Recorded, available proof dependencies are plain imports:
FiniteType (already public), ClosedImmersion, AffineSpace, Flat (the polynomial-projection
Mathlib match), DerivedPullback, PseudoCoherentComplex,
ClosedImmersionPushforwardExact, SchemeDerivedDirectImage, and
ClosedPushforwardPseudoCoherence. The relative-definition module is already public.
`lem-sfb-relative-pseudocoherence-all-affine-charts` and
`lem-sfb-relative-pseudocoherence-flat-base-change` have no recorded Lean declarations
or Mathlib matches at inspection time; their future proof imports remain for the
maintainer. They are not needed to state the present theorem. No import cycle was found.

Edge cases checked before writing:

- Empty X: the relative conditions are vacuous on source points, with the usual affine
  covers on the bases. No nonempty assumption is introduced.
- Empty Y or S: existence of the indicated morphisms forces the corresponding sources
  empty where necessary; there is no exception or chosen point in the signature.
- Zero E and zero rings: no nonzero, nontrivial or rank assumption occurs; the shared
  definitions allow rank-zero affine-space embeddings and approximation complexes.
- m = 0, m negative, and arbitrarily large m: m is unrestricted in ℤ, and the base
  structure-sheaf hypothesis is all-degrees pseudo-coherence, not just one finite stage.
- Identity f or g: the actual composite is used; identities are allowed. Arbitrary
  unbounded E and schemes without Noetherian hypotheses are retained.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A complex on X is m pseudo coherent relative to Y if and
  only if relative to S when O_Y is pseudo coherent relative to S"`: 8 hits, about
  module pullback pseudofunctors and local morphism-property descent; none is this theorem.
- `msearch.py ... loogle '"PseudoCoherent"'`: 0 hits.
- `msearch.py ... grep 'relative.*[Pp]seudo|[Pp]seudo.*[Cc]oher'`: 3 unrelated
  pseudometric/bicategory-coherence hits, no theorem about relative pseudo-coherence.
- `msearch.py ... leansearch "Relative pseudo coherence of complexes is unchanged by
  composition with a pseudo coherent scheme morphism"`: 8 hits on ordinary module
  pushforward composition and morphism properties; none is the derived equivalence.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `PseudoCoherentRelativeTo|pseudoCoherent.*comp|pseudoCoherent.*Comp|pseudocoherence-composition`:
  the relative definitions, the closed-support relative theorem and the separate ring
  predicate occur; none states composition with a relatively pseudo-coherent base.
- `grep -rn 'lem-sfb-relative-pseudocoherence-composition' lean/WeilConjectures`: no match.
- `rg 'isMPseudoCoherentRelativeTo_comp_iff'` over Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no collision with the new declaration name.

No statement fault, correction, dependency repair or new definition node is needed.
The only postponed proof is the theorem associated with this item.

Validation: `scompile.py N0 lem-sfb-relative-pseudocoherence-composition` with the delivered
module succeeded in sandbox and library modes (2.2 s and 2.1 s), without errors or
unexpected warnings. Dry-run and delivery results are recorded below after execution.

## Second reading by N0

Author's separate self-check; independent review is the maintainer's responsibility
under the dispatcher's instructions, and no second agent was started. Reopened the node,
the two relative predicates and the final module. Checked each of the three local-finite-type
assumptions against the corresponding arrow, the degree-zero structure module in hY,
the unrestricted integer m and arbitrary derived object E, and both sides and orientation
of the equivalence. The same E and m occur on both sides; only f versus f ≫ g changes.
The all-degrees hypothesis is on O_Y[0] over g, not on E. No quasi-coherence, finite
presentation, separatedness, flatness or boundedness was added. The global derived-category
binder is the dependency's existing interface. No mismatch was found or change needed.

Dry run: `deliver2.py N0 lem-sfb-relative-pseudocoherence-composition --no-push`
printed `OK (dry run): commit 5c357c0881a passes the preflight and compiles; nothing pushed`.
