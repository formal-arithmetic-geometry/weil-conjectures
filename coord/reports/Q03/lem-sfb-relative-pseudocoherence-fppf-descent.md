## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherenceFppfDescent` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_iff_fppf`. Its sole proof is
`sorry`, as required for stage 2. The node copy changes only `lean`. No new nodes,
dependency repairs or statement corrections are required.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 20630–20682,
Tag 0CSN, `lemma-relative-pseudo-coherent-descends-fppf`. Its statement is exactly
fixed-degree relative pseudo-coherence descent for a quasi-coherent derived object
and an fppf cover of the source of a locally finite type morphism. The docstring
reproduces all eight accepted DAG proof steps, with their input node IDs, including
the repaired refinement over X and the rank-independent splitting argument.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Work within the size convention | Explicit `universe u v w`; schemes in `Scheme.{u}`, arbitrary set `J : Type v`, derived categories with morphism universe `w`. The family `[∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` supplies the shared localization convention used by the relative predicate, including its affine charts. |
| Schemes X and B, morphism f : X → B | `{X B : Scheme.{u}} (f : X ⟶ B)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| Integer m | `(m : ℤ)`; the same parameter appears on both sides of the equivalence. |
| E in D(O_X) | `(E : schemeDerivedCategory X)` |
| Quasi-coherent cohomology sheaves | `(hE : schemeDerivedQCohProperty X E)`, which unfolds to `IsQuasicoherent` for the homology sheaf in every integer degree. This does not impose finite type or coherence. |
| A set J and maps p_j : X_j → X | `{J : Type v} (Xj : J → Scheme.{u}) (p : ∀ j : J, Xj j ⟶ X)` |
| Every p_j flat | `[∀ j : J, Flat (p j)]` |
| Every p_j locally of finite presentation | `[∀ j : J, LocallyOfFinitePresentation (p j)]` |
| Images jointly cover X | `hcover : ∀ x : X, ∃ (j : J) (y : Xj j), p j y = x` |
| Each X_j viewed over B by f ∘ p_j | `p j ≫ f`; Mathlib composes left to right. Local finite type follows by existing instances from local finite presentation and composition. No extra composite hypothesis is imposed. |
| E relatively m-pseudo-coherent iff every Lp_j* E is so | `IsMPseudoCoherentRelativeTo f m E ↔ ∀ j : J, IsMPseudoCoherentRelativeTo (p j ≫ f) m ((derivedPullback (p j)).obj E)` |
| No Noetherian, quasi-compactness, separation or global boundedness hypotheses | No such binders occur. The relative predicate has its own degree-dependent local charts, without a uniform boundedness hypothesis. |

Dependency declarations read and used:

- `def-weil-size-convention`: a metatheoretic convention; rendered by the explicit
  universe and shared `HasDerivedCategory` parameters, not by a duplicate definition.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-pc-morphism-conventions`: a convention pointing to the actual Mathlib
  morphism predicates. `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` supplies
  `LocallyOfFiniteType` and composition; `FinitePresentation` supplies
  `LocallyOfFinitePresentation` and its implication to local finite type;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat` supplies `Flat`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`
  and `schemeDerivedQCohProperty`, using the shared `SheafOfModules` category.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded pqf-def-coherent
  module publicly exposes `SheafOfModules.IsQuasicoherent`. The `hE` predicate
  uses exactly that notion. Its finite-type conjunction is deliberately not
  substituted for quasi-coherence. Also read the exported `RingedSpace.IsCoherent`
  signature and the Mathlib `IsFiniteType` and `IsQuasicoherent` declarations.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: read `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`. The precoverage is precisely the jointly-surjective
  precoverage for `Flat ⊓ LocallyOfFinitePresentation`. The theorem spells out
  these three conditions directly; it introduces no alternative covering notion.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsMPseudoCoherentRelativeTo`, the recorded fixed-degree predicate,
  and its all-integer counterpart `Scheme.IsPseudoCoherentRelativeTo`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, its transported derived-functor definition
  and its K-flat/exact-inverse-image specification. No arbitrary pullback is used.

All proof-dependency modules with recorded Lean declarations or Mathlib file
matches are imported non-publicly, except where already public statement inputs.
The relative flat-lfp, pullback, finite-pushforward, summand, source-locality,
all-affine-chart and composition proof nodes have no recorded module yet, so
there is no import for them; they are named in the complete proof docstring.
They are not prerequisites to elaborating this statement.

Edge cases checked before writing: `J` is not assumed inhabited or finite. For
an empty family, `hcover` forces the underlying source space empty; for empty X,
the relative predicate has only empty-preimage conditions and the right side is
vacuous when J is empty. An empty member is permitted in any cover. The identity
singleton cover specializes to invariance under identity derived pullback. Zero
derived objects, negative m, m = 0, arbitrary positive m, and complexes without a
global cohomological bound are allowed. The index universe v is independent of
u because this quantifies an actual covering family, not test objects in a
potentially empty smaller universe. The finite locally free proof in the
accepted plan splits by a unit coordinate, without dividing by the rank; residue
characteristic dividing the degree is not excluded.

Searches actually run on 2026-10-24 through the prescribed wrapper:

- LeanFinder: `Relative m pseudo coherence of derived complexes descends along
  fppf covering families of schemes`. Eight results concern scheme covers and
  affine-transition limits, including `Scheme.instOverXBind`,
  `Scheme.instOverBind`, and `Scheme.Cover.property_trans`; none is this theorem.
- Loogle: `"PseudoCoherent"`. Zero results.
- Mathlib grep: `pseudo.?coher|relative.*coheren`, subdirectory `AlgebraicGeometry`.
  One result, `Sites/SmallAffineZariski.lean:297`, is a docstring about relative
  gluing of a quasi-coherent algebra, not relative pseudo-coherence.
- LeanSearch: `Relative m pseudo coherence of a quasi coherent derived complex
  is local for fppf covers`. Eight results concern quasi-coherent-data recursors,
  `SheafOfModules.IsQuasicoherent`, finite presentation, and
  `CategoryTheory.ObjectProperty.IsLocal.mk`. None states this theorem.
- `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `pseudocoheren.*fppf|PseudoCoheren.*[Ff]ppf|[Ff]ppf.*PseudoCoheren|lem-sfb-relative-pseudocoherence-fppf-descent`:
  no matches. A second search for the proposed declaration and module in these
  trees and `dag/lean_names_upstream.json` also found no match.

No STATEMENT-DISPUTED issue or node fault was found. The source proof has the
already-repaired refinement-base typo; the node statement itself needs no change.

Validation: the prescribed `scompile.py` compiled this delivery in sandbox and
library module mode, cleanly (1.8 s and 1.9 s on the initial pass). After finalizing imports, `deliver2.py --no-push` compiled both module paths
and printed `OK (dry run): commit 722f99d26a8 passes the preflight and compiles;
nothing pushed`. The final delivery wrapper reruns those checks.

## Second reading by Q03

This is a separate self-review pass, not a claim of an independent second agent:
the dispatch brief prohibits starting agents and assigns independent review to
the maintainer. Reopened the node, dependency predicate definitions and completed
module. Checked each row of the correspondence table against the signature.
The left predicate is the fixed-degree definition, and its right counterpart
uses the same m and the composite to the same base B; no pseudo-coherence in all
degrees replaces it. The complex is quasi-coherent in cohomology only. The three
cover hypotheses express exactly flatness, local finite presentation and joint
surjectivity, without requiring individual surjectivity, quasi-compactness,
a finite family or nonemptiness. No discrepancy was found. Made Flat and
LocallyOfFinitePresentation explicit public imports because the signature uses
them; all remaining proof-only imports retain ordinary visibility.
