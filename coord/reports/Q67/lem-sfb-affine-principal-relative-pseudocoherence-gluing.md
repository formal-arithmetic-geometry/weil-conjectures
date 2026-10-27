## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceGluing`
states `AlgebraicGeometry.exists_affine_embedding_mPseudoCoherent_of_principal_cover`.
There is one theorem, with proof `sorry`, and no definitions or auxiliary theorems.
The item is unchanged except for its `lean` field. No statement correction,
new node, or dependency repair was required.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 09VE,
`lemma-glue-relative-pseudo-coherent`, implication (1) to (2), and Tag 09VC,
`lemma-relatively-pseudo-coherent`, giving its existential embedding formulation.
The full eight-step accepted DAG proof is carried in the theorem docstring,
including the repaired Laurent chart and the empty-scheme case. The false
polynomial-ring assertion at the end of the source proof is already repaired
in the accepted node proof; it does not affect this statement.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S | `{X S : Scheme.{u}}` |
| Both schemes affine | `[IsAffine X] [IsAffine S]` |
| Morphism f : X → S of finite type | `(f : X ⟶ S) [LocallyOfFiniteType f]`; `QuasiCompact f` follows by Mathlib's `isAffineHom_of_isAffine` and the `IsAffineHom` quasi-compactness instance, so no redundant quasi-compactness binder is added. |
| E in the unrestricted derived category of O_X-modules | `(E : schemeDerivedCategory X)`; no quasi-coherent predicate appears. |
| An arbitrary integer m | `(m : ℤ)` |
| Arbitrary cover index set I | `(I : Type v)` with independent universe `v`, without finite or nonempty assumptions. |
| Global sections b_lambda | `(b : I → Γ(X, ⊤))` |
| U_lambda = D_X(b_lambda), the invertibility locus | Every local source is `(X.basicOpen (b t)).toScheme`; Mathlib `Scheme.mem_basicOpen` says precisely that the section's germ is a unit. |
| The principal opens cover X | `hcover : (⨆ t : I, X.basicOpen (b t)) = ⊤` |
| For each lambda, some n_lambda ≥ 0 | `hlocal : ∀ t : I, ∃ n : ℕ, ...` |
| A local closed embedding into A^n_S | `∃ i : (X.basicOpen (b t)).toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S, IsClosedImmersion i ∧ ...` |
| The local embedding is over S | `i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = (X.basicOpen (b t)).ι ≫ f` |
| Local restrictions are derived pullbacks | `((derivedPullback (X.basicOpen (b t)).ι).obj E)` |
| Local derived pushforward is m-pseudo-coherent | `Scheme.IsMPseudoCoherent ... m ((schemeDerivedDirectImage i).obj ((derivedPullback ...).obj E))` |
| Some global n ≥ 0 and closed embedding | Conclusion `∃ n : ℕ, ∃ i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S, IsClosedImmersion i ∧ ...` |
| The global embedding is over S | `i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f` |
| Ri_* E is m-pseudo-coherent | Final conjunct `Scheme.IsMPseudoCoherent ... m ((schemeDerivedDirectImage i).obj E)` |

The universal `HasDerivedCategory.{w}` instance binder is the shared localization
infrastructure used by the recorded relative-pseudo-coherence definition, not a
geometric assumption: it supplies D(O_Y) for each scheme and every open occurring
in the formula. Both the scheme universe and localization universe remain explicit.
The `ULift.{u} (Fin n)` index is Mathlib's finite affine-space convention and retains n=0.
`set_option autoImplicit false` rules out any auto-bound variable.

Recorded statement dependencies used, after opening their full source declarations
and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; the quasi-compact part is automatic for
  morphisms of affine schemes, by `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory` on the shared `SheafOfModules` carrier.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-nagata-relative-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace`, with its canonical projection to S.
- `def-pc-derived-direct-image`:
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`,
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `def-sfb-m-pseudo-coherent-complex`:
  `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`,
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`.
- `def-pc-derived-pullback`: `WeilConjectures.AlgebraicGeometry.DerivedPullback`,
  `AlgebraicGeometry.derivedPullback`.

All eight statement modules are public imports. Recorded proof dependency modules
are plain imports: the Mathlib basic-open, ideal-span, finite-type, tilde,
ideal-sheaf and affine-scheme modules; the upstream tilde finite-limits,
pseudo-coherent complex, linear-equation localization, derived-direct-image
composition, open restriction and derived-pullback composition modules.
The two proof-only nodes `lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance`
and `lem-sfb-closed-pushforward-pseudocoherence` have no recorded declarations
in the read checkout; they remain named in the proof plan, with no speculative
imports. They are not prerequisites for stating this theorem.

Edge cases checked before writing and again after compilation:

- Empty index type: the supremum is bottom; the cover condition therefore allows
  exactly the empty scheme. The local hypothesis is vacuous as intended, and the
  global statement still asks for the empty scheme's closed embedding. No
  nonempty-source or nonzero-ring assumption occurs.
- Infinite and large index sets: `Type v` is independent of `u`, so arbitrary
  principal covers are retained; no finite-index instance occurs.
- Dimension zero: `Fin 0` is allowed locally and globally, giving A^0_S.
- Any positive, zero, or negative m: `ℤ` has no bounds in the theorem.
- Zero E and E with non-quasi-coherent cohomology: neither is excluded.
- Rings with nilpotents, zero divisors, and arbitrary characteristic: no
  reducedness, domain, Noetherian, regularity, or characteristic condition occurs.
- The actual local source-to-S map is the open inclusion followed by f, and both
  over-base equations use the canonical affine-space projection.

Searches for an existing statement (all performed with the prescribed Q67/item wrapper):

- LeanFinder: `A complex on an affine scheme has m pseudo coherent pushforward to polynomial space if this holds on a covering by basic open sets`.
  Eight hits, including `AffineTargetMorphismProperty.IsLocal.of_basicOpenCover`,
  `HasRingHomProperty.of_iSup_eq_top`, and `of_affine_open_cover`. These are
  locality results for morphism properties and affine-open predicates, not the
  asserted derived pushforward gluing theorem.
- LeanSearch: `Glue m pseudo coherence of derived pushforwards to affine space on a cover by principal open subsets`.
  Eight gluing hits on schemes and locally ringed spaces, including
  `Scheme.Cover.glueMorphisms`; none concerns derived pseudo-coherence.
- Loogle: `"pseudo_coherent"`: zero hits.
- Mathlib grep: `PseudoCoherent|pseudo_coherent|pseudoCoherent`, subdirectory
  `AlgebraicGeometry`: zero hits.
- Project/source `rg -n 'PseudoCoherent|pseudoCoherent|pseudo_coherent|lem-sfb-affine-principal-relative-pseudocoherence-gluing' lean/WeilConjectures lean/Sheaf`:
  existing absolute and ring pseudo-coherence tools and the shared m-pseudo-coherent
  and relative definitions, but no theorem gluing these polynomial embeddings.
- More focused `rg -n 'IsMPseudoCoherent'` in both algebraic-geometry source trees:
  the shared definition and its relative definition, plus unrelated approximation
  statements. None gives this theorem.
- `rg` for the item id in `lean/WeilConjectures`, and for the proposed full
  declaration in `lean/Sheaf`, `lean/WeilConjectures`, Mathlib and
  `dag/lean_names_upstream.json`: no match. The item-id source lookup therefore
  also found no existing declaration.

Compilation: the exact delivery file passed `scompile.py Q67
lem-sfb-affine-principal-relative-pseudocoherence-gluing <file>` in both sandbox
and library-module modes (22.5 s and 35.0 s). No errors or unexpected warnings.
No global or local direct build was run.

## Second reading by Q67

The dispatcher prohibits starting other agents, so this is a separate second
reading by the same worker, not a claim of an independent second agent review.
I reopened the node statement and final Lean signature, comparing each clause
with the table above. The affine hypotheses, finite-type condition, unrestricted
E, integer m, arbitrary universe v for I, global sections, exact principal opens
and their covering condition are present. Each local dimension and embedding
is existential inside the quantifier over t, the local embedding is explicitly
over S, and its argument is the canonical derived restriction followed by the
recorded derived direct image. The conclusion has a single global dimension and
closed embedding over S with precisely the requested m-pseudo-coherent
pushforward. Neither an arbitrary comparison map nor an extra quasi-coherence
hypothesis has entered the statement. I checked the automatic quasi-compactness
instances in Mathlib rather than adding a redundant binder. The universal
localization binder and finite-space ULift convention match the landed relative
notion. No statement mismatch was found and no correction was made. The source
proof's Laurent-ring error is already explicitly repaired in the DAG and is
faithfully retained in the docstring. The only postponed proof is the named
item theorem itself.
