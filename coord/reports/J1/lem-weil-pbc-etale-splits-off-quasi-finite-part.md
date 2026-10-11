## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart` states
`AlgebraicGeometry.exists_etale_splits_off_quasiFinitePart`, with one `sorry` proof.
No definition, dependency module, or new node is needed. The node is unchanged except
for `lean`. Its statement agrees with Stacks Project, More on Morphisms,
Lemma 37.41.6, [Tag 02LP](https://stacks.math.columbia.edu/tag/02LP), read on the
Stacks website because the literature checkout is absent on this machine.

Hypotheses and clauses, in order:

- Schemes and their morphism: `{X S : Scheme.{v}} (f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`.
- Separated: `[IsSeparated f]`, the closed-immersion condition on the diagonal.
- Chosen point: `(s : S)`.
- At most finitely many isolated points of the scheme fibre:
  `Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}`.
  An isolated point means precisely an open singleton, as the node specifies.
- Existential scheme, étale morphism, and pointed neighbourhood:
  `∃ (U : Scheme.{v}) (φ : U ⟶ S) (u : U), Etale φ ∧ φ u = s`.
- The *induced* residue-field map is an isomorphism:
  `IsIso (φ.residueFieldMap u)`. Its source is `S.residueField (φ u)`,
  identified with `S.residueField s` by the preceding equality. This is the actual
  induced map, rather than the existence of some unrelated field isomorphism.
- Fibre product `U ×_S X`: `pullback φ f`, with projection `pullback.fst φ f` to `U`.
- Two open subschemes forming a disjoint exhaustive decomposition:
  `∃ (W V : (pullback φ f).Opens), IsCompl W V`. Complementarity in the lattice of
  opens means disjointness and union equal to top. Each is thus also closed;
  the opens coerce to their canonical open subschemes, not arbitrary schemes.
- Finite composite from `V` to `U`: `IsFinite (V.ι ≫ pullback.fst φ f)`.
- The scheme-theoretic fibre of `W → U` has no isolated points:
  `∀ w : (W.ι ≫ pullback.fst φ f).fiber u,
  ¬ IsOpen ({w} : Set ((W.ι ≫ pullback.fst φ f).fiber u))`.
- The final “in particular” is attached to the same witnesses:
  `(f ⁻¹' ({s} : Set S)).Finite → IsEmpty ((W.ι ≫ pullback.fst φ f).fiber u)`.
  This says the fibre is empty. The node's equivalent wording “no point of W maps
  to u” follows from the canonical `Scheme.Hom.fiberHomeo` onto the set-theoretic
  fibre; it is not a separate additional condition.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (through the imports).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (through `Fiber`).
- `def-weil-pbc-scheme-conventions`: a convention record naming the existing
  `AlgebraicGeometry.IsSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Separated`;
  this node explicitly defines no separate notion and needs no dependency module.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `Mathlib.AlgebraicGeometry.Fiber`; `fiberHomeo` justifies the empty-fibre wording.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`
  (through `Fiber`).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (through `Fiber`).
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- Open subschemes and their inclusions use `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι`, `Mathlib.AlgebraicGeometry.Restrict` (through the imports).

Edge cases checked before writing: no isolated points allows `V = ⊥` and `W = ⊤`;
an empty original fibre allows an empty remaining fibre; `X` may be empty;
`S` empty provides no `s` and the universally quantified statement is vacuous.
A finite fibre is discrete for a locally finite type morphism, so the final clause
is compatible with the preceding clause. Positive-dimensional fibres without
isolated points are allowed. No quasi-compactness, Noetherian, affine, finite-type,
nonempty-scheme, algebraically closed residue field, or characteristic hypothesis
is imposed. The explicit universe `v` is arbitrary, and all binders are explicit.
The module docstring contains the eight proof steps of the DAG, including the
empty union case. No statement dispute or node fault was found.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "etale neighbourhood splits a separated locally finite
  type scheme morphism into a finite open part and an open part whose fibre has no
  isolated points"`: eight hits on étale loci and étale composition properties;
  none states this splitting.
- `msearch.py ... loogle "AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt"`:
  one hit. Read the full declaration in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`.
  It handles one quasi-finite point, gives no elementary residue-field condition,
  and gives no condition on the complementary fibre. It is not the node's statement.
- `msearch.py ... grep 'isolated|exists_etale_isCompl|splits.off' AlgebraicGeometry`:
  only the weaker theorem above and its use in Zariski's main theorem.
- `msearch.py ... leansearch "etale elementary neighbourhood splitting finite open
  part no isolated points fibre"`: service unavailable, Internal Server Error.
- `rg -n 'isolated|splits.off|exists_etale_isCompl|lem-weil-pbc-etale-splits-off-quasi-finite-part'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures
  /home/ubuntu/weil-conjectures-sheaf-J1/lean/Sheaf`: unrelated comments and ring-theory
  splitting files only; no exact statement.
- Searched the chosen full declaration name in `dag/lean_names_upstream.json`,
  Mathlib, `WeilConjectures`, and `lean/Sheaf`: no collision.

Validation: `scompile.py J1 lem-weil-pbc-etale-splits-off-quasi-finite-part` on the
module succeeded on the server in 1.7 seconds, exit code 0, without warnings.

## Second reading by J1

I read the node and the module signature side by side. The Lean binders render
the node's objects and hypotheses as follows, in order: schemes `X S : Scheme.{v}`;
a morphism `f : X ⟶ S`; instances `[LocallyOfFiniteType f]` and
`[IsSeparated f]`; a point `s : S`; and the finite set of isolated fibre points
`Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}`. No hypothesis is
added or omitted. The conclusion introduces `U : Scheme.{v}`, `φ : U ⟶ S`, and
`u : U`, with `Etale φ`, `φ u = s`, and `IsIso (φ.residueFieldMap u)`; this is
the induced residue-field map required for an elementary étale neighbourhood.
It then introduces `W V : (pullback φ f).Opens`, states `IsCompl W V`, states
finiteness of `V.ι ≫ pullback.fst φ f`, states for every point of the fibre of
`W.ι ≫ pullback.fst φ f` over `u` that its singleton is not open, and finally
states `(f ⁻¹' ({s} : Set S)).Finite → IsEmpty ((W.ι ≫ pullback.fst φ f).fiber u)`.
Each clause matches the node, including quantifier order and the final
in-particular implication.

Edge cases were checked: the isolated-point set may be empty (so `V` may be
empty and `W` may be the whole pullback); `X` or the relevant fibre may be
empty; the finite-fibre implication can conclude an empty `W` fibre; and the
universe `v` is unrestricted. There is no hidden Noetherian, quasi-compact,
affine, characteristic, nonempty-scheme, or algebraic-closure assumption.

I searched Mathlib, the slopmaster2 source, and this project's `lean/Sheaf`
tree by the concepts “isolated fibre points”, “étale splitting”, “02LP”, and
`exists_etale_isCompl_of_quasiFiniteAt`, using LeanSearch/LeanFinder/Loogle and
`rg`. The only related declaration is Mathlib's weaker one-point
`AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`; it lacks the
elementary residue-field isomorphism and the no-isolated-points conclusion, so
the present declaration is not a duplicate.

No mismatch was found and no source or node correction was needed. The module
was compiled with `scompile.py`; its sole proof remains the required `sorry`.
