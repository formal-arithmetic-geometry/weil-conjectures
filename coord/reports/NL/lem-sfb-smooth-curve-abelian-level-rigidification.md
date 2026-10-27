## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification` states
`AlgebraicGeometry.smoothCurveAbelianLevelRigidification`, with its proof exactly `by sorry`.
It also supplies three transparent helpers belonging to the statement's existing moduli
notion: the smooth category's base projection, the frame-forgetting based functor, and the
specified smooth pullback family. Their data are real constructions from the recorded
dependency; none contains a postponed proof or chooses a mathematical object by existence.
No new DAG node, dependency repair or statement correction is needed.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| g at least two | `(g : ℕ) (hg : 2 ≤ g)` |
| Prime ell at least three, different from char(k) | `ℓ : AbelianLevelPrime (Spec (.of k))`; its recorded definition requires `ℓ.val.Prime`, `3 ≤ ℓ.val`, and invertibility in every stalk of Spec k. For a field this is exactly nonzero image of ell, equivalently char(k) different from the prime ell. There is no extra restriction. |
| The existing unpointed smooth and level groupoids | `StablePointedModuli.Smooth (Spec (.of k)) g 0` and `AbelianLevelModuli (Spec (.of k)) g ℓ`. These are imported unchanged, including their geometric arithmetic-genus, connectedness, projectivity and frame conventions. |
| A scheme L representing the full level groupoid | `∃ L : Over (Spec (.of k)), ... IsRepresentedByScheme (BasedCategory.ofFunctor (AbelianLevelModuli.forget ...)) L`. This is an actual based equivalence from discrete h_L to the level category, retaining automorphisms. |
| L smooth and finite type | `Smooth L.hom ∧ LocallyOfFiniteType L.hom ∧ QuasiCompact L.hom`. Finite type uses the recorded conjunction, not an extra hypothesis on k or the test bases. |
| Every test scheme T and smooth projective geometrically connected genus-g family X/T | `∀ X : StablePointedModuli.Smooth ... g 0`. Its `X.obj.base : Over (Spec k)` varies freely. The bundled family is precisely the definition used by the node; projectivity here includes the projective-bundle convention explicitly specified in the moduli definition and proof. In particular it includes H-projective families, whose ambient projective space is a finite free projective bundle. No Noetherian, reducedness, separatedness or quasi-compactness condition is added to T. |
| H is the specified first direct image | Every occurrence is the dependency's `abelianLevelCohomology X.obj.projection ℓ.val`, namely R^1 of the constant coefficient module. |
| Locally constant free of rank 2g | An actual jointly surjective etale `Cover.{u}` and, on every member, `Nonempty ((Etale.upperStar ...).obj H ≅ abelianLevelConstant ... g ℓ.val)`. The latter is the recorded constant sheaf on `Fin (2 * g) → ULift (ZMod ℓ.val)`. Thus rank is exactly 2g, not merely finite or locally varying. |
| Compatible with arbitrary base change | For every `T : Over (Spec k)` and `a : T ⟶ X.obj.base`, `IsIso (abelianLevelBaseChange (IsPullback.of_hasPullback ...).toCommSq ℓ.val)`. This is the dependency's canonical degree-one exchange with constant-coefficient comparison, not an unspecified isomorphism. |
| The frame functor represented by a finite etale surjective T-scheme | `∃ (P : Over (Spec k)) (r : P ⟶ X.obj.base), IsFinite r.left ∧ Etale r.left ∧ Surjective r.left`, together with universal `frameP` on the specified pullback. For every `a : T ⟶ X.obj.base` and frame `α` on the specified pullback, the statement gives `∃! b : T ⟶ P, b ≫ r = a ∧ ...`. |
| The bijection is natural and uses pulled-back frames | The equation in `HomCondition` says exactly that pulling back `frameP` by the canonical constant comparison, inverse image and `abelianLevelBaseChange` yields `α`. Its arrow `q` must have base `b` and satisfy `q.hom.map ≫ pullback.fst ... r.left = pullback.fst ... a.left`. These equations determine the map between the actual pullbacks uniquely; no arbitrary comparison or arbitrary frame transport is substituted. Composing these canonical arrows and the frame equations gives restriction compatibility, so the universal-pair formulation expresses representation of the frame functor, not just unrelated pointwise cardinalities. |
| Every frame-preserving automorphism is identity | For every base `T`, every `Y : AbelianLevelModuli.Fiber ... T`, and every endomorphism `a : Y ⟶ Y`, `a = 𝟙 Y`. `Fiber` is the recorded core of the actual fibre category. Every family automorphism preserving a frame determines such an arrow. |
| The 2-fibre product is naturally equivalent to the discrete frame functor | The final existential gives a based classifier `t` for X and a based equivalence `e` from discrete h_P to `moduliTwoFiberProduct t (abelianLevelForgetSmooth ...)`, with `ModuliTwoIso` identifying its projection to h_T with the morphism induced by the same `r`. Since that same P represents frames, this is the asserted natural equivalence over h_T. The earlier `IsRepresentedByScheme` identifies the second factor with h_L, giving T times over M with L. |
| Actual family isomorphism, rather than coarse moduli equality | The classifier comes with `η : t.toFunctor ⟶ const X`, whose components are actual cartesian family arrows lifting the Yoneda test maps. The 2-fibre product is the dependency's full comma construction requiring its comparison to be an isomorphism over the identity. Thus each object has an actual family isomorphism to the pullback of X. No skeleton, isomorphism-class quotient or coarse-point set replaces this data. |
| No symplectic condition or rational frame | `abelianLevelConstant` and the full module-sheaf `Iso` are used unchanged. `frameP` is over the cover P, not an assumed section over T. |

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`,
  `StablePointedModuli.Smooth`, `.forget`, `.pullback`, `AbelianLevelPrime`,
  `abelianLevelCohomology`, `abelianLevelConstant`, `abelianLevelBaseChange`,
  `AbelianLevelModuli`, `.HomCondition`, `.forget`, `.Fiber`, and the category instances;
  `CategoryTheory.discreteModuli`, `IsRepresentedByScheme`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`, `discreteModuliMap`. Full signatures and docstrings,
  including frame-pullback coherence, were read.
* `Mathlib.Algebra.Field.Defs`: `Field`.
* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` (their conjunction is the node's finite type).
* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, the recorded
  projective-space convention; the moduli family itself uses its specified bundle convention.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; integral morphisms are not an
  asserted property here.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`; `.Smooth`: `Smooth`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections;
  `IsPullback.of_hasPullback` supplies their specified square.

Stated proof inputs are imported with plain `import`:
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`
(`Etale.hasTorsionBaseChange_of_isProper`),
`WeilConjectures.AlgebraicGeometry.Curve.Estimate`
(`IsConnectedCurve.sheafH_constantZMod_of_isProper`),
`WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`
(`Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`),
`WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable`
(`nonempty_inverseImage_representable_iso`), and
`Mathlib.CategoryTheory.Sites.Point.Basic`
(`GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso`).
The projective-bundle properness input is already publicly imported by the moduli module:
`Sheaf.TraceFormula.ProjectiveBundleProper`, `AlgebraicGeometry.projectiveBundle_proper`.
The remaining four proof-only nodes (smooth-proper local systems, level coarse moduli,
geometric faithfulness, and DM inertia) have no Lean records in the read snapshot; their
steps and node ids are retained in the complete proof-plan docstring. None is required to
type this statement, and no duplicate assertion of those independent nodes is made.

Edge cases checked before writing:

* T empty: the empty etale cover is allowed, P can be empty, and the unique frame between
  the unique module sheaves on the empty site is represented by that empty P. There is no
  `Nonempty P` or `Nonempty T` assumption; surjectivity over the empty base is correct.
* A nonempty T need not have a rational frame. Surjectivity of P is used, never a T-section.
* Nonreduced and non-Noetherian bases are quantified without restriction, including in
  the automorphism clause and all base changes.
* g = 2 and ell = 3 are included; g below two and ell = 2 are correctly excluded. In
  particular the hyperelliptic involution at level two is not erroneously declared trivial.
* Characteristic zero and characteristic two with an admissible odd prime are included.
  No primitive root of unity and no constant symplectic form is assumed.
* Every universe is bound (`universe u`, `autoImplicit false`); schemes and fields use u,
  coefficient modules use u+1 exactly as in the dependency, with its `ULift (ZMod ell)`.
  The cover's index universe is explicitly u; no smaller independently quantified test
  universe can make a geometric condition vacuous.
* The arrow q is forced by both fibre-product projections. Its cartesian condition is
  automatic for these canonical base changes, not an extra restriction on a frame.

Searches for an existing statement (2026-10-22):

* `msearch.py ... leansearch "Smooth curves genus at least two full abelian level rigidification finite etale frames"`:
  eight hits, on smooth morphisms and formally etale algebras; no moduli or rigidity theorem.
* `msearch.py ... leanfinder "Smooth genus g curves full abelian level structure fine moduli scheme frame finite etale cover"`:
  eight hits, on standard smooth rings, Weierstrass curves, and etale morphisms; no match.
* `msearch.py ... loogle "AbelianLevelModuli, IsRepresentedByScheme"`:
  zero hits (remote index does not know the project-specific identifier).
* `msearch.py ... grep "abelianLevel|AbelianLevel|level.*rigid" AlgebraicGeometry`:
  zero Mathlib hits.
* `rg -n 'abelianLevel|AbelianLevel|lem-sfb-smooth-curve-abelian-level-rigidification' lean/WeilConjectures lean/Sheaf`:
  the moduli dependency supplies definitions and its base-change lemma; the projective-level
  parameter module mentions this prerequisite only in its proof docstring. No existing
  theorem states this node. The upstream declaration index has no abelian-level match.
* Exact-name `rg` for all four proposed declaration names in Mathlib, `WeilConjectures`,
  `Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Primary source opened: https://arxiv.org/pdf/alg-geom/9501003, §1.1 (g at least two),
§2.3.3 (the actual full H1 frames and fine smooth scheme), Proposition 2.3.4 and
Remark 2.3.7. This agrees with the node. No `STATEMENT-DISPUTED` or node fault found.
The example module requested by the brief is now withdrawn on this checkout; its node
record and the current moduli and parameter modules supplied the module-mode conventions.

Validation: the module compiled cleanly on the prescribed server wrapper in both the
sandbox elaboration check and the final library module check. Only its named main theorem
is postponed. The final explicit-cover-universe version also passed both compiler checks and the server
preflight: `deliver2.py NL lem-sfb-smooth-curve-abelian-level-rigidification --no-push`
printed `OK (dry run)` at prepared commit `bd7b2dd8087`.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
