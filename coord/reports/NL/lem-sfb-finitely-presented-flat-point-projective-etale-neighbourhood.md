## Worker report

The module states Stacks flat.tex Tag 05ME, with one theorem and its proof postponed by `sorry`.
The source statement and full proof were read at lines 5662–5731. The node's statement is
unchanged. No new definition or dependency repair is needed.

Clause-by-clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; the arbitrary explicit universe
  does not require a field, Noetherian base, affine source or separated morphism.
- Local finite presentation: `[LocallyOfFinitePresentation f]`, without requiring global
  finite presentation of f.
- The quasi-coherent sheaf: `(G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]`.
  Finite presentation is `[SheafOfModules.IsFinitePresentation.{u} G]`; this is over O_X,
  and is not finite presentation or finite generation over the base's global ring.
- The point is `(x : X)`; the named s of the prose is directly `f x`.
- Flatness ONLY at x: `hflat` is `Module.Flat (S.presheaf.stalk (f x))` on the module
  obtained by `ModuleCat.restrictScalars (f.stalkMap x).hom` from
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G`. This uses the actual local
  ring map and does not assume that G is flat at other points.
- The affine elementary etale base neighbourhood is the existential `S'`, `e`, `s'`, with
  `IsAffine S'`, `Etale e`, `e s' = f x`, and `IsIso (e.residueFieldMap s')`. The last
  condition concerns the INDUCED residue-field map, rather than an arbitrary field iso.
  Its source is kappa(e(s')), canonically kappa(s) through the preceding equality.
- The source neighbourhood is `W : (pullback f e).Opens` with `IsAffineOpen W`. Opens carry
  their actual open subscheme and inclusion; no arbitrary immersion or source chart is used.
- Its marked point `z` has `(pullback.fst f e) z = x` and `(pullback.snd f e) z = s'`,
  and `z ∈ W`. The point above this pair is unique because the elementary residue extension
  is an isomorphism: the tensor of kappa(x) with kappa(s') over kappa(s) is kappa(x),
  whose spectrum is a singleton. Existence of z and its membership thus express precisely
  containment of the unique point, without adding an independent uniqueness theorem.
- Sections of the restricted pullback are
  `Γ((Scheme.Modules.tensorPullback (pullback.fst f e)).obj G, W)`. Evaluation on W is the
  sections of the restriction to W, so a second pullback/restriction construction is unnecessary.
- Projectivity is `Module.Projective Γ(S', ⊤)` on exactly those sections. The explicit
  `Module.compHom` uses `(pullback.snd f e).appTop` followed by restriction from the
  pullback's top open to W. Thus the scalar action is induced by W -> X ×_S S' -> S'.
  There is no `Module.Finite`, finite-rank basis or finite-projectivity hypothesis/conclusion.

Recorded dependency declarations used (their docstrings and full signatures were read):

| Node | Module | Declaration used |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType | publicly exposed SheafOfModules.IsQuasicoherent |
| def-weil-pbc-module-finite-type-presentation | Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators and Quasicoherent | SheafOfModules.IsFinitePresentation |
| def-pc-scheme-module-flat-over | WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic | IsFlatOver's documented equivalent stalkwise condition, expressed directly at x |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale | AlgebraicGeometry.Etale |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField | Scheme.residueField, Scheme.Hom.residueFieldMap |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, Mathlib.AlgebraicGeometry.Pullbacks | pullback, pullback.fst, pullback.snd and Scheme pullback existence |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | publicly exposed Scheme.Modules.tensorPullback |
| def-weil-pbc-projective-module | Mathlib.Algebra.Module.Projective | Module.Projective |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme, AffineScheme | IsAffine (the source's being isomorphic to an affine spectrum) |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | canonical Scheme.Opens open subscheme, IsAffineOpen |

The existing `RingedSpace.moduleStalkFunctor` is imported from
WeilConjectures.Algebra.Homology.ModuleStalkFunctor. All recorded proof dependencies with
available declarations are imported privately, or already publicly as statement dependencies.
The following proof dependencies have no Lean declaration on the read base and are omitted
from imports, rather than from the natural-language proof or DAG:
lem-sfb-flat-point-projective-etale-source-chart; lem-a1-map-over-base-finite-presentation;
lem-sfb-affine-flat-fp-projectivity-purity; def-sfb-scheme-relative-purity;
lem-sfb-scheme-etale-assassin-invariance; lem-sfb-flat-fp-purity-open.
They are proof inputs only, and supply no missing notion of the present statement.

Edge cases checked before writing:

- If X or S is empty, the binder x supplies the needed inhabited point or makes the
  statement vacuous. W is nonempty through z, as required by the prose.
- G = 0 is allowed: its stalk is flat and its zero sections are projective.
- No finite-rank restriction: on affine space over a field, O_X has polynomial-ring
  sections, generally of infinite vector-space dimension; the conclusion still applies.
- The theorem works at arbitrary, including nonclosed, x and f(x), with arbitrary residue
  fields; the elementary residue condition gives uniqueness of z for these points too.
- No global-flatness strengthening, and no Noetherian or separatedness assumptions.
- All schemes and module sections use the arbitrary u of the existing project interfaces;
  no additional equality between independent site universes is imposed.

Searches for existing statements (the wrapper's raw results are in searches.jsonl):

- LeanFinder: “A finitely presented quasi coherent sheaf flat at a point has projective
  sections on an affine open after an elementary etale base neighborhood”: 8 hits,
  including Module.Flat.projective_of_finitePresentation, flat morphism criteria and
  sheaf presentation data. None states the etale-neighbourhood theorem. The algebra
  theorem requires finite presentation over the base ring and does not apply here.
- Loogle: `"Projective", "IsFinitePresentation"`: 0 hits.
- LeanSearch: “finitely presented flat quasi coherent sheaf projective sections etale
  affine neighborhood”: 8 hits, all sheaf finite-presentation infrastructure.
- msearch grep `projective.*neighbou?r|neighbou?r.*projective` in Mathlib/AlgebraicGeometry:
  0 hits.
- rg of that concept, pointwise flatness, and the exact node id in lean/WeilConjectures
  and lean/Sheaf: found the henselian finite-type FREE-neighbourhood theorem (05MF)
  and pointwise module-flatness infrastructure; none is the present 05ME statement.
- The proposed declaration name was searched in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no existing declaration.

No STATEMENT-DISPUTED issue or statement correction.

## Second reading by NL

A separate rereading pass by the assigned worker compared the node and final signature;
no other agent was started, as the dispatch brief explicitly prohibits that. The maintainer's
independent review remains the independent second reader. The rereading checked all clauses
in the correspondence above, especially local (not everywhere) flatness, the induced residue
map, the two actual pullback projections, affine-open containment, and projectivity with the
base-ring scalar action. Explicit universes on the sheaf predicates and the argument order of
@Module.Projective were corrected after the first compile. No mathematical statement changed.

Validation: scompile.py compiled both the sandbox and library module cleanly. The required
`deliver2.py --no-push` returned OK: commit c2828bece14 passes preflight and compiles.
The actual delivery wrapper is run after this successful dry run.
