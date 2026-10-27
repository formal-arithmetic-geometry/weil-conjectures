## Worker report

The module `Sheaf.AlgebraicGeometry.ModelFibreAmpleOpen` states
`AlgebraicGeometry.Scheme.Modules.exists_affine_isAmple_of_limit_fiber`.
Its only theorem has proof `sorry`; it introduces no definitions or auxiliary
claims. The node's statement, statement dependencies, and accepted proof are unchanged.

Sources read: Stacks `more-morphisms.tex`, Tag 0D2S,
`lemma-ample-in-neighbourhood`, especially its proof's residue-field colimit,
finite-stage ampleness and Noetherian neighbourhood paragraph; and `coherent.tex`,
Tag 0D2N, `lemma-ample-in-neighbourhood`. The first source explicitly allows
separate affine transition systems for source and base. The second produces
relative ampleness; choosing an affine subneighbourhood gives the absolute
ampleness used by the node and its already recorded Noetherian dependency.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small nonempty directed partially ordered set is `{I : Type u}` with
  `[PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]`. It has least element
  `[OrderBot I]`; the node's label `0` is spelled `⊥`. The index type lives in
  the schemes' universe, as required by the recorded affine-limit interfaces.
- The inverse systems `Y_i` and `X_i` are `DY DX : Iᵒᵖ ⥤ Scheme.{u}`.
  The stage morphisms form `φ : DY ⟶ DX`. Its naturality states exactly
  `q_ji ≫ f_i = f_j ≫ r_ji`; functor laws supply the inverse-system laws.
- Properness of every `f_i` is `[∀ i : I, IsProper (φ.app (op i))]`.
- The two affine-transition hypotheses are `hYaff` and `hXaff`, quantifying
  over every `i ≤ j` and applying `IsAffineHom` to the corresponding diagram map.
- Each base is Noetherian through the two explicit instance families
  `IsLocallyNoetherian (DX.obj (op i))` and `CompactSpace (DX.obj (op i))`.
- The respective limits and projections are `cY : Cone DY`, `cX : Cone DX`,
  and their `π.app` components. `hcY : IsLimit cY` and `hcX : IsLimit cX`
  express unique factorization of every compatible cone from any scheme.
- The induced limit morphism is `f : cY.pt ⟶ cX.pt`; `hf` spells out
  `a_i ≫ f_i = f ≫ b_i` for every index. Together with the limit properties,
  this determines the induced morphism, without imposing a Cartesian stage square.
- The initial invertible module is
  `M₀ : (DY.obj (op (⊥ : I))).Modules` with `[M₀.IsInvertible]`.
  Every occurrence of `M_i` is expanded as
  `(tensorPullback (DY.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀`.
  Thus the statement uses the actual pullback, without extra module-family data.
- The invertible limit module is `M : cY.pt.Modules` with `[M.IsInvertible]`;
  `eM` is exactly the isomorphism from the pullback of `M₀` by `a_0` to `M`.
- The point is `x : cX.pt`; its image `x_i` is `cX.π.app (op i) x`.
- The limit fibre is `f.fiber x`, and its restriction is the tensor pullback
  along `f.fiberι x`. Hypothesis `hM` says this restriction is absolutely ample.
- The conclusion chooses a single `i` and a single `V : (DX.obj (op i)).Opens`.
  Its first two conjuncts are `x_i ∈ V` and `IsAffineOpen V`.
- The third conjunct is absolute `IsAmple` of the tensor pullback of the
  expanded `M_i` along `(φ.app (op i)).fiberι x_i`, on the actual scheme fibre.
- The fourth conjunct is absolute `IsAmple` of the pullback of that same `M_i`
  along `((φ.app (op i)) ⁻¹ᵁ V).ι`, on the whole open inverse-image subscheme.
- The existential `h` in each ampleness expression is a proof of invertibility
  required as an argument by the existing `IsAmple` definition. It adds no
  restriction: the modules in question are pullbacks of invertible modules.
  Proof irrelevance makes the choice of witness immaterial. This is the same
  packaging used by the recorded affine-limit ampleness theorem. No arbitrary
  map, replacement line bundle, or stronger geometric hypothesis is introduced.

Dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| pqf-def-affine-morphism | Mathlib.AlgebraicGeometry.Morphisms.Affine | AlgebraicGeometry.IsAffineHom |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | CompactSpace |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible | AlgebraicGeometry.Scheme.Modules.IsInvertible |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | tensorPullback; tensorPullbackSectionAdjunction |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | AlgebraicGeometry.Scheme.Hom.fiber; fiberι |
| def-weil-pbc-ample-invertible-module | WeilConjectures.AlgebraicGeometry.Ample | AlgebraicGeometry.Scheme.Modules.IsAmple |

The tensor-pullback functor is publicly imported by the dependency's recorded
section-adjunction module from its upstream owning module. Its explicit tensor
construction, and the full invertibility and ampleness definitions, were read.
Every stated proof dependency's module is also imported, with plain imports for
proof-only dependencies: fibre-product limits, affine-limit ampleness descent,
Noetherian fibre-ampleness neighbourhood, invertible pullback/tensor, affine
transition limits, residue-field limits and proper-basic, together with the
Mathlib pullback, separatedness and proper-base-change interfaces.

Edge cases checked before writing and rechecked against the completed signature:

- For a singleton index set, the conclusion reduces, up to identity pullback,
  to the recorded Noetherian fibre-ampleness neighbourhood theorem. The fibre
  ampleness conjunct repeats the hypothesis, at that same sole stage.
- Empty fibres are permitted. Absolute ampleness uses compactness and a
  condition quantified over points, so it allows the empty scheme. Properness
  allows shrinking away from the closed image when a stage fibre is empty.
- No nonempty-fibre, surjectivity, flatness, finite-type-over-a-fixed-ring,
  Cartesian-transition, field-characteristic or projectivity hypothesis occurs.
- If the base limit is empty, the universal assertion over `x` is vacuous,
  as in the node. No inhabitedness of either limit scheme is assumed.
- An arbitrary invertible `M` with the given pullback isomorphism is retained.
  The statement does not identify it definitionally with the initial pullback.
- Distinct source/base diagrams and arbitrary compatible proper maps are allowed;
  no stronger base-change model is substituted for the given systems.

Searches performed for an existing statement (all on 2026-10-24):

- `msearch.py`, LeanFinder: "An ample line bundle on a limit fibre of an inverse
  system of proper morphisms with affine transitions descends to a stage fibre
  and an affine neighbourhood over a Noetherian base". Eight hits concern affine
  transition limits, sections, affine opens and morphism descent. No matching
  ampleness statement.
- `msearch.py`, Loogle: `IsAmple, IsProper, IsLimit`. Zero hits; the service reports
  unknown identifier `IsAmple` (the ampleness definition is project-specific).
- `msearch.py`, grep: `ample.*(fiber|fibre|limit)|(fiber|fibre|limit).*ample`
  restricted to Mathlib `AlgebraicGeometry`. Zero hits.
- `msearch.py`, LeanSearch: "Ampleness of an invertible sheaf on a limit fibre
  descends to a finite stage and an affine neighbourhood for proper morphisms
  over Noetherian bases". Eight hits concern general descent, properness and
  affine-limit sections, with no matching statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-trf-model-fibre-ample-open|model_fibre_ample|exists.*[Aa]mple|[Aa]mple.*[Ff]ib`
  finds the recorded descent and Noetherian-neighbourhood dependencies and other
  ampleness lemmas, but no theorem with both conclusions for these systems.
  The more general ample-neighbourhood theorem addresses a single proper map,
  not finite-stage descent. No matching declaration was found upstream.
- `rg` of `dag/lean_names_upstream.json` and the two source trees for the item id,
  `model_fibre_ample`, and the chosen name `exists_affine_isAmple_of_limit_fiber`
  found no existing declaration. No duplicate notion is defined in this delivery.

There is no statement correction, disputed statement, new node or dependency
repair. The natural-language proof in the declaration follows all six existing
DAG steps and names the dependencies used by each step.

Validation: the prescribed `scompile.py Q61 lem-trf-model-fibre-ample-open` compiled
the file successfully in sandbox and library module modes (1.9 seconds each),
with no errors or warnings. The delivery dry run recompiles the final module
and runs the maintainer's preflight on the server.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
