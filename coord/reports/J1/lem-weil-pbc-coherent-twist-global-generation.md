## Worker report

The module states eventual finite global generation for every finite type quasi-coherent
module and every absolutely ample invertible module on a scheme. The only theorem has
proof `sorry`; its docstring carries all six proof steps of the node. No definitions,
new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{u})`, with arbitrary explicitly bound universe u.
- O_X-modules L and F: `(L F : X.Modules)`.
- Invertibility of L: `[L.IsInvertible]`, the recorded scheme-module notion.
- Absolute ampleness: `(hL : IsAmple X L)`, including quasi-compactness and the affine
  nonvanishing cover. No separate quasi-compactness, separation, Noetherian, projectivity,
  field, or coherence hypothesis is added.
- Quasi-coherence of F: `[F.IsQuasicoherent]`.
- Finite type of F: `[F.IsFiniteType]`; finite presentation/coherence is not required.
- d-fold tensor power: `L.tensorPow d`, including the structure sheaf at d = 0.
- Twisting F: `tensorObj F (L.tensorPow d)`, the sheafified tensor product over O_X.
- An integer threshold: `∃ d₀ : ℤ`.
- Every nonnegative tensor exponent at least that threshold:
  `∀ d : ℕ, d₀ ≤ (d : ℤ) → ...`. The node defines d-fold tensor products, hence
  nonnegative exponents; its dependency explicitly sets L^0 = O_X. An eventual bound
  on nonnegative exponents is equivalent to the usual integer-exponent formulation:
  one may always raise the threshold to max(d₀, 0). No negative tensor power or inverse
  is needed in this signature, and d = 0 is not excluded.
- A family of generating global sections:
  `∃ σ : (tensorObj F (L.tensorPow d)).GeneratingSections, ...`.
  Mathlib's `σ.s : σ.I → M.sections` consists of global sections, and its `σ.epi`
  is `Epi (M.freeHomEquiv.symm σ.s)`, exactly the evaluation map from the free
  sheaf/direct sum of structure sheaves. Epi is local surjectivity as a sheaf map;
  it does not assert surjectivity on sections of every open.
- Finitely many sections: `σ.IsFiniteType`, whose field is `Finite σ.I`.
  Bare `Nonempty M.GeneratingSections` would have omitted this finite-family clause.

Dependencies read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and
  AlgebraicGeometry.Scheme.Hom (available through Ample).
- def-weil-pbc-ample-invertible-module: Sheaf.AlgebraicGeometry.Ample,
  AlgebraicGeometry.Scheme.Modules.IsAmple, imported directly.
- def-sc-invertible-module: WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  AlgebraicGeometry.Scheme.Modules.IsInvertible, imported through Ample.
- pqf-def-coherent: Sheaf.AlgebraicGeometry.Coherent, imported directly. Its docstring
  records that the first two clauses are Mathlib's SheafOfModules.IsQuasicoherent and
  SheafOfModules.IsFiniteType; those are the clauses used here, rather than IsCoherent.
- def-pur-sheaf-tensor-product: Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct,
  imported directly; its documented tensor structure is the source's
  SheafOfModules.monoidalCategory and tensorObjIsoSheafification, also used by
  Scheme.Modules.tensorObj and tensorPow from the Invertible module. PositiveTensorPower
  is not a second tensor structure and is unnecessary because the scheme tensorPow
  already includes degree zero and is the power used by the recorded IsAmple predicate.
- def-weil-pbc-generating-sections: Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators,
  SheafOfModules.GeneratingSections and GeneratingSections.IsFiniteType.

Edge cases checked before writing:

- Empty scheme: allowed; no Nonempty X binder. The ampleness cover condition is vacuous
  but quasi-compactness still holds, and the empty family generates its zero module.
- Zero F: allowed, locally finite type and quasi-coherent. The empty family is permitted
  by GeneratingSections.I and Finite; no positive number of generators is imposed.
- d = 0: tensorPow 0 is O_X, and is included whenever the chosen threshold permits it.
- Arbitrary characteristic and base: no base field or ring appears.
- Arbitrary universe u: all schemes and their modules use their standard universe;
  a finite index set always has a representative in Type u.
- An affine scheme with ample trivial L reduces to finite generation of affine finite
  type quasi-coherent modules, as expected.

Source checked: https://stacks.math.columbia.edu/tag/01Q3, Proposition 28.27.13,
(1) ⇒ (7), and the proof following (1)–(6). The repository has no local
literature/stacks-project/properties.tex, so the source was read online. Finite generation
is the finite-family form established by the node's EGA proof, stronger in presentation
than merely writing arbitrary global generation, but equivalent here by finite type
and quasi-compactness. The natural-language proof is retained in six steps.

Searches made:

- msearch.py leanfinder: "finite type quasi coherent module on a scheme becomes generated
  by finitely many global sections after sufficiently large ample invertible tensor twist".
  Eight hits: IsFiniteType, localGeneratorsData and finite GeneratingSections definitions;
  no ample-twist theorem.
- msearch.py loogle: "SheafOfModules.GeneratingSections,
  AlgebraicGeometry.Scheme.Modules.tensorPow". Zero hits; source tensorPow unknown to Loogle.
- msearch.py grep: "ample|globally generated", AlgebraicGeometry. Ten unrelated Mathlib
  hits (including example substring hits); no matching theorem.
- rg over WeilConjectures and lean/Sheaf for the item id, globallyGenerated,
  global.*generat and exists.*GeneratingSections: found global-generation infrastructure,
  sibling curve lemmas, and Serre.lean theorem A. Read its full signature and docstring:
  exists_generatingSections_tensor_twist requires a closed immersion into projective space
  over a field and finite presentation; it is not this general absolute ample theorem.
  No occurrence of this item id in source Lean.
- rg for the chosen declaration name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

No STATEMENT-DISPUTED issue or node fault found. Server compilation and delivery preflight
results are recorded after verification below.

Verification: scompile.py compiled the single module in 2.4 seconds with exit code 0
and no warnings. deliver2.py --no-push printed OK: compilation and preflight passed
except for the independent second reading, which the second reader must supply.
Nothing was pushed, and no second-reading section was written by this worker.

## Second reading by J1

Statement list and correspondence:

- The scheme `X` is rendered by `(X : Scheme.{u})`; the universe is explicit and unrestricted.
- The ample invertible module `L` is `(L : X.Modules)` with `[L.IsInvertible]` and
  `hL : IsAmple X L`. `IsAmple` is the absolute Stacks 01PS predicate and includes
  quasi-compactness and the affine nonvanishing-locus condition; no extra separation,
  Noetherian, field, or projectivity hypothesis is present.
- The finite type quasi-coherent module `F` is `(F : X.Modules)` with
  `[F.IsQuasicoherent] [F.IsFiniteType]`, exactly the two clauses in `pqf-def-coherent`.
- The twist is `tensorObj F (L.tensorPow d)`, using the project's tensor product and
  natural tensor powers; `tensorPow 0` is the unit module, so degree zero is represented.
- The threshold is `∃ d₀ : ℤ`; exponents are `d : ℕ` with `d₀ ≤ (d : ℤ)`, which is the
  nonnegative tensor-power reading of the node's `d ≥ d₀`.
- Finite global generation is `∃ σ : (tensorObj F (L.tensorPow d)).GeneratingSections,
  σ.IsFiniteType`. `GeneratingSections` supplies global sections and an epimorphic
  evaluation map, while `IsFiniteType` supplies a finite index type.

Each object, hypothesis, and conclusion clause matches the node. The declaration compiled
with no unbound variables or universe metavariables. The node's source, Stacks 01Q3
(Proposition 28.27.13, implication (1) ⇒ (7)), states eventual global generation for
finite type quasi-coherent modules; the finite-family formulation here is the finite-cover
form used in the cited EGA proof and in the node's proof steps.

Edge cases checked: the empty scheme is admitted; the zero module is admitted and may use
an empty finite family; `d = 0` is admitted whenever the threshold permits it; arbitrary
characteristic and base are admitted; and the explicit scheme universe does not restrict
the statement. No mismatch was found, so no source or Lean repair was needed.

Searches were repeated with `rg` over `lean/Sheaf`, the upstream `WeilConjectures`, and
Mathlib, and with the recorded LeanSearch/Loogle/grep queries. Existing generating-section
and tensor-power infrastructure was found, but no theorem for ample twists of finite type
quasi-coherent modules. The nearby upstream `exists_generatingSections_tensor_twist` has
additional projective-over-a-field and finite-presentation hypotheses and is a different
statement. The module therefore remains the required declaration.

Verification: `scompile.py` compiled `AmpleTwistGlobalGeneration.lean` successfully with
exit code 0; no warnings were emitted. No mismatches or changes were made in this second
reading.
