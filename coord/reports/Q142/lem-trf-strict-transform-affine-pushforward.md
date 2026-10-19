## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_moduleStrictTransform_affinePushforward`.
Its only theorem has proof `sorry`. There are no new definitions, helper nodes, dependency
repairs, or statement corrections. The node copy changes only `lean`.

Source read: `literature/stacks-project/divisors.tex`, the strict-transform notation and
Definition 080D at lines 8749–8799, and Lemma 080G (`lemma-strict-transform-affine`), its
statement and complete proof at lines 8908–8939. The source compares affine pushforward
with quotienting by exceptional-support sections. The node retains its finite-type-centre
restriction. The module docstring and theorem docstring explain all six DAG proof steps.

Hypotheses and conclusions, clause by clause:

- Schemes S, X, and Y: `{X Y S : Scheme.{u}}`, with every universe explicitly bound.
- Y is an S-scheme: `(f : Y ⟶ S)`. The S-structure on X is `g ≫ f`, so `(g : X ⟶ Y)` is
  an S-morphism. This parametrizes every S-morphism: an independently named X-structure
  equals this composite by its required commutative triangle. There is no restriction on
  the structure morphisms, the base, or the schemes.
- g is affine: `[IsAffineHom g]`, using the exact Mathlib preimage-of-affines definition.
- A quasi-coherent ideal I in O_S: `(I : S.IdealSheafData)`. This is the existing carrier
  for quasi-coherent ideals, not an unbundled ideal or an arbitrary subsheaf.
- I is of finite type: `[I.toModules.IsFiniteType]`.
- Its blowup b and modified base S^b: `I.blowupMap` and `I.blowup`, from the recorded
  global-blowup construction. They are not independently quantified modifications.
- The module F is `(F : X.Modules)`, with `[F.IsQuasicoherent]`.
- The two modified schemes are `pullback (g ≫ f) I.blowupMap` and
  `pullback f I.blowupMap`. Their projections in the base-change map are the recorded
  `pullback.fst` maps. The other projections are intrinsic to these same fibre products
  and to `moduleStrictTransform`.
- The displayed `pullback.map (g ≫ f) I.blowupMap f I.blowupMap g (𝟙 _) (𝟙 _) ...` is
  exactly g_b, using g on X and identities on S^b and S. Both equality arguments are
  existing identity laws. Its square with g and the first projections commutes by the
  defining projection identities of `pullback.map`.
- F^b is exactly `moduleStrictTransform (g ≫ f) I F`, reusing the recorded definition
  `cokernel (kernel.ι (moduleStrictTransformRestriction ...))`. It retains I.
- g_*F is `(pushforward g).obj F`. Its quasi-coherence is supplied by the existing theorem
  `isQuasicoherent_pushforward_of_isAffineHom g F` as an explicit proof argument to the
  right-hand `@moduleStrictTransform`, rather than added as a hypothesis. Proof
  irrelevance makes this the same strict-transform object for any proof of quasi-coherence.
- The conclusion is an isomorphism `e : (pushforward g_b).obj F^b ≅ (g_*F)^b` in the module
  category of the modified Y, as required.
- Canonicity is specified by `∃! e` and the equation
  `moduleBaseChangeMap ... F ≫ (pushforward g_b).map π_X ≫ e.hom = π_Y`, where both π are
  the actual cokernel projections defining the strict transforms. Thus the comparison is
  precisely the isomorphism induced from affine base change on quotients, as in proof
  Step 6. This adds no independent geometric conclusion: it spells out “canonical”.
  Uniqueness follows because affine base change and the pushed-forward quotient give an
  epic composite. No arbitrary map or unspecified comparison is assumed.

Dependency interfaces inspected and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; their full source
  definitions and docstrings were read.
- `pqf-def-coherent`: `WeilConjectures.AlgebraicGeometry.Coherent`, fetched with
  `scompile.py --source` because it is absent in the older source checkout. Its module
  documents Mathlib's `SheafOfModules.IsQuasicoherent` and `IsFiniteType`, which are the
  exact two notions used; `RingedSpace.IsCoherent` is not needed for this statement.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`; source and docstrings read.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`; read its complete class signature.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and `pullback.map`;
  full signatures and docstrings read. Scheme pullbacks are supplied by the imported
  `Mathlib.AlgebraicGeometry.Pullbacks` through the strict-transform dependency.
- `def-trf-module-strict-transform`: `Sheaf.AlgebraicGeometry.ModuleStrictTransform`,
  `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform`, and
  `moduleStrictTransformRestriction`; the entire recorded module was read, including its
  canonical restriction unit, support kernel, and quotient construction.
- Canonicity uses the existing `moduleBaseChangeMap` from
  `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction` (publicly imported).
  Its adjoint-defined signature and construction were inspected. The affine-pushforward
  theorem and proof plan were read using `scompile.py --source
  WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`.
- The explicit quasi-coherence proof is
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`; its full
  signature and docstring were read. It is the same quasi-coherence assertion supplied
  by the affine-base-change dependency, without requiring an additional pullback square.
- All recorded stated proof-dependency modules are imported without `public`, except
  those needed in the signature. The Mathlib proof leaves contribute Affine,
  QuasiSeparated, AffineScheme, Limits, Prime.Topology, and Ideal.Span. No proof import
  is omitted for a cycle.

Edge cases checked mathematically before writing: F = 0, g = identity, an empty X or Y,
empty S, the unit ideal (blowup is S, exceptional locus empty, quotient unchanged), and
zero ideal (blowup empty, both sides modules on the empty modified base). None requires
nonemptiness or an excluded case. Pulling the exceptional generator to X can make it a
zero divisor; neither statement nor definition assumes otherwise. No flatness,
Noetherianity, finite presentation, separation, or regularity assumption was added.

Searches for an existing declaration:

- `msearch.py ... leanfinder "strict transform of a quasi coherent module commutes with
  affine pushforward"`: 8 hits, all ordinary `Scheme.Modules.pushforward` declarations
  and pseudofunctor compatibility; no strict-transform comparison.
- `msearch.py ... loogle '"strictTransform", "pushforward"'`: 0 hits.
- `msearch.py ... leansearch "Strict transform of a quasicoherent sheaf commutes with
  direct image by an affine morphism"`: 8 hits, including ideal-sheaf maps,
  `instAdditivePushforward`, and base-change property lemmas; no matching statement.
- `msearch.py ... grep 'strictTransform|strict_transform|strict transform'`: 0 Mathlib hits.
- `rg -n 'strictTransform|strict_transform|strict transform'` on the named upstream and
  side Lean trees: upstream has scheme strict transforms and an affine module-torsion
  discussion; the side library has `ModuleStrictTransform` and unrelated scheme-transform
  results. No module strict-transform affine-pushforward theorem exists.
- `grep -rn 'lem-trf-strict-transform-affine-pushforward'` on upstream: no hit.
- Narrow `rg` for `moduleStrictTransform|strict_transform.*push|strictTransform.*push`
  across the upstream-name index and both project trees: only the dependency's module
  strict-transform definitions, no comparison theorem.
- `tools/lean_names_upstream.py show lem-trf-strict-transform-affine-pushforward`: consulted
  the upstream indices (633 blueprint nodes / 913 names and 2482 docstring nodes / 3986
  names); the item has no upstream declaration. No existing declaration was rebound.

Validation: the required `scompile.py Q142 lem-trf-strict-transform-affine-pushforward
<module>` succeeded for the sandbox and library module, with no errors or warnings.
An initial private-import visibility error for `moduleBaseChangeMap` was fixed by publicly
importing its owning upstream module; the recompile passed. Every variable and universe is
explicit, and no file-local notation, instance, or hidden definition is used.
There is no STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by Q142

Author self-check, not an independent review: I reopened the final node and module and
checked the six original statement dependencies, the finite-type hypothesis, the use of
quasi-coherence only (not coherence), the direction of both fibre-product projections,
and the type and direction of the quotient-map equation. The source specifies the
comparison induced by affine base change, and the displayed equation is exactly that
comparison. The explicit proof of quasi-coherence on g_*F adds no hypothesis. The only
implementation mismatch found was the private import noted above, repaired before the
successful compile. The dispatcher assigns independent review to the maintainer; no
additional agent was started.
